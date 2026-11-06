/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Persistent native-code cache for imported modules ("transparent precompileModules").

Code of imported modules that are not part of the running executable (e.g. every Mathlib tactic, linter
and environment extension when Lean is used as a library user) is run by the IR interpreter. The
interpreter already prefers native code: a declaration whose (mangled) symbol is found with `dlsym` is
called natively, and `runModInit` runs a module's native initializer when its symbol exists, exactly as
for `--load-dynlib` / Lake's `precompileModules`. This file adds a cache lookup in front of that:

  $LEAN_NATIVE_CACHE (default $XDG_CACHE_HOME/lean/native, else ~/.cache/lean/native)
    /<githash>-<target>/bundles/<id>.so        shared object with the compiled C of a set S of modules
    /<githash>-<target>/bundles/<id>.manifest  "lean-native-bundle 2 <githash> <toolchain id>" then one line per module
                                               of S: "<st_dev> <st_ino> <size> <mtime_ns> <.olean path>"

Bundles are produced by `lake build`'s background populate job (src/lake/Lake/CLI/NativeCache.lean) or by
tools/dj-native-populate.py; a bundle is produced by a populate step (compile the C that Lake already emits for every module, link
the objects; S must be closed under imports, apart from modules of the toolchain itself). At the first
`runModInit` of a process (all `.olean` files of the import have been read at that point), every
manifest is checked: a bundle is usable iff EVERY module of S was imported by this process from the
very same file (same device and inode, size and modification time, as recorded by
`native_cache_note_olean` from the `fstat` of the open file while it was read; the path is informative
only, so symlinked package directories do not matter, and a rebuilt or replaced file never matches). Then all of S's code is code of imported modules of this exact build, S is closed
under imports so all of its symbols resolve, and no name in it can belong to a non-imported module.
The largest usable bundle is loaded with `dlopen(RTLD_LAZY | RTLD_GLOBAL)`, as `--load-dynlib` does;
nothing else changes: values computed natively are the values the interpreter computes for the same IR.

Off when the directory does not exist (one `stat` per process) or with LEAN_NATIVE_CACHE=0.
LEAN_NATIVE_CACHE_VERBOSE=1 reports the decision on stderr.
Limitation (as for `--load-dynlib`): a process that imports twice keeps the code loaded at its first
import; the cmdline frontend and Lake's worker processes import once.
*/
#include <string>
#include <algorithm>
#include <vector>
#include <unordered_map>
#include <mutex>
#include <fstream>
#include <sstream>
#include <iostream>
#include <cstdlib>
#include <cstring>
#include <sys/stat.h>
#include "library/native_cache.h"
#include "githash.h"
#include "runtime/object.h"
#include "runtime/io.h"
#if !defined(LEAN_WINDOWS) && !defined(LEAN_EMSCRIPTEN)
#include <dirent.h>
#include <dlfcn.h>
#include <fcntl.h>
#include <time.h>
#define LEAN_NATIVE_CACHE_SUPPORTED 1
#endif

namespace lean {
#ifdef LEAN_NATIVE_CACHE_SUPPORTED
namespace {
struct file_stamp { long long m_size; long long m_mtime_ns; };
struct file_id {
    unsigned long long m_dev, m_ino;
    bool operator==(file_id const & o) const { return m_dev == o.m_dev && m_ino == o.m_ino; }
};
struct file_id_hash { size_t operator()(file_id const & f) const { return std::hash<unsigned long long>()(f.m_ino * 0x9E3779B97F4A7C15ull ^ f.m_dev); } };

#if defined(__x86_64__)
static char const * g_target = "x86_64";
#elif defined(__aarch64__)
static char const * g_target = "aarch64";
#else
static char const * g_target = "other";
#endif

struct native_cache_state {
    bool m_enabled = false;
    bool m_verbose = false;
    std::string m_bundles;  // <cache>/<githash>-<target>/bundles
    std::mutex m_mutex;
    std::unordered_map<file_id, file_stamp, file_id_hash> m_seen;
    native_cache_state() {
        char const * v = getenv("LEAN_NATIVE_CACHE");
        if (v && (strcmp(v, "0") == 0 || strcmp(v, "off") == 0)) return;
        std::string dir;
        if (v && *v) {
            dir = v;
        } else if (char const * x = getenv("XDG_CACHE_HOME"); x && *x) {
            dir = std::string(x) + "/lean/native";
        } else if (char const * h = getenv("HOME"); h && *h) {
            dir = std::string(h) + "/.cache/lean/native";
        } else {
            return;
        }
        m_bundles = dir + "/" + LEAN_GITHASH + "-" + g_target + "/bundles";
        struct stat st;
        m_enabled = stat(m_bundles.c_str(), &st) == 0 && S_ISDIR(st.st_mode);
        char const * vb = getenv("LEAN_NATIVE_CACHE_VERBOSE");
        m_verbose = vb && *vb && strcmp(vb, "0") != 0;
    }
};

static std::once_flag g_load_once;  // the automatic bundle choice happens at most once per process

static native_cache_state & get_state() {
    static native_cache_state * s = new native_cache_state();  // never destroyed: used until exit
    return *s;
}

static bool ends_with(std::string const & s, char const * suffix) {
    size_t n = strlen(suffix);
    return s.size() >= n && s.compare(s.size() - n, n, suffix) == 0;
}

/* Identity of the running toolchain's shared runtime: "<name>:<dev>:<ino>:<size>:<mtime_ns>" of every
   libleanshared*.so next to the object that contains this code (sorted by name, ';'-separated), or of
   that object itself when it is not a libleanshared (statically linked executable). Two builds that
   share a githash (e.g. differently patched toolchains) have different files, so a bundle compiled
   against another build's lean.h/runtime is a miss, never a mismatch. */
static std::string file_key(std::string const & path) {
    struct stat st;
    if (stat(path.c_str(), &st) != 0) return "";
#if defined(__APPLE__)
    struct timespec const & mt = st.st_mtimespec;
#else
    struct timespec const & mt = st.st_mtim;
#endif
    return std::to_string(static_cast<unsigned long long>(st.st_dev)) + ":" +
        std::to_string(static_cast<unsigned long long>(st.st_ino)) + ":" + std::to_string(static_cast<long long>(st.st_size)) + ":" +
        std::to_string(static_cast<long long>(mt.tv_sec) * 1000000000LL + mt.tv_nsec);
}

static std::string const & toolchain_id() {
    static std::string * id = [] {
        std::string r;
        Dl_info info;
        if (dladdr(reinterpret_cast<void *>(&file_key), &info) && info.dli_fname) {
            std::string self = info.dli_fname;
            size_t slash = self.rfind('/');
            std::string dir = slash == std::string::npos ? "." : self.substr(0, slash);
            std::string base = slash == std::string::npos ? self : self.substr(slash + 1);
            std::vector<std::string> names;
            if (base.compare(0, 13, "libleanshared") == 0) {
                if (DIR * d = opendir(dir.c_str())) {
                    while (struct dirent * e = readdir(d)) {
                        std::string n = e->d_name;
                        if (n.compare(0, 13, "libleanshared") == 0 && ends_with(n, ".so")) names.push_back(n);
                    }
                    closedir(d);
                }
                std::sort(names.begin(), names.end());
            } else {
                names.push_back(base);
            }
            for (std::string const & n : names) {
                if (!r.empty()) r += ";";
                r += n + ":" + file_key(dir + "/" + n);
            }
        }
        return new std::string(r);
    }();
    return *id;
}

/* Returns the number of modules of the bundle if every module listed in `manifest` was imported from the
   same file, 0 otherwise. */
static size_t check_manifest(native_cache_state & s, std::string const & manifest, std::string & why) {
    std::ifstream in(manifest);
    if (!in) { why = "unreadable"; return 0; }
    std::string magic, githash, tcid; int version = 0;
    in >> magic >> version >> githash >> tcid;
    if (magic != "lean-native-bundle" || version != 2 || githash != LEAN_GITHASH) { why = "bad header"; return 0; }
    if (tcid != toolchain_id()) { why = "built for another toolchain build (" + tcid + " vs " + toolchain_id() + ")"; return 0; }
    size_t n = 0;
    unsigned long long dev, ino; long long size, mtime_ns; std::string path;
    while (in >> dev >> ino >> size >> mtime_ns) {
        in.get();  // the single blank before the path
        if (!std::getline(in, path)) { why = "truncated"; return 0; }
        auto it = s.m_seen.find(file_id { dev, ino });
        if (it == s.m_seen.end()) { why = "not imported: " + path; return 0; }
        if (it->second.m_size != size || it->second.m_mtime_ns != mtime_ns) { why = "changed: " + path; return 0; }
        n++;
    }
    if (n == 0) why = "empty";
    return n;
}
}

void native_cache_note_olean(std::string const & fn, struct stat const & st) {
    native_cache_state & s = get_state();
    if (!s.m_enabled || !ends_with(fn, ".olean")) return;
#if defined(__APPLE__)
    struct timespec const & mt = st.st_mtimespec;
#else
    struct timespec const & mt = st.st_mtim;
#endif
    file_stamp fs { static_cast<long long>(st.st_size), static_cast<long long>(mt.tv_sec) * 1000000000LL + mt.tv_nsec };
    file_id id { static_cast<unsigned long long>(st.st_dev), static_cast<unsigned long long>(st.st_ino) };
    std::lock_guard<std::mutex> lock(s.m_mutex);
    s.m_seen[id] = fs;
}

void native_cache_load_once() {
    std::call_once(g_load_once, [] {
        native_cache_state & s = get_state();
        if (!s.m_enabled) return;
        std::lock_guard<std::mutex> lock(s.m_mutex);
        if (s.m_seen.empty()) return;
        DIR * d = opendir(s.m_bundles.c_str());
        if (!d) return;
        std::string best; size_t best_n = 0;
        while (struct dirent * e = readdir(d)) {
            std::string f = e->d_name;
            if (!ends_with(f, ".manifest")) continue;
            std::string m = s.m_bundles + "/" + f;
            std::string why;
            size_t n = check_manifest(s, m, why);
            if (s.m_verbose)
                std::cerr << "[native-cache] " << f << ": " << (n ? "usable, " + std::to_string(n) + " modules" : "rejected (" + why + ")") << "\n";
            if (n > best_n) { best_n = n; best = m.substr(0, m.size() - strlen(".manifest")) + ".so"; }
        }
        closedir(d);
        if (best_n == 0) return;
        if (void * h = dlopen(best.c_str(), RTLD_LAZY | RTLD_GLOBAL)) {
            (void)h;  // never closed: its code may be referenced until exit
            // recency for the cache's LRU eviction: refresh the manifest's mtime at most once an hour
            std::string man = best.substr(0, best.size() - 3) + ".manifest";
            struct stat mst; struct timespec now;
            if (stat(man.c_str(), &mst) == 0 && clock_gettime(CLOCK_REALTIME, &now) == 0 &&
                now.tv_sec - static_cast<long long>(mst.st_mtime) > 3600)
                utimensat(AT_FDCWD, man.c_str(), nullptr, 0);
            if (s.m_verbose) std::cerr << "[native-cache] loaded " << best << " (" << best_n << " modules)\n";
        } else if (s.m_verbose) {
            std::cerr << "[native-cache] dlopen failed: " << dlerror() << "\n";
        }
    });
}

/* `--incr-load` snapshots (module.cpp) bake closures into the region and record the shared objects
   their code pointers point into. A snapshot saved by a process that had loaded a bundle needs that
   bundle: load exactly the recorded file (the path names a content-addressed bundle) before the
   relocation. A process that starts from a snapshot must not choose a bundle on its own afterwards:
   the snapshot already holds the initialized environment (native or interpreted), and loading a
   bundle later would run module initializers a second time. */
bool native_cache_load_recorded_bundle(std::string const & path) {
    if (!ends_with(path, ".so")) return false;
    std::string man = path.substr(0, path.size() - 3) + ".manifest";
    struct stat st;
    if (stat(man.c_str(), &st) != 0) return false;  // not a native-cache bundle (or evicted)
    bool ok = false;
    std::call_once(g_load_once, [] {});  // no automatic choice after this
    if (void * h = dlopen(path.c_str(), RTLD_LAZY | RTLD_GLOBAL)) { (void)h; ok = true; }
    if (get_state().m_verbose)
        std::cerr << "[native-cache] snapshot needs " << path << ": " << (ok ? "loaded" : dlerror()) << "\n";
    return ok;
}

void native_cache_snapshot_loaded() {
    std::call_once(g_load_once, [] {});
}

/* Lake.NativeCache.fileKey (path : @& String) : IO String: the identity the loader checks */
extern "C" LEAN_EXPORT obj_res lean_native_cache_file_key(b_obj_arg path, obj_arg) {
    struct stat st;
    if (stat(lean_string_cstr(path), &st) != 0)
        return io_result_mk_error((std::string("native cache: cannot stat ") + lean_string_cstr(path)).c_str());
#if defined(__APPLE__)
    struct timespec const & mt = st.st_mtimespec;
#else
    struct timespec const & mt = st.st_mtim;
#endif
    std::string k = std::to_string(static_cast<unsigned long long>(st.st_dev)) + " " +
        std::to_string(static_cast<unsigned long long>(st.st_ino)) + " " + std::to_string(static_cast<long long>(st.st_size)) + " " +
        std::to_string(static_cast<long long>(mt.tv_sec) * 1000000000LL + mt.tv_nsec);
    return io_result_mk_ok(lean_mk_string(k.c_str()));
}
#else
void native_cache_note_olean(std::string const &, struct stat const &) {}
void native_cache_load_once() {}
bool native_cache_load_recorded_bundle(std::string const &) { return false; }
void native_cache_snapshot_loaded() {}
extern "C" LEAN_EXPORT obj_res lean_native_cache_file_key(b_obj_arg, obj_arg) {
    return io_result_mk_error("native cache: not supported on this platform");
}
#endif
}
