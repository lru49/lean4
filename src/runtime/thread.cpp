/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <iostream>
#include <cstring>
#ifdef __linux__
#include <sched.h>
#include <unistd.h>
#include <fstream>
#include <string>
#include <cstdlib>
#include <cstdio>
#endif
#ifdef LEAN_WINDOWS
#include <windows.h>
#else
#include <pthread.h>
#endif
#include <lean/config.h>
#include "runtime/thread.h"
#include "runtime/interrupt.h"
#include "runtime/exception.h"
#include "runtime/alloc.h"
#include "runtime/stack_overflow.h"
#include "runtime/sstream.h"

#ifndef LEAN_DEFAULT_THREAD_STACK_SIZE
#ifdef LEAN_EMSCRIPTEN
#define LEAN_DEFAULT_THREAD_STACK_SIZE 8*1024*1024 // 8MB for 32-bit
#else
#define LEAN_DEFAULT_THREAD_STACK_SIZE 1024*1024*1024 // 1GB for 64-bit
#endif
#endif

namespace lean {
using runnable = std::function<void()>;

extern "C" LEAN_EXPORT void lean_initialize_thread() {
#ifdef LEAN_MIMALLOC
    // cache this thread's mimalloc theap for the allocation fast path; see `runtime/alloc_tls.h`
    lean_mi_theap_cache_init();
#endif
}

extern "C" LEAN_EXPORT void lean_finalize_thread() {
    run_thread_finalizers();
}

static void thread_main(void * p) {
    lean_initialize_thread();
    {
        std::unique_ptr<runnable> f(reinterpret_cast<runnable *>(p));
        (*f)();
    }
    lean_finalize_thread();
}

#if defined(LEAN_MULTI_THREAD)
size_t lthread::m_thread_stack_size = LEAN_DEFAULT_THREAD_STACK_SIZE;

void lthread::set_thread_stack_size(size_t sz) {
    m_thread_stack_size = sz + LEAN_STACK_BUFFER_SPACE;
}

size_t lthread::get_thread_stack_size() {
    return m_thread_stack_size;
}

static runnable mk_thread_proc(runnable const & p, size_t max) {
    return [=]() { set_max_heartbeat(max); p(); }; // NOLINT
}

#if defined(LEAN_WINDOWS)
/* Windows version */
struct lthread::imp {
    std::function<void(void)> m_proc;
    HANDLE                    m_thread;

    static DWORD WINAPI _main(void * p) {
        thread_main(p);
        return 0;
    }

    imp(runnable const & p) {
        std::unique_ptr<runnable> f = std::make_unique<runnable>(mk_thread_proc(p, get_max_heartbeat()));
        // Without `IS_A_RESERVATION`, `m_thread_stack_size` would be the initial *commit* size,
        // quickly exhausting the available address space with our large default stack size.
        m_thread = CreateThread(nullptr, m_thread_stack_size,
                                _main, f.get(), STACK_SIZE_PARAM_IS_A_RESERVATION, nullptr);
        if (m_thread == NULL) {
            throw exception((sstream() << "failed to create thread: " << GetLastError()).str());
        }
        f.release();  // Now owned by thread_main
    }

    ~imp() {
        CloseHandle(m_thread);
    }

    void join() {
        if (WaitForSingleObject(m_thread, INFINITE) == WAIT_FAILED) {
            throw exception("failed to join thread");
        }
    }
};
#else
/* OSX/Linux version based on pthreads */
struct lthread::imp {
    pthread_attr_t            m_attr;
    pthread_t                 m_thread;
    bool                      m_joined = false;

    static void * _main(void * p) {
        stack_guard guard;
        thread_main(p);
        return nullptr;
    }

    imp(runnable const & p) {
        pthread_attr_init(&m_attr);
        if (int err = pthread_attr_setstacksize(&m_attr, m_thread_stack_size); err != 0) {
            throw exception((sstream() << "failed to set thread stack size: " << strerror(err)).str());
        }
        std::unique_ptr<runnable> f = std::make_unique<runnable>(mk_thread_proc(p, get_max_heartbeat()));
        if (int err = pthread_create(&m_thread, &m_attr, _main, f.get()); err != 0) {
            throw exception((sstream() << "failed to create thread: " << strerror(err)).str());
        }
        f.release();  // Now owned by thread_main
    }

    ~imp() {
        pthread_attr_destroy(&m_attr);
        if (!m_joined) pthread_detach(m_thread);
    }

    void join() {
        m_joined = true;
        if (pthread_join(m_thread, nullptr)) {
            throw exception("failed to join thread");
        }
    }
};
#endif
lthread::lthread(std::function<void(void)> const & p):m_imp(new imp(p)) {}

lthread::~lthread() {}

void lthread::join() { m_imp->join(); }
#endif

/* setThreadStackSize (sz : USize) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_internal_set_thread_stack_size(size_t sz) {
    lthread::set_thread_stack_size(sz);
    return lean_box(0);
}

LEAN_EXPORT void set_thread_stack_size_from_env() {
    const char * stack_size_env = std::getenv("LEAN_STACK_SIZE_KB");
    if (stack_size_env) {
        size_t sz = std::strtoull(stack_size_env, nullptr, 10);
        sz = sz / 4 * 4 * 1024; // as in `Shell`
        if (sz > 0) {
            lthread::set_thread_stack_size(sz);
        }
    }
}

LEAN_EXPORT void run_with_thread_stack(std::function<void()> const & fn) {
    const char * use_thread_env = std::getenv("LEAN_MAIN_USE_THREAD");
    if (use_thread_env && std::strcmp(use_thread_env, "0") == 0) {
        fn();
    } else {
        // Start new thread to use given/default stack size
        lthread t(fn);
        t.join();
    }
}

extern "C" LEAN_EXPORT lean_object * lean_run_main(lean_object * (*main_fn)(int, char **), int argc, char ** argv) {
    set_thread_stack_size_from_env();
    lean_object * res = nullptr;
    run_with_thread_stack([&]() { res = main_fn(argc, argv); });
    return res;
}

typedef std::vector<std::pair<thread_finalizer, void*>> thread_finalizers;

void run_thread_finalizers_core(thread_finalizers & fns) {
    unsigned i = fns.size();
    while (i > 0) {
        --i;
        auto fn = fns[i].first;
        fn(fns[i].second);
    }
    fns.clear();
}

LEAN_THREAD_PTR(thread_finalizers, g_finalizers);

void delete_thread_finalizer_manager() {}

void register_thread_finalizer(thread_finalizer fn, void * p) {
    if (!g_finalizers)
        g_finalizers = new thread_finalizers();
    g_finalizers->emplace_back(fn, p);
}

void run_thread_finalizers(thread_finalizers * fns) {
    if (fns) {
        run_thread_finalizers_core(*fns);
        delete fns;
    }
}

void run_thread_finalizers() {
    run_thread_finalizers(g_finalizers);
    g_finalizers = nullptr;
}

/* lean-perf: `LEAN_CPU_AFFINITY`, a general opt-in affinity mask for every Lean executable (lean, lake, ...) on Linux.
   On SMT hosts (two hardware threads per physical core, e.g. Intel Hyper-Threading) a process confined to one thread per
   core never shares a core's execution resources with a sibling process; for a `lake build` of many single-threaded
   `lean` processes this removes the SMT contention tax measured in lean-perf (docs/levers/L-smt-contention.md: +5-6 % on
   a 32-core/64-thread r7i.16xlarge). Values:
     unset, "", "0", "off"      nothing (default)
     "one-per-core" / "cores"   keep, from the CURRENT affinity mask (so `taskset`/cgroups are respected), only the
                                lowest-numbered CPU of each physical core (`/sys/devices/system/cpu/cpuN/topology/
                                thread_siblings_list`); a no-op on hosts without SMT or when the result would be empty
     "<cpu list>"               an explicit list such as "0-31,33", intersected with the current mask
   The mask is set on the calling thread before any worker thread exists and is inherited by every thread and child
   process (Lake's `lean` children). `LEAN_CPU_AFFINITY_DEBUG=1` prints the resulting mask to stderr. Not Linux: ignored. */
#ifdef __linux__
static bool parse_cpu_list(char const * s, cpu_set_t & out) {
    CPU_ZERO(&out);
    char const * p = s;
    while (*p) {
        while (*p == ' ' || *p == ',') p++;
        if (!*p) break;
        char * end = nullptr;
        long a = std::strtol(p, &end, 10);
        if (end == p || a < 0 || a >= CPU_SETSIZE) return false;
        long b = a;
        p = end;
        if (*p == '-') {
            b = std::strtol(p + 1, &end, 10);
            if (end == p + 1 || b < a || b >= CPU_SETSIZE) return false;
            p = end;
        }
        for (long c = a; c <= b; c++) CPU_SET(c, &out);
        if (*p && *p != ',' && *p != ' ') return false;
    }
    return true;
}

static void apply_cpu_affinity_from_env() {
    char const * v = std::getenv("LEAN_CPU_AFFINITY");
    if (!v || !*v || std::strcmp(v, "0") == 0 || std::strcmp(v, "off") == 0) return;
    bool debug = std::getenv("LEAN_CPU_AFFINITY_DEBUG") != nullptr;
    cpu_set_t cur;
    if (sched_getaffinity(0, sizeof(cur), &cur) != 0) return;
    cpu_set_t want;
    if (std::strcmp(v, "one-per-core") == 0 || std::strcmp(v, "cores") == 0) {
        CPU_ZERO(&want);
        for (int c = 0; c < CPU_SETSIZE; c++) {
            if (!CPU_ISSET(c, &cur)) continue;
            std::string path = "/sys/devices/system/cpu/cpu" + std::to_string(c) + "/topology/thread_siblings_list";
            std::ifstream in(path);
            std::string list;
            if (!in || !std::getline(in, list)) { CPU_SET(c, &want); continue; }  // no topology: keep the CPU
            cpu_set_t sib;
            if (!parse_cpu_list(list.c_str(), sib)) { CPU_SET(c, &want); continue; }
            // keep `c` only if no lower-numbered sibling of its core is in the current mask
            bool keep = true;
            for (int d = 0; d < c; d++) if (CPU_ISSET(d, &sib) && CPU_ISSET(d, &cur)) { keep = false; break; }
            if (keep) CPU_SET(c, &want);
        }
    } else {
        if (!parse_cpu_list(v, want)) {
            if (debug) std::fprintf(stderr, "[affinity] LEAN_CPU_AFFINITY=%s: cannot parse, ignored\n", v);
            return;
        }
        CPU_AND(&want, &want, &cur);
    }
    int n = CPU_COUNT(&want), ncur = CPU_COUNT(&cur);
    if (n == 0 || n == ncur) { if (debug) std::fprintf(stderr, "[affinity] LEAN_CPU_AFFINITY=%s: no change (%d of %d cpus)\n", v, n, ncur); return; }
    if (sched_setaffinity(0, sizeof(want), &want) != 0) {
        if (debug) std::fprintf(stderr, "[affinity] sched_setaffinity failed\n");
        return;
    }
    if (debug) {
        std::string s;
        for (int c = 0; c < CPU_SETSIZE; c++) if (CPU_ISSET(c, &want)) { if (!s.empty()) s += ","; s += std::to_string(c); }
        std::fprintf(stderr, "[affinity] LEAN_CPU_AFFINITY=%s: pid %d confined to %d of %d cpus: %s\n", v, (int)getpid(), n, ncur, s.c_str());
    }
}
#endif

void initialize_thread() {
#ifdef __linux__
    apply_cpu_affinity_from_env();
#endif
}
void finalize_thread() {}
}
