/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdlib>
#ifdef LEAN_MIMALLOC
#include <mimalloc.h>
#endif
#include <lean/lean.h>
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/alloc.h"

#ifndef LEAN_MIMALLOC
// with mimalloc, `runtime/mimalloc.cpp` defines it instead (see `runtime/alloc_tls.h`)
#ifdef _MSC_VER
extern "C" __declspec(thread) lean_runtime_tls lean_g_tls = {};
#else
extern "C" __thread lean_runtime_tls lean_g_tls = {};
#endif
#endif

namespace lean {

void initialize_alloc() {
#ifdef LEAN_MIMALLOC
    // the main thread does not go through `lean_initialize_thread`; see `runtime/alloc_tls.h`
    lean_mi_theap_cache_init();
    /* Lean's allocation pattern is churn: large terms and caches are built, freed and rebuilt within one process
       (an elaboration + kernel check per declaration). mimalloc's default returns freed segments to the OS one second
       after they empty (`purge_delay` = 1000 ms), so the next declaration re-faults the same pages in. Keeping the
       memory (no purging) removed ~0.8 % of the wall of a kernel-heavy project build (lean-perf, mimalloc 2.2.7);
       the process's peak RSS is unchanged (purging never lowers the peak). The environment keeps the last word:
       `MIMALLOC_PURGE_DELAY=<ms>` restores purging. */
    if (getenv("MIMALLOC_PURGE_DELAY") == nullptr)
        mi_option_set(mi_option_purge_delay, -1);
#endif
}

void finalize_alloc() {
}

void set_heartbeats(uint64_t count) {
    lean_g_tls.heartbeat = count;
}

void add_heartbeats(uint64_t count) {
    lean_g_tls.heartbeat += count;
}

extern "C" LEAN_EXPORT void lean_inc_heartbeat() {
    add_heartbeats(1);
}

uint64_t get_num_heartbeats() {
    return lean_g_tls.heartbeat;
}

}
