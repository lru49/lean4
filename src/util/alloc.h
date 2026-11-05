/*
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
*/
#pragma once
#include <cstdlib>
#include <lean/config.h>
#include <unordered_map>
#include <unordered_set>

#ifdef LEAN_MIMALLOC
#include <lean/mimalloc.h>
#endif

namespace lean {

// We do not override `new` to avoid FFI issues for users but use `lean::allocator`
// explicitly where using the custom allocator is important.

#ifdef LEAN_MIMALLOC
template<class T> using allocator = mi_stl_allocator<T>;
#else
template<class T> using allocator = std::allocator<T>;
#endif

// `unordered_map/set` allocates per insert, so specializing to the custom allocator can
// save significant time for maps with frequent inserts.

template<
    class Key,
    class T,
    class Hash = std::hash<Key>,
    class KeyEqual = std::equal_to<Key>,
    class Allocator = lean::allocator<std::pair<const Key, T>>
> using unordered_map = std::unordered_map<Key, T, Hash, KeyEqual, Allocator>;

template<
    class Key,
    class Hash = std::hash<Key>,
    class KeyEqual = std::equal_to<Key>,
    class Allocator = lean::allocator<Key>
> using unordered_set = std::unordered_set<Key, Hash, KeyEqual, Allocator>;

/* Zero-initialized raw blocks from the same allocator as the containers above (the open-addressing tables of
   `replace_fn.h`, `expr_eq_fn.cpp` and `expr_maps.h` grow through these). With mimalloc the blocks come from the
   calling thread's heap and are released to it like the hash-map nodes they replaced; glibc's per-thread arenas
   instead retained the freed tables of concurrent kernel checks (+4-6 % peak RSS at -j 8 on a large `decide` module). */
inline void * alloc_zeroed_block(size_t n, size_t size) {
#ifdef LEAN_MIMALLOC
    return mi_calloc(n, size);
#else
    return std::calloc(n, size);
#endif
}
inline void free_block(void * p) {
#ifdef LEAN_MIMALLOC
    mi_free(p);
#else
    std::free(p);
#endif
}
};
