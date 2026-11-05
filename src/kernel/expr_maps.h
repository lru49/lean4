/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include <cstdlib>
#include "util/alloc.h"
#include "kernel/expr.h"

namespace lean {
// Maps based on structural equality. That is, two keys are equal iff they are structurally equal
template<typename T>
using expr_map = typename lean::unordered_map<expr, T, expr_hash, std::equal_to<expr>>;

/** \brief Cache from expressions to `T` keyed by structural equality (`std::equal_to<expr>`, i.e. `is_equal`), as
    `expr_map<T>`, but as an open-addressing table (linear probing, power-of-two capacity, load factor <= 2/3) of
    16-byte `{key, value}` entries: no node is allocated per entry, and the structural hash is read from the key object
    itself (an `Expr` stores it in its header), so the table costs 24-48 B per entry over a doubling cycle, below the
    ~48 B of a `std::unordered_map` node (a stored hash made it 36-72 B and, with up to eight kernel checks running at
    once, +0.6 GB of peak RSS on a large `decide` module). Owns one reference to every key and value. Used for the kernel type checker's
    per-declaration caches (`infer_type`, `whnf_core`, `whnf`, `unfold`), where the `std::unordered_map` node
    allocation, rehashing and teardown took 3-5 % of the cycles of kernel-heavy files. Lookups return a borrowed
    pointer to the stored value (nullptr if absent); `insert` keeps an existing entry, like `unordered_map::insert`. */
template<typename T>
class expr_flat_map {
    struct entry { lean_object * m_key; lean_object * m_val; };  // m_key == nullptr: empty; 16 B, the hash lives in the key
    entry *  m_tab  = nullptr;
    size_t   m_mask = 0;
    size_t   m_size = 0;
    // Small first table: a type_checker::state (and so its five caches) is created for every kernel call, most of which
    // touch a handful of terms; 64 initial slots (1.5 KB zeroed and scanned per cache) cost 1.4 % of cycles on a module
    // of many small declarations, 8 slots cost nothing measurable and the table doubles when needed.
    static constexpr size_t INITIAL_CAP = 8;

    static size_t slot(unsigned h, size_t mask) {
        uint64_t x = (uint64_t)h * 0x9E3779B97F4A7C15ull;  // the expr hash is a 32-bit mix; spread it over the table
        return (size_t)(x >> 32) & mask;
    }
    static unsigned key_hash(entry const & e) { return hash(*reinterpret_cast<expr const *>(&e.m_key)); }  // expr = one pointer
    static bool key_eq(entry const & e, expr const & k) {
        // pointer equality first (the common hit: the same object is looked up again); `std::equal_to<expr>` = is_equal
        // itself compares the two objects' stored hashes before anything structural
        return e.m_key == k.raw() || std::equal_to<expr>()(k, *reinterpret_cast<expr const *>(&e.m_key));
    }
    void grow() {
        size_t new_cap  = m_tab ? (m_mask + 1) * 2 : INITIAL_CAP;
        entry * new_tab = static_cast<entry *>(alloc_zeroed_block(new_cap, sizeof(entry)));
        if (new_tab == nullptr) lean_internal_panic_out_of_memory();
        size_t new_mask = new_cap - 1;
        if (m_tab) {
            for (size_t i = 0; i <= m_mask; i++) {
                entry const & e = m_tab[i];
                if (e.m_key == nullptr) continue;
                size_t j = slot(key_hash(e), new_mask);
                while (new_tab[j].m_key != nullptr) j = (j + 1) & new_mask;
                new_tab[j] = e;
            }
            free_block(m_tab);
        }
        m_tab = new_tab; m_mask = new_mask;
    }
public:
    expr_flat_map() {}
    expr_flat_map(expr_flat_map const &) = delete;
    expr_flat_map & operator=(expr_flat_map const &) = delete;
    ~expr_flat_map() {
        if (m_tab == nullptr) return;
        for (size_t i = 0; i <= m_mask; i++) {
            if (m_tab[i].m_key != nullptr) { lean_dec(m_tab[i].m_key); lean_dec(m_tab[i].m_val); }
        }
        free_block(m_tab);
    }
    size_t size() const { return m_size; }
    /** \brief Borrowed reference to the value stored for a key structurally equal to `k`, or nullptr. */
    lean_object * find(expr const & k) const {
        if (m_tab == nullptr) return nullptr;
        unsigned h = hash(k);
        size_t i = slot(h, m_mask);
        while (true) {
            entry const & e = m_tab[i];
            if (e.m_key == nullptr) return nullptr;
            if (key_eq(e, k)) return e.m_val;
            i = (i + 1) & m_mask;
        }
    }
    /** \brief Store `v` for `k` unless a structurally equal key is present. */
    void insert(expr const & k, T const & v) {
        // Load factor 2/3: about two probes per hit with linear probing.
        if (m_tab == nullptr || (m_size + 1) * 3 > (m_mask + 1) * 2) grow();
        unsigned h = hash(k);
        size_t i = slot(h, m_mask);
        while (true) {
            entry & e = m_tab[i];
            if (e.m_key == nullptr) {
                lean_inc(k.raw()); lean_inc(v.raw());
                e.m_key = k.raw(); e.m_val = v.raw();
                m_size++;
                return;
            }
            if (key_eq(e, k)) return;
            i = (i + 1) & m_mask;
        }
    }
};
};
