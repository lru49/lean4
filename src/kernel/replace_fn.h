/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdlib>
#include <cstring>
#include <functional>
#include <tuple>
#include <type_traits>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"

namespace lean {

/** \brief Memo table of the `replace` traversal: (sub-expression pointer, binder offset) -> result.

    Open-addressing hash table with linear probing, power-of-two capacity and a load factor of at most 1/2,
    keyed by the address of the visited sub-expression (which stays alive for the whole traversal because the
    root expression is held by the caller) and the number of binders above it. The table owns one reference to
    every stored result and releases them when the traversal ends. The first `INLINE_CAP` slots live inside the
    object itself, so a traversal that visits only a few shared sub-terms performs no heap allocation at all, and a
    traversal that visits none does not even initialize the table.

    This replaces the `std::unordered_map<std::pair<lean_object *, unsigned>, expr>` memo, whose node allocation,
    bucket array, rehashing and node release took 8-10 % of the cycles of elaboration-heavy files
    (`instantiate`/`instantiateMVars`/`abstract` call `replace` on every beta reduction and unfolding). */
class replace_cache {
    struct entry {
        lean_object * m_key;
        unsigned      m_offset;
        lean_object * m_val;  // nullptr = empty slot
    };
    static constexpr size_t INLINE_CAP = 32;  // 32 * 24 B = 768 B inside the object
    entry   m_inline[INLINE_CAP];
    entry * m_tab;   // nullptr until the first insertion
    size_t  m_mask;  // capacity - 1
    size_t  m_size;

    static size_t hash(lean_object * k, unsigned offset) {
        uint64_t h = (uint64_t)(uintptr_t)k >> 3;      // objects are 8-byte aligned
        h ^= (uint64_t)offset * 0x9E3779B97F4A7C15ull;
        h *= 0xff51afd7ed558ccdull;                     // murmur3 finalizer step: spreads the pointer bits
        h ^= h >> 33;
        return (size_t)h;
    }

    void init() {
        std::memset(m_inline, 0, sizeof(m_inline));
        m_tab  = m_inline;
        m_mask = INLINE_CAP - 1;
        m_size = 0;
    }

    void grow() {
        size_t new_cap  = (m_mask + 1) * 2;
        entry * new_tab = static_cast<entry *>(std::calloc(new_cap, sizeof(entry)));
        if (new_tab == nullptr) lean_internal_panic_out_of_memory();
        size_t new_mask = new_cap - 1;
        for (size_t i = 0; i <= m_mask; i++) {
            entry const & e = m_tab[i];
            if (e.m_val == nullptr) continue;
            size_t j = hash(e.m_key, e.m_offset) & new_mask;
            while (new_tab[j].m_val != nullptr) j = (j + 1) & new_mask;
            new_tab[j] = e;
        }
        if (m_tab != m_inline) std::free(m_tab);
        m_tab  = new_tab;
        m_mask = new_mask;
    }

public:
    replace_cache():m_tab(nullptr), m_mask(0), m_size(0) {}
    replace_cache(replace_cache const &) = delete;
    replace_cache & operator=(replace_cache const &) = delete;
    ~replace_cache() {
        if (m_tab == nullptr) return;
        for (size_t i = 0; i <= m_mask; i++)
            if (m_tab[i].m_val != nullptr) lean_dec(m_tab[i].m_val);
        if (m_tab != m_inline) std::free(m_tab);
    }

    /** \brief Borrowed reference to the stored result for `(k, offset)`, or nullptr. */
    lean_object * find(lean_object * k, unsigned offset) const {
        if (m_tab == nullptr) return nullptr;
        size_t i = hash(k, offset) & m_mask;
        while (true) {
            entry const & e = m_tab[i];
            if (e.m_val == nullptr) return nullptr;
            if (e.m_key == k && e.m_offset == offset) return e.m_val;
            i = (i + 1) & m_mask;
        }
    }

    /** \brief Store `v` (borrowed; the table takes its own reference) for `(k, offset)` unless the key is present. */
    void insert(lean_object * k, unsigned offset, lean_object * v) {
        if (m_tab == nullptr) init();
        if ((m_size + 1) * 2 > m_mask + 1) grow();
        size_t i = hash(k, offset) & m_mask;
        while (true) {
            entry & e = m_tab[i];
            if (e.m_val == nullptr) {
                lean_inc(v);
                e.m_key = k; e.m_offset = offset; e.m_val = v;
                m_size++;
                return;
            }
            if (e.m_key == k && e.m_offset == offset) return;
            i = (i + 1) & m_mask;
        }
    }
};

/** \brief The traversal behind `replace`, parametric in the functor type so that the per-node callback is inlined
    (the previous `std::function` cost one indirect call per visited node). `F` is invoked as `f(e, offset)`
    (number of enclosing binders) or, if that is not well-formed, as `f(e)`. */
template<typename F>
class replace_rec_fn {
    replace_cache m_cache;
    F const &     m_f;
    bool          m_use_cache;

    optional<expr> call(expr const & e, unsigned offset) {
        if constexpr (std::is_invocable_v<F const &, expr const &, unsigned>) {
            return m_f(e, offset);
        } else {
            return m_f(e);
        }
    }

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared)
            m_cache.insert(e.raw(), offset, r.raw());
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        bool shared = false;
        if (m_use_cache && !is_likely_unshared(e)) {
            if (lean_object * r = m_cache.find(e.raw(), offset))
                return expr(r, true);
            shared = true;
        }
        if (optional<expr> r = call(e, offset)) {
            return save_result(e, offset, std::move(*r), shared);
        } else {
            switch (e.kind()) {
            case expr_kind::Const: case expr_kind::Sort:
            case expr_kind::BVar:  case expr_kind::Lit:
            case expr_kind::MVar:  case expr_kind::FVar:
                return save_result(e, offset, e, shared);
            case expr_kind::MData: {
                expr new_e = apply(mdata_expr(e), offset);
                return save_result(e, offset, update_mdata(e, new_e), shared);
            }
            case expr_kind::Proj: {
                expr new_e = apply(proj_expr(e), offset);
                return save_result(e, offset, update_proj(e, new_e), shared);
            }
            case expr_kind::App: {
                expr new_f = apply(app_fn(e), offset);
                expr new_a = apply(app_arg(e), offset);
                return save_result(e, offset, update_app(e, new_f, new_a), shared);
            }
            case expr_kind::Pi: case expr_kind::Lambda: {
                expr new_d = apply(binding_domain(e), offset);
                expr new_b = apply(binding_body(e), offset+1);
                return save_result(e, offset, update_binding(e, new_d, new_b), shared);
            }
            case expr_kind::Let: {
                expr new_t = apply(let_type(e), offset);
                expr new_v = apply(let_value(e), offset);
                expr new_b = apply(let_body(e), offset+1);
                return save_result(e, offset, update_let(e, new_t, new_v, new_b), shared);
            }
            }
            lean_unreachable();
        }
    }
public:
    replace_rec_fn(F const & f, bool use_cache):m_f(f), m_use_cache(use_cache) {}

    expr operator()(expr const & e) { return apply(e, 0); }
};

/**
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.

   `f` may be any functor taking `(expr const &, unsigned)` or `(expr const &)`; lambdas are inlined into the
   traversal. The `std::function` overloads below are kept for callers that already hold one. */
template<typename F>
expr replace(expr const & e, F const & f, bool use_cache = true) {
    return replace_rec_fn<F>(f, use_cache)(e);
}

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true);
inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}
}
