/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include <cstdlib>
#include <cstring>
#include "runtime/alloc.h"
#include "runtime/interrupt.h"
#include "runtime/thread.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "util/alloc.h"

namespace lean {
/** \brief Set of pointer pairs already under comparison. Open addressing, linear probing, power-of-two capacity,
    load factor <= 1/2, 32 inline slots (512 B) so the common case allocates nothing. The pointers are borrowed: both
    expressions are held by the caller for the whole comparison, so no reference counting is needed. This replaces a
    heap-allocated `std::unordered_set<std::pair<lean_object *, lean_object *>>` (one node allocation per shared pair). */
class ptr_pair_set {
    struct entry { lean_object * m_a; lean_object * m_b; };  // m_a == nullptr: empty
    static constexpr size_t INLINE_CAP = 32;
    entry   m_inline[INLINE_CAP];
    entry * m_tab = nullptr;
    size_t  m_mask = 0;
    size_t  m_size = 0;

    static size_t hash(lean_object * a, lean_object * b) {
        uint64_t h = ((uint64_t)(uintptr_t)a >> 3) * 0x9E3779B97F4A7C15ull;
        h ^= ((uint64_t)(uintptr_t)b >> 3) * 0xC2B2AE3D27D4EB4Full;
        h ^= h >> 29;
        h *= 0xff51afd7ed558ccdull;
        h ^= h >> 32;
        return (size_t)h;
    }
    void grow() {
        size_t new_cap  = (m_mask + 1) * 2;
        entry * new_tab = static_cast<entry *>(std::calloc(new_cap, sizeof(entry)));
        if (new_tab == nullptr) lean_internal_panic_out_of_memory();
        size_t new_mask = new_cap - 1;
        for (size_t i = 0; i <= m_mask; i++) {
            entry const & e = m_tab[i];
            if (e.m_a == nullptr) continue;
            size_t j = hash(e.m_a, e.m_b) & new_mask;
            while (new_tab[j].m_a != nullptr) j = (j + 1) & new_mask;
            new_tab[j] = e;
        }
        if (m_tab != m_inline) std::free(m_tab);
        m_tab = new_tab; m_mask = new_mask;
    }
public:
    ptr_pair_set() {}
    ptr_pair_set(ptr_pair_set const &) = delete;
    ptr_pair_set & operator=(ptr_pair_set const &) = delete;
    ~ptr_pair_set() { if (m_tab != nullptr && m_tab != m_inline) std::free(m_tab); }
    /** \brief Insert `(a, b)`; return true iff it was already present. */
    bool check_and_insert(lean_object * a, lean_object * b) {
        if (m_tab == nullptr) {
            std::memset(m_inline, 0, sizeof(m_inline));
            m_tab = m_inline; m_mask = INLINE_CAP - 1; m_size = 0;
        } else if ((m_size + 1) * 2 > m_mask + 1) {
            grow();
        }
        size_t i = hash(a, b) & m_mask;
        while (true) {
            entry & e = m_tab[i];
            if (e.m_a == nullptr) { e.m_a = a; e.m_b = b; m_size++; return false; }
            if (e.m_a == a && e.m_b == b) return true;
            i = (i + 1) & m_mask;
        }
    }
};

/**
\brief Functional object for comparing expressions.

Remark if CompareBinderInfo is true, then functional object will also compare
binder information attached to lambda and Pi expressions
*/
template<bool CompareBinderInfo>
class expr_eq_fn {
    ptr_pair_set m_cache;
    size_t m_counter = 0;
    bool check_cache(expr const & a, expr const & b) {
        if (!is_shared(a) || !is_shared(b))
            return false;
        return m_cache.check_and_insert(a.raw(), b.raw());
    }
    bool apply(expr const & a, expr const & b, bool root = false) {
        if (is_eqp(a, b))          return true;
        if (hash(a) != hash(b))    return false;
        if (a.kind() != b.kind())  return false;
        switch (a.kind()) {
        case expr_kind::BVar: return bvar_idx(a) == bvar_idx(b);
        case expr_kind::Lit:  return lit_value(a) == lit_value(b);
        case expr_kind::MVar: return mvar_name(a) == mvar_name(b);
        case expr_kind::FVar: return fvar_name(a) == fvar_name(b);
        case expr_kind::Sort: return sort_level(a) == sort_level(b);
        default: break;
        }
        if (!root && check_cache(a, b)) {
            return true;
        }
        /*
           We increase the number of heartbeats here because some code (e.g., `simp`) may spend a lot of time comparing
           `Expr`s (e.g., checking a cache with many collisions) without allocating any significant amount of memory.
           We use the counter to invoke `add_heartbeats` later. Reason: heartbeat is a thread local storage, and morexpensive to update.
         */
        m_counter++;
        switch (a.kind()) {
        case expr_kind::BVar:
        case expr_kind::Lit:
        case expr_kind::MVar:
        case expr_kind::FVar:
        case expr_kind::Sort:
            lean_unreachable(); // LCOV_EXCL_LINE
        case expr_kind::MData:
            return
                apply(mdata_expr(a), mdata_expr(b)) &&
                mdata_data(a) == mdata_data(b);
        case expr_kind::Proj:
            return
                apply(proj_expr(a), proj_expr(b)) &&
                proj_sname(a) == proj_sname(b) &&
                proj_idx(a) == proj_idx(b);
        case expr_kind::Const:
            return
                const_name(a) == const_name(b) &&
                compare(const_levels(a), const_levels(b), [](level const & l1, level const & l2) { return l1 == l2; });
        case expr_kind::App: {
            if (!apply(app_arg(a), app_arg(b))) return false;
            expr const * curr_a = &app_fn(a);
            expr const * curr_b = &app_fn(b);
            while (true) {
                if (!is_app(*curr_a)) break;
                if (!is_app(*curr_b)) return false;
                if (!apply(app_arg(*curr_a), app_arg(*curr_b))) return false;
                curr_a = &app_fn(*curr_a);
                curr_b = &app_fn(*curr_b);
            }
            return apply(*curr_a, *curr_b);
        }
        case expr_kind::Lambda: case expr_kind::Pi:
            return
                apply(binding_domain(a), binding_domain(b)) &&
                apply(binding_body(a), binding_body(b)) &&
                (!CompareBinderInfo || binding_name(a) == binding_name(b)) &&
                (!CompareBinderInfo || binding_info(a) == binding_info(b));
        case expr_kind::Let:
            return
                apply(let_type(a), let_type(b)) &&
                apply(let_value(a), let_value(b)) &&
                apply(let_body(a), let_body(b)) &&
                let_nondep(a) == let_nondep(b) &&
                (!CompareBinderInfo || let_name(a) == let_name(b));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
public:
    expr_eq_fn() {}
    ~expr_eq_fn() {
        if (m_counter > 0) add_heartbeats(m_counter);
    }
    bool operator()(expr const & a, expr const & b) { return apply(a, b, true); }
};

bool is_equal(expr const & a, expr const & b) {
    return expr_eq_fn<false>()(a, b);
}

extern "C" LEAN_EXPORT uint8 lean_expr_eqv(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<false>()(TO_REF(expr, a), TO_REF(expr, b));
}

extern "C" LEAN_EXPORT uint8 lean_expr_equal(b_obj_arg a, b_obj_arg b) {
    return expr_eq_fn<true>()(TO_REF(expr, a), TO_REF(expr, b));
}
}
