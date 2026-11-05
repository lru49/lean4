/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include <vector>
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "runtime/buffer.h"

namespace lean {
expr abstract(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_fvar(e); }));
    if (!has_fvar(e))
        return e;
    return replace_tpl(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (is_fvar(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (fvar_name(subst[i]) == fvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        }, true, [](expr const & m, unsigned) { return !has_fvar(m); });
}

namespace {
/* lean-perf (CV abstracttbl): for a large substitution, `Expr.abstract`/`abstractRange` (every `mkLambdaFVars`,
   `mkForallFVars`, `mkLetFVars`, `MetavarContext.mkBinding`) compared each free/meta variable node of the term with
   all `n` entries of the substitution. This index maps (kind, name) to the highest index `i` whose entry is a variable of
   that kind with an equal name (`lean_name_eq`), which is exactly the entry the downward linear scan finds first. */
class abstract_index {
    struct slot { lean_object * m_name; size_t m_idx; uint64_t m_hash; bool m_mvar; bool m_used; };
    buffer<slot, 64> m_slots;
    size_t m_mask;
    static uint64_t hash_of(lean_object * nm, bool mv) {
        uint64_t h = lean_name_hash(nm) * 0x9E3779B97F4A7C15ull;
        return (h ^ (h >> 29)) + (mv ? 0x51ED27u : 0u);
    }
    size_t probe(lean_object * nm, bool mv, uint64_t h) const {
        size_t j = h & m_mask;
        while (m_slots[j].m_used) {
            slot const & s = m_slots[j];
            if (s.m_hash == h && s.m_mvar == mv && lean_name_eq(s.m_name, nm))
                return j;
            j = (j + 1) & m_mask;
        }
        return j;
    }
public:
    abstract_index(size_t n, object * subst) {
        size_t cap = 16;
        while (cap < 2 * n) cap *= 2;
        m_mask = cap - 1;
        m_slots.resize(cap, slot{nullptr, 0, 0, false, false});
        size_t i = n;
        while (i > 0) {
            --i;
            object * v = lean_array_get_core(subst, i);
            bool fv = is_fvar_core(v), mv = is_mvar_core(v);
            if (!fv && !mv) continue;
            lean_object * nm = fv ? fvar_name_core(v).raw() : mvar_name_core(v).raw();
            uint64_t h = hash_of(nm, mv);
            size_t j = probe(nm, mv, h);
            if (!m_slots[j].m_used) // keep the higher index inserted first
                m_slots[j] = slot{nm, i, h, mv, true};
        }
    }
    /* the highest `i` whose entry is a variable of this kind named `nm`, or -1 */
    long find(lean_object * nm, bool mv) const {
        slot const & s = m_slots[probe(nm, mv, hash_of(nm, mv))];
        return s.m_used ? static_cast<long>(s.m_idx) : -1;
    }
};
}

static object * lean_expr_abstract_core(object * e0, size_t n, object * subst) {
    lean_assert(n <= lean_array_size(subst));
    expr const & e = reinterpret_cast<expr const &>(e0);
    if (!has_fvar(e) && !has_mvar(e)) {
        lean_inc(e0);
        return e0;
    }
    if (n >= 16) {
        abstract_index idx(n, subst);
        expr r = replace_tpl(e, [&](expr const & m, unsigned offset) -> optional<expr> {
                bool fv = is_fvar(m);
                bool mv = is_mvar(m);
                if (fv || mv) {
                    long i = idx.find(fv ? fvar_name(m).raw() : mvar_name(m).raw(), mv);
                    if (i >= 0)
                        return some_expr(mk_bvar(offset + n - static_cast<size_t>(i) - 1));
                    return none_expr();
                }
                return none_expr();
            }, true, [](expr const & m, unsigned) { return !has_fvar(m) && !has_mvar(m); });
        return r.steal();
    }
    expr r = replace_tpl(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            bool fv = is_fvar(m);
            bool mv = is_mvar(m);
            if (fv || mv) {
                size_t i = n;
                while (i > 0) {
                    --i;
                    object * v = lean_array_get_core(subst, i);
                    if (fv && is_fvar_core(v) && fvar_name_core(v) == fvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                    if (mv && is_mvar_core(v) && mvar_name_core(v) == mvar_name(m))
                        return some_expr(mk_bvar(offset + n - i - 1));
                }
                return none_expr();
            }
            return none_expr();
        }, true, [](expr const & m, unsigned) { return !has_fvar(m) && !has_mvar(m); });
    return r.steal();
}

extern "C" LEAN_EXPORT object * lean_expr_abstract_range(object * e, object * n, object * subst) {
    if (!lean_is_scalar(n))
        return lean_expr_abstract_core(e, lean_array_size(subst), subst);
    else
        return lean_expr_abstract_core(e, std::min(lean_unbox(n), lean_array_size(subst)), subst);
}

extern "C" LEAN_EXPORT object * lean_expr_abstract(object * e, object * subst) {
    return lean_expr_abstract_core(e, lean_array_size(subst), subst);
}
}
