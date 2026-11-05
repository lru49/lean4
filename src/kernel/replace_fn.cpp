/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <memory>
#include <utility>
#include <unordered_map>
#include "kernel/replace_fn.h"
#include "util/alloc.h"

namespace lean {

expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache) {
    return replace_tpl(e, f, use_cache);
}

class replace_fn {
    replace_cache m_cache;
    lean_object * m_f;

    expr save_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(e.raw(), 0, r);
        return r;
    }

    expr apply(expr const & e) {
        bool shared = false;
        if (is_shared(e)) {
            if (lean_object * r = m_cache.find(e.raw()))
                return expr(r, true);
            shared = true;
        }

        lean_inc(e.raw());
        lean_inc_ref(m_f);
        lean_object * r = lean_apply_1(m_f, e.raw());
        if (!lean_is_scalar(r)) {
            expr e_new(lean_ctor_get(r, 0), true);
            lean_dec_ref(r);
            return save_result(e, e_new, shared);
        }

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return save_result(e, e, shared);
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e));
            return save_result(e, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e));
            return save_result(e, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e));
            expr new_a = apply(app_arg(e));
            return save_result(e, update_app(e, new_f, new_a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e));
            expr new_b = apply(binding_body(e));
            return save_result(e, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e));
            expr new_v = apply(let_value(e));
            expr new_b = apply(let_body(e));
            return save_result(e, update_let(e, new_t, new_v, new_b), shared);
        }}
        lean_unreachable();
    }
public:
    replace_fn(lean_object * f):m_f(f) {}
    expr operator()(expr const & e) { return apply(e); }
};

extern "C" LEAN_EXPORT obj_res lean_replace_expr(b_obj_arg f, b_obj_arg e) {
    expr r = replace_fn(f)(TO_REF(expr, e));
    return r.steal();
}

/* Native port of the Lean-side `Level.substParams` with `Level.getParamSubst` (src/Lean/Level.lean), used by
   `Expr.instantiateLevelParams` below; it previously called the exported `Level.instantiateParams` for every
   level that is neither parameter-free nor a parameter (a cross-module call, a closure for `getParamSubst`,
   reference-count traffic on the parameter lists). Every case mirrors the Lean definition, including the
   cheap simplifications of `mkLevelMax'` / `mkLevelIMax'` (applied when a child changed) and `simpLevelMax'` /
   `simpLevelIMax'` (applied with the original node as default when no child changed), so the result is the
   same level, with the same sharing. `==` on levels is `lean_level_eq` on both sides. */
namespace level_subst {
// `Level.isExplicit`: `zero`, or `succ u` with `u` free of metavariables and parameters and explicit
static bool sp_is_explicit(level const & l) {
    level const * p = &l;
    while (is_succ(*p)) {
        level const & c = succ_of(*p);
        if (has_mvar(c) || has_param(c)) return false;
        p = &c;
    }
    return is_zero(*p);
}
static unsigned sp_get_offset(level const & l) {
    unsigned k = 0;
    level const * p = &l;
    while (is_succ(*p)) { p = &succ_of(*p); k++; }
    return k;
}
static level const & sp_get_level_offset(level const & l) {
    level const * p = &l;
    while (is_succ(*p)) p = &succ_of(*p);
    return *p;
}
// `subsumes` inside `mkLevelMaxCore`
static bool sp_subsumes(level const & u, level const & v) {
    if (sp_is_explicit(v) && sp_get_offset(u) >= sp_get_offset(v)) return true;
    if (is_max(u)) return v == max_lhs(u) || v == max_rhs(u);
    return false;
}
// `mkLevelMaxCore u v elseK`; `d` = the `elseK ()` result (`none`: `mkLevelMax u v`)
static level sp_max_core(level const & u, level const & v, level const * d) {
    if (u == v) return u;
    if (is_zero(u)) return v;
    if (is_zero(v)) return u;
    if (sp_subsumes(u, v)) return u;
    if (sp_subsumes(v, u)) return v;
    if (sp_get_level_offset(u) == sp_get_level_offset(v))
        return sp_get_offset(u) >= sp_get_offset(v) ? u : v;
    return d ? *d : mk_max_core(u, v);
}
// `mkLevelIMaxCore u v elseK` (`Level.isNeverZero` = `is_not_zero`)
static level sp_imax_core(level const & u, level const & v, level const * d) {
    if (is_not_zero(v)) return sp_max_core(u, v, nullptr);
    if (is_zero(v)) return v;
    if (is_zero(u)) return v;
    if (u == v) return u;
    return d ? *d : mk_imax_core(u, v);
}
// `Level.substParams.go` with `s := getParamSubst ps us`
static level sp_subst(level const & u, b_obj_arg ps0, b_obj_arg us0) {
    switch (kind(u)) {
    case level_kind::Zero: case level_kind::MVar:
        return u;
    case level_kind::Param: {
        b_obj_arg ps = ps0;
        b_obj_arg us = us0;
        while (!lean_is_scalar(ps) && !lean_is_scalar(us)) {
            if (lean_name_eq(lean_ctor_get(ps, 0), param_id(u).raw()))
                return level(lean_ctor_get(us, 0), true);
            ps = lean_ctor_get(ps, 1);
            us = lean_ctor_get(us, 1);
        }
        return u;
    }
    case level_kind::Succ: {
        if (!has_param(u)) return u;
        level n = sp_subst(succ_of(u), ps0, us0);
        return is_eqp(succ_of(u), n) ? u : mk_succ(n);
    }
    case level_kind::Max: case level_kind::IMax: {
        if (!has_param(u)) return u;
        level n1 = sp_subst(level_lhs(u), ps0, us0);
        level n2 = sp_subst(level_rhs(u), ps0, us0);
        bool same = is_eqp(level_lhs(u), n1) && is_eqp(level_rhs(u), n2);
        if (is_max(u))
            return sp_max_core(n1, n2, same ? &u : nullptr);
        else
            return sp_imax_core(n1, n2, same ? &u : nullptr);
    }}
    lean_unreachable();
}
}

/* `Expr.instantiateLevelParams`: `replace_fn` with `Expr.instantiateLevelParamsCore.replaceFn`
   inlined, so that the traversal and the result are the same as with `Expr.replace`. Levels are
   instantiated by `Level.instantiateParams`. */
class instantiate_level_params_fn {
    replace_cache m_cache;
    b_obj_arg m_ps;
    b_obj_arg m_us;

    expr save_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(e.raw(), 0, r);
        return r;
    }

    level instantiate(level const & l) {
        // `Level.instantiateParams` returns a level without parameters unchanged and replaces a
        // parameter by its `getParamSubst` value; the remaining levels go through `level_subst::sp_subst`
        if (!has_param(l))
            return l;
        if (is_param(l)) {
            b_obj_arg ps = m_ps;
            b_obj_arg us = m_us;
            while (!lean_is_scalar(ps) && !lean_is_scalar(us)) {
                if (lean_name_eq(lean_ctor_get(ps, 0), param_id(l).raw()))
                    return level(lean_ctor_get(us, 0), true);
                ps = lean_ctor_get(ps, 1);
                us = lean_ctor_get(us, 1);
            }
            return l;
        }
        return level_subst::sp_subst(l, m_ps, m_us);
    }

    // Keep the level buffer out of the recursive traversal's stack frame.
    __attribute__((noinline))
    expr instantiate_const(expr const & e) {
        buffer<level> new_ls;
        bool same = true;
        for (level const & l : const_levels(e)) {
            level new_l = instantiate(l);
            same = same && is_eqp(new_l, l);
            new_ls.push_back(new_l);
        }
        return same ? e : mk_constant(const_name(e), levels(new_ls));
    }

    expr apply(expr const & e) {
        // cheaper than consulting the cache
        if (!has_param_univ(e))
            return e;

        bool shared = false;
        if (is_shared(e)) {
            if (lean_object * r = m_cache.find(e.raw()))
                return expr(r, true);
            shared = true;
        }

        switch (e.kind()) {
        case expr_kind::Const:
            return save_result(e, instantiate_const(e), shared);
        case expr_kind::Sort: {
            level new_l = instantiate(sort_level(e));
            return save_result(e, is_eqp(new_l, sort_level(e)) ? e : mk_sort(new_l), shared);
        }
        case expr_kind::BVar: case expr_kind::Lit:
        case expr_kind::MVar: case expr_kind::FVar:
            return save_result(e, e, shared);
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e));
            return save_result(e, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e));
            return save_result(e, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e));
            expr new_a = apply(app_arg(e));
            return save_result(e, update_app(e, new_f, new_a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e));
            expr new_b = apply(binding_body(e));
            return save_result(e, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e));
            expr new_v = apply(let_value(e));
            expr new_b = apply(let_body(e));
            return save_result(e, update_let(e, new_t, new_v, new_b), shared);
        }}
        lean_unreachable();
    }
public:
    instantiate_level_params_fn(b_obj_arg ps, b_obj_arg us):m_ps(ps), m_us(us) {}
    expr operator()(expr const & e) { return apply(e); }
};

/* instantiateLevelParamsImpl (e : @& Expr) (paramNames : @& List Name) (lvls : @& List Level) : Expr */
extern "C" LEAN_EXPORT obj_res lean_expr_instantiate_level_params(b_obj_arg e, b_obj_arg ps, b_obj_arg us) {
    expr r = instantiate_level_params_fn(ps, us)(TO_REF(expr, e));
    return r.steal();
}
}
