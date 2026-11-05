/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include <functional>
#include "runtime/buffer.h"
#include "kernel/expr.h"
#include "kernel/expr_sets.h"
#include "kernel/ptr_pair_set.h"

namespace lean {
/* lean-perf (CV foreachtpl): the traversals are templates over the callback type, so that callers with a lambda
   (`has_loose_bvar`, `find`, `Expr.find?`/`findExt?`) get it inlined instead of an indirect `std::function` call per visited
   node; the `std::function` overloads of `for_each` below instantiate the same templates. Same visiting order and
   visited-set policy as before. */
/*
If `partial_apps = true`, then given a term `g a b`, we also apply the function `m_f` to `g a`,
and not only to `g`, `a`, and `b`.
*/
template<bool partial_apps, typename F> class for_each_fn {
    ptr_pair_set m_cache;
    F & m_f;

    bool visited(expr const & e) {
        if (is_likely_unshared(e)) return false;
        return !m_cache.insert(e.raw(), 0);
    }

    void apply_fn(expr const & e) {
        if (is_app(e)) {
            apply_fn(app_fn(e));
            apply(app_arg(e));
        } else {
            apply(e);
        }
    }

    void apply(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar: case expr_kind::Sort:
            m_f(e);
            return;
        default:
            break;
        }

        if (visited(e))
            return;

        if (!m_f(e))
            return;

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar:
        case expr_kind::Sort:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return;
        case expr_kind::MData:
            apply(mdata_expr(e));
            return;
        case expr_kind::Proj:
            apply(proj_expr(e));
            return;
        case expr_kind::App:
            if (partial_apps)
                apply(app_fn(e));
            else
                apply_fn(app_fn(e));
            apply(app_arg(e));
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e));
            apply(binding_body(e));
            return;
        case expr_kind::Let:
            apply(let_type(e));
            apply(let_value(e));
            apply(let_body(e));
            return;
        }
    }

public:
    explicit for_each_fn(F & f):m_f(f) {}
    void operator()(expr const & e) { apply(e); }
};

template<typename F> class for_each_offset_fn {
    ptr_pair_set m_cache;
    F & m_f;

    bool visited(expr const & e, unsigned offset) {
        if (is_likely_unshared(e)) return false;
        return !m_cache.insert(e.raw(), offset);
    }

    void apply(expr const & e, unsigned offset) {
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar: case expr_kind::Sort:
            m_f(e, offset);
            return;
        default:
            break;
        }

        if (visited(e, offset))
            return;

        if (!m_f(e, offset))
            return;

        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::BVar:
        case expr_kind::Sort:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return;
        case expr_kind::MData:
            apply(mdata_expr(e), offset);
            return;
        case expr_kind::Proj:
            apply(proj_expr(e), offset);
            return;
        case expr_kind::App:
            apply(app_fn(e), offset);
            apply(app_arg(e), offset);
            return;
        case expr_kind::Lambda: case expr_kind::Pi:
            apply(binding_domain(e), offset);
            apply(binding_body(e), offset+1);
            return;
        case expr_kind::Let:
            apply(let_type(e), offset);
            apply(let_value(e), offset);
            apply(let_body(e), offset+1);
            return;
        }
    }

public:
    explicit for_each_offset_fn(F & f):m_f(f) {}
    void operator()(expr const & e) { apply(e, 0); }
};


/** \brief `for_each` with offsets for a statically known callback `f(e, offset)`. */
template<typename F> void for_each_offset_tpl(expr const & e, F & f) { for_each_offset_fn<F>{f}(e); }

/**
\brief Expression visitor.

The argument \c f must be a lambda (function object) containing the method

<code>
bool operator()(expr const & e, unsigned offset)
</code>

The \c offset is the number of binders under which \c e occurs.
*/
void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f); // NOLINT

void for_each(expr const & e, std::function<bool(expr const &)> && f); // NOLINT
}
