/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <unordered_map>
#include <utility>
#include "runtime/memory.h"
#include "runtime/interrupt.h"
#include "runtime/flet.h"
#include "kernel/for_each_fn.h"
#include "kernel/ptr_pair_set.h"

namespace lean {

void for_each(expr const & e, std::function<bool(expr const &)> && f) { // NOLINT
    for_each_fn<true, std::function<bool(expr const &)>>{f}(e);
}

void for_each(expr const & e, std::function<bool(expr const &, unsigned)> && f) { // NOLINT
    for_each_offset_fn<std::function<bool(expr const &, unsigned)>>{f}(e);
}

extern "C" LEAN_EXPORT obj_res lean_find_expr(b_obj_arg p, b_obj_arg e_) {
    lean_object * found = nullptr;
    expr const & e = TO_REF(expr, e_);
    auto fn = [&](expr const & e) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        if (lean_unbox(lean_apply_1(p, e.raw()))) {
            found = e.raw();
            return false;
        }
        return true;
    };
    for_each_fn<true, decltype(fn)>{fn}(e);
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}

/*
Similar to `lean_find_expr`, but `p` returns
```
inductive FindStep where
  /-- Found desired subterm -/ | found
  /-- Search subterms -/ | visit
  /-- Do not search subterms -/ | done
```
*/
extern "C" LEAN_EXPORT obj_res lean_find_ext_expr(b_obj_arg p, b_obj_arg e_) {
    lean_object * found = nullptr;
    expr const & e = TO_REF(expr, e_);
    // Recall that `findExt?` skips partial applications.
    auto fn = [&](expr const & e) {
        if (found != nullptr) return false;
        lean_inc(p);
        lean_inc(e.raw());
        switch(lean_unbox(lean_apply_1(p, e.raw()))) {
        case 0: // found
            found = e.raw();
            return false;
        case 1: // visit
            return true;
        case 2: // done
            return false;
        default:
            lean_unreachable();
        }
    };
    for_each_fn<false, decltype(fn)>{fn}(e);
    if (found) {
        lean_inc(found);
        lean_object * r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, found);
        return r;
    } else {
        return lean_box(0);
    }
}
}
