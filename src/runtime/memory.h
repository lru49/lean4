/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdlib>
#include <lean/lean.h>

namespace lean {
/** \brief Set maximum amount of memory in bytes */
LEAN_EXPORT void set_max_memory(size_t max);
LEAN_EXPORT void check_memory(char const * component_name);
/** \brief Maximum amount of memory in bytes; 0 (the default) = `check_memory` does nothing. */
LEAN_EXPORT extern size_t g_max_memory;
inline bool memory_check_enabled() { return g_max_memory != 0; }
}
