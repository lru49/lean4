/*
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <string>
#include <sys/stat.h>

namespace lean {
/* Persistent native-code cache for imported modules (see native_cache.cpp).
   `native_cache_note_olean` records the identity (size, mtime) of every `.olean` read by the import;
   `native_cache_load_once` is called before the first module initializer is looked up and, if a cached
   bundle of native code exists whose modules are all imported with identical files, loads it, so the
   interpreter (which prefers native symbols) and `runModInit` use native code for those modules. */
void native_cache_note_olean(std::string const & fn, struct stat const & st);
void native_cache_load_once();
}
