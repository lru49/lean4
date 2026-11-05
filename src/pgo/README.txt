lean.profdata.tar.xz: LLVM IR instrumentation profile (llvm-profdata merge --sparse, LLVM 18) used by
src/CMakeLists.txt (LEAN_PGO_PROFILE) for profile-guided optimization of the C++ runtime/kernel and the
core library's C code.

Recorded on x86_64 Linux with a Release stage1 configured with
  -DLEAN_EXTRA_CXX_FLAGS=-fprofile-generate=<dir> -DLEANC_EXTRA_CC_FLAGS=-fprofile-generate=<dir>
  -DLEAN_EXTRA_LINKER_FLAGS="-fuse-ld=lld -fprofile-generate=<dir>" -DLEAN_PGO_PROFILE=
and the training workload: elaborating 23 Mathlib modules with `lean -j 4` (Algebra/Group/Basic,
Order/Lattice, Tactic/Ring/Basic, Data/Nat/Factorization/Basic, Analysis/SpecialFunctions/Gamma/Basic,
Topology/Basic, LinearAlgebra/Matrix/Determinant/Basic, Data/Finset/Card, Analysis/Calculus/FDeriv/Basic,
RingTheory/Ideal/Operations, MeasureTheory/Measure/MeasureSpace, Topology/Algebra/Module/Basic,
Analysis/Normed/Group/Basic, CategoryTheory/Limits/Shapes/Pullback/HasPullback, Data/Real/Basic,
LinearAlgebra/Basis/Basic, Order/Filter/Basic, Analysis/SpecialFunctions/Trigonometric/Basic,
NumberTheory/Padics/PadicVal/Basic, GroupTheory/Sylow, Data/Matrix/Basic, SetTheory/Cardinal/Basic,
Combinatorics/SimpleGraph/Basic), one `import Mathlib` file with linarith/positivity/simp/omega/#eval at
-j 8, and a no-op `lake build --no-build` of a Mathlib target. Raw profiles (LLVM_PROFILE_FILE=<dir>/lean-%8m.profraw)
merged with: llvm-profdata merge --sparse -o lean.profdata <dir>/*.profraw; tar -cJf lean.profdata.tar.xz lean.profdata
