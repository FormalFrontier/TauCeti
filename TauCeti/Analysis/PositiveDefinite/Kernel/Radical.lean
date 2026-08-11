/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds
public import TauCeti.Analysis.PositiveDefinite.Kernel.Finsupp

/-!
# The kernel of a positive-definite kernel Gram form

This file records the next algebraic step in the GNS/Kolmogorov construction for a
positive-definite kernel. The finitely supported Gram form from
`TauCeti.Analysis.PositiveDefinite.Kernel.Finsupp` is bundled there as a sesquilinear form; here
we define its radical, the submodule of finitely supported coefficient vectors that pair to zero
with every vector. This is the submodule by which the free space is quotiented before completing.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the
positive-definite-function API item "the PD-function ↔ PD-kernel equivalence (`K(a, b) =
F(a + b⋆)`; `F(a − b)` for a group), pullbacks, and the GNS/Kolmogorov decomposition" as a
clean prerequisite for quotienting the finitely supported space by the null space. No Mathlib
code is vendored; the proofs reuse Tau Ceti's finitely supported Gram form and sesquilinear-form
bundle.

## Main declarations

* `TauCeti.positiveDefiniteKernelFinsuppSesqFormKer`: the null submodule of the Gram form.
* `TauCeti.mem_positiveDefiniteKernelFinsuppSesqFormKer`: membership means pairing to zero with
  every finitely supported vector.
* `TauCeti.positiveDefiniteKernelFinsuppForm_self_eq_zero_iff_mem_ker`: a positive-definite
  kernel has zero finitely supported Gram seminorm exactly on the null submodule.
* `TauCeti.positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_left` and
  `TauCeti.positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_right`: vectors in the
  null submodule pair to zero on the left and, for positive-definite kernels, on the right.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

namespace TauCeti

universe u v

open ComplexConjugate
open scoped ComplexOrder

variable {𝕜 : Type u} [RCLike 𝕜] {α : Type v} {K : α → α → 𝕜}

/-- The radical, or null submodule, of the finitely supported Gram form attached to a kernel.

This is the submodule by which the free space `α →₀ 𝕜` is quotiented in the algebraic
GNS/Kolmogorov construction. It is defined as the kernel of the bundled sesquilinear form, so
membership means pairing to zero with every finitely supported vector. -/
noncomputable def positiveDefiniteKernelFinsuppSesqFormKer (K : α → α → 𝕜) : Submodule 𝕜 (α →₀ 𝕜) :=
  LinearMap.ker (positiveDefiniteKernelFinsuppSesqForm K)

/-- Membership in the null submodule means that the finitely supported vector pairs to zero with
every vector. -/
@[simp]
theorem mem_positiveDefiniteKernelFinsuppSesqFormKer (x : α →₀ 𝕜) :
    x ∈ positiveDefiniteKernelFinsuppSesqFormKer K ↔
      ∀ y : α →₀ 𝕜, positiveDefiniteKernelFinsuppForm K x y = 0 := by
  rw [positiveDefiniteKernelFinsuppSesqFormKer, LinearMap.mem_ker]
  constructor
  · intro hx y
    simpa [positiveDefiniteKernelFinsuppSesqForm_apply] using
      congrArg (fun f : (α →₀ 𝕜) →ₗ[𝕜] 𝕜 => f y) hx
  · intro hx
    apply LinearMap.ext
    intro y
    simpa [positiveDefiniteKernelFinsuppSesqForm_apply] using hx y

/-- A vector in the null submodule pairs to zero with every vector on the left. -/
theorem positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_left
    {x y : α →₀ 𝕜} (hx : x ∈ positiveDefiniteKernelFinsuppSesqFormKer K) :
    positiveDefiniteKernelFinsuppForm K x y = 0 :=
  (mem_positiveDefiniteKernelFinsuppSesqFormKer (K := K) x).mp hx y

/-- A vector in the null submodule has zero diagonal Gram value. -/
theorem positiveDefiniteKernelFinsuppForm_self_eq_zero_of_mem_ker
    {x : α →₀ 𝕜} (hx : x ∈ positiveDefiniteKernelFinsuppSesqFormKer K) :
    positiveDefiniteKernelFinsuppForm K x x = 0 :=
  positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_left hx

/-- For a positive-definite kernel, zero finitely supported Gram seminorm characterizes the null
submodule. -/
theorem positiveDefiniteKernelFinsuppForm_self_eq_zero_iff_mem_ker
    (hK : IsPositiveDefiniteKernel K) {x : α →₀ 𝕜} :
    positiveDefiniteKernelFinsuppForm K x x = 0 ↔
      x ∈ positiveDefiniteKernelFinsuppSesqFormKer K := by
  refine ⟨?_, positiveDefiniteKernelFinsuppForm_self_eq_zero_of_mem_ker⟩
  intro hx
  rw [mem_positiveDefiniteKernelFinsuppSesqFormKer]
  intro y
  exact isPositiveDefiniteKernel_eq_zero_of_apply_self_eq_zero_left
    (positiveDefiniteKernelFinsuppForm_isPositiveDefiniteKernel hK) hx

/-- For a conjugate-symmetric kernel, a vector in the null submodule also pairs to zero on the
right. This is the column-vanishing form obtained from symmetry of the bundled sesquilinear
form. -/
theorem positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_right_of_conj_symm
    (hsymm : ∀ a b, conj (K a b) = K b a) {x y : α →₀ 𝕜}
    (hy : y ∈ positiveDefiniteKernelFinsuppSesqFormKer K) :
    positiveDefiniteKernelFinsuppForm K x y = 0 := by
  have hzero : positiveDefiniteKernelFinsuppSesqForm K y x = 0 := by
    simpa [positiveDefiniteKernelFinsuppSesqForm_apply] using
      positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_left hy
  have hsymmB : (positiveDefiniteKernelFinsuppSesqForm K).IsSymm :=
    ⟨fun a b => by
      simpa [positiveDefiniteKernelFinsuppSesqForm_apply] using
        positiveDefiniteKernelFinsuppForm_conj_symm_of_conj_symm hsymm a b⟩
  simpa [positiveDefiniteKernelFinsuppSesqForm_apply] using
    (hsymmB.eq_iff (x := y) (y := x)).mp hzero

/-- For a positive-definite kernel, a vector in the null submodule also pairs to zero on the
right. This is the column-vanishing form obtained from conjugate symmetry. -/
theorem positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_right
    (hK : IsPositiveDefiniteKernel K) {x y : α →₀ 𝕜}
    (hy : y ∈ positiveDefiniteKernelFinsuppSesqFormKer K) :
    positiveDefiniteKernelFinsuppForm K x y = 0 :=
  positiveDefiniteKernelFinsuppForm_eq_zero_of_mem_ker_right_of_conj_symm
    (isPositiveDefiniteKernel_conj_symm hK) hy

end TauCeti
