/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic

/-!
# The finitely supported Gram form of a positive-definite kernel

This file packages the finitely supported Hermitian form attached to a positive-definite kernel.
For a kernel `K : α → α → 𝕜` and finitely supported coefficient vectors `x y : α →₀ 𝕜`, the form is

`∑ a ∈ x.support, ∑ b ∈ y.support, conj (x a) * y b * K a b`.

The diagonal nonnegativity of this form is exactly the `Matrix.PosSemidef` content in
`TauCeti.IsPositiveDefiniteKernel`, but a named finitely supported form is the object needed by
the later GNS/Kolmogorov construction: its null space is quotiented, then completed.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C ("Positive-definite
functions and Bochner's theorem"), specifically the positive-definite-kernel / GNS-Kolmogorov API
prerequisite. No Mathlib code is vendored; the proofs reuse Mathlib's positive-semidefinite matrix
API through `TauCeti.IsPositiveDefiniteKernel`.

## Main declarations

* `TauCeti.positiveDefiniteKernelFinsuppForm`: the finitely supported Gram form attached to a
  kernel.
* `TauCeti.positiveDefiniteKernelFinsuppSesqForm`: the same form bundled as a sesquilinear form.
* `TauCeti.positiveDefiniteKernelFinsuppForm_self_nonneg`: nonnegativity on the diagonal for
  positive-definite kernels.
* `TauCeti.positiveDefiniteKernelFinsuppForm_add_left` and related lemmas: sesquilinearity of
  the form.
* `TauCeti.positiveDefiniteKernelFinsuppForm_conj_symm`: conjugate symmetry of the form.
* `TauCeti.positiveDefiniteKernelFinsuppForm_single_single`: the value on two basis vectors.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {α : Type v}

/-- The finitely supported Gram expression associated to a kernel `K`.

For positive-definite `K`, the diagonal value
`positiveDefiniteKernelFinsuppForm K x x` is nonnegative, and the form is Hermitian. This is the
pre-inner-product expression used before quotienting by its null space in the GNS/Kolmogorov
construction. -/
noncomputable def positiveDefiniteKernelFinsuppForm (K : α → α → 𝕜) (x y : α →₀ 𝕜) : 𝕜 :=
  x.sum fun a xa => y.sum fun b yb => conj xa * yb * K a b

variable {K : α → α → 𝕜}

/-- The finitely supported Gram form unfolds to the double `Finsupp.sum` expression. -/
theorem positiveDefiniteKernelFinsuppForm_def (K : α → α → 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K x y =
      x.sum fun a xa => y.sum fun b yb => conj xa * yb * K a b := by
  rfl

/-- The finitely supported Gram form is zero when the left vector is zero. -/
@[simp]
theorem positiveDefiniteKernelFinsuppForm_zero_left (y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K 0 y = 0 := by
  simp [positiveDefiniteKernelFinsuppForm]

/-- The finitely supported Gram form is zero when the right vector is zero. -/
@[simp]
theorem positiveDefiniteKernelFinsuppForm_zero_right (x : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K x 0 = 0 := by
  simp [positiveDefiniteKernelFinsuppForm]

private theorem positiveDefiniteKernelFinsuppForm_eq_posSemidef_sum (x : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K x x =
      x.sum fun i xi => x.sum fun j xj => star xi * (Matrix.of fun a b => K a b) i j * xj := by
  simp [positiveDefiniteKernelFinsuppForm, RCLike.star_def, Matrix.of_apply, mul_left_comm,
    mul_comm]

/-- The diagonal finitely supported Gram form of a positive-definite kernel is nonnegative. -/
theorem positiveDefiniteKernelFinsuppForm_self_nonneg
    (hK : IsPositiveDefiniteKernel K) (x : α →₀ 𝕜) :
    0 ≤ positiveDefiniteKernelFinsuppForm K x x := by
  have hK' := (isPositiveDefiniteKernel_def K).mp hK
  rw [positiveDefiniteKernelFinsuppForm_eq_posSemidef_sum]
  exact hK'.2 x

/-- The finitely supported Gram form is additive in the left argument. -/
theorem positiveDefiniteKernelFinsuppForm_add_left (x y z : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K (x + y) z =
      positiveDefiniteKernelFinsuppForm K x z + positiveDefiniteKernelFinsuppForm K y z := by
  classical
  simp only [positiveDefiniteKernelFinsuppForm]
  rw [Finsupp.sum_add_index]
  · intro a _
    simp
  · intro a _ xa ya
    simp [map_add, add_mul]

/-- The finitely supported Gram form is additive in the right argument. -/
theorem positiveDefiniteKernelFinsuppForm_add_right (x y z : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K x (y + z) =
      positiveDefiniteKernelFinsuppForm K x y + positiveDefiniteKernelFinsuppForm K x z := by
  classical
  simp only [positiveDefiniteKernelFinsuppForm]
  simp only [Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simpa [Finsupp.sum] using
    (Finsupp.sum_add_index (f := y) (g := z)
      (h := fun b yb => conj (x a) * yb * K a b)
      (fun b _ => by simp) (fun b _ yb zb => by ring))

/-- The finitely supported Gram form is conjugate-linear in the left scalar. -/
theorem positiveDefiniteKernelFinsuppForm_smul_left (c : 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K (c • x) y =
      conj c * positiveDefiniteKernelFinsuppForm K x y := by
  classical
  simp only [positiveDefiniteKernelFinsuppForm]
  rw [Finsupp.sum_smul_index]
  · simp only [Finsupp.sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  · intro a
    simp

/-- The finitely supported Gram form is linear in the right scalar. -/
theorem positiveDefiniteKernelFinsuppForm_smul_right (c : 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K x (c • y) =
      c * positiveDefiniteKernelFinsuppForm K x y := by
  classical
  simp only [positiveDefiniteKernelFinsuppForm]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc
    ∑ b ∈ (c • y).support, (starRingEnd 𝕜) (x a) * (c • y) b * K a b =
        y.sum fun b yb => conj (x a) * (c * yb) * K a b := by
      simpa [Finsupp.sum] using
        (Finsupp.sum_smul_index (g := y) (b := c)
          (h := fun b yb => conj (x a) * yb * K a b) (fun b => by simp))
    _ = c * ∑ b ∈ y.support, (starRingEnd 𝕜) (x a) * y b * K a b := by
      simp [Finsupp.sum, Finset.mul_sum, mul_left_comm, mul_comm]

/-- The finitely supported Gram form is zero for the zero kernel. -/
@[simp]
theorem positiveDefiniteKernelFinsuppForm_zero_kernel (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm (fun _ _ : α => (0 : 𝕜)) x y = 0 := by
  simp [positiveDefiniteKernelFinsuppForm]

/-- The finitely supported Gram form is additive in the kernel. -/
theorem positiveDefiniteKernelFinsuppForm_add_kernel (K L : α → α → 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm (fun a b => K a b + L a b) x y =
      positiveDefiniteKernelFinsuppForm K x y + positiveDefiniteKernelFinsuppForm L x y := by
  classical
  simp only [positiveDefiniteKernelFinsuppForm, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The finitely supported Gram form is homogeneous in the kernel. -/
theorem positiveDefiniteKernelFinsuppForm_smul_kernel (c : 𝕜) (K : α → α → 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm (fun a b => c • K a b) x y =
      c * positiveDefiniteKernelFinsuppForm K x y := by
  classical
  simp only [positiveDefiniteKernelFinsuppForm, Finsupp.sum, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The finitely supported Gram form is homogeneous in a real scalar on the kernel. -/
theorem positiveDefiniteKernelFinsuppForm_real_smul_kernel (r : ℝ) (K : α → α → 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm (fun a b => r • K a b) x y =
      r • positiveDefiniteKernelFinsuppForm K x y := by
  simpa [Algebra.smul_def] using
    positiveDefiniteKernelFinsuppForm_smul_kernel (𝕜 := 𝕜) (α := α) (r : 𝕜) K x y

/-- The finitely supported Gram form sends finite sums of kernels to sums of Gram forms. -/
theorem positiveDefiniteKernelFinsuppForm_sum_kernel {ι : Type*}
    (s : Finset ι) (K : ι → α → α → 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm (fun a b => ∑ i ∈ s, K i a b) x y =
      ∑ i ∈ s, positiveDefiniteKernelFinsuppForm (K i) x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s his ih =>
      simp [his, positiveDefiniteKernelFinsuppForm_add_kernel, ih]

/-- The finitely supported Gram form bundled as a sesquilinear form. -/
noncomputable def positiveDefiniteKernelFinsuppSesqForm (K : α → α → 𝕜) :
    (α →₀ 𝕜) →ₗ⋆[𝕜] (α →₀ 𝕜) →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
    (positiveDefiniteKernelFinsuppForm K)
    positiveDefiniteKernelFinsuppForm_add_left
    (fun c x y => by
      simp [positiveDefiniteKernelFinsuppForm_smul_left])
    positiveDefiniteKernelFinsuppForm_add_right
    (fun c x y => by
      simp [positiveDefiniteKernelFinsuppForm_smul_right])

/-- Applying the bundled sesquilinear form gives the finitely supported Gram expression. -/
@[simp]
theorem positiveDefiniteKernelFinsuppSesqForm_apply (K : α → α → 𝕜) (x y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppSesqForm K x y =
      positiveDefiniteKernelFinsuppForm K x y := by
  rfl

/-- A pointwise conjugate-symmetric kernel gives a conjugate-symmetric finitely supported Gram
form. -/
theorem positiveDefiniteKernelFinsuppForm_conj_symm_of_conj_symm
    (hsymm : ∀ a b, conj (K a b) = K b a) (x y : α →₀ 𝕜) :
    conj (positiveDefiniteKernelFinsuppForm K x y)
      = positiveDefiniteKernelFinsuppForm K y x := by
  classical
  rw [positiveDefiniteKernelFinsuppForm, positiveDefiniteKernelFinsuppForm]
  simp_rw [Finsupp.sum, map_sum, map_mul, RCLike.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hsymm a b]
  ring

/-- The finitely supported Gram form attached to a positive-definite kernel is conjugate
symmetric. -/
theorem positiveDefiniteKernelFinsuppForm_conj_symm
    (hK : IsPositiveDefiniteKernel K) (x y : α →₀ 𝕜) :
    conj (positiveDefiniteKernelFinsuppForm K x y)
      = positiveDefiniteKernelFinsuppForm K y x :=
  positiveDefiniteKernelFinsuppForm_conj_symm_of_conj_symm
    (isPositiveDefiniteKernel_conj_symm hK) x y

/-- Positive-definite kernels give positive-semidefinite finitely supported sesquilinear forms. -/
theorem positiveDefiniteKernelFinsuppSesqForm_isPosSemidef (hK : IsPositiveDefiniteKernel K) :
    (positiveDefiniteKernelFinsuppSesqForm K).IsPosSemidef where
  isSymm := ⟨fun x y => positiveDefiniteKernelFinsuppForm_conj_symm hK x y⟩
  isNonneg := ⟨fun x => by
    simpa using positiveDefiniteKernelFinsuppForm_self_nonneg hK x⟩

/-- The finitely supported Gram form of a positive-definite kernel is itself a positive-definite
kernel on the finitely supported coefficient space. -/
theorem positiveDefiniteKernelFinsuppForm_isPositiveDefiniteKernel
    (hK : IsPositiveDefiniteKernel K) :
    IsPositiveDefiniteKernel fun x y : α →₀ 𝕜 =>
      positiveDefiniteKernelFinsuppForm K x y := by
  classical
  refine (isPositiveDefiniteKernel_iff.{u, max u v, 0} (𝕜 := 𝕜) (α := α →₀ 𝕜)).mpr
    ⟨positiveDefiniteKernelFinsuppForm_conj_symm hK, ?_⟩
  intro ι _ v c
  let z : α →₀ 𝕜 := ∑ i, c i • v i
  have hz := positiveDefiniteKernelFinsuppForm_self_nonneg hK z
  have hz' : 0 ≤ positiveDefiniteKernelFinsuppSesqForm K z z := by
    simpa [positiveDefiniteKernelFinsuppSesqForm_apply] using hz
  convert hz' using 1
  · rw [Finset.sum_comm]
    simp [z, positiveDefiniteKernelFinsuppSesqForm_apply, Finset.mul_sum, mul_left_comm,
      mul_comm]

/-- The finitely supported Gram form takes the expected value on two basis vectors. -/
@[simp]
theorem positiveDefiniteKernelFinsuppForm_single_single (a b : α) (r s : 𝕜) :
    positiveDefiniteKernelFinsuppForm K (Finsupp.single a r) (Finsupp.single b s)
      = conj r * s * K a b := by
  classical
  simp [positiveDefiniteKernelFinsuppForm]

private theorem RCLike.cast_normSq_eq_norm_sq (r : 𝕜) :
    ((‖r‖ : 𝕜) ^ 2) = (RCLike.normSq r : 𝕜) := by
  rw [← map_pow, RCLike.normSq_eq_def']

/-- On a single finitely supported basis vector, the diagonal Gram form is the scalar norm-square
times the corresponding diagonal kernel value. -/
theorem positiveDefiniteKernelFinsuppForm_single_self (a : α) (r : 𝕜) :
    positiveDefiniteKernelFinsuppForm K (Finsupp.single a r) (Finsupp.single a r)
      = RCLike.normSq r * K a a := by
  classical
  rw [positiveDefiniteKernelFinsuppForm_single_single, RCLike.conj_mul,
    RCLike.cast_normSq_eq_norm_sq]

end TauCeti
