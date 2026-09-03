/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.InvariantForm
public import TauCeti.Algebra.Lie.Weights.Integrality

public section

/-!
# The invariant form is positive definite on the integral weights

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero and let `H` be a splitting Cartan subalgebra. The invariant form
`TauCeti.invForm` of `TauCeti/Algebra/Lie/Weights/InvariantForm.lean` is symmetric and
non-degenerate on `Module.Dual K H`, but `K` carries no order, so "positive definite" cannot be
said of it directly: over `ℂ` a non-degenerate form may perfectly well vanish on a nonzero vector.

What is true, and what this file proves, is that the form is positive definite on the **rational
form** of the weight space. A weight is **integral** (`TauCeti.IsIntegralWeight`) when it takes
integer values on every coroot; the weights of finite-dimensional modules are integral
(`TauCeti.exists_int_apply_coroot`), and so are the dominant integral weights of the highest-weight
classification. On such a weight `lam` the scalar `⟨lam, lam⟩` is the image of a *rational* number,
that rational number is nonnegative, and it is positive unless `lam = 0`
(`TauCeti.IsIntegralWeight.exists_pos_rat_invForm_self`). In particular `⟨lam, lam⟩ ≠ 0`.

## The argument

Everything rests on one identity. The Killing form restricted to `H` is the sum
`κ(x, y) = ∑_α α x * α y` over the roots (Mathlib's
`LieAlgebra.IsKilling.restrict_killingForm_eq_sum`), and `invForm` is the transport of `κ|H` along
`LieAlgebra.IsKilling.cartanEquivDual`, so

`⟨a, b⟩ = ∑_α ⟨α, a⟩ ⟨α, b⟩`

(`TauCeti.invForm_eq_sum_root`): the form is a sum of products of the coordinates that the roots
define. Two consequences follow at once. A weight orthogonal to every root is zero
(`TauCeti.eq_zero_of_forall_invForm_root_eq_zero`), and `⟨lam, lam⟩ = ∑_α ⟨lam, α⟩²`.

It remains to see that each coordinate `⟨lam, α⟩` is rational when `lam` is integral. The
normalisation `TauCeti.invForm_coroot_weight` reads `⟨lam, α⟩ = ⟨α, α⟩ lam(α^∨) / 2`, so this is
the rationality of the root length `⟨α, α⟩`, which the same sum-over-roots identity supplies:
`TauCeti.traceForm_coroot_self_mul_invForm_self_eq_four` gives `κ(α^∨, α^∨) ⟨α, α⟩ = 4` while
`κ(α^∨, α^∨) = ∑_β β(α^∨)²` is a sum of squares of Cartan integers, hence an integer, nonnegative
and nonzero.

## Main definitions and results

* `TauCeti.invForm_eq_sum_root`: the invariant form is the sum over the roots of the products of
  the coordinates the roots define.
* `TauCeti.exists_pos_rat_invForm_root_self`: a root has positive rational length.
* `TauCeti.IsIntegralWeight.exists_pos_rat_invForm_self`: the invariant form of a nonzero integral
  weight with itself is a positive rational.
* `TauCeti.IsIntegralWeight.invForm_self_ne_zero`: in particular it is nonzero.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §8.5, where
  the form is shown to be positive definite on the rational span of the roots.

This is the positivity behind the Casimir argument of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.
-/

namespace TauCeti

open Finset LieAlgebra LieAlgebra.IsKilling LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-! ### The invariant form as a sum over the roots -/

/-- **The invariant form is the sum over the roots**: `⟨a, b⟩ = ∑_α ⟨α, a⟩ ⟨α, b⟩`. The roots
supply a coordinate system in which the form is a sum of products of coordinates, which is all that
positivity needs. -/
theorem invForm_eq_sum_root (a b : Module.Dual K H) :
    invForm a b =
      ∑ α ∈ H.root, invForm (α : Module.Dual K H) a * invForm (α : Module.Dual K H) b := by
  rw [invForm_apply_apply_eq_traceForm, ← restrict_killingForm K L H,
    restrict_killingForm_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul,
    Weight.toLinear_apply]
  exact Finset.sum_congr rfl fun α _ ↦ by
    rw [invForm_apply_apply (α : Module.Dual K H) a, invForm_apply_apply (α : Module.Dual K H) b]
    simp only [Weight.toLinear_apply]

/-- **A weight orthogonal to every root vanishes.** This is the span of the roots, in the form in
which the sum-over-roots identity delivers it. -/
theorem eq_zero_of_forall_invForm_root_eq_zero {a : Module.Dual K H}
    (h : ∀ α ∈ H.root, invForm (α : Module.Dual K H) a = 0) : a = 0 := by
  refine invForm_nondegenerate.1 a fun b ↦ ?_
  rw [invForm_eq_sum_root]
  exact Finset.sum_eq_zero fun α hα ↦ by rw [h α hα, zero_mul]

/-! ### The length of a root is a positive rational -/

/-- **The length of a coroot is a nonnegative integer**: `κ(α^∨, α^∨) = ∑_β β(α^∨)²` is a sum of
squares of Cartan integers. -/
theorem exists_int_traceForm_coroot_self (α : Weight K H L) :
    ∃ n : ℤ, 0 ≤ n ∧ traceForm K H L (coroot α) (coroot α) = (n : K) := by
  refine ⟨∑ β ∈ H.root, (chainBotCoeff α β - chainTopCoeff α β) ^ 2,
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _, ?_⟩
  rw [← restrict_killingForm K L H, restrict_killingForm_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul,
    Weight.toLinear_apply]
  push_cast
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  rw [apply_coroot_eq_cast α β]
  push_cast
  ring

/-- **A root has positive rational length.** Combining `κ(α^∨, α^∨) ⟨α, α⟩ = 4` with the
integrality of `κ(α^∨, α^∨)` gives `⟨α, α⟩ = 4 / κ(α^∨, α^∨)`, a positive rational. -/
theorem exists_pos_rat_invForm_root_self {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ q : ℚ, 0 < q ∧ invForm (α : Module.Dual K H) α = (q : K) := by
  obtain ⟨n, hn0, hn⟩ := exists_int_traceForm_coroot_self α
  have h4 : traceForm K H L (coroot α) (coroot α) * invForm (α : Module.Dual K H) α = 4 :=
    traceForm_coroot_self_mul_invForm_self_eq_four hα
  rw [hn] at h4
  have hne : n ≠ 0 := by
    rintro rfl
    norm_num at h4
  have hnK : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hne
  refine ⟨4 / n, div_pos (by norm_num) (by exact_mod_cast lt_of_le_of_ne hn0 (Ne.symm hne)), ?_⟩
  have h : invForm (α : Module.Dual K H) α = 4 / (n : K) := by
    field_simp
    linear_combination h4
  rw [h]
  push_cast
  ring

/-! ### Integral weights -/

/-- **An integral weight has rational coordinates**: `⟨lam, α⟩ = ⟨α, α⟩ lam(α^∨) / 2` is rational,
both factors being so. -/
theorem IsIntegralWeight.exists_rat_invForm_root {lam : Module.Dual K H}
    (hlam : IsIntegralWeight lam) (α : Weight K H L) :
    ∃ q : ℚ, invForm lam (α : Module.Dual K H) = (q : K) := by
  rcases eq_or_ne (α : Module.Dual K H) 0 with h | h
  · exact ⟨0, by rw [h, map_zero, Rat.cast_zero]⟩
  have hα : α.IsNonZero := fun hz ↦ h (Weight.coe_toLinear_eq_zero_iff.mpr hz)
  obtain ⟨n, hn⟩ := hlam.exists_int_apply_coroot α
  obtain ⟨r, -, hr⟩ := exists_pos_rat_invForm_root_self hα
  have h2 := invForm_coroot_weight lam α
  rw [hn, hr] at h2
  refine ⟨n * r / 2, ?_⟩
  push_cast
  linear_combination -h2 / 2

/-- **The invariant form of an integral weight with itself is a nonnegative rational**, namely the
sum `∑_α ⟨lam, α⟩²` of the squares of its rational coordinates; it vanishes only at `lam = 0`. -/
theorem IsIntegralWeight.exists_nonneg_rat_invForm_self {lam : Module.Dual K H}
    (hlam : IsIntegralWeight lam) :
    ∃ q : ℚ, 0 ≤ q ∧ invForm lam lam = (q : K) ∧ (q = 0 → lam = 0) := by
  choose f hf using hlam.exists_rat_invForm_root
  have hcoord : ∀ α : Weight K H L, invForm (α : Module.Dual K H) lam = (f α : K) := fun α ↦ by
    rw [(invForm_isSymm (H := H)).eq (α : Module.Dual K H) lam]
    exact hf α
  refine ⟨∑ α ∈ H.root, f α ^ 2, Finset.sum_nonneg fun _ _ ↦ sq_nonneg _, ?_, ?_⟩
  · rw [invForm_eq_sum_root]
    push_cast
    exact Finset.sum_congr rfl fun α _ ↦ by rw [hcoord α]; ring
  · intro hq
    have hall : ∀ α ∈ H.root, f α = 0 := fun α hα ↦
      pow_eq_zero_iff two_ne_zero |>.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hq α hα)
    exact eq_zero_of_forall_invForm_root_eq_zero fun α hα ↦ by
      rw [hcoord α, hall α hα, Rat.cast_zero]

/-- **The invariant form is positive definite on the integral weights.** For a nonzero integral
weight the scalar `⟨lam, lam⟩` is the image of a positive rational. -/
theorem IsIntegralWeight.exists_pos_rat_invForm_self {lam : Module.Dual K H}
    (hlam : IsIntegralWeight lam) (h0 : lam ≠ 0) :
    ∃ q : ℚ, 0 < q ∧ invForm lam lam = (q : K) := by
  obtain ⟨q, hq0, hq, hq'⟩ := hlam.exists_nonneg_rat_invForm_self
  exact ⟨q, lt_of_le_of_ne hq0 fun h ↦ h0 (hq' h.symm), hq⟩

/-- **A nonzero integral weight has nonzero length.** -/
theorem IsIntegralWeight.invForm_self_ne_zero {lam : Module.Dual K H}
    (hlam : IsIntegralWeight lam) (h0 : lam ≠ 0) : invForm lam lam ≠ 0 := by
  obtain ⟨q, hq0, hq⟩ := hlam.exists_pos_rat_invForm_self h0
  rw [hq]
  exact_mod_cast hq0.ne'

end TauCeti
