/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Casimir
public import TauCeti.Algebra.Lie.Weights.Positivity

public section

/-!
# The Casimir element separates the trivial module from the others

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `base` be a base of its root
system. `TauCeti/Algebra/Lie/HighestWeight/Casimir.lean` computes the scalar by which the Casimir
element `Ω` acts on a highest weight module of weight `lam`, namely

`c(lam) = ⟨lam + ρ, lam + ρ⟩ - ⟨ρ, ρ⟩`.

This file proves that this scalar is **nonzero** as soon as `lam` is a nonzero dominant integral
weight (`TauCeti.casimirScalar_ne_zero`), while `Ω` acts by zero on a module with trivial action
(`TauCeti.representation_casimirElement_eq_zero_of_isTrivial`). Together these two statements are
what makes `Ω` separate the trivial module from the nontrivial finite-dimensional irreducibles,
the mechanism behind Weyl's complete reducibility theorem: on an extension of the trivial module
by a nontrivial irreducible, the Casimir element acts by two different scalars on the two pieces,
so its kernel splits the extension.

## The argument

Expanding the square, `c(lam) = ⟨lam, lam⟩ + ∑_{α > 0} ⟨lam, α⟩`
(`TauCeti.invForm_add_weylVector_sub_invForm_weylVector`), and both summands are read off by the
positivity of `TauCeti/Algebra/Lie/Weights/Positivity.lean`. A dominant integral weight is integral
(`TauCeti.IsDominantIntegral.isIntegralWeight`, the passage from the simple coroots to all of them
going through `TauCeti.IsDominantIntegral.exists_nat_apply_coroot` and, for a negative root, the
sign change `LieAlgebra.IsKilling.coroot_neg`), so `⟨lam, lam⟩` is a positive rational when
`lam ≠ 0`. And `⟨lam, α⟩ = ⟨α, α⟩ lam(α^∨) / 2` is a nonnegative rational for a positive root `α`,
the root length being positive and `lam(α^∨)` a natural number by dominance. A positive rational
plus nonnegative rationals is nonzero, and a nonzero rational stays nonzero in a field of
characteristic zero.

Dominance is essential, not decoration: for a general integral `lam` the two summands have opposite
signs and `c(lam)` really can vanish, as it does at every `lam` on the shifted cone
`⟨lam + ρ, lam + ρ⟩ = ⟨ρ, ρ⟩`.

## Main results

* `TauCeti.IsDominantIntegral.isIntegralWeight`: a dominant integral weight is integral.
* `TauCeti.casimirScalar_ne_zero` and `TauCeti.casimirScalar_eq_zero_iff`: the Casimir scalar of a
  dominant integral weight vanishes exactly at the zero weight.
* `TauCeti.casimir_apply_ne_zero_of_isHighestWeightVector_of_lieSpan_eq_top`: on a highest weight
  module with nonzero dominant integral highest weight, the Casimir element kills no nonzero
  vector.
* `TauCeti.representation_casimirElement_eq_zero_of_isTrivial`: on a module with trivial action the
  Casimir element acts by zero.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.3, where
  the separation is the engine of Weyl's theorem.

This is the "the eigenvalue separates the trivial module from nontrivial irreducibles" step of
Layer 5 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.
-/

namespace TauCeti

open Finset LieAlgebra LieAlgebra.IsKilling LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {base : (IsKilling.rootSystem H).Base} {lam : Module.Dual K H}

/-! ### Dominant integral weights are integral -/

/-- **A dominant integral weight is integral**: it takes integer values on every coroot, not just
natural values on the simple ones. A coroot is the coroot of a positive root or the negative of
one, and on a positive coroot dominance gives a natural value. -/
theorem IsDominantIntegral.isIntegralWeight (hlam : IsDominantIntegral base lam) :
    IsIntegralWeight lam := by
  rw [isIntegralWeight_iff]
  intro α
  rcases eq_or_ne (α : Module.Dual K H) 0 with h | h
  · refine ⟨0, ?_⟩
    rw [show coroot α = 0 from coroot_eq_zero_iff.mpr (Weight.coe_toLinear_eq_zero_iff.mp h)]
    simp
  have hα : α.IsNonZero := fun hz ↦ h (Weight.coe_toLinear_eq_zero_iff.mpr hz)
  obtain ⟨i, rfl⟩ : ∃ i : H.root, (i : Weight K H L) = α :=
    ⟨⟨α, by simpa [LieSubalgebra.root] using hα⟩, rfl⟩
  rcases mem_posRoots_or_mem_negRoots (IsKilling.rootSystem H) base i with hi | hi
  · obtain ⟨n, hn⟩ := hlam.exists_nat_apply_coroot hi
    exact ⟨n, by simpa using hn⟩
  · have hi' : -i ∈ posRoots (IsKilling.rootSystem H) base := by
      rw [← IsKilling.rootSystem_reflectionPerm_self_eq_neg]
      exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots (IsKilling.rootSystem H) base i).mpr
        hi
    obtain ⟨n, hn⟩ := hlam.exists_nat_apply_coroot hi'
    refine ⟨-n, ?_⟩
    rw [IsKilling.rootSystem_coroot_apply, IsKilling.val_neg_root, coroot_neg, map_neg] at hn
    push_cast
    linear_combination -hn

/-! ### The Casimir scalar of a dominant integral weight -/

/-- **A dominant integral weight pairs nonnegatively with a positive root.** The normalisation
`⟨lam, α⟩ = ⟨α, α⟩ lam(α^∨) / 2` has a positive root length and, by dominance, a natural value
`lam(α^∨)`. -/
theorem IsDominantIntegral.exists_nonneg_rat_invForm_root (hlam : IsDominantIntegral base lam)
    {i : H.root} (hi : i ∈ posRoots (IsKilling.rootSystem H) base) :
    ∃ q : ℚ, 0 ≤ q ∧ invForm lam ((IsKilling.rootSystem H).root i) = (q : K) := by
  obtain ⟨n, hn⟩ := hlam.exists_nat_apply_coroot hi
  obtain ⟨r, hr0, hr⟩ := exists_pos_rat_invForm_root_self (H.isNonZero_coe_root i)
  have h2 := invForm_coroot lam i
  simp only [IsKilling.rootSystem_root_apply] at h2 hr ⊢
  rw [hn, hr] at h2
  refine ⟨n * r / 2, by positivity, ?_⟩
  push_cast
  linear_combination -h2 / 2

/-- **The Casimir scalar of a nonzero dominant integral weight is nonzero.** Expanded, the scalar
is `⟨lam, lam⟩ + ∑_{α > 0} ⟨lam, α⟩`: a positive rational plus a sum of nonnegative rationals.

This is the statement that makes the Casimir element separate the trivial module from the
nontrivial ones, since the scalar of the zero weight is `0`. -/
theorem casimirScalar_ne_zero (hlam : IsDominantIntegral base lam) (h0 : lam ≠ 0) :
    invForm (lam + weylVector (IsKilling.rootSystem H) base)
          (lam + weylVector (IsKilling.rootSystem H) base) -
        invForm (weylVector (IsKilling.rootSystem H) base)
          (weylVector (IsKilling.rootSystem H) base) ≠ 0 := by
  classical
  rw [invForm_add_weylVector_sub_invForm_weylVector]
  obtain ⟨q, hq0, hq⟩ := hlam.isIntegralWeight.exists_pos_rat_invForm_self h0
  choose g hg using fun i : H.root ↦
    hlam.isIntegralWeight.exists_rat_invForm_root (i : Weight K H L)
  have hgnn : ∀ i ∈ posRootsFinset (IsKilling.rootSystem H) base, 0 ≤ g i := by
    intro i hi
    obtain ⟨s, hs0, hs⟩ :=
      hlam.exists_nonneg_rat_invForm_root
        ((mem_posRootsFinset (IsKilling.rootSystem H) base i).mp hi)
    have : (g i : K) = (s : K) := by
      rw [← hg i, ← hs, IsKilling.rootSystem_root_apply]
    rwa [Rat.cast_injective this]
  have hsum : ∑ i ∈ posRootsFinset (IsKilling.rootSystem H) base,
      invForm lam ((IsKilling.rootSystem H).root i) =
      ((∑ i ∈ posRootsFinset (IsKilling.rootSystem H) base, g i : ℚ) : K) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [IsKilling.rootSystem_root_apply, hg i]
  rw [hq, hsum, ← Rat.cast_add]
  have : (0 : ℚ) < q + ∑ i ∈ posRootsFinset (IsKilling.rootSystem H) base, g i := by
    have := Finset.sum_nonneg hgnn
    linarith
  exact_mod_cast this.ne'

/-- **The Casimir scalar of a dominant integral weight vanishes exactly at the zero weight.** The
converse direction is the computation `⟨ρ, ρ⟩ - ⟨ρ, ρ⟩ = 0`. -/
theorem casimirScalar_eq_zero_iff (hlam : IsDominantIntegral base lam) :
    invForm (lam + weylVector (IsKilling.rootSystem H) base)
          (lam + weylVector (IsKilling.rootSystem H) base) -
        invForm (weylVector (IsKilling.rootSystem H) base)
          (weylVector (IsKilling.rootSystem H) base) = 0 ↔ lam = 0 := by
  refine ⟨fun h ↦ by_contra fun h0 ↦ casimirScalar_ne_zero hlam h0 h, ?_⟩
  rintro rfl
  rw [zero_add, sub_self]

/-! ### Separation on modules -/

/-- **The Casimir element kills no nonzero vector of a highest weight module whose highest weight
is a nonzero dominant integral weight.** It acts by the scalar of
`TauCeti.casimir_smul_of_isHighestWeightVector_of_lieSpan_eq_top`, which
`TauCeti.casimirScalar_ne_zero` shows to be nonzero. -/
theorem casimir_apply_ne_zero_of_isHighestWeightVector_of_lieSpan_eq_top {v : M}
    (hv : IsHighestWeightVector base lam v) (hgen : LieSubmodule.lieSpan K L {v} = ⊤)
    (hlam : IsDominantIntegral base lam) (h0 : lam ≠ 0) {m : M} (hm : m ≠ 0) :
    UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m ≠ 0 := by
  rw [casimir_smul_of_isHighestWeightVector_of_lieSpan_eq_top hv hgen m]
  exact smul_ne_zero (casimirScalar_ne_zero hlam h0) hm

omit [CharZero K] in
/-- **The Casimir element acts by zero on a module with trivial action.** Every summand
`xᵢ yᵢ` of `Ω` acts by a double bracket, and brackets vanish. -/
theorem representation_casimirElement_eq_zero_of_isTrivial [LieModule.IsTrivial L M] (m : M) :
    UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m = 0 := by
  classical
  rw [casimirElement_eq_sum (Module.finBasis K L), map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [map_mul, Module.End.mul_apply, UniversalEnvelopingAlgebra.representation_ι,
    UniversalEnvelopingAlgebra.representation_ι]
  simp [trivial_lie_zero]

end TauCeti
