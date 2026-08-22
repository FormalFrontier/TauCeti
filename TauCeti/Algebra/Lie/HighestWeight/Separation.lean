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
# Casimir nonvanishing for nonzero dominant integral highest weights

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `base` be a base of its root
system. `TauCeti/Algebra/Lie/HighestWeight/Casimir.lean` computes the scalar by which the Casimir
element `Ω` acts on a highest weight module of weight `lam`, namely

`c(lam) = ⟨lam + ρ, lam + ρ⟩ - ⟨ρ, ρ⟩`.

This file proves that this scalar is **nonzero** as soon as `lam` is a nonzero dominant integral
weight (`TauCeti.casimirScalar_ne_zero`), while `Ω` acts by zero on a module with trivial action
(`TauCeti.representation_casimirElement_apply_eq_zero_of_isTrivial`). Together these statements
separate the trivial module from highest-weight modules whose dominant integral highest weight is
known to be nonzero. Applying this to every nontrivial finite-dimensional irreducible additionally
requires the theorem that an irreducible highest-weight module of highest weight zero is trivial;
that theorem is not proved here.

## The argument

Expanding the square, `c(lam) = ⟨lam, lam⟩ + ∑_{α > 0} ⟨lam, α⟩`
(`TauCeti.casimirScalar_eq_add_sum`), and both summands are read off by the
positivity of `TauCeti/Algebra/Lie/Weights/Positivity.lean`. A dominant integral weight is integral
(`TauCeti.IsDominantIntegral.isIntegralWeight`, the passage from the simple coroots to all of them
going through `TauCeti.IsDominantIntegral.exists_nat_apply_coroot` and, for a negative root, the
sign change `LieAlgebra.IsKilling.coroot_neg`), so `⟨lam, lam⟩` is a positive rational when
`lam ≠ 0`. And `⟨lam, α⟩ = ⟨α, α⟩ lam(α^∨) / 2` is a nonnegative rational for a positive root `α`,
the root length being positive and `lam(α^∨)` a natural number by dominance. A positive rational
plus nonnegative rationals is nonzero, and a nonzero rational stays nonzero in a field of
characteristic zero.

Dominance is essential, not decoration: for a general integral `lam` the two summands can have
opposite signs and `c(lam)` can vanish. For example, `lam = -2ρ` is integral and satisfies
`lam + ρ = -ρ`, hence `c(lam) = 0`.

## Main results

* `TauCeti.casimirScalar_ne_zero` and `TauCeti.casimirScalar_eq_zero_iff`: the Casimir scalar of a
  dominant integral weight vanishes exactly at the zero weight.
* `TauCeti.casimir_apply_ne_zero_of_isHighestWeightVector_of_lieSpan_eq_top`: on a highest weight
  module with nonzero dominant integral highest weight, the Casimir element kills no nonzero
  vector.
* `TauCeti.representation_casimirElement_apply_eq_zero_of_isTrivial`: on a module with trivial
  action the Casimir element acts by zero.

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

This distinguishes such a highest-weight module from a trivial module, whose Casimir scalar is
`0`. -/
theorem casimirScalar_ne_zero (hlam : IsDominantIntegral base lam) (h0 : lam ≠ 0) :
    casimirScalar base lam ≠ 0 := by
  classical
  rw [casimirScalar_eq_add_sum]
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
@[simp]
theorem casimirScalar_eq_zero_iff (hlam : IsDominantIntegral base lam) :
    casimirScalar base lam = 0 ↔ lam = 0 := by
  refine ⟨fun h ↦ by_contra fun h0 ↦ casimirScalar_ne_zero hlam h0 h, ?_⟩
  rintro rfl
  exact casimirScalar_zero

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

end TauCeti
