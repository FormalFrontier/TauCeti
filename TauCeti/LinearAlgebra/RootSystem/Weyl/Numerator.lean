/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Int.Order.Units
public import TauCeti.LinearAlgebra.RootSystem.Weyl.DotAction
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Sign

/-!
# The Weyl numerator

The Weyl character formula is an identity in the integral group algebra `ℤ[M]` of the weight space
of a root pairing, between the formal character of an irreducible module and two universal
elements of that algebra: the Weyl numerator `N(λ)` and the Weyl denominator `Δ`. As soon as there
is a positive root, `Δ` is not invertible in `ℤ[M]` — it then augments to `0`, whereas a unit
augments to `±1` — so the formula is read there in the cross-multiplied form
`ch L(λ) · Δ = N(λ)`, the familiar quotient `N(λ) / Δ` living in a localization where `Δ` becomes
invertible. This file builds the **Weyl numerator**
`N(λ) = ∑_{w ∈ W} sgn(w) e^{w ⬝ λ}`, the alternating sum over the *dot* orbit of `λ`, and its
combinatorics, with no Lie algebra in sight. The denominator `Δ = ∏_{α > 0} (1 - e^{-α})` is
`TauCeti.weylDenominator`, which needs far less and lives in its own earlier file.

Writing the numerator through the dot action `w ⬝ λ = w(λ + ρ) - ρ` (`TauCeti.dotAction`) rather
than as `∑ sgn(w) e^{w(λ+ρ)}` is what keeps every exponent inside the weight lattice, matching the
normalization `∏_{α>0}(1 - e^{-α})` of the denominator rather than the symmetric one
`∏_{α>0}(e^{α/2} - e^{-α/2})`, which needs half-roots. The two normalizations differ by the factor
`e^{ρ}`.

The signs come from `TauCeti.weylSign`, the character `w ↦ (-1)^{ℓ(w)}` of the Weyl group; they
are what makes the numerator *alternating*, which is the content of
`TauCeti.weylNumerator_dotAction` and of everything derived from it.

## Main definitions

* `TauCeti.weylNumerator`: `N(λ) = ∑_{w ∈ W} sgn(w) e^{w ⬝ λ}`, an element of `ℤ[M]`.

## Main results

* `TauCeti.weylNumerator_dotAction`: **the numerator is alternating**, `N(v ⬝ λ) = sgn(v) · N(λ)`;
  `TauCeti.coeff_weylNumerator_dotAction` is the corresponding coefficient transformation rule.
* `TauCeti.weylNumerator_eq_zero_of_dotAction_eq_self`: a weight fixed by an odd element of the
  Weyl group has vanishing numerator, and `TauCeti.weylNumerator_eq_zero_of_coroot'_eq_neg_one`:
  so does a weight on a wall `⟨λ, αᵢ^∨⟩ = -1` of a simple reflection for the dot action, which is
  the case the highest-weight theory meets.
* `TauCeti.coeff_weylNumerator_dotAction_of_injective`,
  `TauCeti.support_coeff_weylNumerator_of_injective`,
  `TauCeti.card_support_coeff_weylNumerator_of_injective` and
  `TauCeti.weylNumerator_ne_zero_of_injective`: when the dot orbit map `w ↦ w ⬝ λ` is injective the
  `|W|` terms sit at `|W|` distinct weights, so the coefficient at `w ⬝ λ` is `sgn(w)`, the support
  is exactly the dot orbit and has `|W|` elements, and the numerator does not vanish. A **dominant**
  weight has an injective dot orbit map by
  `TauCeti.dotAction_eq_dotAction_iff_of_mem_dominantChamber`, whence
  `TauCeti.support_coeff_weylNumerator`, `TauCeti.card_support_coeff_weylNumerator` and
  `TauCeti.weylNumerator_ne_zero_of_mem_dominantChamber`.

## Implementation notes

`TauCeti.weylNumerator` sums over `Finset.univ` and so carries `[Fintype P.weylGroup]` rather than
`[Finite P.weylGroup]`. The Weyl group of a finite root system is finite
(`TauCeti.RootPairing.finite_weylGroup`), and a consumer holding only that instance
supplies the `Fintype` with `Fintype.ofFinite`; the value of the sum does not depend on which one,
since `Fintype` is a subsingleton.

The freeness statements are proved from the injectivity of the dot orbit map, which is all they
use; dominance enters only through the corollaries of the last section, which is also the only
place the ordered hypotheses appear. Those hypotheses already supply `IsDomain R` through
`IsStrictOrderedRing.isDomain`, so it is not repeated there.

## References

This builds the `weylNumerator` target of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, Layer 6 ("the character,
dimension, and Kostant formulas"), whose `Suggested.lean` pins it on `Module.Dual K H` for the root
system of a Cartan subalgebra. As with `TauCeti.weylVector` and `TauCeti.dotAction`, the
combinatorics lives at the level of an abstract root pairing, so the Lie-algebra target is a
specialization rather than a rebuild.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII.
-/

public section

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

section Numerator

variable [IsDomain R] [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced]
  [Fintype P.weylGroup]

/-- **The Weyl numerator** `N(λ) = ∑_{w ∈ W} sgn(w) e^{w ⬝ λ}` of a weight, the alternating sum
over the *dot* orbit of `λ`.

The dot action `w ⬝ λ = w(λ + ρ) - ρ` (`TauCeti.dotAction`) is the `ρ`-shifted form: the
un-shifted numerator `∑_w sgn(w) e^{w(λ+ρ)}` is `e^{ρ}` times this one, and matches the symmetric
normalization of the denominator rather than `TauCeti.weylDenominator`. -/
noncomputable def weylNumerator (lam : M) : AddMonoidAlgebra ℤ M :=
  ∑ w : P.weylGroup, AddMonoidAlgebra.single (dotAction P b w lam) ((weylSign P b w : ℤ))

/-- `N(λ)` is the signed sum `∑_{w ∈ W} sgn(w) e^{w ⬝ λ}` over the dot orbit, by definition. -/
lemma weylNumerator_def (lam : M) : weylNumerator P b lam =
    ∑ w : P.weylGroup, AddMonoidAlgebra.single (dotAction P b w lam) ((weylSign P b w : ℤ)) := by
  rw [weylNumerator]

/-- **The numerator is supported on the dot orbit**: its coefficient at a weight outside the orbit
of `λ` vanishes, since no term of the sum sits there. -/
theorem coeff_weylNumerator_eq_zero {lam x : M} (hx : ∀ w : P.weylGroup, dotAction P b w lam ≠ x) :
    (weylNumerator P b lam).coeff x = 0 := by
  simp only [weylNumerator_def, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single]
  exact Finset.sum_eq_zero fun w _ ↦
    Finsupp.single_apply_eq_zero.mpr fun h ↦ absurd h (Ne.symm (hx w))

/-- **The Weyl numerator is alternating**: replacing `λ` by its dot translate `v ⬝ λ` multiplies
the numerator by `sgn(v)`.

This is the reindexing `w ↦ w * v` of the defining sum, and it is the source of every vanishing
statement below: a weight fixed by an odd element of the Weyl group is one where the sum cancels
against itself. -/
@[simp]
theorem weylNumerator_dotAction (v : P.weylGroup) (lam : M) :
    weylNumerator P b (dotAction P b v lam)
      = ((weylSign P b v : ℤ)) • weylNumerator P b lam := by
  rw [weylNumerator_def, weylNumerator_def, Finset.smul_sum]
  refine Fintype.sum_bijective (· * v) (Group.mulRight_bijective v) _ _ fun w ↦ ?_
  have hsign : weylSign P b v * weylSign P b (w * v) = weylSign P b w := by
    rw [map_mul, mul_left_comm, Int.units_mul_self, mul_one]
  rw [← dotAction_mul, AddMonoidAlgebra.smul_single', ← Units.val_mul, hsign]

/-- **The coefficients of the Weyl numerator transform by the sign character under the dot
action:** `[e^{w ⬝ x}] N(λ) = sgn(w) [e^x] N(λ)`. -/
@[simp]
theorem coeff_weylNumerator_dotAction (lam : M) (w : P.weylGroup) (x : M) :
    (weylNumerator P b lam).coeff (dotAction P b w x) =
      (weylSign P b w : ℤ) * (weylNumerator P b lam).coeff x := by
  simp only [weylNumerator_def, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finset.mul_sum]
  refine Fintype.sum_bijective (w⁻¹ * ·) (Group.mulLeft_bijective w⁻¹) _ _ fun v ↦ ?_
  have hsign : weylSign P b w * weylSign P b (w⁻¹ * v) = weylSign P b v := by
    rw [← map_mul, mul_inv_cancel_left]
  have hdot : dotAction P b (w⁻¹ * v) lam = x ↔ dotAction P b v lam = dotAction P b w x := by
    rw [dotAction_mul]
    exact ⟨fun h ↦ by rw [← h, dotAction_dotAction_inv],
      fun h ↦ by rw [h, dotAction_inv_dotAction]⟩
  by_cases hv : dotAction P b v lam = dotAction P b w x
  · rw [hv, Finsupp.single_eq_same, (hdot.mpr hv), Finsupp.single_eq_same, ← Units.val_mul, hsign]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hv),
      Finsupp.single_eq_of_ne (Ne.symm fun h ↦ hv (hdot.mp h)), mul_zero]

/-- **A weight fixed by an odd Weyl-group element has vanishing numerator.** The alternating
identity turns such a fixed point into `N(λ) = -N(λ)`, and `ℤ[M]` is torsion-free. -/
theorem weylNumerator_eq_zero_of_dotAction_eq_self {v : P.weylGroup} {lam : M}
    (hv : weylSign P b v = -1) (hlam : dotAction P b v lam = lam) :
    weylNumerator P b lam = 0 := by
  have key : weylNumerator P b lam = -weylNumerator P b lam := by
    have h := weylNumerator_dotAction P b v lam
    rw [hlam, hv] at h
    simpa using h
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  refine two_nsmul_eq_zero.mp ?_
  rw [two_nsmul, ← AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_eq_zero]
  exact add_eq_zero_iff_eq_neg.mpr key

/-- **A weight on a wall of the dot action has vanishing numerator.** The wall of the simple
reflection `sᵢ` for the dot action is `⟨λ, αᵢ^∨⟩ = -1` (`TauCeti.dotAction_ofIdx_eq_self_iff`), and
a simple reflection is odd. This is the case the highest-weight theory meets. -/
theorem weylNumerator_eq_zero_of_coroot'_eq_neg_one {i : ι} (hi : i ∈ b.support) {lam : M}
    (h : P.coroot' i lam = -1) : weylNumerator P b lam = 0 :=
  weylNumerator_eq_zero_of_dotAction_eq_self P b (weylSign_ofIdx P b i)
    ((dotAction_ofIdx_eq_self_iff P b hi lam).mpr h)

/-! ### Weights with a free dot orbit

Nothing below asks for more than the injectivity of the dot orbit map `w ↦ w ⬝ λ`: it makes the
`|W|` terms of the numerator sit at `|W|` distinct weights, so none of them cancels. A dominant
weight is the case of interest, and is treated in the last section.
-/

/-- **The coefficients of the numerator along a free dot orbit are the signs.** No two Weyl-group
elements carry `λ` to the same place, so the term of `w` sits alone at `w ⬝ λ`. -/
theorem coeff_weylNumerator_dotAction_of_injective {lam : M}
    (hlam : Function.Injective fun w : P.weylGroup ↦ dotAction P b w lam) (w : P.weylGroup) :
    (weylNumerator P b lam).coeff (dotAction P b w lam) = ((weylSign P b w : ℤ)) := by
  simp only [weylNumerator_def, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single w]
  · exact Finsupp.single_eq_same
  · exact fun v _ hvw ↦ Finsupp.single_eq_of_ne fun h ↦ hvw (hlam h.symm)
  · exact fun h ↦ absurd (Finset.mem_univ w) h

/-- **A numerator with a free dot orbit is supported exactly on that orbit.** -/
theorem support_coeff_weylNumerator_of_injective [DecidableEq M] {lam : M}
    (hlam : Function.Injective fun w : P.weylGroup ↦ dotAction P b w lam) :
    (weylNumerator P b lam).coeff.support
      = Finset.univ.image fun w : P.weylGroup ↦ dotAction P b w lam := by
  ext y
  rw [Finsupp.mem_support_iff, Finset.mem_image]
  refine ⟨fun hy ↦ ?_, ?_⟩
  · by_contra hcon
    exact hy (coeff_weylNumerator_eq_zero P b fun w h ↦ hcon ⟨w, Finset.mem_univ w, h⟩)
  · rintro ⟨w, -, rfl⟩
    rw [coeff_weylNumerator_dotAction_of_injective P b hlam w]
    exact_mod_cast Units.ne_zero (weylSign P b w)

/-- **A numerator with a free dot orbit has exactly `|W|` terms**, one for each element of the
Weyl group. -/
theorem card_support_coeff_weylNumerator_of_injective {lam : M}
    (hlam : Function.Injective fun w : P.weylGroup ↦ dotAction P b w lam) :
    (weylNumerator P b lam).coeff.support.card = Fintype.card P.weylGroup := by
  classical
  rw [support_coeff_weylNumerator_of_injective P b hlam,
    Finset.card_image_of_injective _ hlam, Finset.card_univ]

/-- **A numerator with a free dot orbit does not vanish**: its coefficient at `λ` itself is `1`. -/
theorem weylNumerator_ne_zero_of_injective {lam : M}
    (hlam : Function.Injective fun w : P.weylGroup ↦ dotAction P b w lam) :
    weylNumerator P b lam ≠ 0 := by
  intro hcon
  have h := coeff_weylNumerator_dotAction_of_injective P b hlam 1
  rw [dotAction_one, hcon, map_one] at h
  simp at h

end Numerator

/-! ### Dominant weights

For a dominant weight the dot action is free
(`TauCeti.eq_one_of_dotAction_eq_self_of_mem_dominantChamber`), so the results of the previous
section apply verbatim. The linearly ordered hypotheses of this section already supply
`IsDomain R` through `IsStrictOrderedRing.isDomain`, so it is not repeated.
-/

section Dominant

variable [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced] [Fintype P.weylGroup]
  [LinearOrder R] [IsStrictOrderedRing R] [P.flip.IsReduced]

/-- **The numerator of a weight of the open dot chamber has coefficient `1` there.** -/
@[simp]
theorem coeff_weylNumerator_self_of_mem_openDotDominantChamber {lam : M}
    (hlam : lam ∈ openDotDominantChamber P b) : (weylNumerator P b lam).coeff lam = 1 := by
  have h := coeff_weylNumerator_dotAction_of_injective P b
    (dotAction_injective_of_mem_openDotDominantChamber P b hlam) 1
  rwa [dotAction_one, map_one, Units.val_one] at h

omit [Fintype P.weylGroup] in
/-- The dot orbit map of a dominant weight is injective: a dominant weight is reached from itself
by a unique Weyl-group element. -/
private lemma injective_dotAction_of_mem_dominantChamber {lam : M}
    (hlam : lam ∈ dominantChamber P b) :
    Function.Injective fun w : P.weylGroup ↦ dotAction P b w lam :=
  fun _ _ h ↦ ((dotAction_eq_dotAction_iff_of_mem_dominantChamber P b hlam hlam).mp h).2

/-- **The numerator of a dominant weight is supported exactly on its dot orbit.** -/
theorem support_coeff_weylNumerator [DecidableEq M] {lam : M}
    (hlam : lam ∈ dominantChamber P b) :
    (weylNumerator P b lam).coeff.support
      = Finset.univ.image fun w : P.weylGroup ↦ dotAction P b w lam :=
  support_coeff_weylNumerator_of_injective P b
    (injective_dotAction_of_mem_dominantChamber P b hlam)

/-- **The numerator of a dominant weight has exactly `|W|` terms**, one for each element of the
Weyl group. -/
theorem card_support_coeff_weylNumerator {lam : M} (hlam : lam ∈ dominantChamber P b) :
    (weylNumerator P b lam).coeff.support.card = Fintype.card P.weylGroup :=
  card_support_coeff_weylNumerator_of_injective P b
    (injective_dotAction_of_mem_dominantChamber P b hlam)

/-- **The numerator of a dominant weight does not vanish**: its coefficient at `λ` itself is `1`.
With `TauCeti.weylNumerator_eq_zero_of_coroot'_eq_neg_one` this says the numerator vanishes on the
walls of the simple reflections for the dot action, and on no dominant weight. -/
theorem weylNumerator_ne_zero_of_mem_dominantChamber {lam : M}
    (hlam : lam ∈ dominantChamber P b) : weylNumerator P b lam ≠ 0 :=
  weylNumerator_ne_zero_of_injective P b (injective_dotAction_of_mem_dominantChamber P b hlam)

end Dominant

end TauCeti
