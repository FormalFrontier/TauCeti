/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.Order.Units
public import TauCeti.LinearAlgebra.RootSystem.Weyl.DotAction
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Sign

public section

/-!
# The two sides of the Weyl character formula

The Weyl character formula is an identity in the integral group algebra `ℤ[M]` of the weight space
of a root pairing, between the formal character of an irreducible module and the quotient of two
universal elements of that algebra. This file builds the two universal elements and their
combinatorics, with no Lie algebra in sight:

* the **Weyl denominator** `Δ = ∏_{α > 0} (1 - e^{-α})`, and
* the **Weyl numerator** `N(λ) = ∑_{w ∈ W} sgn(w) e^{w ⬝ λ}`, the alternating sum over the *dot*
  orbit of `λ`.

Writing the numerator through the dot action `w ⬝ λ = w(λ + ρ) - ρ` (`TauCeti.dotAction`) rather
than as `∑ sgn(w) e^{w(λ+ρ)}` is what keeps every exponent inside the weight lattice: the
symmetric form `∏_{α>0}(e^{α/2} - e^{-α/2})` of the denominator needs the half-weights `α/2`,
which are not weights, whereas `∏_{α>0}(1 - e^{-α})` and the `ρ`-shifted numerator both have all
their exponents in `M`. The two normalizations differ by the factor `e^{ρ}`.

The signs come from `TauCeti.weylSign`, the character `w ↦ (-1)^{ℓ(w)}` of the Weyl group; they
are what makes the numerator *alternating*, which is the content of
`TauCeti.weylNumerator_dotAction` and of everything derived from it.

## Main definitions

* `TauCeti.weylDenominator`: `Δ = ∏_{α > 0} (1 - e^{-α})`, an element of `ℤ[M]`.
* `TauCeti.weylNumerator`: `N(λ) = ∑_{w ∈ W} sgn(w) e^{w ⬝ λ}`, an element of `ℤ[M]`.

## Main results

* `TauCeti.weylDenominator_eq_sum_powerset`: expanding the product, `Δ` is the signed sum
  `∑_{T ⊆ Φ⁺} (-1)^{|T|} e^{-∑_{α ∈ T} α}` over the subsets of the positive roots; hence
  `TauCeti.coeff_weylDenominator_eq_zero`, that `Δ` is supported on the negatives of the sums of
  sets of positive roots.
* `TauCeti.weylNumerator_dotAction`: **the numerator is alternating**, `N(v ⬝ λ) = sgn(v) · N(λ)`.
* `TauCeti.weylNumerator_eq_zero_of_dotAction_eq_self`: a weight fixed by an odd element of the
  Weyl group has vanishing numerator, and `TauCeti.weylNumerator_eq_zero_of_coroot'_eq_neg_one`:
  so does a weight on a wall `⟨λ, αᵢ^∨⟩ = -1` of the dot action, which is the case the
  highest-weight theory meets.
* `TauCeti.coeff_weylNumerator_dotAction`, `TauCeti.support_coeff_weylNumerator` and
  `TauCeti.weylNumerator_ne_zero_of_mem_dominantChamber`: for a **dominant** weight the dot orbit
  has no repetitions, so the numerator has exactly `|W|` terms, with coefficients `±1`, and in
  particular does not vanish. Together with the two vanishing results this says the numerator sees
  the walls of the dot action.

## Implementation notes

`TauCeti.weylNumerator` sums over `Finset.univ` and so carries `[Fintype P.weylGroup]` rather than
`[Finite P.weylGroup]`. The Weyl group of a finite root system is finite
(`TauCeti.RootPairing.finite_weylGroup`), and a consumer holding only that instance
supplies the `Fintype` with `Fintype.ofFinite`; the value of the sum does not depend on which one,
since `Fintype` is a subsingleton.

The Weyl denominator asks for far less than the numerator: it is a product over the positive roots
of the base and needs neither the crystallographic nor the reduced hypothesis, nor an invertible
`2`, so it is stated in its own section carrying only the hypotheses `TauCeti.posRootsFinset`
needs. Symmetrically, the dominant-weight section drops `[IsDomain R]`, which the ordered
hypotheses it adds already imply.

## References

This builds the `weylDenominator` and `weylNumerator` targets of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, Layer 6 ("the character,
dimension, and Kostant formulas"), whose `Suggested.lean` pins them on `Module.Dual K H` for the
root system of a Cartan subalgebra. As with `TauCeti.weylVector` and `TauCeti.dotAction`, the
combinatorics lives at the level of an abstract root pairing, so the Lie-algebra target is a
specialization rather than a rebuild.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

/-! ### A product of basis elements -/

/-- A product of basis elements of an integral group algebra is the basis element at the sum of
the exponents, with the product of the coefficients. -/
private theorem prod_single {α : Type*} (s : Finset α) (f : α → M) (c : α → ℤ) :
    ∏ i ∈ s, AddMonoidAlgebra.single (f i) (c i)
      = AddMonoidAlgebra.single (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Finset.sum_empty, AddMonoidAlgebra.one_def]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, ih, AddMonoidAlgebra.single_mul_single, Finset.sum_insert hi,
      Finset.prod_insert hi]

omit [AddCommGroup M] in
/-- The negative of a basis element is the basis element with coefficient `-1`. -/
private theorem neg_single_one (m : M) :
    -AddMonoidAlgebra.single m (1 : ℤ) = AddMonoidAlgebra.single m (-1) := by
  rw [← neg_one_smul ℤ (AddMonoidAlgebra.single m (1 : ℤ)), AddMonoidAlgebra.smul_single', mul_one]

/-! ### The Weyl denominator -/

/-- **The Weyl denominator** `Δ = ∏_{α > 0} (1 - e^{-α})` of a base, an element of the integral
group algebra of the weight space.

This is the normalization all of whose exponents lie in the weight lattice; the symmetric form
`∏_{α>0} (e^{α/2} - e^{-α/2})` is `e^{ρ}` times this one and needs the half-weights `α/2`, which
are not weights. -/
noncomputable def weylDenominator : AddMonoidAlgebra ℤ M :=
  ∏ i ∈ posRootsFinset P b, (1 - AddMonoidAlgebra.single (-P.root i) 1)

/-- `TauCeti.weylDenominator` unfolded: the product of `1 - e^{-α}` over the positive roots. -/
theorem weylDenominator_def :
    weylDenominator P b = ∏ i ∈ posRootsFinset P b, (1 - AddMonoidAlgebra.single (-P.root i) 1) :=
  (rfl)

/-- **The Weyl denominator, expanded.** Multiplying out `∏_{α>0} (1 - e^{-α})` indexes the terms by
the subsets `T` of the positive roots, the term of `T` being `(-1)^{|T|} e^{-∑_{α ∈ T} α}`.

Every exponent occurring is therefore minus a sum of positive roots, which is the statement that
`Δ` lives in the negative cone; `TauCeti.coeff_weylDenominator_eq_zero` reads that off. -/
theorem weylDenominator_eq_sum_powerset :
    weylDenominator P b =
      ∑ T ∈ (posRootsFinset P b).powerset,
        AddMonoidAlgebra.single (-∑ i ∈ T, P.root i) ((-1) ^ T.card) := by
  classical
  have hrw : ∀ i : ι, (1 : AddMonoidAlgebra ℤ M) - AddMonoidAlgebra.single (-P.root i) 1
      = AddMonoidAlgebra.single (-P.root i) (-1) + 1 := fun i ↦ by
    rw [← neg_single_one, neg_add_eq_sub]
  rw [weylDenominator_def, Finset.prod_congr rfl fun i _ ↦ hrw i, Finset.prod_add]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [Finset.prod_const_one, mul_one, prod_single, Finset.prod_const, Finset.sum_neg_distrib]

/-- **The Weyl denominator is supported on the negative cone**: a coefficient of `Δ` at a weight
that is not minus the sum of a set of positive roots vanishes. -/
theorem coeff_weylDenominator_eq_zero {x : M}
    (hx : ∀ T ⊆ posRootsFinset P b, x ≠ -∑ i ∈ T, P.root i) :
    (weylDenominator P b).coeff x = 0 := by
  rw [weylDenominator_eq_sum_powerset, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  refine Finset.sum_eq_zero fun T hT ↦ ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply_eq_zero]
  exact fun h ↦ absurd h (hx T (Finset.mem_powerset.mp hT))

/-! ### The Weyl numerator -/

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

/-- `TauCeti.weylNumerator` unfolded: the signed sum over the dot orbit. -/
theorem weylNumerator_def (lam : M) :
    weylNumerator P b lam
      = ∑ w : P.weylGroup, AddMonoidAlgebra.single (dotAction P b w lam) ((weylSign P b w : ℤ)) :=
  (rfl)

/-- **The numerator is supported on the dot orbit**: its coefficient at a weight outside the orbit
of `λ` vanishes, since no term of the sum sits there. -/
theorem coeff_weylNumerator_eq_zero {lam x : M} (hx : ∀ w : P.weylGroup, dotAction P b w lam ≠ x) :
    (weylNumerator P b lam).coeff x = 0 := by
  rw [weylNumerator_def, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply_eq_zero]
  exact fun h ↦ absurd h (Ne.symm (hx w))

/-- **The Weyl numerator is alternating**: replacing `λ` by its dot translate `v ⬝ λ` multiplies
the numerator by `sgn(v)`.

This is the reindexing `w ↦ w * v` of the defining sum, and it is the source of every vanishing
statement below: a weight fixed by an odd element of the Weyl group is one where the sum cancels
against itself. -/
theorem weylNumerator_dotAction (v : P.weylGroup) (lam : M) :
    weylNumerator P b (dotAction P b v lam)
      = ((weylSign P b v : ℤ)) • weylNumerator P b lam := by
  rw [weylNumerator_def, weylNumerator_def, Finset.smul_sum]
  refine Fintype.sum_bijective (· * v) (Group.mulRight_bijective v) _ _ fun w ↦ ?_
  have hsign : weylSign P b v * weylSign P b (w * v) = weylSign P b w := by
    rw [map_mul, ← mul_assoc, mul_comm (weylSign P b v) (weylSign P b w), mul_assoc,
      Int.units_mul_self, mul_one]
  rw [← dotAction_mul, AddMonoidAlgebra.smul_single', ← Units.val_mul, hsign]

/-- **A weight fixed by an odd Weyl-group element has vanishing numerator.** The alternating
identity turns such a fixed point into `N(λ) = -N(λ)`. -/
theorem weylNumerator_eq_zero_of_dotAction_eq_self {v : P.weylGroup} {lam : M}
    (hv : weylSign P b v = -1) (hlam : dotAction P b v lam = lam) :
    weylNumerator P b lam = 0 := by
  have key : -weylNumerator P b lam = weylNumerator P b lam := by
    have h := weylNumerator_dotAction P b v lam
    rw [hlam, hv] at h
    simpa using h.symm
  have hadd : weylNumerator P b lam + weylNumerator P b lam = 0 := by
    nth_rewrite 1 [← key]
    rw [neg_add_cancel]
  refine AddMonoidAlgebra.ext (Finsupp.ext fun y ↦ ?_)
  have hy : (weylNumerator P b lam).coeff y + (weylNumerator P b lam).coeff y = 0 := by
    simpa using congrArg (fun z : AddMonoidAlgebra ℤ M ↦ z.coeff y) hadd
  have hzero : (0 : AddMonoidAlgebra ℤ M).coeff y = 0 := by simp
  rw [hzero]
  omega

/-- **A weight on a wall of the dot action has vanishing numerator.** The wall of the simple
reflection `sᵢ` for the dot action is `⟨λ, αᵢ^∨⟩ = -1` (`TauCeti.dotAction_ofIdx_eq_self_iff`), and
a simple reflection is odd. This is the case the highest-weight theory meets: the numerator of a
weight that is not dot-regular carries no information. -/
theorem weylNumerator_eq_zero_of_coroot'_eq_neg_one {i : ι} (hi : i ∈ b.support) {lam : M}
    (h : P.coroot' i lam = -1) : weylNumerator P b lam = 0 :=
  weylNumerator_eq_zero_of_dotAction_eq_self P b (weylSign_ofIdx P b i)
    ((dotAction_ofIdx_eq_self_iff P b hi lam).mpr h)

end Numerator

/-! ### Dominant weights

For a dominant weight the dot action is free
(`TauCeti.eq_one_of_dotAction_eq_self_of_mem_dominantChamber`), so the `|W|` terms of the numerator
sit at `|W|` distinct weights and none of them cancels. The linearly ordered hypotheses of this
section already supply `IsDomain R` through `IsStrictOrderedRing.isDomain`, so it is not repeated.
-/

section Dominant

variable [Invertible (2 : R)] [P.IsCrystallographic] [P.IsReduced] [Fintype P.weylGroup]
  [LinearOrder R] [IsStrictOrderedRing R] [P.flip.IsReduced]

/-- **The coefficients of the numerator of a dominant weight are the signs.** No two Weyl-group
elements carry a dominant weight to the same place, so the term of `w` sits alone at `w ⬝ λ`. -/
theorem coeff_weylNumerator_dotAction {lam : M} (hlam : lam ∈ dominantChamber P b)
    (w : P.weylGroup) :
    (weylNumerator P b lam).coeff (dotAction P b w lam) = ((weylSign P b w : ℤ)) := by
  rw [weylNumerator_def, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single w]
  · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro v _ hvw
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply_eq_zero]
    intro h
    refine absurd ?_ hvw
    exact ((dotAction_eq_dotAction_iff_of_mem_dominantChamber P b hlam hlam).mp h).2.symm
  · exact fun h ↦ absurd (Finset.mem_univ w) h

/-- **The numerator of a dominant weight is supported exactly on its dot orbit.** -/
theorem support_coeff_weylNumerator [DecidableEq M] {lam : M}
    (hlam : lam ∈ dominantChamber P b) :
    (weylNumerator P b lam).coeff.support
      = Finset.univ.image fun w : P.weylGroup ↦ dotAction P b w lam := by
  ext y
  rw [Finsupp.mem_support_iff, Finset.mem_image]
  refine ⟨fun hy ↦ ?_, ?_⟩
  · by_contra hcon
    exact hy (coeff_weylNumerator_eq_zero P b fun w h ↦ hcon ⟨w, Finset.mem_univ w, h⟩)
  · rintro ⟨w, -, rfl⟩
    rw [coeff_weylNumerator_dotAction P b hlam w]
    exact_mod_cast Units.ne_zero (weylSign P b w)

/-- **The numerator of a dominant weight has exactly `|W|` terms**, one for each element of the
Weyl group. -/
theorem card_support_coeff_weylNumerator {lam : M} (hlam : lam ∈ dominantChamber P b) :
    (weylNumerator P b lam).coeff.support.card = Fintype.card P.weylGroup := by
  classical
  rw [support_coeff_weylNumerator P b hlam, Finset.card_image_of_injective _
      fun v w h ↦ ((dotAction_eq_dotAction_iff_of_mem_dominantChamber P b hlam hlam).mp h).2,
    Finset.card_univ]

/-- **The numerator of a dominant weight does not vanish**: its coefficient at `λ` itself is `1`.
With `TauCeti.weylNumerator_eq_zero_of_coroot'_eq_neg_one` this says the numerator vanishes on the
weights the dot action does not move freely, and on no dominant weight. -/
theorem weylNumerator_ne_zero_of_mem_dominantChamber {lam : M}
    (hlam : lam ∈ dominantChamber P b) : weylNumerator P b lam ≠ 0 := by
  intro hcon
  have h := coeff_weylNumerator_dotAction P b hlam 1
  rw [dotAction_one, hcon, map_one] at h
  simp at h

end Dominant

end TauCeti
