/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.StronglyNoetherian
public import TauCeti.RingTheory.Huber.WeightedEval.Quotient

import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# The Laurent quotient of a numerator enlargement, and the maps between it and `A⟨T'/s⟩`

Let `(T', s)` refine `(T, s)` by enlarging the numerators, and let `t ∈ T'`. Adjoining a variable
`X` to `A⟨T/s⟩` and imposing the relation `X = t/s` gives `A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)`. This file
constructs the two canonical continuous ring homomorphisms between that quotient and `A⟨T'/s⟩`,
each the only one of its kind:

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  →  A⟨T'/s⟩          constants ↦ restriction,  X ↦ t/s
A⟨T'/s⟩  →  A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)          compatibly with the structure maps from `A`
```

The first needs nothing of the shape of `T'`, which is what keeps `DecidableEq A` out of the
statements. The second needs the numerators of `T'` to be exhausted by those of `T` together with
`t`, since the fractions `u/s` for `u ∈ T'` must land in the power-bounded elements of the
quotient; that is the hypothesis `hsplit`, again a splitting rather than `T' = insert t T`. It
needs one hypothesis more, to make its target a legitimate one for the universal property of
`A⟨T'/s⟩`: the relation ideal must be **closed**, which is what separates the quotient. A
topologically nilpotent `s` over a strongly noetherian `A⟨T/s⟩` gives that, and the
`..._of_isStronglyNoetherian` forms below take those two in its place.

**The two maps are mutually inverse**, under the same `hsplit` that the second one needs, and so
the quotient *is* `A⟨T'/s⟩`: this is Wedhorn's Remark 7.55, and
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv` is the resulting isomorphism. For a
general enlargement no identification is expected, since `T'` may adjoin numerators other than
`t`; `hsplit` is what rules that out. Proposition 8.30 consumes the identification to reduce
flatness of an arbitrary restriction map to the elementary one-numerator case.

The restriction map itself, and the fact that it carries `t/s` to `t/s`, live one file earlier in
`TauCeti.RingTheory.Huber.LocalizationTopology.Restriction`: they need only the
restriction/localisation theory, not the weighted-evaluation machinery imported here.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal`: the ideal `(t/s - X)` of `A⟨T/s⟩⟨X⟩`,
  where `t/s` is `TauCeti.Localization.divBy` read in the completion via
  `TauCeti.Huber.PairOfDefinition.toCompletionLoc_mul_unit_inv_eq_divBy`.

## Main results

* `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal_quotientMk_weightedC`: in the quotient,
  the constant `t/s` and the variable `X` agree. This is the relation the ideal imposes.
* `TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_laurentQuotient_restriction`:
  the map out of the quotient, with its uniqueness; and
  `TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom`, that map named, with
  `TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRestrictionRingHom`, its two
  evaluation lemmas and `TauCeti.Huber.PairOfDefinition.eq_laurentQuotientRestrictionRingHom`
  as its interface.
* `TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_laurentQuotient`:
  the map into it, with its uniqueness, for a closed relation ideal; the
  `..._of_isStronglyNoetherian` variant takes the hypotheses in the form they are met in.
* `TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom`: that map, named, with
  `TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRingHom`,
  `TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom_comp_toCompletionLoc` and
  `TauCeti.Huber.PairOfDefinition.eq_laurentQuotientRingHom` as its interface.
* `TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv`: **Wedhorn's Remark 7.55** — the two
  maps are mutually inverse, so `A⟨T/s⟩⟨X⟩ ⧸ (t/s - X) ≃+* A⟨T'/s⟩`, with
  `TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRingEquiv`, its `symm` form and two
  coercion `@[simp]` lemmas as its interface. The two composite identities it is built from,
  `TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom_comp_laurentQuotientRingHom`
  and
  `TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom_comp_laurentQuotientRestrictionRingHom`,
  are available separately.
* `TauCeti.Huber.PairOfDefinition.isClosed_laurentRelationIdeal`: the relation ideal is closed
  when `A⟨T/s⟩` is Tate and `A⟨T/s⟩⟨X⟩` is noetherian; the `..._of_isStronglyNoetherian` variant
  takes a topologically nilpotent denominator over a strongly noetherian base instead.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.55 and
  Proposition 8.30.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

open scoped Uniformity

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (s t : A)
  (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

/-- **The Laurent relation ideal** of `A⟨T/s⟩⟨X⟩`: the ideal generated by `t/s - X`. -/
noncomputable def laurentRelationIdeal :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    Ideal (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  Ideal.span {weightedC _ isWeightFamily_one_weight ((divBy t s : S) : UniformSpace.Completion S) -
    weightedX _ isWeightFamily_one_weight 0}

/-- Unfolding lemma for `TauCeti.Huber.PairOfDefinition.laurentRelationIdeal`. -/
theorem laurentRelationIdeal_def :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    laurentRelationIdeal P T s t S hden = Ideal.span
      {weightedC _ isWeightFamily_one_weight ((divBy t s : S) : UniformSpace.Completion S) -
        weightedX _ isWeightFamily_one_weight 0} := (rfl)

/-- **The relation the ideal imposes**: in `A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` the constant `t/s` and the
variable `X` have the same class. This is what a consumer needs, rather than the span. -/
@[simp]
theorem laurentRelationIdeal_quotientMk_weightedC :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
        (weightedC _ isWeightFamily_one_weight ((divBy t s : S) : UniformSpace.Completion S))
      = Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
        (weightedX _ isWeightFamily_one_weight 0) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, laurentRelationIdeal_def]
  exact Ideal.subset_span rfl

/-- **The Laurent relation ideal is closed** when `A⟨T/s⟩` is Tate and `A⟨T/s⟩⟨X⟩` is
noetherian: in a complete metrisable noetherian Tate ring every submodule is closed. Closedness
is what the quotient needs to be separated, and hence a legitimate target for the universal
property of a completion. -/
theorem isClosed_laurentRelationIdeal
    (hTate : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsTateRing (UniformSpace.Completion S))
    (hnoeth : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsNoetherianRing (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  -- the types of `hTate` and `hnoeth` are `let`s, so they are instances only once re-elaborated
  have _ := hTate
  have _ := hnoeth
  have _ : (𝓤 (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S)))
        isWeightFamily_one_weight)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  exact isClosed_of_isNoetherian _

/-- **The Laurent relation ideal is closed**, for a topologically nilpotent denominator over a
strongly noetherian base. A topologically nilpotent `s` makes `A⟨T/s⟩` a Tate ring, and the
`k = 1` component of strong noetherianity makes `A⟨T/s⟩⟨X⟩` noetherian. -/
theorem isClosed_laurentRelationIdeal_of_isStronglyNoetherian
    (hnil : IsTopologicallyNilpotent s)
    (hSN : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  have _ := hSN
  exact isClosed_laurentRelationIdeal P T s t S hden
    (isTateRing_completion_locTopology_of_isTopologicallyNilpotent P T s S hden hnil)
    (isNoetherianRing_of_ringEquiv _
      (restrictedMvPowerSeriesCompletionEquiv 1 (UniformSpace.Completion S)))

-- Each fraction `u/s` allowed by the splitting is power-bounded in the Laurent quotient: an old
-- numerator is already power-bounded in `A⟨T/s⟩`, and the new one `t` is the class of the
-- variable, which is power-bounded because the weight is `{1}`.
private theorem isPowerBounded_quotientMk_weightedC_fraction :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    ∀ (hs : IsUnit (toCompletionLoc P T s S hden s)) {u : A}, u ∈ T ∨ u = t →
      IsPowerBounded (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
        (weightedC _ isWeightFamily_one_weight
          (toCompletionLoc P T s S hden u * ↑hs.unit⁻¹))) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  rintro hs u (h | h)
  · exact (isPowerBounded_weightedC (k := 1) isWeightFamily_one_weight
      (isPowerBounded_toCompletionLoc_mul_unit_inv P T s S hden (mul_one s).symm hs
        (by simpa using h))).map_of_isOpenMap continuous_quotient_mk'.continuousAt
      (QuotientRing.isOpenMap_coe _)
  · rw [h, toCompletionLoc_mul_unit_inv_eq_divBy P T s S hden t hs,
      laurentRelationIdeal_quotientMk_weightedC P T s t S hden]
    exact (isPowerBounded_weightedX (k := 1) isWeightFamily_one_weight
      rfl).map_of_isOpenMap continuous_quotient_mk'.continuousAt
      (QuotientRing.isOpenMap_coe _)

section OneStep

variable (T' : Finset A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P T' s S') (hTT' : ∀ u ∈ T, u ∈ T')

-- The abbreviation the two maps of this section are compared through: the structure map of the
-- Laurent quotient, `a ↦ [a]` on constants.
private noncomputable abbrev laurentStructureHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    UniformSpace.Completion S →+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
    (weightedC _ isWeightFamily_one_weight)

section OneStep

variable (T' : Finset A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P T' s S') (hTT' : ∀ u ∈ T, u ∈ T')

/-- **The canonical evaluation out of the Laurent quotient.** There is exactly one
continuous ring homomorphism

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  →  A⟨T'/s⟩
```

restricting to `TauCeti.Huber.PairOfDefinition.restrictionRingHomOfSubset` on constants, and
sending `X` to `t/s`.

The only fact particular to this situation is
`TauCeti.Huber.PairOfDefinition.restrictionRingHomOfSubset_coe_divBy`; everything else is the
universal property
`TauCeti.Huber.existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring` of the
quotient. In the special case `T' = insert t T`, Wedhorn's Remark 7.55 chains such refinements and
Proposition 8.30 reduces flatness of a general restriction map along that chain to the elementary
one; the identification that reduction needs is
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv`, below. -/
theorem existsUnique_continuous_ringHom_laurentQuotient_restriction (ht : t ∈ T') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P (T') s S' hden'
    letI := isUniformAddGroup_locUniformSpace P (T') s S' hden'
    letI := isTopologicalRing_locUniformSpace P (T') s S' hden'
    letI := isHuberRing_locUniformSpace P (T') s S' hden'
    ∃! ψ : (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight) ⧸
          laurentRelationIdeal P T s t S hden →+* UniformSpace.Completion S',
      Continuous ψ ∧
      (∀ a, ψ (Ideal.Quotient.mk _ (weightedC _ isWeightFamily_one_weight a)) =
        restrictionRingHomOfSubset P T s S hden T' S' hden' hTT' a) ∧
      ∀ i, ψ (Ideal.Quotient.mk _ (weightedX _ isWeightFamily_one_weight i)) =
        ((divBy t s : S') : UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P (T') s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P (T') s S' hden'
  have _ := isTopologicalRing_locUniformSpace P (T') s S' hden'
  have _ := isHuberRing_locUniformSpace P (T') s S' hden'
  have hu' : IsUnit (toCompletionLoc P (T') s S' hden' s) :=
    isUnit_toCompletionLoc_of_dvd P (T') s S' hden' dvd_rfl
  set φ := restrictionRingHomOfSubset P T s S hden T' S' hden' hTT' with hφdef
  have hφ : ContinuousAt φ 0 :=
    (continuous_restrictionRingHomOfSubset P T s S hden T' S' hden' hTT').continuousAt
  set b : Fin 1 → UniformSpace.Completion S' :=
    fun _ ↦ ((divBy t s : S') : UniformSpace.Completion S') with hbdef
  have hb : IsWeightBounded φ (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) b :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).2 fun _ ↦ by
      rw [hbdef, ← toCompletionLoc_mul_unit_inv_eq_divBy P (T') s S' hden' t hu']
      exact isPowerBounded_toCompletionLoc_mul_unit_inv P (T') s S' hden'
        (mul_one s).symm hu' (by simpa using ht)
  -- the evaluation kills `t/s - X`, so the relation ideal lands in its kernel
  have h𝔞 : laurentRelationIdeal P T s t S hden ≤
      RingHom.ker (weightedEvalHom isWeightFamily_one_weight hφ hb) := by
    rw [laurentRelationIdeal_def, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker, map_sub, weightedEvalHom_weightedC, weightedEvalHom_weightedX,
      sub_eq_zero]
    exact restrictionRingHomOfSubset_coe_divBy P T s S hden T' S' hden' hTT' t
  exact existsUnique_continuous_ringHom_quotient_weightedRestrictedSubring
    isWeightFamily_one_weight hφ hb h𝔞

/-- **The map out of the Laurent quotient**, `A⟨T/s⟩⟨X⟩ ⧸ (t/s - X) → A⟨T'/s⟩`.

Its defining properties are
`TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRestrictionRingHom`,
`TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom_quotientMk_weightedC` and
`TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom_quotientMk_weightedX`, and
`TauCeti.Huber.PairOfDefinition.eq_laurentQuotientRestrictionRingHom` says they determine it.
This is the companion of `TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom`, in the other
direction. -/
noncomputable def laurentQuotientRestrictionRingHom (ht : t ∈ T') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) →+* UniformSpace.Completion S' :=
  (existsUnique_continuous_ringHom_laurentQuotient_restriction P T s t S hden T' S' hden'
    hTT' ht).choose

/-- The map out of the Laurent quotient is continuous. -/
theorem continuous_laurentQuotientRestrictionRingHom (ht : t ∈ T') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    Continuous (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht) :=
  (existsUnique_continuous_ringHom_laurentQuotient_restriction P T s t S hden T' S' hden'
    hTT' ht).choose_spec.1.1

/-- **On constants the map out of the Laurent quotient is the restriction map.** -/
@[simp]
theorem laurentQuotientRestrictionRingHom_quotientMk_weightedC (ht : t ∈ T')
    (a : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      UniformSpace.Completion S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht
        (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
          (weightedC _ isWeightFamily_one_weight a))
      = restrictionRingHomOfSubset P T s S hden T' S' hden' hTT' a :=
  (existsUnique_continuous_ringHom_laurentQuotient_restriction P T s t S hden T' S' hden'
    hTT' ht).choose_spec.1.2.1 a

/-- **The variable goes to the fraction `t/s`.** -/
@[simp]
theorem laurentQuotientRestrictionRingHom_quotientMk_weightedX (ht : t ∈ T') (i : Fin 1) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht
        (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
          (weightedX _ isWeightFamily_one_weight i))
      = ((divBy t s : S') : UniformSpace.Completion S') :=
  (existsUnique_continuous_ringHom_laurentQuotient_restriction P T s t S hden T' S' hden'
    hTT' ht).choose_spec.1.2.2 i

/-- **The three properties determine the map out of the Laurent quotient.** -/
theorem eq_laurentQuotientRestrictionRingHom (ht : t ∈ T') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ ψ : (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) →+* UniformSpace.Completion S',
      Continuous ψ →
      (∀ a, ψ (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
          (weightedC _ isWeightFamily_one_weight a))
        = restrictionRingHomOfSubset P T s S hden T' S' hden' hTT' a) →
      (∀ i, ψ (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
          (weightedX _ isWeightFamily_one_weight i))
        = ((divBy t s : S') : UniformSpace.Completion S')) →
      ψ = laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  exact fun ψ hc hC hX ↦
    (existsUnique_continuous_ringHom_laurentQuotient_restriction P T s t S hden T' S' hden'
      hTT' ht).choose_spec.2 ψ ⟨hc, hC, hX⟩

-- The fraction `t/s` downstairs goes to the class of the variable. This is where the Laurent
-- relation is used, and it needs nothing of the target beyond the ring structure: expand both
-- fractions, move the inverse across with `IsUnit.unit_inv_map`, and read off the relation.
private theorem apply_divBy_eq_quotientMk_weightedX :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ g : UniformSpace.Completion S' →+* (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
          laurentRelationIdeal P T s t S hden),
      g.comp (toCompletionLoc P T' s S' hden')
          = (laurentStructureHom P T s t S hden).comp (toCompletionLoc P T s S hden) →
        g ((divBy t s : S') : UniformSpace.Completion S')
          = Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
            (weightedX _ isWeightFamily_one_weight 0) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  intro g hge
  rw [map_divBy_of_comp_toCompletionLoc_eq P T s S hden T' S' hden' t g _ hge]
  exact laurentRelationIdeal_quotientMk_weightedC P T s t S hden

-- Agreement on the image of `A` propagates to all of `A⟨T/s⟩`: two continuous ring homomorphisms
-- out of a completion that agree after the structure map are equal.
private theorem comp_restrictionRingHomOfSubset_eq (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ g : UniformSpace.Completion S' →+* (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
          laurentRelationIdeal P T s t S hden), Continuous g →
      g.comp (toCompletionLoc P T' s S' hden')
          = (laurentStructureHom P T s t S hden).comp (toCompletionLoc P T s S hden) →
        g.comp (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT')
          = laurentStructureHom P T s t S hden := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have _ : T1Space (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    (Ideal.Quotient.t1Space_iff _).mpr hcl
  intro g hgc hge
  exact (eq_comp_of_comp_toCompletionLoc_eq P T s S hden (toCompletionLoc P T' s S' hden')
    ((laurentStructureHom P T s t S hden).comp (toCompletionLoc P T s S hden))
    (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT')
    (continuous_restrictionRingHomOfSubset P T s S hden T' S' hden' hTT')
    (restrictionRingHomOfSubset_comp_toCompletionLoc P T s S hden T' S' hden' hTT') g hgc hge
    (laurentStructureHom P T s t S hden)
    (continuous_quotient_mk'.comp (continuous_weightedC isWeightFamily_one_weight)) rfl).symm

/-- **The forward map of the Laurent presentation.** If every numerator of `T'` either already
lies in `T` or is the new one `t`, there is exactly one continuous ring homomorphism

```text
A⟨T'/s⟩  →  A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)
```

compatible with the two structure maps from `A`.

Paired with
`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_laurentQuotient_restriction`
this gives the two maps of Wedhorn's Remark 7.55, which Proposition 8.30 uses to reduce flatness
of a general restriction map to the elementary one. They are mutually inverse — see
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv` and the two composite identities it is
built from.

The hypothesis beyond the splitting is what makes the target legitimate for
`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`: a closed
relation ideal separates the quotient, and the quotient of a complete group by a closed subgroup
is complete. `TauCeti.Huber.PairOfDefinition.isClosed_laurentRelationIdeal` supplies closedness
when `A⟨T/s⟩` is Tate and `A⟨T/s⟩⟨X⟩` is noetherian. -/
theorem existsUnique_continuous_ringHom_completion_laurentQuotient
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∃! g : UniformSpace.Completion S' →+* (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
          laurentRelationIdeal P T s t S hden),
      Continuous g ∧ g.comp (toCompletionLoc P T' s S' hden') =
        ((Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
          (weightedC _ isWeightFamily_one_weight)).comp (toCompletionLoc P T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  -- the target is a complete Hausdorff Huber ring, which is what the universal property asks
  have _ := IsHuberRing.quotient (laurentRelationIdeal P T s t S hden)
  have _ : T1Space (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    (Ideal.Quotient.t1Space_iff _).mpr hcl
  let _ : UniformSpace (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    IsTopologicalAddGroup.rightUniformSpace _
  have _ : IsUniformAddGroup (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    QuotientAddGroup.completeSpace_right _ (laurentRelationIdeal P T s t S hden).toAddSubgroup
  set ψ := (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
    (weightedC _ isWeightFamily_one_weight) with hψ
  have hsC : IsUnit (toCompletionLoc P T s S hden s) :=
    isUnit_toCompletionLoc_of_dvd P T s S hden dvd_rfl
  have hcont : Continuous (ψ.comp (toCompletionLoc P T s S hden)) := by
    rw [hψ]
    exact continuous_quotient_mk'.comp ((continuous_weightedC isWeightFamily_one_weight).comp
      (continuous_toCompletionLoc P T s S hden))
  refine existsUnique_continuous_ringHom_completion_locTopology P T' s S' hden'
    hcont.continuousAt (hsC.map ψ) fun u hu ↦ ?_
  rw [RingHom.comp_apply, IsUnit.unit_inv_map ψ hsC, ← map_mul]
  exact isPowerBounded_quotientMk_weightedC_fraction P T s t S hden hsC (hsplit u hu)

/-- **The forward map for a topologically nilpotent denominator over a strongly noetherian base.**
The hypotheses of
`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_laurentQuotient` in the
form in which they are met in practice: `hnil` and `hSN` give the closedness of the relation ideal
through `TauCeti.Huber.PairOfDefinition.isClosed_laurentRelationIdeal`. -/
theorem existsUnique_continuous_ringHom_completion_laurentQuotient_of_isStronglyNoetherian
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t) (hnil : IsTopologicallyNilpotent s)
    (hSN : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∃! g : UniformSpace.Completion S' →+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden),
      Continuous g ∧ g.comp (toCompletionLoc P T' s S' hden') =
        ((Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
        (weightedC _ isWeightFamily_one_weight)).comp (toCompletionLoc P T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  exact existsUnique_continuous_ringHom_completion_laurentQuotient P T s t S hden T' S' hden'
    hsplit (isClosed_laurentRelationIdeal_of_isStronglyNoetherian P T s t S hden hnil hSN)

/-- **The map into the Laurent quotient**, `A⟨T'/s⟩ → A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)`.

Its two defining properties are
`TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRingHom` and
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom_comp_toCompletionLoc`, and
`TauCeti.Huber.PairOfDefinition.eq_laurentQuotientRingHom` says they determine it. Those three are
the interface to use. -/
noncomputable def laurentQuotientRingHom (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)))
    :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    UniformSpace.Completion S' →+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) :=
  (existsUnique_continuous_ringHom_completion_laurentQuotient P T s t S hden T' S' hden'
    hsplit hcl).choose

/-- The map into the Laurent quotient is continuous. -/
theorem continuous_laurentQuotientRingHom (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)))
    :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    Continuous (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl) :=
  (existsUnique_continuous_ringHom_completion_laurentQuotient P T s t S hden T' S' hden'
    hsplit hcl).choose_spec.1.1

/-- **The map into the Laurent quotient is compatible with the structure maps from `A`.** This is
the equation that characterises it. -/
@[simp]
theorem laurentQuotientRingHom_comp_toCompletionLoc (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)))
    :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl).comp
        (toCompletionLoc P T' s S' hden') =
      ((Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
        (weightedC _ isWeightFamily_one_weight)).comp (toCompletionLoc P T s S hden) :=
  (existsUnique_continuous_ringHom_completion_laurentQuotient P T s t S hden T' S' hden'
    hsplit hcl).choose_spec.1.2

/-- **The two properties determine the map into the Laurent quotient.** -/
theorem eq_laurentQuotientRingHom (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight)))
    :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ g : UniformSpace.Completion S' →+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden),
      Continuous g → g.comp (toCompletionLoc P T' s S' hden') =
          ((Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
        (weightedC _ isWeightFamily_one_weight)).comp (toCompletionLoc P T s S hden) →
        g = laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  exact fun g hgc hge ↦
    (existsUnique_continuous_ringHom_completion_laurentQuotient P T s t S hden T' S' hden'
      hsplit hcl).choose_spec.2 g ⟨hgc, hge⟩

end OneStep

/-- **The two maps of Remark 7.55 compose to the identity of `A⟨T'/s⟩`**: going into the Laurent
quotient and back out again is the identity of the enlarged rational localisation. -/
@[simp]
theorem laurentQuotientRestrictionRingHom_comp_laurentQuotientRingHom (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht).comp
        (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl)
      = RingHom.id (UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have hψc := continuous_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht
  have hψC :=
    laurentQuotientRestrictionRingHom_quotientMk_weightedC P T s t S hden T' S' hden' hTT' ht
  have hgc := continuous_laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl
  have hge := laurentQuotientRingHom_comp_toCompletionLoc P T s t S hden T' S' hden' hsplit hcl
  refine eq_id_of_comp_toCompletionLoc_eq_self P T' s S' hden' _ (hψc.comp hgc) ?_
  rw [RingHom.comp_assoc, hge]
  exact RingHom.ext fun a ↦ (hψC _).trans <| DFunLike.congr_fun
    (restrictionRingHomOfSubset_comp_toCompletionLoc P T s S hden T' S' hden' hTT') a

/-- **The two maps of Remark 7.55 compose to the identity of the Laurent quotient**: going out of
`A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` and back in again is its identity. -/
@[simp]
theorem laurentQuotientRingHom_comp_laurentQuotientRestrictionRingHom (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl).comp
        (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht)
      = RingHom.id (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have _ := IsHuberRing.quotient (laurentRelationIdeal P T s t S hden)
  have _ : T1Space (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    (Ideal.Quotient.t1Space_iff _).mpr hcl
  have hψc := continuous_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht
  have hψC :=
    laurentQuotientRestrictionRingHom_quotientMk_weightedC P T s t S hden T' S' hden' hTT' ht
  have hψX :=
    laurentQuotientRestrictionRingHom_quotientMk_weightedX P T s t S hden T' S' hden' hTT' ht
  set g := laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl
  have hgc := continuous_laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl
  have hge := laurentQuotientRingHom_comp_toCompletionLoc P T s t S hden T' S' hden' hsplit hcl
  refine Ideal.Quotient.ringHom_ext <|
    weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      ((hgc.comp hψc).comp continuous_quot_mk) continuous_quot_mk ?_ ?_
  · intro a
    exact (congrArg g (hψC a)).trans <| DFunLike.congr_fun
      (comp_restrictionRingHomOfSubset_eq P T s t S hden T' S' hden' hTT' hcl _ hgc hge) a
  · intro i
    rw [Subsingleton.elim i 0]
    exact (congrArg g (hψX 0)).trans
      (apply_divBy_eq_quotientMk_weightedX P T s t S hden T' S' hden' _ hge)

/-- **Wedhorn's Remark 7.55**: when the numerators of `T'` are those of `T` together with `t`, the
Laurent quotient *is* `A⟨T'/s⟩`,

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  ≃  A⟨T'/s⟩
```

the two maps already constructed being mutually inverse. This is the identification Proposition
8.30 consumes: it turns a statement about the Laurent quotient, such as its flatness over
`A⟨T/s⟩`, into the same statement about `A⟨T'/s⟩`.

Use `TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRingEquiv` and its `symm` form for
continuity, and the `@[simp]` lemmas below to compute: the equivalence is
`TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom` and its inverse is
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom`. -/
noncomputable def laurentQuotientRingEquiv (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) ≃+* UniformSpace.Completion S' :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  letI := locUniformSpace P T' s S' hden'
  letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
  letI := isTopologicalRing_locUniformSpace P T' s S' hden'
  letI := isHuberRing_locUniformSpace P T' s S' hden'
  RingEquiv.ofRingHom (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht)
    (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl)
    (laurentQuotientRestrictionRingHom_comp_laurentQuotientRingHom P T s t S hden T' S' hden'
      hTT' ht hsplit hcl)
    (laurentQuotientRingHom_comp_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden'
      hTT' ht hsplit hcl)

/-- **The identification is `laurentQuotientRestrictionRingHom`**, as a ring homomorphism: it
packages that map together with the inverse supplied by
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom`, rather than introducing a new one. -/
@[simp]
theorem laurentQuotientRingEquiv_coe (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ((laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl :
        (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) ≃+* UniformSpace.Completion S') :
        (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) →+* UniformSpace.Completion S')
      = laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht := by
  simp only [laurentQuotientRingEquiv, RingEquiv.coe_ringHom_ofRingHom]
/-- The pointwise form of `TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv_coe`. -/
@[simp]
theorem laurentQuotientRingEquiv_apply (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ x, laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl x
      = laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht x :=
  fun x ↦ DFunLike.congr_fun
    (laurentQuotientRingEquiv_coe P T s t S hden T' S' hden' hTT' ht hsplit hcl) x


/-- **The inverse of the identification is `laurentQuotientRingHom`**, as a ring homomorphism. -/
@[simp]
theorem laurentQuotientRingEquiv_symm_coe (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (((laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).symm :
        UniformSpace.Completion S' ≃+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden)) :
        UniformSpace.Completion S' →+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden))
      = laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl := by
  simp only [laurentQuotientRingEquiv, RingEquiv.ofRingHom_symm,
    RingEquiv.coe_ringHom_ofRingHom]
/-- The pointwise form of
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv_symm_coe`. -/
@[simp]
theorem laurentQuotientRingEquiv_symm_apply (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ x, (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).symm x
      = laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl x :=
  fun x ↦ DFunLike.congr_fun
    (laurentQuotientRingEquiv_symm_coe P T s t S hden T' S' hden' hTT' ht hsplit hcl) x


/-- The identification is continuous. -/
theorem continuous_laurentQuotientRingEquiv (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    Continuous (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl) := by
  simpa only [funext (laurentQuotientRingEquiv_apply P T s t S hden T' S' hden' hTT' ht hsplit hcl)]
    using continuous_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht

/-- The inverse of the identification is continuous, so it is a homeomorphism. -/
theorem continuous_laurentQuotientRingEquiv_symm (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    Continuous (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).symm := by
  simpa only
    [funext (laurentQuotientRingEquiv_symm_apply P T s t S hden T' S' hden' hTT' ht hsplit hcl)]
    using continuous_laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl

end OneStep

end PairOfDefinition

end TauCeti.Huber

end
