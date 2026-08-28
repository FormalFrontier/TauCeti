/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# Holomorphy rings in an extension: `𝒪'_P` is the integral closure of `𝒪_P`

Let `F' / k'` be an extension of the algebraic function field `F / k`, integral both on the
constants and on the functions. Every place `P'` of `F' / k'` restricts to a place
`P'.restrict k F` of `F / k` (`TauCeti.Place.restrict`), and this file computes the holomorphy
ring of a fibre of that restriction map: for a set `S` of places of `F / k`, the intersection of
the valuation rings `𝒪_{P'}` over the places `P'` lying over `S` is the integral closure of the
holomorphy ring `𝒪_S = ⋂_{P ∈ S} 𝒪_P` in `F'`, and in particular, at a single place,

`⋂_{P' ∣ P} 𝒪_{P'} = 𝒪'_P`, the integral closure of `𝒪_P` in `F'`.

This identification is what turns `𝒪'_P` — the ring underlying the local integral bases of
Stichtenoth's Section III.3, and the base of the complementary module and the different of his
Section III.4 — into an intersection of valuation rings, so that its arithmetic is the arithmetic
of the places over `P`.

One inclusion is formal: `𝒪_P` sits inside every `𝒪_{P'}` with `P' ∣ P`, and a valuation ring is
integrally closed. For the other, a function of `F'` not integral over the base is separated from
the integral closure by a valuation subring
(`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`, the domination lemma behind
Stichtenoth's Theorem 3.2.6) which — containing the constants `k'` and being proper — is the
valuation ring of a place of `F' / k'`; that the place lies over `S` is Stichtenoth's
Corollary 3.2.8, already available as `TauCeti.coe_holomorphyRing_subset_integers_iff`.

## Main results

* `TauCeti.coe_holomorphyRing_setOf_restrict_eq`: the holomorphy ring of the places over `P` is
  the integral closure `𝒪'_P` of `𝒪_P` in `F'`, with
  `TauCeti.mem_holomorphyRing_setOf_restrict_eq_iff_isIntegral` its membership form.
* `TauCeti.coe_holomorphyRing_setOf_restrict_mem` and
  `TauCeti.mem_holomorphyRing_setOf_restrict_mem_iff_isIntegral`: the same statement over a set
  of places, with the holomorphy ring `𝒪_S` as the base.
* `TauCeti.isIntegral_integers_iff_forall_ord_nonneg`: the same criterion in additive form,
  through the order functions at the places over `P`.
* `TauCeti.coe_integralClosure_integers_subset_integers_iff`: the places of `F' / k'` at which
  every function of `𝒪'_P` is regular are exactly the places over `P`, so `𝒪'_P` remembers the
  fibre; `TauCeti.coe_integralClosure_holomorphyRing_subset_integers_iff` is the version over a
  set of places.
* `TauCeti.Place.isIntegral_algebraMap_iff_mem_integers`: `𝒪'_P` contracts to `𝒪_P`, that is, a
  function of `F` is integral over `𝒪_P` exactly when it is regular at `P`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.2 and III.3.  The description of the integral closure of `𝒪_P` in `F'` as the
  intersection of the valuation rings of the places over `P` is the opening result of
  Section III.3, on which its local integral bases rest.
-/

public section

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral k k'] [Algebra.IsIntegral F F']

section Engine

variable (k F)

/-- **Separating a non-integral function by a place.** If `z : F'` is not integral over a
`k`-algebra `R` acting on `F'` through `F`, there is a place `P'` of `F' / k'` at which `z` is
irregular while every function of `R` is regular at the place of `F / k` below `P'`.

This is the engine of the theorems below: the integral closure of `R` in `F'` is integrally
closed in `F'`, so it is dominated by a valuation subring avoiding `z`, and that valuation
subring contains `k'` because `k'` is integral over `k`. -/
private theorem exists_place_of_not_isIntegral (hF' : IsFunctionField k' F')
    {R : Type*} [CommRing R] [Algebra k R] [Algebra R F] [Algebra R F']
    [IsScalarTower k R F'] [IsScalarTower R F F'] {z : F'} (hz : ¬ IsIntegral R z) :
    ∃ P' : Place k' F',
      (∀ r : R, algebraMap R F r ∈ (P'.restrict k F).integers) ∧ z ∉ P'.integers := by
  obtain ⟨V, hRV, hzV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure R F').toSubring) hz
  have hk' : ∀ c : k', algebraMap k' F' c ∈ V := fun c ↦
    hRV (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  have hV : V ≠ ⊤ := fun h ↦ hzV (h ▸ ValuationSubring.mem_top _)
  have hint : (Place.ofValuationSubring hF' hk' hV).integers = V :=
    Place.integers_ofValuationSubring hF' hk' hV
  refine ⟨Place.ofValuationSubring hF' hk' hV, fun r ↦ ?_, fun h ↦ hzV (hint ▸ h)⟩
  rw [Place.mem_integers_restrict_iff, hint, ← IsScalarTower.algebraMap_apply R F F']
  exact hRV (Subalgebra.algebraMap_mem (integralClosure R F') r)

end Engine

/-! ### The integral closure of a holomorphy ring -/

/-- **The integral closure of a holomorphy ring**, over a set of places: a function of `F'` is
regular at every place of `F' / k'` lying over `S` exactly when it is integral over the holomorphy
ring `𝒪_S` (Stichtenoth, Section III.3). -/
theorem mem_holomorphyRing_setOf_restrict_mem_iff_isIntegral (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') {S : Set (Place k F)} {z : F'} :
    z ∈ holomorphyRing {P' : Place k' F' | P'.restrict k F ∈ S} ↔
      IsIntegral ↥(holomorphyRing S) z := by
  rw [mem_holomorphyRing_iff]
  refine ⟨fun hz ↦ by_contra fun hint ↦ ?_, fun hint P' hP' ↦ ?_⟩
  · obtain ⟨P', hP', hzP'⟩ := exists_place_of_not_isIntegral k F hF' hint
    refine hzP' (hz P' ((coe_holomorphyRing_subset_integers_iff hF).mp fun x hx ↦ ?_))
    simpa using hP' ⟨x, hx⟩
  · refine P'.mem_integers_of_isIntegral (fun r ↦ ?_) hint
    rw [IsScalarTower.algebraMap_apply ↥(holomorphyRing S) F F']
    exact (Place.mem_integers_restrict_iff k F P' _).mp (mem_holomorphyRing_iff.mp r.2 _ hP')

/-- **The integral closure of a holomorphy ring**, over a set of places: the holomorphy ring of
the places of `F' / k'` lying over `S` is the integral closure of `𝒪_S` in `F'` (Stichtenoth,
Section III.3). -/
theorem coe_holomorphyRing_setOf_restrict_mem (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (S : Set (Place k F)) :
    (holomorphyRing {P' : Place k' F' | P'.restrict k F ∈ S} : Set F') =
      integralClosure ↥(holomorphyRing S) F' :=
  Set.ext fun _ ↦ mem_holomorphyRing_setOf_restrict_mem_iff_isIntegral hF hF'

/-- **`𝒪'_P` is the ring of functions regular over `P`**: a function of `F'` is regular at every
place of `F' / k'` lying over the place `P` of `F / k` exactly when it is integral over `𝒪_P`
(Stichtenoth, Section III.3).  Unlike the version over a set of places, this needs no hypothesis
on `F / k`: a valuation ring containing `𝒪_P` is `𝒪_P`. -/
theorem mem_holomorphyRing_setOf_restrict_eq_iff_isIntegral (hF' : IsFunctionField k' F')
    (P : Place k F) {z : F'} :
    z ∈ holomorphyRing {P' : Place k' F' | P'.restrict k F = P} ↔
      IsIntegral ↥P.integers z := by
  have : IsScalarTower k ↥P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply ↥P.integers F F',
      ← IsScalarTower.algebraMap_apply k ↥P.integers F]
  rw [mem_holomorphyRing_iff]
  refine ⟨fun hz ↦ by_contra fun hint ↦ ?_, fun hint P' hP' ↦ ?_⟩
  · obtain ⟨Q, hQ, hzQ⟩ := exists_place_of_not_isIntegral k F hF' hint
    refine hzQ (hz Q (Place.eq_of_integers_le (SetLike.le_def.mpr fun x hx ↦ ?_)).symm)
    simpa using hQ ⟨x, hx⟩
  · replace hP' : P'.restrict k F = P := hP'
    refine P'.mem_integers_of_isIntegral (fun r ↦ ?_) hint
    rw [IsScalarTower.algebraMap_apply ↥P.integers F F']
    exact (Place.mem_integers_restrict_iff k F P' _).mp (by rw [hP']; exact r.2)

/-- **`𝒪'_P` is the ring of functions regular over `P`**: the holomorphy ring of the places of
`F' / k'` lying over the place `P` of `F / k` is the integral closure `𝒪'_P` of `𝒪_P` in `F'`
(Stichtenoth, Section III.3). -/
theorem coe_holomorphyRing_setOf_restrict_eq (hF' : IsFunctionField k' F') (P : Place k F) :
    (holomorphyRing {P' : Place k' F' | P'.restrict k F = P} : Set F') =
      integralClosure ↥P.integers F' :=
  Set.ext fun _ ↦ mem_holomorphyRing_setOf_restrict_eq_iff_isIntegral hF' P

/-- **`𝒪'_P` in additive form**: a function of `F'` is integral over `𝒪_P` exactly when it has no
pole at any place of `F' / k'` lying over `P`. -/
theorem isIntegral_integers_iff_forall_ord_nonneg (hF' : IsFunctionField k' F') (P : Place k F)
    {z : F'} :
    IsIntegral ↥P.integers z ↔ ∀ P' : Place k' F', P'.restrict k F = P → 0 ≤ P'.ord z := by
  rw [← mem_holomorphyRing_setOf_restrict_eq_iff_isIntegral hF' P,
    mem_holomorphyRing_iff_forall_ord_nonneg]
  exact Iff.rfl

/-! ### Recovering the fibre from the integral closure -/

/-- The places of `F' / k'` at which every function of the integral closure of `𝒪_S` is regular
are exactly the places lying over `S` (Stichtenoth, Corollary 3.2.8 read through the theorem
above). -/
theorem coe_integralClosure_holomorphyRing_subset_integers_iff (hF : IsFunctionField k F)
    (hF' : IsFunctionField k' F') (S : Set (Place k F)) (P' : Place k' F') :
    (integralClosure ↥(holomorphyRing S) F' : Set F') ⊆ P'.integers ↔ P'.restrict k F ∈ S := by
  rw [← coe_holomorphyRing_setOf_restrict_mem hF hF' S,
    coe_holomorphyRing_subset_integers_iff hF', Set.mem_ofPred_eq]

/-- The places of `F' / k'` at which every function of `𝒪'_P` is regular are exactly the places
lying over `P`, so the fibre over `P` is recovered from `𝒪'_P` (Stichtenoth, Corollary 3.2.8 read
through the theorem above). -/
theorem coe_integralClosure_integers_subset_integers_iff (hF' : IsFunctionField k' F')
    (P : Place k F) (P' : Place k' F') :
    (integralClosure ↥P.integers F' : Set F') ⊆ P'.integers ↔ P'.restrict k F = P := by
  rw [← coe_holomorphyRing_setOf_restrict_eq hF' P,
    coe_holomorphyRing_subset_integers_iff hF', Set.mem_ofPred_eq]

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F'] [Algebra.IsIntegral k k'] [Algebra.IsIntegral F F'] in
/-- **`𝒪'_P` contracts to `𝒪_P`**: a function of `F` is integral over `𝒪_P` in the extension `F'`
exactly when it is regular at `P`.  So enlarging the field does not enlarge the ring of functions
of `F` integral over `𝒪_P`, and `𝒪'_P ∩ F = 𝒪_P`. -/
theorem Place.isIntegral_algebraMap_iff_mem_integers (P : Place k F) {x : F} :
    IsIntegral ↥P.integers (algebraMap F F' x) ↔ x ∈ P.integers :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥P.integers F F')
      (algebraMap F F').injective (x := x)).trans
    ⟨fun hx ↦ P.mem_integers_of_isIntegral (fun r ↦ r.2) hx,
      fun hx ↦ isIntegral_algebraMap (x := (⟨x, hx⟩ : P.integers))⟩

end TauCeti
