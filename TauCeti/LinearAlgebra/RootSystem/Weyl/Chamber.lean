/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.DominantChamber
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

/-!
# The Weyl chambers of a base

The dominant chamber of a base is one of a family: its translates under the Weyl group are the
**Weyl chambers**. This file introduces them, in both the closed and the open form, and proves
that the Weyl group permutes them **simply transitively**.

Two facts drive everything. A weight interior to the dominant chamber is moved by every
nontrivial Weyl-group element, indeed out of the closed dominant chamber
(`TauCeti.eq_one_of_smul_mem_dominantChamber`); and every weight is Weyl-conjugate into the closed
dominant chamber (`TauCeti.exists_mem_dominantChamber`). The first says an open chamber meets the
closed chamber of no other Weyl-group element, so the labelling `w ↦ w • openDominantChamber` is
injective as soon as the open dominant chamber has a point to distinguish two labels by; the set of
open chambers is by definition the range of that labelling, so surjectivity is free, and the two
together make it a bijection from the Weyl group onto the set of open chambers, which is what simple
transitivity means here. The second fact is what covers the weights: it is how every *regular*
weight is shown to lie in an open chamber.

The weights lying in an open chamber are exactly the **regular** ones (`TauCeti.IsRegularWeight`,
defined with the dominant chamber), those killed by no coroot functional. That is the sense in
which the open chambers are the complement of the walls:
`TauCeti.iUnion_openWeylChamber_eq_setOf_isRegularWeight` identifies their union with the regular
weights, and `TauCeti.existsUnique_mem_openWeylChamber` puts each regular weight in exactly one of
them.

Unlike the uniqueness statements, the bijection needs the open dominant chamber to be *nonempty*,
which is a genuine hypothesis rather than a formality: the open chambers are cut out by strict
inequalities, and over a coefficient ring where `2` is not invertible a base may have no strictly
dominant weight to offer. So it is carried as an explicit argument, and
`TauCeti.openDominantChamber_nonempty` discharges it whenever `2` is invertible, the Weyl vector
`ρ` being strictly dominant there.

## Main definitions

* `TauCeti.weylChamber` and `TauCeti.openWeylChamber`: the Weyl translates of the closed and the
  open dominant chamber.
* `TauCeti.openWeylChambers`: the set of open Weyl chambers of a base, carrying the Weyl-group
  action restricted from the pointwise action on `Set M`.
* `TauCeti.weylGroupEquivOpenWeylChambers`: the Weyl group as an index set for the open chambers.

## Main results

* `TauCeti.mem_weylChamber_iff` and `TauCeti.mem_openWeylChamber_iff`: the chamber of `w` is the
  sign-pattern cone of the coroot functionals of the roots `w(αᵢ)`.
* `TauCeti.eq_of_mem_openWeylChamber_of_mem_weylChamber`: an open chamber meets the closed chamber
  of no other Weyl-group element; hence `TauCeti.pairwise_disjoint_openWeylChamber`.
* `TauCeti.openWeylChamber_injective`, `TauCeti.stabilizer_openWeylChamber_eq_bot` and
  `TauCeti.openWeylChambers.stabilizer_eq_bot`: the Weyl group acts freely on the open chambers.
* `TauCeti.exists_smul_eq_of_mem_openWeylChambers` and the `MulAction.IsPretransitive` instance on
  `TauCeti.openWeylChambers`: the Weyl group acts transitively on the open chambers.
* `TauCeti.iUnion_openWeylChamber_eq_setOf_isRegularWeight` and
  `TauCeti.existsUnique_mem_openWeylChamber`: the open chambers partition the regular weights.

## Implementation notes

Chambers are indexed by Weyl-group elements rather than cut out one at a time by a sign pattern,
because that is the form simple transitivity takes: the content of the theorem is that the
indexing is injective. The sign-pattern description is recovered as
`TauCeti.mem_openWeylChamber_iff`. Both readings of "acts simply transitively" are available: the
labelling bijection `TauCeti.weylGroupEquivOpenWeylChambers`, and the transitive free action on
the type `TauCeti.openWeylChambers P b`.

The covering statements are proved as `..._of_finite_weylGroup`, which asks only that the Weyl
group be finite, and the root-system forms are read off from those using
`TauCeti.RootPairing.finite_weylGroup`; this follows the shape of
`TauCeti.exists_mem_dominantChamber_of_finite_weylGroup`, which is what they consume.

## References

This file implements the remaining chamber items of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`: that "the general chambers are the
`W`-translates of the dominant chamber", and that the closed dominant chamber being a strict
fundamental domain is the Weyl group "acting **simply transitively on the open chambers**". The
existence and the uniqueness of the dominant representative are `TauCeti.exists_mem_dominantChamber`
and `TauCeti.eq_one_of_smul_mem_dominantChamber`, proved elsewhere.

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §10.3, and N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*,
Ch. V, §3.
-/

public section

open Pointwise Set

namespace TauCeti

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N)

variable [LinearOrder R] (b : P.Base)

/-! ### The chambers -/

/-- The **closed Weyl chamber** attached to a Weyl-group element: the translate of the closed
dominant chamber by that element. -/
def weylChamber (w : P.weylGroup) : Set M := w • dominantChamber P b

/-- The **open Weyl chamber** attached to a Weyl-group element: the translate of the open dominant
chamber by that element. -/
def openWeylChamber (w : P.weylGroup) : Set M := w • openDominantChamber P b

/-- Membership in a closed Weyl chamber, pulled back to the dominant one. -/
@[simp]
lemma mem_weylChamber (w : P.weylGroup) (x : M) :
    x ∈ weylChamber P b w ↔ w⁻¹ • x ∈ dominantChamber P b :=
  Set.mem_smul_set_iff_inv_smul_mem

/-- Membership in an open Weyl chamber, pulled back to the dominant one. -/
@[simp]
lemma mem_openWeylChamber (w : P.weylGroup) (x : M) :
    x ∈ openWeylChamber P b w ↔ w⁻¹ • x ∈ openDominantChamber P b :=
  Set.mem_smul_set_iff_inv_smul_mem

/-- The chamber of the identity is the dominant chamber. -/
@[simp]
lemma weylChamber_one : weylChamber P b 1 = dominantChamber P b := one_smul _ _

/-- The open chamber of the identity is the open dominant chamber. -/
@[simp]
lemma openWeylChamber_one : openWeylChamber P b 1 = openDominantChamber P b := one_smul _ _

/-- The Weyl group permutes the closed chambers, translating the index. -/
@[simp]
lemma smul_weylChamber (v w : P.weylGroup) :
    v • weylChamber P b w = weylChamber P b (v * w) := (mul_smul v w _).symm

/-- The Weyl group permutes the open chambers, translating the index. -/
@[simp]
lemma smul_openWeylChamber (v w : P.weylGroup) :
    v • openWeylChamber P b w = openWeylChamber P b (v * w) := (mul_smul v w _).symm

/-- An open chamber lies in the closed chamber of the same Weyl-group element. -/
lemma openWeylChamber_subset_weylChamber (w : P.weylGroup) :
    openWeylChamber P b w ⊆ weylChamber P b w :=
  Set.smul_set_mono (openDominantChamber_subset_dominantChamber P b)

/-- **A closed Weyl chamber is a sign-pattern cone**: the chamber of `w` is cut out by the coroot
functionals of the roots `w(αᵢ)`, for `αᵢ` simple. -/
lemma mem_weylChamber_iff (w : P.weylGroup) (x : M) :
    x ∈ weylChamber P b w ↔ ∀ i ∈ b.support, 0 ≤ P.coroot' (P.weylGroupToPerm w i) x := by
  rw [mem_weylChamber, mem_dominantChamber]
  exact forall₂_congr fun i _ ↦ by
    rw [← RootPairing.coroot'_weylGroupToPerm_smul P w i (w⁻¹ • x), smul_inv_smul]

/-- **An open Weyl chamber is a sign-pattern cone**: the open chamber of `w` is cut out by the
coroot functionals of the roots `w(αᵢ)`, for `αᵢ` simple. -/
lemma mem_openWeylChamber_iff (w : P.weylGroup) (x : M) :
    x ∈ openWeylChamber P b w ↔ ∀ i ∈ b.support, 0 < P.coroot' (P.weylGroupToPerm w i) x := by
  rw [mem_openWeylChamber, mem_openDominantChamber]
  exact forall₂_congr fun i _ ↦ by
    rw [← RootPairing.coroot'_weylGroupToPerm_smul P w i (w⁻¹ • x), smul_inv_smul]

/-! ### The set of open chambers -/

/-- The set of **open Weyl chambers** of a base: the Weyl translates of the open dominant
chamber. -/
def openWeylChambers : Set (Set M) := Set.range (openWeylChamber P b)

/-- Membership in the set of open Weyl chambers: a set is a chamber exactly when some Weyl-group
element labels it. -/
@[simp]
lemma mem_openWeylChambers {C : Set M} :
    C ∈ openWeylChambers P b ↔ ∃ w : P.weylGroup, openWeylChamber P b w = C := Iff.rfl

/-- Every labelled open chamber is a chamber. -/
lemma openWeylChamber_mem_openWeylChambers (w : P.weylGroup) :
    openWeylChamber P b w ∈ openWeylChambers P b := ⟨w, rfl⟩

/-- The open dominant chamber is a chamber. -/
lemma openDominantChamber_mem_openWeylChambers :
    openDominantChamber P b ∈ openWeylChambers P b :=
  ⟨1, openWeylChamber_one P b⟩

/-- **The Weyl group acts transitively on the open chambers.** -/
theorem exists_smul_eq_of_mem_openWeylChambers {C D : Set M} (hC : C ∈ openWeylChambers P b)
    (hD : D ∈ openWeylChambers P b) : ∃ u : P.weylGroup, u • C = D := by
  obtain ⟨v, rfl⟩ := hC
  obtain ⟨w, rfl⟩ := hD
  exact ⟨w * v⁻¹, by rw [smul_openWeylChamber, inv_mul_cancel_right]⟩

/-- The Weyl group acts on the open chambers themselves: a translate of a chamber is a chamber, so
the pointwise action on `Set M` restricts to `TauCeti.openWeylChambers`. -/
instance : SMul P.weylGroup (openWeylChambers P b) where
  smul v C := ⟨v • (C : Set M), by
    obtain ⟨w, hw⟩ := C.2
    exact ⟨v * w, by rw [← smul_openWeylChamber, hw]⟩⟩

/-- The action on the chambers is the pointwise action on the underlying set. -/
@[simp]
lemma openWeylChambers.coe_smul (v : P.weylGroup) (C : openWeylChambers P b) :
    ((v • C : openWeylChambers P b) : Set M) = v • (C : Set M) := (rfl)

/-- The restricted action is a `MulAction`, inherited from the pointwise action on `Set M`. -/
instance : MulAction P.weylGroup (openWeylChambers P b) where
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

/-- **The Weyl group acts transitively on the open chambers**, as an action on the chambers
themselves. -/
instance : MulAction.IsPretransitive P.weylGroup (openWeylChambers P b) where
  exists_smul_eq C D := by
    obtain ⟨u, hu⟩ := exists_smul_eq_of_mem_openWeylChambers P b C.2 D.2
    exact ⟨u, Subtype.ext ((openWeylChambers.coe_smul P b u C).trans hu)⟩

/-! ### Simple transitivity -/

section Regular

variable [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.flip.IsReduced]

/-- **A weight in an open Weyl chamber is regular**, regularity being Weyl-invariant. -/
lemma isRegularWeight_of_mem_openWeylChamber {w : P.weylGroup} {x : M}
    (hx : x ∈ openWeylChamber P b w) : IsRegularWeight P x := by
  rw [mem_openWeylChamber] at hx
  have h := isRegularWeight_of_mem_openDominantChamber P b hx
  rwa [isRegularWeight_smul] at h

/-- **An open Weyl chamber meets the closed chamber of no other Weyl-group element.** This is the
uniqueness half of the fundamental-domain property, read as a statement about chambers: a weight
interior to one chamber is dominant for no second translate of the base. -/
theorem eq_of_mem_openWeylChamber_of_mem_weylChamber {v w : P.weylGroup} {x : M}
    (hv : x ∈ openWeylChamber P b v) (hw : x ∈ weylChamber P b w) : v = w := by
  rw [mem_openWeylChamber] at hv
  rw [mem_weylChamber] at hw
  have key : (w⁻¹ * v) • (v⁻¹ • x) ∈ dominantChamber P b := by
    rwa [mul_smul, smul_inv_smul]
  exact (inv_mul_eq_one.mp (eq_one_of_smul_mem_dominantChamber P b (w⁻¹ * v) hv key)).symm

/-- **Distinct Weyl-group elements give disjoint open chambers.** -/
theorem eq_of_mem_openWeylChamber {v w : P.weylGroup} {x : M}
    (hv : x ∈ openWeylChamber P b v) (hw : x ∈ openWeylChamber P b w) : v = w :=
  eq_of_mem_openWeylChamber_of_mem_weylChamber P b hv
    (openWeylChamber_subset_weylChamber P b w hw)

/-- An open chamber is disjoint from every other closed chamber. -/
theorem disjoint_openWeylChamber_weylChamber {v w : P.weylGroup} (h : v ≠ w) :
    Disjoint (openWeylChamber P b v) (weylChamber P b w) :=
  Set.disjoint_left.mpr fun _ hv hw ↦
    h (eq_of_mem_openWeylChamber_of_mem_weylChamber P b hv hw)

/-- **The open Weyl chambers are pairwise disjoint.** -/
theorem pairwise_disjoint_openWeylChamber :
    Pairwise fun v w : P.weylGroup ↦ Disjoint (openWeylChamber P b v) (openWeylChamber P b w) :=
  fun _ _ h ↦ Set.disjoint_left.mpr fun _ hv hw ↦ h (eq_of_mem_openWeylChamber P b hv hw)

/-- **Distinct Weyl-group elements give distinct open chambers**, provided the open dominant
chamber has a point at all. -/
theorem openWeylChamber_injective (hne : (openDominantChamber P b).Nonempty) :
    Function.Injective (openWeylChamber P b) := by
  intro v w h
  obtain ⟨x, hx⟩ := hne
  have hv : v • x ∈ openWeylChamber P b v := ⟨x, hx, rfl⟩
  exact eq_of_mem_openWeylChamber P b hv (h ▸ hv)

/-- Two open chambers agree exactly when their labels do. -/
theorem openWeylChamber_inj (hne : (openDominantChamber P b).Nonempty) {v w : P.weylGroup} :
    openWeylChamber P b v = openWeylChamber P b w ↔ v = w :=
  (openWeylChamber_injective P b hne).eq_iff

/-- **The Weyl group acts freely on the open chambers**: only the identity fixes one. -/
theorem eq_one_of_smul_openWeylChamber_eq (hne : (openDominantChamber P b).Nonempty)
    {v w : P.weylGroup} (h : v • openWeylChamber P b w = openWeylChamber P b w) : v = 1 := by
  rw [smul_openWeylChamber] at h
  simpa using openWeylChamber_injective P b hne h

/-- **The stabilizer of an open Weyl chamber is trivial.** -/
theorem stabilizer_openWeylChamber_eq_bot (hne : (openDominantChamber P b).Nonempty)
    (w : P.weylGroup) :
    MulAction.stabilizer P.weylGroup (openWeylChamber P b w) = ⊥ := by
  ext v
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  exact ⟨eq_one_of_smul_openWeylChamber_eq P b hne, fun h ↦ by rw [h, one_smul]⟩

/-- **The Weyl group acts freely on the open chambers**: the stabilizer of a chamber, as an element
of `TauCeti.openWeylChambers`, is trivial. Together with the transitivity instance above this is
simple transitivity of the action on the chambers. -/
theorem openWeylChambers.stabilizer_eq_bot (hne : (openDominantChamber P b).Nonempty)
    (C : openWeylChambers P b) : MulAction.stabilizer P.weylGroup C = ⊥ := by
  obtain ⟨w, hw⟩ := C.2
  ext v
  rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj, openWeylChambers.coe_smul, ← hw,
    Subgroup.mem_bot]
  exact ⟨eq_one_of_smul_openWeylChamber_eq P b hne, fun h ↦ by rw [h, one_smul]⟩

/-- **The Weyl group acts simply transitively on the open Weyl chambers**: labelling a chamber by
the Weyl-group element carrying the dominant one to it is a bijection.

Transitivity of the action is `TauCeti.exists_smul_eq_of_mem_openWeylChambers` and freeness is
`TauCeti.stabilizer_openWeylChamber_eq_bot`; this packages the two as an equivalence. -/
noncomputable def weylGroupEquivOpenWeylChambers (hne : (openDominantChamber P b).Nonempty) :
    P.weylGroup ≃ openWeylChambers P b :=
  Equiv.ofInjective (openWeylChamber P b) (openWeylChamber_injective P b hne)

@[simp]
lemma weylGroupEquivOpenWeylChambers_apply (hne : (openDominantChamber P b).Nonempty)
    (w : P.weylGroup) :
    (weylGroupEquivOpenWeylChambers P b hne w : Set M) = openWeylChamber P b w := (rfl)

end Regular

/-! ### Nonemptiness, from the Weyl vector -/

section Nonempty

variable [IsStrictOrderedRing R] [Invertible (2 : R)] [Finite ι] [P.IsCrystallographic]
  [P.IsReduced]

/-- Every open Weyl chamber is nonempty once `2` is invertible. -/
theorem openWeylChamber_nonempty (w : P.weylGroup) : (openWeylChamber P b w).Nonempty :=
  (openDominantChamber_nonempty P b).image _

end Nonempty

/-! ### The chambers and the regular weights -/

section Covering

variable [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.flip.IsReduced]

section FiniteWeylGroup

variable [Finite P.weylGroup]

/-- **The open Weyl chambers cover exactly the regular weights**, for a pairing whose Weyl group is
finite. A regular weight is Weyl-conjugate into the closed dominant chamber, and regularity
upgrades that to the open one; conversely every weight in an open chamber is regular. -/
theorem iUnion_openWeylChamber_eq_setOf_isRegularWeight_of_finite_weylGroup :
    ⋃ w : P.weylGroup, openWeylChamber P b w = {x : M | IsRegularWeight P x} := by
  refine Set.eq_of_subset_of_subset (Set.iUnion_subset fun w x hx ↦ ?_) fun x hx ↦ ?_
  · exact isRegularWeight_of_mem_openWeylChamber P b hx
  · obtain ⟨w, hw⟩ := exists_mem_dominantChamber_of_finite_weylGroup P b x
    refine Set.mem_iUnion.mpr ⟨w⁻¹, ?_⟩
    rw [mem_openWeylChamber, inv_inv]
    exact mem_openDominantChamber_of_isRegularWeight P b hw ((isRegularWeight_smul P w x).mpr hx)

/-- **Every regular weight lies in exactly one open Weyl chamber**, for a pairing whose Weyl group
is finite. -/
theorem existsUnique_mem_openWeylChamber_of_finite_weylGroup {x : M} (hx : IsRegularWeight P x) :
    ∃! w : P.weylGroup, x ∈ openWeylChamber P b w := by
  have hmem : x ∈ ⋃ w : P.weylGroup, openWeylChamber P b w := by
    rw [iUnion_openWeylChamber_eq_setOf_isRegularWeight_of_finite_weylGroup]
    exact hx
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hmem
  exact ⟨w, hw, fun v hv ↦ eq_of_mem_openWeylChamber P b hv hw⟩

end FiniteWeylGroup

/-- **The open Weyl chambers cover exactly the regular weights.** -/
theorem iUnion_openWeylChamber_eq_setOf_isRegularWeight [P.IsRootSystem] :
    ⋃ w : P.weylGroup, openWeylChamber P b w = {x : M | IsRegularWeight P x} :=
  letI := RootPairing.finite_weylGroup P
  iUnion_openWeylChamber_eq_setOf_isRegularWeight_of_finite_weylGroup P b

/-- **Every regular weight lies in exactly one open Weyl chamber.** -/
theorem existsUnique_mem_openWeylChamber [P.IsRootSystem] {x : M} (hx : IsRegularWeight P x) :
    ∃! w : P.weylGroup, x ∈ openWeylChamber P b w :=
  letI := RootPairing.finite_weylGroup P
  existsUnique_mem_openWeylChamber_of_finite_weylGroup P b hx

end Covering

end TauCeti
