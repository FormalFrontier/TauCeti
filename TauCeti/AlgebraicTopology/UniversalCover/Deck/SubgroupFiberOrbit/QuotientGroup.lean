/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit.Basic

/-!
# Subgroup fibre orbits of a regular cover as deck-group quotients

For a regular preconnected covering map, evaluation at any point of a fibre identifies the
deck group with that fibre. This file records the corresponding quotient-level statement:
orbits of a subgroup `H ≤ Deck p` on the fibre are equivalent to the coset quotient
`Deck p ⧸ H`.

This is bookkeeping for the universal-covers roadmap. The classification of connected covers
uses fibre quotients by subgroups, while the regular-cover computation of the deck group of
the cover attached to `H` is expressed algebraically as a normalizer quotient. The bridge here
lets later arguments move between those fibre-orbit quotients and subgroup quotients without
unfolding either construction.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivQuotientGroup`: identifies
  `SubgroupFiberOrbitQuotient H b` with `Deck p ⧸ H`.
* `TauCeti.Deck.regularSubgroupFiberOrbitQuotientEquivQuotientGroup`: the regular-cover
  specialization that installs the free-transitive deck action on the fibre.
* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE`: compatibility with
  the maps induced by subgroup inclusions.
* `TauCeti.Deck.subgroupFiberOrbitQuotientBotEquivDeck`: for `H = ⊥`, the quotient is the
  deck group, with the inverse orientation coming from Mathlib's quotient convention.
* Endpoint collapse lemmas for `H = ⊤`.

## References

This supplies a prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, items
7 and 8, especially the regular-cover milestones comparing fibre quotients with the
normalizer quotient `N(H)/H`. It is a deck-specific specialization of Mathlib's
`MulAction.equivSubgroupOrbitsQuotientGroup`, the orbit-quotient form of the
orbit-stabilizer theorem for free transitive actions.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

private lemma quotientGroup_quotientBot_mk (φ : Deck p) :
    QuotientGroup.quotientBot (G := Deck p)
        (QuotientGroup.mk (s := (⊥ : Subgroup (Deck p))) φ) =
      φ :=
  rfl

/-- The subgroup-fibre orbit quotient is equivalent to the quotient of the deck group by the
subgroup, once the deck action on the chosen fibre is free and transitive. -/
noncomputable def subgroupFiberOrbitQuotientEquivQuotientGroup
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Deck p ⧸ H :=
  MulAction.equivSubgroupOrbitsQuotientGroup e H

/-- For a regular preconnected covering map, the subgroup-fibre orbit quotient is equivalent
to the quotient of the deck group by the subgroup. -/
noncomputable def regularSubgroupFiberOrbitQuotientEquivQuotientGroup
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient H b ≃ Deck p ⧸ H :=
  @subgroupFiberOrbitQuotientEquivQuotientGroup E B _ p b
    (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H e

/-- The inverse quotient equivalence sends the coset of a deck transformation `φ` to the
`H`-orbit class of the point `φ⁻¹ • e`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  simp [subgroupFiberOrbitQuotientEquivQuotientGroup, subgroupFiberOrbitClass_eq_mk,
    MulAction.equivSubgroupOrbitsQuotientGroup_symm_mk H e φ]

/-- For a regular cover, the inverse quotient equivalence sends the coset of a deck
transformation `φ` to the `H`-orbit class of `φ⁻¹ • e`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e).symm
        (QuotientGroup.mk (s := H) φ) =
      subgroupFiberOrbitClass H (φ⁻¹ • e) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk H e φ]

/-- On underlying points, the inverse quotient equivalence sends the coset of `φ` to the
class of the value of `φ⁻¹` on the chosen fibre point. -/
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk_coe
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm (QuotientGroup.mk φ) =
      subgroupFiberOrbitClass H
        ⟨φ.1.symm e.1, by
          rw [Set.mem_preimage, Set.mem_singleton_iff]
          exact (map_proj φ⁻¹ e.1).trans (Set.mem_singleton_iff.mp e.2)⟩ := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk]
  apply congrArg (subgroupFiberOrbitClass H)
  ext
  exact fiber_smul_coe φ⁻¹ e

/-- The inverse quotient equivalence sends the identity coset to the orbit class of the chosen
fibre point. -/
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_symm_one
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    (subgroupFiberOrbitQuotientEquivQuotientGroup H e).symm
        (QuotientGroup.mk (s := H) (1 : Deck p)) =
      subgroupFiberOrbitClass H e := by
  rw [subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk, inv_one, one_smul]

/-- The quotient equivalence sends the orbit class of `φ⁻¹ • e` to the coset of `φ`. -/
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  rw [← subgroupFiberOrbitQuotientEquivQuotientGroup_symm_mk H e φ]
  exact (subgroupFiberOrbitQuotientEquivQuotientGroup H e).apply_symm_apply
    (QuotientGroup.mk (s := H) φ)

/-- For a regular cover, the quotient equivalence sends the orbit class of `φ⁻¹ • e` to the
coset of `φ`. -/
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ⁻¹ • e)) =
      QuotientGroup.mk (s := H) φ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp only [regularSubgroupFiberOrbitQuotientEquivQuotientGroup]
  exact subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e φ

/-- The quotient equivalence sends the chosen fibre point to the identity coset. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_base
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H e) =
      QuotientGroup.mk (s := H) (1 : Deck p) := by
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e (1 : Deck p)

/-- The quotient equivalence sends the orbit class of `φ • e` to the coset of `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientEquivQuotientGroup H e
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  simpa using
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_inv_smul H e φ⁻¹

/-- For a regular cover, the quotient equivalence sends the orbit class of `φ • e` to the
coset of `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e
        (subgroupFiberOrbitClass H (φ • e)) =
      QuotientGroup.mk (s := H) φ⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup]

/-- For a free transitive deck action on a fibre, quotienting the fibre by the trivial
subgroup identifies that quotient with the deck group. The representative convention is the
same as `subgroupFiberOrbitQuotientEquivQuotientGroup`: the class of `φ • e` corresponds to
`φ⁻¹`. -/
noncomputable def subgroupFiberOrbitQuotientBotEquivDeck
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient (⊥ : Subgroup (Deck p)) b ≃ Deck p :=
  (subgroupFiberOrbitQuotientEquivQuotientGroup (⊥ : Subgroup (Deck p)) e).trans
    (QuotientGroup.quotientBot (G := Deck p) : Deck p ⧸ (⊥ : Subgroup (Deck p)) ≃ Deck p)

/-- For a regular preconnected covering map, the quotient of a fibre by the trivial deck
subgroup is the deck group. -/
noncomputable def regularSubgroupFiberOrbitQuotientBotEquivDeck
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) :
    SubgroupFiberOrbitQuotient (⊥ : Subgroup (Deck p)) b ≃ Deck p :=
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  subgroupFiberOrbitQuotientBotEquivDeck e

/-- The bottom-subgroup quotient-to-deck equivalence sends the class of `φ • e` to `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquivDeck_apply_smul
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : Deck p) :
    subgroupFiberOrbitQuotientBotEquivDeck e
        (subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) (φ • e)) =
      φ⁻¹ := by
  have h := congrArg (QuotientGroup.quotientBot (G := Deck p))
    (subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul
      (H := (⊥ : Subgroup (Deck p))) e φ)
  simpa [subgroupFiberOrbitQuotientBotEquivDeck] using h.trans (quotientGroup_quotientBot_mk φ⁻¹)

/-- For a regular cover, the bottom-subgroup quotient-to-deck equivalence sends the class of
`φ • e` to `φ⁻¹`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientBotEquivDeck_apply_smul
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ : Deck p) :
    regularSubgroupFiberOrbitQuotientBotEquivDeck hp hreg e
        (subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) (φ • e)) =
      φ⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  exact subgroupFiberOrbitQuotientBotEquivDeck_apply_smul e φ

/-- The chosen fibre point maps to the identity deck transformation under the
bottom-subgroup quotient-to-deck equivalence. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquivDeck_apply_base
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientBotEquivDeck e
        (subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e) =
      1 := by
  simpa using subgroupFiberOrbitQuotientBotEquivDeck_apply_smul e (1 : Deck p)

/-- For a regular cover, the chosen fibre point maps to the identity deck transformation
under the bottom-subgroup quotient-to-deck equivalence. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientBotEquivDeck_apply_base
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) :
    regularSubgroupFiberOrbitQuotientBotEquivDeck hp hreg e
        (subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) e) =
      1 := by
  simpa using
    regularSubgroupFiberOrbitQuotientBotEquivDeck_apply_smul hp hreg e (1 : Deck p)

/-- The inverse bottom-subgroup quotient-to-deck equivalence sends a deck transformation to
the class of its inverse acting on the chosen fibre point. -/
@[simp]
lemma subgroupFiberOrbitQuotientBotEquivDeck_symm_apply
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (φ : Deck p) : (subgroupFiberOrbitQuotientBotEquivDeck e).symm φ =
      subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) (φ⁻¹ • e) := by
  apply (subgroupFiberOrbitQuotientBotEquivDeck e).injective
  rw [Equiv.apply_symm_apply, subgroupFiberOrbitQuotientBotEquivDeck_apply_smul]
  simp

/-- For a regular cover, the inverse bottom-subgroup quotient-to-deck equivalence sends a
deck transformation to the class of its inverse acting on the chosen fibre point. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientBotEquivDeck_symm_apply
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (φ : Deck p) :
    (regularSubgroupFiberOrbitQuotientBotEquivDeck hp hreg e).symm φ =
      subgroupFiberOrbitClass (⊥ : Subgroup (Deck p)) (φ⁻¹ • e) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientBotEquivDeck]

/-- Under the quotient-group equivalence, the full-subgroup fibre quotient lands in the
unique coset of `Deck p ⧸ ⊤`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_top
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient (⊤ : Subgroup (Deck p)) b) :
    subgroupFiberOrbitQuotientEquivQuotientGroup (⊤ : Subgroup (Deck p)) e x =
      QuotientGroup.mk (s := (⊤ : Subgroup (Deck p))) (1 : Deck p) := by
  haveI := QuotientGroup.subsingleton_quotient_top (G := Deck p)
  exact Subsingleton.elim _ _

/-- For a regular cover, the full-subgroup fibre quotient lands in the unique coset of
`Deck p ⧸ ⊤`. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_top
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient (⊤ : Subgroup (Deck p)) b) :
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg (⊤ : Subgroup (Deck p)) e x =
      QuotientGroup.mk (s := (⊤ : Subgroup (Deck p))) (1 : Deck p) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_top e x]

/-- The subgroup-fibre quotient equivalence is natural in subgroup inclusions. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (subgroupFiberOrbitQuotientEquivQuotientGroup H e x) =
      subgroupFiberOrbitQuotientEquivQuotientGroup K e
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  simp [subgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitMapOfLE, MulAction.equivSubgroupOrbitsQuotientGroup_mapOfLE
      (G := Deck p) (X := p ⁻¹' {b}) hHK e x]

/-- For a regular cover, the subgroup-fibre quotient equivalence is natural in subgroup
inclusions. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    {H K : Subgroup (Deck p)} (hHK : H ≤ K) (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    Subgroup.quotientMapOfLE hHK
        (regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg H e x) =
      regularSubgroupFiberOrbitQuotientEquivQuotientGroup hp hreg K e
        (subgroupFiberOrbitMapOfLE (b := b) hHK x) := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  simp [regularSubgroupFiberOrbitQuotientEquivQuotientGroup,
    subgroupFiberOrbitQuotientEquivQuotientGroup_mapOfLE hHK e x]

/-- Equality of subgroup fibre-orbit classes is equality of the corresponding deck cosets
under the quotient equivalence, with the inverse orientation coming from Mathlib's quotient
convention. -/
lemma subgroupFiberOrbitClass_eq_iff_quotientGroup_mk_inv_eq
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) (φ ψ : Deck p) :
    subgroupFiberOrbitClass H (φ • e) = subgroupFiberOrbitClass H (ψ • e) ↔
      QuotientGroup.mk (s := H) φ⁻¹ = QuotientGroup.mk (s := H) ψ⁻¹ := by
  constructor
  · intro h
    have h' := congrArg
      (subgroupFiberOrbitQuotientEquivQuotientGroup H e) h
    rw [subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul] at h'
    exact h'
  · intro h
    apply (subgroupFiberOrbitQuotientEquivQuotientGroup H e).injective
    rw [subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
      subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]
    exact h

end Deck

end TauCeti
