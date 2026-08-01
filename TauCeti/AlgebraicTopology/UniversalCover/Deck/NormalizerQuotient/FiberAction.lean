/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbit.Basic

/-!
# Normalizer-quotient actions on subgroup fibre quotients

For a subgroup `H ≤ Deck p`, the normalizer of `H` acts on the quotient of a fibre by
`H`-orbits: a normalizer representative sends the class of `e` to the class of its deck
translate. Elements of `H` act trivially on this quotient, so the action descends to the
normalizer quotient `N(H) / H`.

This is the fibre-level action bookkeeping needed before the universal-covers roadmap can
identify the deck group of the cover attached to `H` with `N(H) / H`.

## Main declarations

* `TauCeti.Deck.normalizerSubgroupFiberOrbitEquiv`: the permutation of the `H`-fibre
  quotient induced by one normalizer representative.
* `TauCeti.Deck.normalizerSubgroupFiberOrbitPermHom`: the homomorphism from the normalizer
  to permutations of the `H`-fibre quotient.
* `TauCeti.Deck.normalizerQuotientSubgroupFiberOrbitPermHom`: the descended homomorphism
  from `N(H) / H`.
* `TauCeti.Deck.instNormalizerQuotientSubgroupFiberOrbitMulAction`: the resulting action of
  `N(H) / H` on `SubgroupFiberOrbitQuotient H b`.
* `TauCeti.Deck.normalizerQuotientSubgroupFiberOrbitIsPretransitive`: transitivity of this
  descended action when the normalizer action on the fibre is transitive.
* `TauCeti.Deck.instNormalizerQuotientSubgroupFiberOrbitIsPretransitiveOfNormal`: the
  normal-subgroup instance for this descended action.
* `TauCeti.Deck.instNormalizerQuotientSubgroupFiberOrbitIsCancelSMul`: freeness of this
  descended action when the deck action on the fibre is free.

## References

This supplies a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 8: for the cover attached to `H`, the deck group is `N(H)/H`, with the regular case
specializing to `π₁(X, x₀)/H`.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- A normalizer representative acts on the quotient of one fibre by `H`-orbits. -/
def normalizerSubgroupFiberOrbitMap (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    SubgroupFiberOrbitQuotient H b → SubgroupFiberOrbitQuotient H b :=
  TauCeti.MulAction.normalizerOrbitRelQuotientMap H φ

/-- The normalizer action on fibre quotients sends the class of a point to the class of its
deck translate. -/
@[simp]
lemma normalizerSubgroupFiberOrbitMap_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerSubgroupFiberOrbitMap H φ (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  by simp [normalizerSubgroupFiberOrbitMap, subgroupFiberOrbitClass]

/-- The normalizer representative `1` acts trivially on the subgroup fibre quotient. -/
@[simp]
lemma normalizerSubgroupFiberOrbitMap_one (H : Subgroup (Deck p)) :
    normalizerSubgroupFiberOrbitMap (b := b) H ⟨1, by simp⟩ = id := by
  exact TauCeti.MulAction.normalizerOrbitRelQuotientMap_one (X := p ⁻¹' {b}) H

/-- Normalizer representatives act by composition on the subgroup fibre quotient. -/
@[simp]
lemma normalizerSubgroupFiberOrbitMap_mul (H : Subgroup (Deck p))
    (φ ψ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    normalizerSubgroupFiberOrbitMap (b := b) H (φ * ψ) =
      normalizerSubgroupFiberOrbitMap H φ ∘ normalizerSubgroupFiberOrbitMap H ψ := by
  exact TauCeti.MulAction.normalizerOrbitRelQuotientMap_mul (X := p ⁻¹' {b}) H φ ψ

/-- A normalizer representative acts on the subgroup fibre quotient by a permutation. -/
def normalizerSubgroupFiberOrbitEquiv (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    Equiv.Perm (SubgroupFiberOrbitQuotient H b) :=
  TauCeti.MulAction.normalizerOrbitRelQuotientEquiv H φ

/-- A normalizer representative permutes the subgroup fibre quotient by translating
representatives. -/
@[simp]
lemma normalizerSubgroupFiberOrbitEquiv_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerSubgroupFiberOrbitEquiv H φ (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  by simp [normalizerSubgroupFiberOrbitEquiv, subgroupFiberOrbitClass]

/-- The inverse normalizer permutation translates fibre-orbit representatives by the inverse
deck transformation. -/
@[simp]
lemma normalizerSubgroupFiberOrbitEquiv_symm_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    (normalizerSubgroupFiberOrbitEquiv H φ).symm (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p)⁻¹ • e) :=
  by simp [normalizerSubgroupFiberOrbitEquiv, subgroupFiberOrbitClass]

/-- The normalizer action on the subgroup fibre quotient as a permutation representation. -/
noncomputable def normalizerSubgroupFiberOrbitPermHom (H : Subgroup (Deck p)) :
    _root_.Subgroup.normalizer (H : Set (Deck p)) →*
      Equiv.Perm (SubgroupFiberOrbitQuotient H b) :=
  TauCeti.MulAction.normalizerOrbitRelQuotientPermHom H

/-- The normalizer permutation homomorphism sends representatives to the expected deck
translate on fibre-orbit classes. -/
@[simp]
lemma normalizerSubgroupFiberOrbitPermHom_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerSubgroupFiberOrbitPermHom (b := b) H φ (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  by simp [normalizerSubgroupFiberOrbitPermHom, subgroupFiberOrbitClass]

/-- Any normalizer representative whose underlying deck transformation lies in `H` maps to
the identity permutation on the quotient of each fibre by `H`-orbits. -/
lemma normalizerSubgroupFiberOrbitPermHom_eq_one_of_mem
    (H : Subgroup (Deck p)) (φ : _root_.Subgroup.normalizer (H : Set (Deck p)))
    (hφ : (φ : Deck p) ∈ H) :
    normalizerSubgroupFiberOrbitPermHom (b := b) H φ = 1 := by
  exact TauCeti.MulAction.normalizerOrbitRelQuotientPermHom_eq_one_of_mem
    (X := p ⁻¹' {b}) H φ hφ

/-- The action of the normalizer on subgroup fibre quotients descends to `N(H) / H`. -/
noncomputable def normalizerQuotientSubgroupFiberOrbitPermHom (H : Subgroup (Deck p)) :
    Subgroup.normalizerQuotient H →*
      Equiv.Perm (SubgroupFiberOrbitQuotient H b) :=
  TauCeti.MulAction.normalizerQuotientOrbitRelQuotientPermHom H

/-- The descended normalizer-quotient action sends a normalizer representative to the
corresponding deck translate on fibre-orbit classes. -/
@[simp]
lemma normalizerQuotientSubgroupFiberOrbitPermHom_mk_apply (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    normalizerQuotientSubgroupFiberOrbitPermHom (b := b) H
        (φ : Subgroup.normalizerQuotient H) (subgroupFiberOrbitClass H e) =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  by
    simpa [normalizerQuotientSubgroupFiberOrbitPermHom, subgroupFiberOrbitClass] using
      TauCeti.MulAction.normalizerQuotientOrbitRelQuotientPermHom_mk_apply
        (X := p ⁻¹' {b}) H φ e

/-- The normalizer quotient `N(H) / H` acts on the quotient of a fibre by `H`-orbits. -/
noncomputable instance instNormalizerQuotientSubgroupFiberOrbitMulAction (H : Subgroup (Deck p)) :
    MulAction (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) :=
  TauCeti.MulAction.normalizerQuotientOrbitRelQuotientMulAction H

/-- Representative formula for the action of `N(H) / H` on subgroup fibre quotients. -/
@[simp]
lemma normalizerQuotient_smul_subgroupFiberOrbitClass (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) (e : p ⁻¹' {b}) :
    (φ : Subgroup.normalizerQuotient H) • subgroupFiberOrbitClass H e =
      subgroupFiberOrbitClass H ((φ : Deck p) • e) :=
  by
    simpa [instNormalizerQuotientSubgroupFiberOrbitMulAction,
      subgroupFiberOrbitClass] using
        TauCeti.MulAction.normalizerQuotientOrbitRelQuotient_smul_mk
          (X := p ⁻¹' {b}) H φ e

/-- The identity class in `N(H) / H` fixes every subgroup fibre-orbit class. -/
lemma normalizerQuotient_one_smul_subgroupFiberOrbitClass (H : Subgroup (Deck p)) (e : p ⁻¹' {b}) :
    (1 : Subgroup.normalizerQuotient H) • subgroupFiberOrbitClass H e =
      subgroupFiberOrbitClass H e := by
  simp

/-- A representative from `H` acts trivially through the normalizer quotient. -/
lemma normalizerQuotient_mk_of_mem_smul_subgroupFiberOrbitClass
    (H : Subgroup (Deck p)) (φ : Deck p) (hφ : φ ∈ H) (e : p ⁻¹' {b}) :
    ((⟨φ, _root_.Subgroup.le_normalizer hφ⟩ :
          _root_.Subgroup.normalizer (H : Set (Deck p))) :
        Subgroup.normalizerQuotient H) •
        subgroupFiberOrbitClass H e =
      subgroupFiberOrbitClass H e := by
  rw [normalizerQuotient_smul_subgroupFiberOrbitClass]
  exact (subgroupFiberOrbitClass_eq_iff H (φ • e) e).2 ⟨⟨φ, hφ⟩, rfl⟩

/-- If the normalizer of `H` acts transitively on the chosen fibre, then the descended
`N(H) / H` action on the quotient of that fibre by `H`-orbits is transitive. -/
theorem normalizerQuotientSubgroupFiberOrbitIsPretransitive (H : Subgroup (Deck p))
    [MulAction.IsPretransitive (_root_.Subgroup.normalizer (H : Set (Deck p))) (p ⁻¹' {b})] :
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) :=
  TauCeti.MulAction.normalizerQuotientOrbitRelQuotientIsPretransitive
    (X := p ⁻¹' {b}) H

/-- If `H` is normal and the deck action on the chosen fibre is transitive, then the
descended `N(H) / H` action on the quotient of that fibre by `H`-orbits is transitive. -/
theorem normalizerQuotientSubgroupFiberOrbitIsPretransitiveOfNormal
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] (H : Subgroup (Deck p)) [H.Normal] :
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) :=
  TauCeti.MulAction.normalizerQuotientOrbitRelQuotientIsPretransitiveOfNormal
    (X := p ⁻¹' {b}) H

/-- The normalizer quotient acts transitively on a normal subgroup fibre quotient whenever the
deck action on the fibre is transitive. -/
noncomputable instance instNormalizerQuotientSubgroupFiberOrbitIsPretransitiveOfNormal
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] (H : Subgroup (Deck p)) [H.Normal] :
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) :=
  normalizerQuotientSubgroupFiberOrbitIsPretransitiveOfNormal H

/-- For a regular map and a normal deck subgroup, the descended `N(H) / H` action on each
subgroup fibre quotient is transitive. This is the fibre-action half of the regular-cover
specialization from the normalizer quotient to an ordinary quotient by a normal subgroup. -/
theorem normalizerQuotientSubgroupFiberOrbitIsPretransitiveOfNormal_of_isRegular
    (hreg : IsRegular p) (H : Subgroup (Deck p)) [H.Normal] :
    MulAction.IsPretransitive
      (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) := by
  letI := hreg.fiber_isPretransitive b
  exact normalizerQuotientSubgroupFiberOrbitIsPretransitiveOfNormal H

/-- Equality after the `N(H) / H` action on an `H`-fibre quotient is equality of
normalizer-quotient elements, provided the deck action on that fibre is free. -/
lemma normalizerQuotient_smul_subgroupFiberOrbit_eq_smul_iff
    [IsCancelSMul (Deck p) (p ⁻¹' {b})] (H : Subgroup (Deck p))
    (a c : Subgroup.normalizerQuotient H) (x : SubgroupFiberOrbitQuotient H b) :
    a • x = c • x ↔ a = c :=
  TauCeti.MulAction.normalizerQuotientOrbitRelQuotient_smul_eq_smul_iff H a c x

/-- If the deck action on a fibre is free, then the descended `N(H) / H` action on the
quotient of that fibre by `H`-orbits is free. -/
noncomputable instance instNormalizerQuotientSubgroupFiberOrbitIsCancelSMul
    [IsCancelSMul (Deck p) (p ⁻¹' {b})] (H : Subgroup (Deck p)) :
    IsCancelSMul (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) :=
  TauCeti.MulAction.normalizerQuotientOrbitRelQuotientIsCancelSMul (X := p ⁻¹' {b}) H

/-- For a preconnected covering map, the descended `N(H) / H` action on every `H`-fibre
quotient is free. -/
theorem normalizerQuotientSubgroupFiberOrbitIsCancelSMulOfIsCoveringMap
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (H : Subgroup (Deck p)) :
    IsCancelSMul (Subgroup.normalizerQuotient H) (SubgroupFiberOrbitQuotient H b) := by
  letI := fiber_isCancelSMul (b := b) hp
  exact instNormalizerQuotientSubgroupFiberOrbitIsCancelSMul H

end Deck

end TauCeti
