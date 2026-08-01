/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.NormalSubgroupFiberQuotient.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.NormalizerQuotient.FiberAction

/-!
# Equivariance for normal deck-subgroup fibre quotients

For a normal subgroup `H ≤ Deck p`, the existing free-transitive fibre-action equivalence
identifies the quotient of a fibre by `H` with the normalizer quotient `N(H) / H`. This file
records how that identification, and its regular preconnected-cover specialization, interacts
with the descended `N(H) / H` action on the fibre quotient.

The orientation is important: the existing fibre-quotient equivalence sends the orbit class
of `φ • e` to the normalizer-quotient class of `φ⁻¹`. Consequently, acting on the fibre
quotient by a normalizer-quotient element `a` corresponds, under this equivalence, to right
multiplication by `a⁻¹`.

## Main declarations

* `TauCeti.Deck.subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv`:
  the `N(H) / H` action becomes right multiplication by the inverse.
* the regular `..._map_smul_eq_mul_inv` wrapper:
  the same statement for a regular preconnected covering map.
* Inverse-form lemmas for applying the inverse equivalence after right multiplication.

## References

This supplies a small bookkeeping prerequisite for
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8: the deck group of the cover
attached to `H` is `N(H) / H`, with the normal case specializing to a quotient by `H`.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

private lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_eq
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (x : SubgroupFiberOrbitQuotient H b) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e x =
      @subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal E B _ p b
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H _ e x := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  apply (Subgroup.normalizerQuotientEquivQuotientOfNormal H).injective
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) e e'
  rw [← hφ, ← subgroupFiberOrbitClass_eq_mk H (φ • e),
    normalizerQuotientEquivQuotientOfNormal_regularSubgroupFiberOrbitQuotientEquiv,
    normalizerQuotientEquivQuotientOfNormal_subgroupFiberOrbitQuotientEquiv,
    regularSubgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul,
    subgroupFiberOrbitQuotientEquivQuotientGroup_apply_smul]

private lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_apply_eq
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (y : Subgroup.normalizerQuotient H) :
    (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm y =
      (@subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal E B _ p b
        (hreg.fiber_isPretransitive b) (fiber_isCancelSMul (b := b) hp) H _ e).symm y := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  apply (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).injective
  rw [Equiv.apply_symm_apply,
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_eq,
    Equiv.apply_symm_apply]

private lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_eq
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e =
      TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal
        (G := Deck p) (X := p ⁻¹' {b}) H e := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro e'
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) e e'
  rw [← hφ, ← subgroupFiberOrbitClass_eq_mk H (φ • e),
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_smul,
    subgroupFiberOrbitClass_eq_mk,
    TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_apply_smul]

/-- Under the normal-subgroup fibre quotient equivalence, the descended normalizer-quotient
action is right multiplication by the inverse. This is the representative-free form of the
convention that `φ • e` maps to the class of `φ⁻¹`. -/
@[simp]
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (a : Subgroup.normalizerQuotient H) (x : SubgroupFiberOrbitQuotient H b) :
    subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e (a • x) =
      subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e x * a⁻¹ := by
  rw [subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_eq]
  exact TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv
    (G := Deck p) (X := p ⁻¹' {b}) H e a x

/-- For a regular preconnected covering map, the normal-subgroup fibre quotient equivalence
turns the descended normalizer-quotient action into right multiplication by the inverse. -/
@[simp]
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b})
    (a : Subgroup.normalizerQuotient H) (x : SubgroupFiberOrbitQuotient H b) :
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e (a • x) =
      regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e x * a⁻¹ := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  rw [regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_eq,
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_apply_eq]
  exact subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_map_smul_eq_mul_inv H e a x

/-- Applying the inverse normal-subgroup fibre quotient equivalence after right multiplication
by `a⁻¹` is the same as acting by `a` on the fibre quotient. -/
lemma subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] [IsCancelSMul (Deck p) (p ⁻¹' {b})]
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (a y : Subgroup.normalizerQuotient H) :
    (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm (y * a⁻¹) =
      a • (subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal H e).symm y := by
  rw [subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_eq]
  exact TauCeti.MulAction.orbitRelQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv
    (G := Deck p) (X := p ⁻¹' {b}) H e a y

/-- For a regular preconnected covering map, applying the inverse normal-subgroup fibre
quotient equivalence after right multiplication by `a⁻¹` is the same as acting by `a` on the
fibre quotient. -/
lemma regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv
    [TopologicalSpace B] [PreconnectedSpace E] (hp : IsCoveringMap p) (hreg : IsRegular p)
    (H : Subgroup (Deck p)) [H.Normal] (e : p ⁻¹' {b}) (a y : Subgroup.normalizerQuotient H) :
    (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm (y * a⁻¹) =
      a • (regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal hp hreg H e).symm
        y := by
  letI := hreg.fiber_isPretransitive b
  letI := fiber_isCancelSMul (b := b) hp
  rw [regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_apply_eq,
    regularSubgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_apply_eq]
  exact subgroupFiberOrbitQuotientEquivNormalizerQuotientOfNormal_symm_mul_inv H e a y

end Deck

end TauCeti
