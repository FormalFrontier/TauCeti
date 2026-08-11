/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8

public section

/-!
# The simply connected root datum of type `E₈`

This file builds the pinned integral root datum of type `E₈` on the character and cocharacter
lattices `Fin 8 → ℤ`, out of the enumeration of the two hundred and forty roots in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8`. The character lattice is
written in the fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so
that the `i`-th simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix
`CartanMatrix.E₈` and the `i`-th simple coroot is the `i`-th standard basis vector.

Everything the datum is made of — the two coordinate tables, the reflection permutations, and the
identities relating them — is fixed in that file, and nothing here adds data: this file only
assembles those pieces into `RootDatum` and `RootPairing.Base`, and records the two properties
Layer 6 asks of the result, its Cartan type and the lattice its coroots span.

## The lattices

Only the coroots are asked to span their lattice, in
`TauCeti.DynkinType.corootSpan_e8SimplyConnectedRootDatum_eq_top`, which is the condition the
pinned Chevalley--Demazure construction consumes. In the sibling files that condition is the
asymmetric half of the pinning, the roots spanning the root lattice at the index recorded by the
Cartan determinant inside the weight lattice. Type `E₈` is one of the three types — with `F₄` and
`G₂` — whose Cartan determinant is `1`, so here the root and the weight lattice agree and the
simply connected form is also the adjoint one; the datum is nevertheless stated through the same
coroot-side condition as its siblings, which is what the per-type dispatcher will collect.

## Main definitions

* `TauCeti.DynkinType.e8SimplyConnectedRootDatum`: the pinned root datum of type `E₈`.
* `TauCeti.DynkinType.e8SimplyConnectedBase`: the base formed by the first eight root indices.

## Main results

* `TauCeti.DynkinType.hasCartanType_e8SimplyConnectedRootDatum`: the pinned base has Cartan type
  `E8`.
* `TauCeti.DynkinType.corootSpan_e8SimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate VII, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `E₈` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. Its formal construction follows
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6`.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-! ## The pinned datum -/

/-- The pinned simply connected root datum of type `E₈`.

Both lattices are `Fin 8 → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Root indices `0` through `7` are the Bourbaki
simple roots; see `TauCeti.DynkinType.root_e8SimpleIndex`. -/
def e8SimplyConnectedRootDatum : RootDatum (Fin 240) (Fin 8 → ℤ) (Fin 8 → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin 8)).toLinearMap
  root := e8Root
  coroot := e8Coroot
  root_coroot_two i := e8Root_dotProduct_coroot i
  reflectionPerm := e8ReflectionPerm
  reflectionPerm_root i j := e8ReflectionPerm_root i j
  reflectionPerm_coroot i j := e8ReflectionPerm_coroot i j

/-- The root embedding of the pinned `E₈` datum is the explicit table `e8Root`. -/
@[simp] lemma e8SimplyConnectedRootDatum_root : e8SimplyConnectedRootDatum.root = e8Root := (rfl)

/-- The coroot embedding of the pinned `E₈` datum is the explicit table `e8Coroot`. -/
@[simp] lemma e8SimplyConnectedRootDatum_coroot :
    e8SimplyConnectedRootDatum.coroot = e8Coroot := (rfl)

/-- The perfect pairing of the pinned `E₈` datum is the dot product of coordinate vectors, the
fundamental-weight and simple-coroot bases being dual to one another. -/
@[simp] lemma e8SimplyConnectedRootDatum_toLinearMap (x y : Fin 8 → ℤ) :
    e8SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y := (rfl)

/-- Pairing a pinned `E₈` root with a coroot computes as their coordinate dot product. -/
@[simp] lemma e8SimplyConnectedRootDatum_pairing (i j : Fin 240) :
    e8SimplyConnectedRootDatum.pairing i j = e8Root i ⬝ᵥ e8Coroot j := (rfl)

/-- **The coroots of the pinned type `E₈` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. -/
theorem corootSpan_e8SimplyConnectedRootDatum_eq_top :
    e8SimplyConnectedRootDatum.corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single coroot_e8SimpleIndex

/-! ## The pinned base -/

/-- The support of the pinned base of type `E₈`: the first eight root indices. -/
private abbrev e8SimpleSupport : Finset (Fin 240) := simpleSupport e8SimpleIndex_injective

/-- Every `E₈` coroot has simple-coroot coordinates that are all nonnegative or all nonpositive,
the positive half of the table being nonnegative and the negative half its negation. -/
private lemma e8Coroot_nonneg_or_nonpos (j : Fin 240) :
    (∀ k, 0 ≤ e8Coroot j k) ∨ (∀ k, e8Coroot j k ≤ 0) := by
  induction j using Fin.addCases (m := 120) (n := 120) with
  | left j =>
    refine Or.inl fun k => ?_
    rw [e8Coroot_castAdd]
    exact e8PositiveCoroot_nonneg _ k
  | right j =>
    refine Or.inr fun k => ?_
    rw [Fin.natAdd_eq_addNat, e8Coroot_addNat, Pi.neg_apply, neg_nonpos]
    exact e8PositiveCoroot_nonneg _ k

/-- In the cocharacter lattice a coroot is the combination of the simple coroots recorded by its
own coordinates, the simple coroots being the standard basis. -/
private lemma sum_smul_coroot_e8SimpleIndex (j : Fin 240) :
    ∑ k : Fin 8, e8Coroot j k • e8Coroot (e8SimpleIndex k) = e8Coroot j := by
  have hk (k : Fin 8) :
      e8Coroot j k • e8Coroot (e8SimpleIndex k) = Pi.single k (e8Coroot j k) := by
    rw [coroot_e8SimpleIndex, ← Pi.single_smul', smul_eq_mul, mul_one]
  simpa only [hk] using LinearMap.sum_single_apply _ (e8Coroot j)

/-- In the character lattice a root is the combination of the simple roots recorded by the same
coordinates, the two tables differing by the Cartan-matrix map. -/
private lemma sum_smul_root_e8SimpleIndex (j : Fin 240) :
    ∑ k : Fin 8, e8Coroot j k • e8Root (e8SimpleIndex k) = e8Root j := by
  have h := congrArg CartanMatrix.E₈.mulVecLin (sum_smul_coroot_e8SimpleIndex j)
  rw [map_sum] at h
  simpa only [map_zsmul, mulVecLin_apply, ← e8Root_eq_mulVec] using h

private lemma linearIndependent_root_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 => e8Root (e8SimpleIndex i) := by
  have h : (fun i : Fin 8 => e8Root (e8SimpleIndex i)) = fun i => CartanMatrix.E₈ i :=
    funext root_e8SimpleIndex
  rw [h]
  exact linearIndependent_rows_of_det_ne_zero (by rw [CartanMatrix.E₈_det]; norm_num)

private lemma linearIndependent_coroot_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 => e8Coroot (e8SimpleIndex i) := by
  simpa only [coroot_e8SimpleIndex] using Pi.linearIndependent_single_one (Fin 8) ℤ

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `E₈`. Its support
is the set of the first eight root indices, carrying the simple roots in Bourbaki order. -/
def e8SimplyConnectedBase : e8SimplyConnectedRootDatum.Base where
  support := e8SimpleSupport
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ linearIndependent_root_e8SimpleIndex
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ linearIndependent_coroot_e8SimpleIndex
  root_mem_or_neg_mem k := by
    simp only [e8SimplyConnectedRootDatum_root]
    rw [image_simpleSupport, ← sum_smul_root_e8SimpleIndex k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e8Coroot_nonneg_or_nonpos k)
  coroot_mem_or_neg_mem k := by
    simp only [e8SimplyConnectedRootDatum_coroot]
    rw [image_simpleSupport, ← sum_smul_coroot_e8SimpleIndex k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e8Coroot_nonneg_or_nonpos k)

/-- The support of the pinned base of type `E₈` is the image of the simple index map, the field
it is built from. -/
private lemma e8SimplyConnectedBase_support :
    e8SimplyConnectedBase.support = simpleSupport e8SimpleIndex_injective := (rfl)

/-- Membership in the pinned base support is exactly membership among the first eight root
indices. -/
@[simp] theorem mem_e8SimplyConnectedBase_support {k : Fin 240} :
    k ∈ e8SimplyConnectedBase.support ↔ (k : ℕ) < 8 := by
  rw [e8SimplyConnectedBase_support, mem_simpleSupport]
  constructor
  · rintro ⟨i, rfl⟩
    rw [e8SimpleIndex_val]
    exact i.isLt
  · exact fun hk => ⟨⟨k, hk⟩, Fin.ext (by rw [e8SimpleIndex_val])⟩

/-- **The Cartan integers at the first eight root indices are Mathlib's Bourbaki-numbered `E₈`
matrix.** This pins the node order independently of the existential relabelling in
`TauCeti.HasCartanType`. -/
theorem pairing_e8SimpleIndex (i j : Fin 8) :
    e8SimplyConnectedRootDatum.pairing (e8SimpleIndex i) (e8SimpleIndex j) =
      CartanMatrix.E₈ i j := by
  rw [e8SimplyConnectedRootDatum_pairing, root_e8SimpleIndex, coroot_e8SimpleIndex,
    dotProduct_single, mul_one]

/-- **The pinned datum of type `E₈` has Cartan type `E8`.** Its Bourbaki-numbered base realizes the
standard Cartan matrix `CartanMatrix.E₈`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_e8SimplyConnectedRootDatum :
    HasCartanType e8SimplyConnectedRootDatum e8SimplyConnectedBase E8 :=
  hasCartanType_of_pairing_eq e8SimpleIndex_injective rfl fun i j =>
    (pairing_e8SimpleIndex i j).trans (by simp)

end DynkinType

end TauCeti
