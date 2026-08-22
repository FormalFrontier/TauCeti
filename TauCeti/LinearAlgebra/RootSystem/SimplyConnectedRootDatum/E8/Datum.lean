/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Lattice
import TauCeti.LinearAlgebra.Matrix.Gram

public section

/-!
# The simply connected root datum of type `E₈`

This file builds the pinned integral root datum of type `E₈` on the character and cocharacter
lattices `Fin 8 → ℤ`, out of the enumeration of the two hundred and forty roots in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Basic`. The character lattice is
written in the fundamental-weight basis and the cocharacter lattice in the simple-coroot basis, so
that the `i`-th simple root is the `i`-th row of the Bourbaki-numbered Cartan matrix
`CartanMatrix.E 8` and the `i`-th simple coroot is the `i`-th standard basis vector.

## Reflection stability

Reflection in a norm-two vector preserves the `E₈` Gram form of the simple-coroot basis
(`TauCeti.reflect_vecMul_dotProduct_self`, which needs nothing beyond symmetry of the matrix), so
it maps norm-two vectors to norm-two vectors. The enumeration exhausts the norm-two vectors
(`TauCeti.DynkinType.exists_e8Coroot_eq`), and hence the root and coroot families are stable under
reflection. Mathlib's `RootPairing.mk'` then constructs the permutations of `Fin 240` required by a
root datum, without a two hundred and forty by two hundred and forty table.

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

* `TauCeti.DynkinType.e8Root_dotProduct_e8Coroot_comm`: the pairing of the pinned tables is
  symmetric, type `E₈` being simply laced.
* `TauCeti.DynkinType.hasCartanType_e8SimplyConnectedRootDatum`: the pinned base has Cartan type
  `E8`.
* `TauCeti.DynkinType.corootSpan_e8SimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice, the simply connected condition.

## References

The coordinates and the node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, Plate VII, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section
12.1. This is the `E₈` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. Its assembly follows
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.Basic`.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-! ## Reflection stability -/

/-- **The pairing of the pinned tables is symmetric.** This is the simply-laced feature of `E₈`:
both sides are the value at the simple-coroot coordinates of the symmetric form carried by
`CartanMatrix.E 8`. -/
theorem e8Root_dotProduct_e8Coroot_comm (i j : Fin 240) :
    e8Root i ⬝ᵥ e8Coroot j = e8Root j ⬝ᵥ e8Coroot i := by
  rw [e8Root_apply, e8Root_apply, vecMul_dotProduct_comm (CartanMatrix.E_isSymm 8)]

private lemma exists_e8Coroot_reflection (i j : Fin 240) :
    ∃ k, e8Coroot k =
      e8Coroot j - (e8Root i ⬝ᵥ e8Coroot j) • e8Coroot i := by
  have hnorm (k : Fin 240) : (e8Coroot k ᵥ* CartanMatrix.E 8) ⬝ᵥ e8Coroot k = 2 := by
    rw [← e8Root_apply]
    exact e8Root_dotProduct_coroot k
  refine exists_e8Coroot_eq ?_
  rw [e8Root_apply, vecMul_dotProduct_comm (CartanMatrix.E_isSymm 8) (e8Coroot i) (e8Coroot j)]
  exact (reflect_vecMul_dotProduct_self (CartanMatrix.E_isSymm 8) (hnorm i) (e8Coroot j)).trans
    (hnorm j)

/-! ## The pinned datum -/

/-- The pinned simply connected root datum of type `E₈`.

Both lattices are `Fin 8 → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Root indices `0` through `7` are the Bourbaki
simple roots; see `TauCeti.DynkinType.root_e8SimpleIndex`. -/
noncomputable def e8SimplyConnectedRootDatum : RootDatum (Fin 240) (Fin 8 → ℤ) (Fin 8 → ℤ) :=
  RootPairing.mk' (dotProductEquiv ℤ (Fin 8)).toLinearMap e8Root e8Coroot
    e8Root_dotProduct_coroot
    (by
      rintro i _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := exists_e8Coroot_reflection i j
      refine ⟨k, ?_⟩
      have hroot : e8Root k =
          e8Root j - (e8Root i ⬝ᵥ e8Coroot j) • e8Root i := by
        simpa only [sub_vecMul, smul_vecMul, ← e8Root_apply] using
          congrArg (fun x : Fin 8 → ℤ ↦ x ᵥ* CartanMatrix.E 8) hk
      rw [e8Root_dotProduct_e8Coroot_comm] at hroot
      simpa [Module.preReflection_apply, dotProductEquiv_apply_apply] using hroot)
    (by
      rintro i _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := exists_e8Coroot_reflection i j
      refine ⟨k, ?_⟩
      simpa [Module.preReflection_apply, dotProductEquiv_apply_apply] using hk)

/-- The root embedding of the pinned `E₈` datum is the explicit table `e8Root`. -/
@[simp] lemma e8SimplyConnectedRootDatum_root : e8SimplyConnectedRootDatum.root = e8Root := (rfl)

/-- The coroot embedding of the pinned `E₈` datum is the explicit table `e8Coroot`. -/
@[simp] lemma e8SimplyConnectedRootDatum_coroot :
    e8SimplyConnectedRootDatum.coroot = e8Coroot := (rfl)

/-- The perfect pairing of the pinned `E₈` datum is the dot product of coordinate vectors, the
fundamental-weight and simple-coroot bases being dual to one another. -/
@[simp] lemma e8SimplyConnectedRootDatum_toLinearMap_apply (x y : Fin 8 → ℤ) :
    e8SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y := (rfl)

/-- Pairing a pinned `E₈` root with a coroot computes as their coordinate dot product. -/
@[simp] lemma e8SimplyConnectedRootDatum_pairing (i j : Fin 240) :
    e8SimplyConnectedRootDatum.pairing i j = e8Root i ⬝ᵥ e8Coroot j := (rfl)

/-! ## The pinned base -/

/-- **The coroots of the pinned type `E₈` datum span the cocharacter lattice.** This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. -/
theorem corootSpan_e8SimplyConnectedRootDatum_eq_top :
    e8SimplyConnectedRootDatum.corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single coroot_e8SimpleIndex

/-- The support of the pinned base of type `E₈`: the first eight root indices. -/
private abbrev e8SimpleSupport : Finset (Fin 240) := simpleSupport e8SimpleIndex_injective

/-- Every `E₈` coroot has simple-coroot coordinates that are all nonnegative or all nonpositive,
the positive half of the table being nonnegative and the negative half its negation. -/
private lemma e8Coroot_nonneg_or_nonpos (j : Fin 240) :
    (∀ k, 0 ≤ e8Coroot j k) ∨ (∀ k, e8Coroot j k ≤ 0) := by
  induction j using Fin.addCases (m := 120) (n := 120) with
  | left j =>
    refine Or.inl fun k ↦ ?_
    rw [e8Coroot_castAdd]
    exact e8PositiveCoroot_nonneg _ k
  | right j =>
    refine Or.inr fun k ↦ ?_
    rw [Fin.natAdd_eq_addNat, e8Coroot_addNat, Pi.neg_apply, neg_nonpos]
    exact e8PositiveCoroot_nonneg _ k

/-- In the cocharacter lattice a coroot is the combination of the simple coroots recorded by its
own coordinates, the simple coroots being the standard basis. -/
private lemma sum_smul_coroot_e8SimpleIndex (j : Fin 240) :
    ∑ k : Fin 8, e8Coroot j k • e8Coroot (e8SimpleIndex k) = e8Coroot j := by
  simpa only [coroot_e8SimpleIndex] using (pi_eq_sum_univ' (e8Coroot j)).symm

/-- In the character lattice a root is the combination of the simple roots recorded by the same
coordinates, the two tables differing by the Cartan-matrix map. -/
private lemma sum_smul_root_e8SimpleIndex (j : Fin 240) :
    ∑ k : Fin 8, e8Coroot j k • e8Root (e8SimpleIndex k) = e8Root j := by
  have h := congrArg (CartanMatrix.E 8).mulVecLin (sum_smul_coroot_e8SimpleIndex j)
  rw [map_sum] at h
  simpa only [map_zsmul, mulVecLin_apply, ← e8Root_eq_mulVec] using h

private lemma linearIndependent_root_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 ↦ e8Root (e8SimpleIndex i) := by
  simpa only [root_e8SimpleIndex] using
    linearIndependent_rows_of_det_ne_zero (A := CartanMatrix.E 8)
      (by rw [CartanMatrix.E₈_det]; norm_num)

private lemma linearIndependent_coroot_e8SimpleIndex :
    LinearIndependent ℤ fun i : Fin 8 ↦ e8Coroot (e8SimpleIndex i) := by
  simpa only [coroot_e8SimpleIndex] using Pi.linearIndependent_single_one (Fin 8) ℤ

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `E₈`. Its support
is the set of the first eight root indices, carrying the simple roots in Bourbaki order. -/
noncomputable def e8SimplyConnectedBase : e8SimplyConnectedRootDatum.Base where
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
@[simp] theorem mem_support_e8SimplyConnectedBase {k : Fin 240} :
    k ∈ e8SimplyConnectedBase.support ↔ (k : ℕ) < 8 := by
  rw [e8SimplyConnectedBase_support]
  exact mem_simpleSupport_iff_lt e8SimpleIndex_injective e8SimpleIndex_val

/-- **The Cartan integers at the first eight root indices are Mathlib's Bourbaki-numbered `E₈`
matrix.** This pins the node order independently of the existential relabelling in
`TauCeti.HasCartanType`. -/
theorem pairing_e8SimpleIndex (i j : Fin 8) :
    e8SimplyConnectedRootDatum.pairing (e8SimpleIndex i) (e8SimpleIndex j) =
      CartanMatrix.E 8 i j := by
  rw [e8SimplyConnectedRootDatum_pairing, root_e8SimpleIndex, coroot_e8SimpleIndex,
    dotProduct_single, mul_one]

/-- **The pinned datum of type `E₈` has Cartan type `E8`.** Its Bourbaki-numbered base realizes the
standard Cartan matrix `CartanMatrix.E 8`, with the node numbering of `TauCeti.DynkinType`. -/
theorem hasCartanType_e8SimplyConnectedRootDatum :
    HasCartanType e8SimplyConnectedRootDatum e8SimplyConnectedBase E8 :=
  hasCartanType_of_pairing_eq e8SimpleIndex_injective rfl fun i j ↦
    (pairing_e8SimpleIndex i j).trans (by simp)

end DynkinType

end TauCeti
