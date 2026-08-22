/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Lattice
import TauCeti.LinearAlgebra.Matrix.Gram

public section

/-!
# The simply connected root datum of type `E₇`

This file builds the pinned integral root datum of type `E₇` on the character and cocharacter
lattices `Fin 7 → ℤ`. The character lattice is written in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Thus the `i`-th simple root is the `i`-th row of
the Bourbaki-numbered Cartan matrix `CartanMatrix.E 7`, while the `i`-th simple coroot is the
`i`-th standard basis vector.

Reflection in a norm-two vector preserves the `E₇` Gram form. The completeness theorem
`TauCeti.DynkinType.exists_e7Coroot_eq` therefore supplies the reflected coroot from the pinned
enumeration, and Mathlib's `RootPairing.mk'` constructs the required permutations of the 126 root
indices. In particular, no reflection table is needed.

The coroots span their lattice, which is the simply connected condition consumed by the pinned
Chevalley--Demazure construction. The roots instead span a sublattice of index two in the weight
lattice, as recorded by the determinant of `CartanMatrix.E 7`.

## Main definitions

* `TauCeti.DynkinType.e7SimplyConnectedRootDatum`: the pinned root datum of type `E₇`.
* `TauCeti.DynkinType.e7SimplyConnectedBase`: the base formed by the first seven root indices.

## Main results

* `TauCeti.DynkinType.hasCartanType_e7SimplyConnectedRootDatum`: the pinned base has Cartan type
  `E7`.
* `TauCeti.DynkinType.corootSpan_e7SimplyConnectedRootDatum_eq_top`: the coroots span the
  cocharacter lattice.

## References

The coordinates and node numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VI, and Humphreys, *Introduction to Lie Algebras and Representation Theory*, section 12.1.
This is the `E₇` branch of the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. Its assembly follows the existing
`E₈` construction in this directory.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-! ## Reflection stability -/

/-- The pairing of the pinned root and coroot tables is symmetric, as type `E₇` is simply laced. -/
theorem e7Root_dotProduct_e7Coroot_comm (i j : Fin 126) :
    e7Root i ⬝ᵥ e7Coroot j = e7Root j ⬝ᵥ e7Coroot i := by
  rw [e7Root_apply, e7Root_apply, vecMul_dotProduct_comm (CartanMatrix.E_isSymm 7)]

private lemma exists_e7Coroot_reflection (i j : Fin 126) :
    ∃ k, e7Coroot k =
      e7Coroot j - (e7Root i ⬝ᵥ e7Coroot j) • e7Coroot i := by
  have hnorm (k : Fin 126) : (e7Coroot k ᵥ* CartanMatrix.E 7) ⬝ᵥ e7Coroot k = 2 := by
    rw [← e7Root_apply]
    exact e7Root_dotProduct_coroot k
  refine exists_e7Coroot_eq ?_
  rw [e7Root_apply, vecMul_dotProduct_comm (CartanMatrix.E_isSymm 7) (e7Coroot i) (e7Coroot j)]
  exact (reflect_vecMul_dotProduct_self (CartanMatrix.E_isSymm 7) (hnorm i) (e7Coroot j)).trans
    (hnorm j)

/-! ## The pinned datum -/

/-- The pinned simply connected root datum of type `E₇`.

Both lattices are `Fin 7 → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Root indices `0` through `6` are the Bourbaki
simple roots; see `TauCeti.DynkinType.root_e7SimpleIndex`. -/
noncomputable def e7SimplyConnectedRootDatum : RootDatum (Fin 126) (Fin 7 → ℤ) (Fin 7 → ℤ) :=
  RootPairing.mk' (dotProductEquiv ℤ (Fin 7)).toLinearMap e7Root e7Coroot
    e7Root_dotProduct_coroot
    (by
      rintro i _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := exists_e7Coroot_reflection i j
      refine ⟨k, ?_⟩
      have hroot : e7Root k =
          e7Root j - (e7Root i ⬝ᵥ e7Coroot j) • e7Root i := by
        simpa only [sub_vecMul, smul_vecMul, ← e7Root_apply] using
          congrArg (fun x : Fin 7 → ℤ ↦ x ᵥ* CartanMatrix.E 7) hk
      rw [e7Root_dotProduct_e7Coroot_comm] at hroot
      simpa [Module.preReflection_apply, dotProductEquiv_apply_apply] using hroot)
    (by
      rintro i _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := exists_e7Coroot_reflection i j
      refine ⟨k, ?_⟩
      simpa [Module.preReflection_apply, dotProductEquiv_apply_apply] using hk)

/-- The root embedding of the pinned `E₇` datum is the explicit table `e7Root`. -/
@[simp] lemma e7SimplyConnectedRootDatum_root : e7SimplyConnectedRootDatum.root = e7Root := (rfl)

/-- The coroot embedding of the pinned `E₇` datum is the explicit table `e7Coroot`. -/
@[simp] lemma e7SimplyConnectedRootDatum_coroot :
    e7SimplyConnectedRootDatum.coroot = e7Coroot := (rfl)

/-- The perfect pairing is the dot product in the dual coordinate bases. -/
@[simp] lemma e7SimplyConnectedRootDatum_toLinearMap_apply (x y : Fin 7 → ℤ) :
    e7SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y := (rfl)

/-- Pairing a pinned `E₇` root with a coroot computes as their coordinate dot product. -/
@[simp] lemma e7SimplyConnectedRootDatum_pairing (i j : Fin 126) :
    e7SimplyConnectedRootDatum.pairing i j = e7Root i ⬝ᵥ e7Coroot j := (rfl)

/-! ## The pinned base -/

/-- The coroots of the pinned type `E₇` datum span the cocharacter lattice. This is the simply
connected lattice condition required by the pinned Chevalley--Demazure construction. -/
theorem corootSpan_e7SimplyConnectedRootDatum_eq_top :
    e7SimplyConnectedRootDatum.corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single coroot_e7SimpleIndex

/-- The support of the pinned base of type `E₇`: the first seven root indices. -/
private abbrev e7SimpleSupport : Finset (Fin 126) := simpleSupport e7SimpleIndex_injective

private lemma e7Coroot_nonneg_or_nonpos (j : Fin 126) :
    (∀ k, 0 ≤ e7Coroot j k) ∨ (∀ k, e7Coroot j k ≤ 0) := by
  induction j using Fin.addCases (m := 63) (n := 63) with
  | left j =>
    exact Or.inl (e7Coroot_nonneg j)
  | right j =>
    refine Or.inr fun k ↦ ?_
    rw [Fin.natAdd_eq_addNat, e7Coroot_addNat, Pi.neg_apply, neg_nonpos]
    exact e7Coroot_nonneg j k

private lemma sum_smul_coroot_e7SimpleIndex (j : Fin 126) :
    ∑ k : Fin 7, e7Coroot j k • e7Coroot (e7SimpleIndex k) = e7Coroot j := by
  simpa only [coroot_e7SimpleIndex] using (pi_eq_sum_univ' (e7Coroot j)).symm

private lemma sum_smul_root_e7SimpleIndex (j : Fin 126) :
    ∑ k : Fin 7, e7Coroot j k • e7Root (e7SimpleIndex k) = e7Root j := by
  have h := congrArg (CartanMatrix.E 7).mulVecLin (sum_smul_coroot_e7SimpleIndex j)
  rw [map_sum] at h
  simpa only [map_zsmul, mulVecLin_apply, ← e7Root_eq_mulVec] using h

private lemma linearIndependent_root_e7SimpleIndex :
    LinearIndependent ℤ fun i : Fin 7 ↦ e7Root (e7SimpleIndex i) := by
  simpa only [root_e7SimpleIndex] using
    linearIndependent_rows_of_det_ne_zero (A := CartanMatrix.E 7)
      (by rw [CartanMatrix.E₇_det]; norm_num)

private lemma linearIndependent_coroot_e7SimpleIndex :
    LinearIndependent ℤ fun i : Fin 7 ↦ e7Coroot (e7SimpleIndex i) := by
  simpa only [coroot_e7SimpleIndex] using Pi.linearIndependent_single_one (Fin 7) ℤ

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `E₇`. Its support
is the first seven root indices, carrying the simple roots in Bourbaki order. -/
noncomputable def e7SimplyConnectedBase : e7SimplyConnectedRootDatum.Base where
  support := e7SimpleSupport
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ linearIndependent_root_e7SimpleIndex
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ linearIndependent_coroot_e7SimpleIndex
  root_mem_or_neg_mem k := by
    simp only [e7SimplyConnectedRootDatum_root]
    rw [image_simpleSupport, ← sum_smul_root_e7SimpleIndex k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e7Coroot_nonneg_or_nonpos k)
  coroot_mem_or_neg_mem k := by
    simp only [e7SimplyConnectedRootDatum_coroot]
    rw [image_simpleSupport, ← sum_smul_coroot_e7SimpleIndex k]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e7Coroot_nonneg_or_nonpos k)

private lemma e7SimplyConnectedBase_support :
    e7SimplyConnectedBase.support = simpleSupport e7SimpleIndex_injective := (rfl)

/-- Membership in the pinned base support is exactly membership among the first seven root
indices. -/
@[simp] theorem mem_support_e7SimplyConnectedBase {k : Fin 126} :
    k ∈ e7SimplyConnectedBase.support ↔ (k : ℕ) < 7 := by
  rw [e7SimplyConnectedBase_support]
  exact mem_simpleSupport_iff_lt e7SimpleIndex_injective e7SimpleIndex_val

/-- The Cartan integers at the first seven root indices are Mathlib's Bourbaki-numbered `E₇`
matrix. -/
theorem pairing_e7SimpleIndex (i j : Fin 7) :
    e7SimplyConnectedRootDatum.pairing (e7SimpleIndex i) (e7SimpleIndex j) =
      CartanMatrix.E 7 i j := by
  rw [e7SimplyConnectedRootDatum_pairing, root_e7SimpleIndex, coroot_e7SimpleIndex,
    dotProduct_single, mul_one]

/-- The pinned datum of type `E₇` has Cartan type `E7`, in Bourbaki node order. -/
theorem hasCartanType_e7SimplyConnectedRootDatum :
    HasCartanType e7SimplyConnectedRootDatum e7SimplyConnectedBase E7 :=
  hasCartanType_of_pairing_eq e7SimpleIndex_injective rfl fun i j ↦
    (pairing_e7SimpleIndex i j).trans (by simp)

end DynkinType

end TauCeti
