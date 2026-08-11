/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Reflection

public section

/-!
# The pinned simply connected root datum of type E7

This file turns the explicit table of 126 integral `E7` roots into a `RootDatum`. Both lattices
are `Fin 7 → ℤ`: roots use the fundamental-weight basis and coroots use the simple-coroot basis,
paired by the dot product. The first seven root indices are the Bourbaki simple roots.

The reflection on indices is recovered from the explicit root table after verifying that every
coordinate reflection lands back in that table. The resulting datum carries its Bourbaki-numbered
base, realizes `CartanMatrix.E₇`, and has coroots spanning the cocharacter lattice. These are the
type `E7` acceptance requirements in Layer 6 of the root-systems roadmap.

The coordinates and numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VI.
-/

namespace TauCeti

open Function Set
open _root_.Matrix

namespace DynkinType

/-! ## The simple indices -/

/-- The first seven entries in the `E7` root table, in Bourbaki order. -/
def e7SimpleIndex (i : Fin 7) : Fin 126 :=
  Fin.castAdd 119 i

@[simp] theorem e7SimpleIndex_val (i : Fin 7) : (e7SimpleIndex i : ℕ) = i :=
  (rfl)

theorem e7SimpleIndex_injective : Injective e7SimpleIndex :=
  fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)

/-! ## The pinned datum -/

/-- Reflection in an `E7` root as a permutation of the pinned root indices. -/
private def e7ReflectionPerm (i : Fin 126) : Fin 126 ≃ Fin 126 :=
  Function.Involutive.toPerm (e7ReflectionIndex i) (e7ReflectionIndex_involutive i)

/-- The pinned simply connected root datum of type `E7`.

The character lattice uses the fundamental-weight basis, the cocharacter lattice uses the
simple-coroot basis, and root indices `0` through `6` are the Bourbaki simple roots. -/
def e7SimplyConnectedRootDatum : RootDatum (Fin 126) (Fin 7 → ℤ) (Fin 7 → ℤ) where
  toLinearMap := (dotProductEquiv ℤ (Fin 7)).toLinearMap
  root := e7Root
  coroot := e7Coroot
  root_coroot_two := e7Root_dotProduct_coroot
  reflectionPerm := e7ReflectionPerm
  reflectionPerm_root := e7ReflectionIndex_root
  reflectionPerm_coroot := e7ReflectionIndex_coroot

/-- The root embedding of the pinned `E7` datum is the explicit root table. -/
@[simp] theorem e7SimplyConnectedRootDatum_root : e7SimplyConnectedRootDatum.root = e7Root :=
  (rfl)

/-- The coroot embedding of the pinned `E7` datum is the explicit coroot table. -/
@[simp] theorem e7SimplyConnectedRootDatum_coroot : e7SimplyConnectedRootDatum.coroot = e7Coroot :=
  (rfl)

/-- The perfect pairing of the pinned `E7` datum is the dot product. -/
@[simp] theorem e7SimplyConnectedRootDatum_toLinearMap (x y : Fin 7 → ℤ) :
    e7SimplyConnectedRootDatum.toLinearMap x y = x ⬝ᵥ y :=
  (rfl)

/-- Pairing a pinned `E7` root and coroot computes as their coordinate dot product. -/
@[simp] theorem e7SimplyConnectedRootDatum_pairing (i j : Fin 126) :
    e7SimplyConnectedRootDatum.pairing i j = e7Root i ⬝ᵥ e7Coroot j :=
  (rfl)

/-! ## The Bourbaki-numbered base -/

private lemma sum_smul_e7Coroot_simple (i : Fin 126) :
    ∑ k, e7Coroot i k • e7Coroot (e7SimpleIndex k) = e7Coroot i := by
  ext j
  simp only [e7SimpleIndex, e7Coroot_simple, Finset.sum_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

private lemma sum_smul_e7Root_simple (i : Fin 126) :
    ∑ k, e7Coroot i k • e7Root (e7SimpleIndex k) = e7Root i := by
  ext j
  simp only [e7SimpleIndex, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [e7Root_simple]
  rw [e7Root_apply]
  rfl

private lemma e7Coroot_nonneg_or_nonpos (i : Fin 126) :
    (∀ j, 0 ≤ e7Coroot i j) ∨ (∀ j, e7Coroot i j ≤ 0) := by
  rcases lt_or_ge (i : ℕ) 63 with hi | hi
  · left
    intro j
    have hindex : i = Fin.castAdd 63 (⟨i, hi⟩ : Fin 63) := Fin.ext rfl
    rw [hindex]
    exact e7Coroot_nonneg _ _
  · right
    intro j
    let k : Fin 63 := ⟨(i : ℕ) - 63, by omega⟩
    have hindex : i = Fin.addNat k 63 := Fin.ext (by simp [k]; omega)
    rw [hindex, e7Coroot_addNat, Pi.neg_apply]
    exact neg_nonpos.mpr (e7Coroot_nonneg k j)

private lemma image_e7Root_simpleSupport :
    e7SimplyConnectedRootDatum.root ''
        (simpleSupport e7SimpleIndex_injective : Set (Fin 126)) =
      range (fun i => e7SimplyConnectedRootDatum.root (e7SimpleIndex i)) :=
  image_simpleSupport _ _

private lemma image_e7Coroot_simpleSupport :
    e7SimplyConnectedRootDatum.coroot ''
        (simpleSupport e7SimpleIndex_injective : Set (Fin 126)) =
      range (fun i => e7SimplyConnectedRootDatum.coroot (e7SimpleIndex i)) :=
  image_simpleSupport _ _

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `E7`. Its support
is the set of the first seven root indices. -/
def e7SimplyConnectedBase : e7SimplyConnectedRootDatum.Base where
  support := simpleSupport e7SimpleIndex_injective
  linearIndepOn_root := by
    apply linearIndepOn_simpleSupport _ _
    have h : (fun i : Fin 7 => e7Root (e7SimpleIndex i)) = fun i => CartanMatrix.E₇ i := by
      funext i
      exact e7Root_simple i
    rw [show e7SimplyConnectedRootDatum.root ∘ e7SimpleIndex =
      fun i => e7Root (e7SimpleIndex i) from rfl, h]
    exact Matrix.linearIndependent_rows_of_det_ne_zero (by rw [CartanMatrix.E₇_det]; norm_num)
  linearIndepOn_coroot := by
    apply linearIndepOn_simpleSupport _ _
    have h : e7SimplyConnectedRootDatum.coroot ∘ e7SimpleIndex =
        fun i : Fin 7 => (Pi.basisFun ℤ (Fin 7)) i := by
      funext i
      rw [Function.comp_apply, e7SimplyConnectedRootDatum_coroot]
      change e7Coroot (Fin.castAdd 119 i) = _
      rw [e7Coroot_simple]
      simp
    rw [h]
    exact (Pi.basisFun ℤ (Fin 7)).linearIndependent
  root_mem_or_neg_mem i := by
    rw [image_e7Root_simpleSupport, e7SimplyConnectedRootDatum_root,
      ← sum_smul_e7Root_simple i]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e7Coroot_nonneg_or_nonpos i)
  coroot_mem_or_neg_mem i := by
    rw [image_e7Coroot_simpleSupport, e7SimplyConnectedRootDatum_coroot,
      ← sum_smul_e7Coroot_simple i]
    exact sum_smul_mem_or_neg_mem_closure _ _ (e7Coroot_nonneg_or_nonpos i)

/-- Membership in the pinned `E7` base support is membership among the first seven root indices. -/
@[simp] theorem mem_e7SimplyConnectedBase_support {i : Fin 126} :
    i ∈ e7SimplyConnectedBase.support ↔ (i : ℕ) < 7 := by
  rw [show e7SimplyConnectedBase.support = simpleSupport e7SimpleIndex_injective from rfl,
    mem_simpleSupport]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i, hi⟩, Fin.ext rfl⟩

/-- The simple pairings of the pinned `E7` datum are the entries of `CartanMatrix.E₇`. -/
theorem pairing_e7SimpleIndex (i j : Fin 7) :
    e7SimplyConnectedRootDatum.pairing (e7SimpleIndex i) (e7SimpleIndex j) =
      CartanMatrix.E₇ i j := by
  rw [e7SimplyConnectedRootDatum_pairing]
  change e7Root (Fin.castAdd 119 i) ⬝ᵥ e7Coroot (Fin.castAdd 119 j) = _
  rw [e7Root_simple, e7Coroot_simple, dotProduct_single, mul_one]
  rfl

/-- The pinned datum of type `E7` has Cartan type `E7` in the Bourbaki node order. -/
theorem hasCartanType_e7SimplyConnectedRootDatum :
    HasCartanType e7SimplyConnectedRootDatum e7SimplyConnectedBase E7 :=
  hasCartanType_of_pairing_eq e7SimpleIndex_injective rfl fun i j =>
    (pairing_e7SimpleIndex i j).trans (by simp)

/-- The coroots of the pinned type `E7` datum span the cocharacter lattice. This is the simply
connected lattice condition. The analogous root-span statement is false: the root lattice has
index two in the weight lattice. -/
theorem corootSpan_e7SimplyConnectedRootDatum_eq_top :
    e7SimplyConnectedRootDatum.corootSpan ℤ = ⊤ :=
  corootSpan_eq_top_of_coroot_eq_single fun i => by
    rw [e7SimplyConnectedRootDatum_coroot, e7Coroot_simple]

end DynkinType

end TauCeti
