/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight

import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior powers of the standard general-linear module

The infinitesimal exterior-power action restricts along the matrix-to-endomorphism equivalence to
an action of a general linear Lie algebra. Over a nontrivial ring, for `d ≤ n`, the wedge of the
first `d` standard basis vectors in `Kⁿ` is a highest-weight vector for this action.

## Main definitions

* `exteriorPower.glLieMap`: the action of matrices on an exterior power.
* `exteriorPower.firstBasisWedge`: the wedge of the first standard basis vectors.
* `exteriorPower.fundamentalWeight`: the first-`d` coordinate-indicator weight.

## Main result

* `exteriorPower.isGlHighestWeightVector_firstBasisWedge`: over a nontrivial ring, the first basis
  wedge is a highest-weight vector when `d ≤ n`.

## Roadmap context

The [highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
uses these exterior modules in two places: Layer 9 constructs the fundamental `gl_n` modules,
while Layer 8 uses the `sl₉` action on `⋀³(K⁹)` in the Vinberg model of `E₈`.
-/

public section

open scoped Matrix

namespace exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

section Action

variable {K : Type*} [CommRing K]

/-- The natural matrix action on an exterior power of the standard module. -/
noncomputable def glLieMap (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    Matrix n n K →ₗ⁅K⁆ Module.End K (⋀[K]^d (n → K)) :=
  (lieMap d).comp (lieEquivMatrix' (R := K) (n := n)).symm

/-- A matrix acts on a decomposable wedge by acting on one factor at a time. -/
@[simp]
theorem glLieMap_apply_ιMulti (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (v : Fin d → (n → K)) :
    glLieMap d A (ιMulti K d v) =
      ∑ i : Fin d, ιMulti K d (Function.update v i (A *ᵥ v i)) := by
  rw [glLieMap, LieHom.comp_apply]
  have hmatrix :
      (lieEquivMatrix' (R := K) (n := n)).symm.toLieHom A = Matrix.toLin' A :=
    lieEquivMatrix'_symm_apply A
  rw [hmatrix, lieMap_apply_ιMulti]
  simp only [Matrix.toLin'_apply]

/-- The Lie-ring module structure on an exterior power induced by the standard matrix action. -/
noncomputable scoped instance glLieRingModule (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    LieRingModule (Matrix n n K) (⋀[K]^d (n → K)) :=
  LieRingModule.compLieHom _ (glLieMap d)

/-- The Lie-module structure on an exterior power induced by the standard matrix action. -/
noncomputable scoped instance glLieModule (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    LieModule K (Matrix n n K) (⋀[K]^d (n → K)) :=
  LieModule.compLieHom _ (glLieMap d)

/-- The scoped Lie action is the action represented by `glLieMap`. -/
@[simp]
theorem gl_lie_def (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (x : ⋀[K]^d (n → K)) :
    letI : LieRingModule (Matrix n n K) (⋀[K]^d (n → K)) :=
      glLieRingModule (K := K) (n := n) d
    ⁅A, x⁆ = glLieMap d A x := by
  rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]

/-- The subset of the first `d` coordinates in `Fin n`. -/
private noncomputable def firstBasisSet (d n : ℕ) (h : d ≤ n) : Set.powersetCard (Fin n) d :=
  Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb h)

/-- The wedge of the first `d` standard basis vectors of `K^n`. -/
noncomputable def firstBasisWedge (d n : ℕ) (h : d ≤ n) : ⋀[K]^d (Fin n → K) :=
  ιMulti_family K d (Pi.basisFun K (Fin n)) (firstBasisSet d n h)

/-- The first basis wedge written as an exterior product of standard basis vectors. -/
@[simp]
theorem firstBasisWedge_eq_ιMulti (d n : ℕ) (h : d ≤ n) :
    firstBasisWedge (K := K) d n h =
      ιMulti K d (fun i => Pi.single (Fin.castLE h i) 1) := by
  simp only [firstBasisWedge, ιMulti_family, firstBasisSet, Equiv.symm_apply_apply]
  apply congrArg (ιMulti K d)
  funext i x
  simp [Pi.basisFun_apply, Pi.single_apply]

end Action

section Weight

variable {K : Type*} [Zero K] [One K]

/-- The tuple that is `1` on the first `d` coordinates and `0` afterward. When `d ≤ n`, this is
the weight of the first basis wedge in the `d`-th exterior power of the standard `gl_n` module. -/
def fundamentalWeight (d n : ℕ) : Fin n → K :=
  fun j => if j.val < d then 1 else 0

/-- The fundamental exterior weight is `1` on the first `d` coordinates and `0` afterward. -/
@[simp]
theorem fundamentalWeight_apply (d n : ℕ) (j : Fin n) :
    fundamentalWeight (K := K) d n j = if j.val < d then 1 else 0 := by
  rw [fundamentalWeight]

end Weight

section HighestWeight

variable {K : Type*} [CommRing K]

/-- The fundamental exterior weight is dominant integral in characteristic zero. -/
theorem isGlDominantIntegral_fundamentalWeight [CharZero K] (d n : ℕ) :
    TauCeti.IsGlDominantIntegral (fundamentalWeight (K := K) d n) := by
  rw [TauCeti.isGlDominantIntegral_iff]
  intro i j hij
  by_cases hi : i.val < d
  · by_cases hj : j.val < d
    · exact ⟨0, by simp [hi, hj]⟩
    · exact ⟨1, by simp [hi, hj]⟩
  · have hj : ¬j.val < d := by omega
    exact ⟨0, by simp [hi, hj]⟩

/-- The first basis wedge is nonzero. -/
theorem firstBasisWedge_ne_zero [Nontrivial K] (d n : ℕ) (h : d ≤ n) :
    firstBasisWedge (K := K) d n h ≠ 0 := by
  rw [firstBasisWedge]
  exact (ιMulti_family_linearIndependent_ofBasis K d (Pi.basisFun K (Fin n))).ne_zero
    (firstBasisSet d n h)

private theorem single_mulVec_firstBasis (d n : ℕ) (h : d ≤ n) (i j : Fin n) (k : Fin d) :
    Matrix.single i j 1 *ᵥ (Pi.single (Fin.castLE h k) 1 : Fin n → K) =
      if j = Fin.castLE h k then Pi.single i 1 else 0 := by
  rw [Matrix.single_mulVec_eq]
  by_cases hjk : j = Fin.castLE h k
  · subst j
    simp
  · simp [hjk]

private theorem lie_single_self_firstBasisWedge (d n : ℕ) (h : d ≤ n) (k : Fin n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    ⁅Matrix.single k k (1 : K), firstBasisWedge (K := K) d n h⁆ =
      fundamentalWeight (K := K) d n k • firstBasisWedge (K := K) d n h := by
  classical
  rw [firstBasisWedge_eq_ιMulti, gl_lie_def, glLieMap_apply_ιMulti]
  simp_rw [single_mulVec_firstBasis d n h]
  by_cases hk : k.val < d
  · let a : Fin d := ⟨k.val, hk⟩
    have hka : k = Fin.castLE h a := Fin.ext rfl
    simp only [fundamentalWeight_apply, hk, ite_true, one_smul]
    rw [Finset.sum_eq_single a]
    · simp only [hka, ite_true]
      simp
    · intro b _ hba
      have hkb : k ≠ Fin.castLE h b := by
        intro hkb
        exact hba (Fin.castLE_injective h (hkb.symm.trans hka))
      simp only [hkb, ite_false]
      exact (ιMulti K d).map_update_zero _ _
    · simp
  · simp only [fundamentalWeight_apply, hk, ite_false, zero_smul]
    apply Finset.sum_eq_zero
    intro a _
    have hka : k ≠ Fin.castLE h a := by
      intro hka
      apply hk
      rw [hka]
      exact a.isLt
    simp only [hka, ite_false]
    exact (ιMulti K d).map_update_zero _ _

private theorem lie_single_firstBasisWedge_of_lt (d n : ℕ) (h : d ≤ n)
    {i j : Fin n} (hij : i < j) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    ⁅Matrix.single i j (1 : K), firstBasisWedge (K := K) d n h⁆ = 0 := by
  classical
  rw [firstBasisWedge_eq_ιMulti, gl_lie_def, glLieMap_apply_ιMulti]
  simp_rw [single_mulVec_firstBasis d n h]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hjk : j = Fin.castLE h k
  · simp only [hjk, ite_true]
    have hjd : j.val < d := by
      rw [hjk]
      exact k.isLt
    have hi : i.val < d := lt_trans hij hjd
    let l : Fin d := ⟨i.val, hi⟩
    have hil : i = Fin.castLE h l := Fin.ext rfl
    have hlk : l ≠ k := by
      intro hlk
      apply hij.ne
      rw [hil, hjk, hlk]
    refine (ιMulti K d).map_eq_zero_of_eq
      (Function.update
        (fun a : Fin d => (Pi.single (Fin.castLE h a) (1 : K) : Fin n → K)) k
        (Pi.single i 1))
      (i := l) (j := k) ?_ hlk
    rw [Function.update_of_ne hlk]
    rw [hil]
    rw [Function.update_self]
  · simp only [hjk, ite_false]
    exact (ιMulti K d).map_update_zero _ _

/-- Over a nontrivial ring, the first basis wedge is a highest-weight vector for the exterior-power
action when `d ≤ n`. -/
theorem isGlHighestWeightVector_firstBasisWedge [Nontrivial K] (d n : ℕ) (h : d ≤ n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    TauCeti.IsGlHighestWeightVector (fundamentalWeight (K := K) d n)
      (firstBasisWedge (K := K) d n h) := by
  refine TauCeti.isGlHighestWeightVector_iff.mpr
    ⟨firstBasisWedge_ne_zero (K := K) d n h, fun i => ?_, fun i j hij => ?_⟩
  · exact lie_single_self_firstBasisWedge (K := K) d n h i
  · exact lie_single_firstBasisWedge_of_lt (K := K) d n h hij

end HighestWeight

end exteriorPower
