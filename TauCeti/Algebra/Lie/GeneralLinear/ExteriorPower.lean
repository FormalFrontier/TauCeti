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
an action of a general linear Lie algebra. A matrix unit acts on the wedge of the standard basis
vectors indexed by a finite set `S` of coordinates in a way read off from `S`: the diagonal unit
`Eᵢᵢ` scales it by one or by zero according as `i` lies in `S`, and `Eᵢⱼ` with `i ≠ j` annihilates
it whenever `S` contains `i` as soon as it contains `j`. Over a nontrivial ring, for `d ≤ n`, this
makes the wedge of the first `d` standard basis vectors in `Kⁿ` a highest-weight vector.

## Main definitions

* `exteriorPower.glLieMap`: the action of matrices on an exterior power.
* `exteriorPower.basisWedge`: the wedge of the standard basis vectors indexed by a finite set of
  coordinates.
* `exteriorPower.firstBasisWedge`: the wedge of the first standard basis vectors.
* `exteriorPower.fundamentalWeight`: the first-`d` coordinate-indicator weight.

## Main results

* `exteriorPower.lie_single_self_basisWedge` and
  `exteriorPower.lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem`: how a matrix unit acts on the
  wedge of a set of standard basis vectors.
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
theorem gl_lie_def (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n]
    (A : Matrix n n K) (x : ⋀[K]^d (n → K)) :
    letI : LieRingModule (Matrix n n K) (⋀[K]^d (n → K)) :=
      glLieRingModule (K := K) (n := n) d
    ⁅A, x⁆ = glLieMap d A x := by
  rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]

section BasisWedge

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n] {N : ℕ}

variable (K) in
/-- The wedge of the standard basis vectors of `n → K` indexed by a finite set `S` of coordinates,
an element of the exterior power of degree the size of `S`. The factors are wedged together in the
order `S` inherits from `n`. -/
noncomputable def basisWedge (S : Finset n) (h : S.card = N) : ⋀[K]^N (n → K) :=
  ιMulti_family K N (Pi.basisFun K n) ⟨S, h⟩

omit [DecidableEq n] in
/-- The wedge of a set of basis vectors is the member of the standard basis of the exterior power
that the set indexes. -/
theorem basisWedge_eq_ιMulti_family (S : Finset n) (h : S.card = N) :
    basisWedge K S h = ιMulti_family K N (Pi.basisFun K n) ⟨S, h⟩ := by
  rw [basisWedge]

/-- The wedge of a set of basis vectors, written as an exterior product. -/
theorem basisWedge_eq_ιMulti (S : Finset n) (h : S.card = N) :
    basisWedge K S h = ιMulti K N fun k => Pi.single (S.orderEmbOfFin h k) 1 := by
  rw [basisWedge_eq_ιMulti_family, ιMulti_family]
  refine congrArg (ιMulti K N) (funext fun k => ?_)
  simp [Pi.basisFun_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]

omit [DecidableEq n] in
/-- The wedge of a set of basis vectors is nonzero. -/
theorem basisWedge_ne_zero [Nontrivial K] (S : Finset n) (h : S.card = N) :
    basisWedge K S h ≠ 0 := by
  rw [basisWedge_eq_ιMulti_family]
  exact (ιMulti_family_linearIndependent_ofBasis K N (Pi.basisFun K n)).ne_zero _

/-- The diagonal matrix unit `Eᵢᵢ` fixes the factors of a wedge of standard basis vectors that lie
in direction `i` and kills the others, so it scales the wedge by one when `i` is one of its indices
and annihilates it otherwise. -/
@[simp]
theorem lie_single_self_basisWedge (S : Finset n) (h : S.card = N) (i : n) :
    ⁅Matrix.single i i (1 : K), basisWedge K S h⁆ =
      (if i ∈ S then (1 : K) else 0) • basisWedge K S h := by
  rw [basisWedge_eq_ιMulti, gl_lie_def, glLieMap_apply_ιMulti]
  simp only [Matrix.single_mulVec_eq, Pi.single_apply, one_mul, ite_smul, one_smul, zero_smul,
    eq_comm]
  by_cases hiS : i ∈ S
  · obtain ⟨k₀, hk₀⟩ := (S.range_orderEmbOfFin h).ge (Finset.mem_coe.2 hiS)
    rw [ite_eq_left hiS, Finset.sum_eq_single k₀]
    · rw [ite_eq_left hk₀.symm, ← hk₀]
      exact (congrArg (ιMulti K N) (Function.update_eq_self k₀ _)).symm
    · intro k _ hk
      have hik : ¬i = S.orderEmbOfFin h k := fun hik =>
        hk ((S.orderEmbOfFin h).injective (hk₀.trans hik)).symm
      rw [ite_eq_right hik]
      exact (ιMulti K N).map_update_zero _ _
    · exact fun hk => absurd (Finset.mem_univ k₀) hk
  · rw [ite_eq_right hiS]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    have hik : ¬i = S.orderEmbOfFin h k := by
      intro hik
      exact hiS (by rw [hik]; exact Finset.orderEmbOfFin_mem S h k)
    rw [ite_eq_right hik]
    exact (ιMulti K N).map_update_zero _ _

/-- A matrix unit `Eᵢⱼ` with `i ≠ j` annihilates the wedge of the standard basis vectors indexed by
`S`, as soon as `S` contains `i` whenever it contains `j`: the `j`-th factor is carried to a factor
already present, so every summand of the Leibniz expansion has a repeated factor. -/
theorem lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem (S : Finset n) (h : S.card = N)
    {i j : n} (hij : i ≠ j) (hS : j ∈ S → i ∈ S) :
    ⁅Matrix.single i j (1 : K), basisWedge K S h⁆ = 0 := by
  rw [basisWedge_eq_ιMulti, gl_lie_def, glLieMap_apply_ιMulti]
  simp only [Matrix.single_mulVec_eq, Pi.single_apply, one_mul, ite_smul, one_smul, zero_smul,
    eq_comm]
  refine (Finset.sum_eq_zero fun k _ => ?_).symm
  by_cases hjk : j = S.orderEmbOfFin h k
  · have hjS : j ∈ S := by rw [hjk]; exact Finset.orderEmbOfFin_mem S h k
    obtain ⟨l, hl⟩ := (S.range_orderEmbOfFin h).ge (Finset.mem_coe.2 (hS hjS))
    have hlk : l ≠ k := by
      rintro rfl
      exact hij (hl.symm.trans hjk.symm)
    rw [ite_eq_left hjk]
    refine (ιMulti K N).map_eq_zero_of_eq _ (i := l) (j := k) ?_ hlk
    rw [Function.update_of_ne hlk, Function.update_self, hl]
  · rw [ite_eq_right hjk]
    exact (ιMulti K N).map_update_zero _ _

end BasisWedge

/-- The subset of the first `d` coordinates in `Fin n`. -/
private noncomputable def firstBasisSet (d n : ℕ) (h : d ≤ n) : Set.powersetCard (Fin n) d :=
  Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb h)

private theorem mem_firstBasisSet (d n : ℕ) (h : d ≤ n) (k : Fin n) :
    k ∈ (firstBasisSet d n h : Finset (Fin n)) ↔ (k : ℕ) < d := by
  rw [Set.powersetCard.mem_coe_iff, firstBasisSet,
    Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  simp [Fin.castLEOrderEmb, Fin.range_castLE]

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

/-- The first basis wedge is the wedge of the basis vectors indexed by the first `d` coordinates. -/
private theorem firstBasisWedge_eq_basisWedge (d n : ℕ) (h : d ≤ n) :
    firstBasisWedge (K := K) d n h =
      basisWedge K (firstBasisSet d n h : Finset (Fin n))
        (Set.powersetCard.card_eq (firstBasisSet d n h)) :=
  rfl

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
  rw [firstBasisWedge_eq_basisWedge]
  exact basisWedge_ne_zero _ _

/-- Over a nontrivial ring, the first basis wedge is a highest-weight vector for the exterior-power
action when `d ≤ n`. -/
theorem isGlHighestWeightVector_firstBasisWedge [Nontrivial K] (d n : ℕ) (h : d ≤ n) :
    letI : LieRingModule (Matrix (Fin n) (Fin n) K) (⋀[K]^d (Fin n → K)) :=
      glLieRingModule (K := K) (n := Fin n) d
    TauCeti.IsGlHighestWeightVector (fundamentalWeight (K := K) d n)
      (firstBasisWedge (K := K) d n h) := by
  rw [firstBasisWedge_eq_basisWedge]
  refine TauCeti.isGlHighestWeightVector_iff.mpr
    ⟨basisWedge_ne_zero _ _, fun i => ?_, fun i j hij => ?_⟩
  · rw [lie_single_self_basisWedge, fundamentalWeight_apply]
    simp only [mem_firstBasisSet]
  · exact lie_single_basisWedge_eq_zero_of_ne_of_mem_imp_mem _ _ hij.ne fun hj =>
      (mem_firstBasisSet d n h i).2
        ((Fin.lt_def.1 hij).trans ((mem_firstBasisSet d n h j).1 hj))

end HighestWeight

end exteriorPower
