/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.FieldPoints

/-!
# Maximality of the type A weight torus on field-valued points

Over an infinite field, the standard carrier's weight-torus points are precisely the
determinant-one diagonal matrices and form a maximal commutative subgroup of the carrier points.
The proof first uses the distinct standard weights to compute the centralizer of the weight torus,
then identifies its image by an explicit partial-product inverse to the weight parametrization.

## Main declarations

* `TauCeti.SlStd.weight_injective`: the weights of the standard representation are distinct.
* `TauCeti.SlStd.centralizer_range_weightTorusPoints`: the centralizer of the weight torus is the
  determinant-one diagonal subgroup.
* `TauCeti.SlStd.range_weightTorusPoints_eq_diagonalPoints`: the weight torus consists of all
  determinant-one diagonal carrier points.
* `TauCeti.SlStd.eq_range_weightTorusPoints_of_le_of_isMulCommutative`: the weight torus is maximal
  among commutative subgroups of the carrier points.

This advances the "Pinnings" target in Layer 9 of the ReductiveGroups roadmap. Its consumer is
milestone L0, "pinned ambient groups", of the CFSGStatement roadmap.
-/

public section

namespace TauCeti.SlStd

universe u

noncomputable section

variable (r : ℕ)

/-! ## The standard weights -/

/-- The weights of the standard representation of `sl_{r+1}` are pairwise distinct. -/
theorem weight_injective : Function.Injective (weight r) := by
  intro k l hkl
  by_contra hne
  have aux {a b : Fin (r + 1)} (hab : (a : ℕ) < b)
      (hweight : weight r a = weight r b) : False := by
    have ha : (a : ℕ) < r := by omega
    let i : Fin r := ⟨a, ha⟩
    have hvalue := congrFun hweight i
    simp only [weight_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hvalue
    dsimp only [i] at hvalue
    split_ifs at hvalue <;> omega
  have hval : (k : ℕ) ≠ l := fun h ↦ hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact aux hlt hkl
  · exact aux hgt hkl.symm

/-- The standard weight at coordinate `k` evaluates as the quotient of two adjacent partial
products. Missing factors at the two ends are interpreted as one. -/
private theorem torusCharacter_weight (K : Type u) [CommRing K]
    (s : Fin r → Kˣ) (k : Fin (r + 1)) :
    torusCharacter s (weight r k) =
      (if hk : (k : ℕ) < r then s ⟨k, hk⟩ else 1) *
        (if hk : 0 < (k : ℕ) then (s ⟨k - 1, by omega⟩)⁻¹ else 1) := by
  classical
  rw [torusCharacter_def]
  simp only [weight_def, zpow_sub, Finset.prod_mul_distrib]
  congr 1
  · have hfactor : ∀ i : Fin r,
        s i ^ (if k = i.castSucc then (1 : ℤ) else 0) =
          if k = i.castSucc then s i else 1 := by
      intro i
      split_ifs <;> simp
    rw [Finset.prod_congr rfl fun i _ ↦ hfactor i]
    split_ifs with hk
    · let c : Fin r := ⟨k, hk⟩
      have hkc : k = c.castSucc := Fin.ext (by simp [c])
      rw [Finset.prod_eq_single c]
      · simp only [hkc, ↓reduceIte]
        congr 1
      · intro j _ hj
        split_ifs with h
        · exact (hj (Fin.castSucc_inj.mp (hkc.symm.trans h)).symm).elim
        · rfl
      · exact fun h ↦ absurd (Finset.mem_univ c) h
    · have : ∀ i : Fin r, k ≠ i.castSucc := by
        intro i hi
        apply hk
        have hv := congrArg Fin.val hi
        rw [Fin.val_castSucc] at hv
        rw [hv]
        exact i.isLt
      simp [this]
  · have hfactor : ∀ i : Fin r,
        (s i ^ (if k = i.succ then (1 : ℤ) else 0))⁻¹ =
          if k = i.succ then (s i)⁻¹ else 1 := by
      intro i
      split_ifs <;> simp
    rw [Finset.prod_congr rfl fun i _ ↦ hfactor i]
    split_ifs with hk
    · have hi : (k - 1 : ℕ) < r := by omega
      let c : Fin r := ⟨k - 1, hi⟩
      have hkc : k = c.succ := Fin.ext (by simp [c]; omega)
      rw [Finset.prod_eq_single c]
      · simp only [hkc, ↓reduceIte]
        congr 1
      · intro j _ hj
        split_ifs with h
        · exact (hj (Fin.succ_inj.mp (hkc.symm.trans h)).symm).elim
        · rfl
      · exact fun h ↦ absurd (Finset.mem_univ c) h
    · have : ∀ i : Fin r, k ≠ i.succ := by
        intro i hi
        apply hk
        have := congrArg Fin.val hi
        simp only [Fin.val_succ] at this
        omega
      simp [this]

/-- Partial products invert the standard weight parametrization on determinant-one diagonal
families. -/
private def partialProducts {K : Type u} [CommRing K]
    (t : Fin (r + 1) → Kˣ) (i : Fin r) : Kˣ :=
  ∏ j ∈ Finset.range (i + 1), if hj : j < r + 1 then t ⟨j, hj⟩ else 1

private theorem torusCharacter_partialProducts {K : Type u} [CommRing K]
    (t : Fin (r + 1) → Kˣ) (ht : ∏ i, t i = 1) (k : Fin (r + 1)) :
    torusCharacter (partialProducts r t) (weight r k) = t k := by
  rw [torusCharacter_weight]
  split_ifs with hkr hk0
  · rw [partialProducts, partialProducts]
    have hpred : (k - 1 : ℕ) + 1 = k := by omega
    rw [hpred, ← div_eq_mul_inv, Finset.prod_range_succ_div_prod]
    rw [dite_eq_left (by omega)]
  · have hkzero : (k : ℕ) = 0 := by omega
    have hkfin : k = 0 := Fin.ext hkzero
    subst k
    simp [partialProducts]
  · have hkmax : (k : ℕ) = r := by omega
    have hrpos : 0 < r := by omega
    have hkfin : k = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext hkmax
    subst k
    rw [partialProducts]
    have hpred : (r - 1 : ℕ) + 1 = r := by omega
    rw [hpred]
    have htotal :
        (∏ j ∈ Finset.range r,
            if hj : j < r + 1 then t ⟨j, hj⟩ else 1) *
              t ⟨r, Nat.lt_succ_self r⟩ = 1 := by
      conv_lhs => rhs; rw [← show
        (if hj : r < r + 1 then t ⟨r, hj⟩ else 1) =
          t ⟨r, Nat.lt_succ_self r⟩ by simp]
      rw [← Finset.prod_range_succ]
      simpa only [Finset.prod_fin_eq_prod_range] using ht
    rw [one_mul, eq_inv_of_mul_eq_one_left htotal, inv_inv]
  · have hrzero : r = 0 := by omega
    subst r
    have hkfin : k = 0 := Fin.eq_zero k
    subst k
    simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] using ht.symm

/-! ## The centralizer on field-valued points -/

/-- The diagonal points of the standard carrier. -/
def diagonalPoints (K : Type u) [CommRing K] : Subgroup (points r K) :=
  (diagonalTorus K (r + 1)).comap (points r K).subtype

/-- A carrier point lies in `diagonalPoints` exactly when its ambient matrix is diagonal. -/
@[simp]
theorem mem_diagonalPoints_iff {K : Type u} [CommRing K] {g : points r K} :
    g ∈ diagonalPoints r K ↔ g.1.1.IsDiag := by
  rw [diagonalPoints, Subgroup.mem_comap, mem_diagonalTorus_iff]
  rfl

/-- Over an infinite field, a carrier point centralizing the weight torus is diagonal. -/
theorem centralizer_range_weightTorusPoints (K : Type u) [Field K] [Infinite K] :
    Subgroup.centralizer
        ((weightTorusPoints r K).range : Set (points r K)) = diagonalPoints r K := by
  apply le_antisymm
  · intro g hg
    rw [mem_diagonalPoints_iff]
    intro i j hij
    have hweight : weight r i ≠ weight r j := fun h ↦ hij (weight_injective r h)
    have hchar : weightChar K (weight r i) ≠ weightChar K (weight r j) :=
      fun h ↦ hweight (weightChar_injective h)
    have hexists : ∃ s, weightChar K (weight r i) s ≠ weightChar K (weight r j) s := by
      by_contra h
      push Not at h
      exact hchar (MonoidHom.ext h)
    obtain ⟨s, hs⟩ := hexists
    let d := weightTorusPoints r K s
    have hcomm : Commute d g :=
      Subgroup.mem_centralizer_iff.mp hg d ⟨s, rfl⟩
    have hmatrix : Commute
        d.1.1 g.1.1 :=
      congrArg (fun x : points r K ↦
        x.1.1) hcomm.eq
    change Commute (weightTorusPoints r K s).1.1 g.1.1 at hmatrix
    rw [coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe] at hmatrix
    apply apply_eq_zero_of_commute_diagonal hmatrix
    rw [weightChar_apply, weightChar_apply] at hs
    exact fun h ↦ hs (Units.ext h)
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨s, rfl⟩ := hd
    have hdDiag :
        (weightTorusPoints r K s : Matrix.GeneralLinearGroup (Fin (r + 1)) K) ∈
          diagonalTorus K (r + 1) := by
      rw [mem_diagonalTorus_iff]
      simp only [coe_weightTorusPoints,
        UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
      exact Matrix.isDiag_diagonal _
    have hcomm : Commute
        (weightTorusPoints r K s : Matrix.GeneralLinearGroup (Fin (r + 1)) K) g :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.le_centralizer (diagonalTorus K (r + 1)) hdDiag) g hg |>.symm
    apply Subtype.ext
    exact hcomm.eq

/-- **Over a field, the standard weight torus consists of all determinant-one diagonal carrier
points.** The partial products of the diagonal entries give an explicit inverse to the weight
parametrization. -/
theorem range_weightTorusPoints_eq_diagonalPoints (K : Type u) [Field K] :
    (weightTorusPoints r K).range = diagonalPoints r K := by
  apply le_antisymm
  · rintro g ⟨s, rfl⟩
    rw [mem_diagonalPoints_iff]
    simp only [coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · intro g hg
    rw [mem_diagonalPoints_iff] at hg
    obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp
      (mem_diagonalTorus_iff.mpr hg)
    have hprod : ∏ i, t i = 1 := by
      have hdet := (mem_points_iff_det_eq_one r g.1).mp g.property
      have hdet' := congrArg Matrix.GeneralLinearGroup.det ht
      rw [det_diagGL] at hdet'
      exact hdet'.trans hdet
    refine ⟨partialProducts r t, ?_⟩
    apply Subtype.ext
    rw [coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
    have hchars : (fun i ↦ torusCharacter (partialProducts r t) (weight r i)) = t :=
      funext (torusCharacter_partialProducts r t hprod)
    rw [hchars, ht]

/-- **The standard weight torus is maximal among commutative subgroups of the type `A_r`
carrier over an infinite field.** -/
theorem eq_range_weightTorusPoints_of_le_of_isMulCommutative
    (K : Type u) [Field K] [Infinite K]
    (H : Subgroup (points r K)) [IsMulCommutative H]
    (hle : (weightTorusPoints r K).range ≤ H) :
    H = (weightTorusPoints r K).range :=
  le_antisymm
    (by
      rw [range_weightTorusPoints_eq_diagonalPoints r K,
        ← centralizer_range_weightTorusPoints r K]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

end

end TauCeti.SlStd
