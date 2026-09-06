/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne

/-!
# Maximality of the type A weight torus on field-valued points

Over an infinite field, the standard carrier's weight-torus points are precisely the
determinant-one diagonal matrices and form a maximal commutative subgroup of the carrier points.
The centralizer calculation and maximality theorem identify the subgroup singled out by the
standard weights as the distinguished torus used in the type `A` pinning.

## Main declarations

* `TauCeti.SlStd.centralizer_range_weightTorusPoints`: the centralizer of the weight torus is the
  determinant-one diagonal subgroup.
* `TauCeti.SlStd.range_weightTorusPoints_eq_diagonalPoints`: the weight torus consists of all
  determinant-one diagonal carrier points.
* `TauCeti.SlStd.eq_range_weightTorusPoints_of_le_of_isMulCommutative`: the weight torus is maximal
  among commutative subgroups of the carrier points.
-/

public section

namespace TauCeti.SlStd

universe u

noncomputable section

variable (r : ℕ)

private theorem prod_ite_eq_of_eq {M : Type*} [CommMonoid M] (f : Fin r → M)
    (e : Fin r → Fin (r + 1)) (he : Function.Injective e) (k : Fin (r + 1)) (c : Fin r)
    (hkc : k = e c) :
    (∏ i, if k = e i then f i else 1) = f c := by
  rw [Finset.prod_eq_single c]
  · simp only [hkc, ↓reduceIte]
  · intro j _ hj
    split_ifs with h
    · exact (hj (he (hkc.symm.trans h)).symm).elim
    · rfl
  · exact fun h ↦ absurd (Finset.mem_univ c) h

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
      rw [prod_ite_eq_of_eq r s Fin.castSucc
        (fun _ _ h ↦ Fin.castSucc_inj.mp h) k c hkc]
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
      rw [prod_ite_eq_of_eq r (fun i ↦ (s i)⁻¹) Fin.succ
        (fun _ _ h ↦ Fin.succ_inj.mp h) k c hkc]
    · have : ∀ i : Fin r, k ≠ i.succ := by
        intro i hi
        apply hk
        have := congrArg Fin.val hi
        simp only [Fin.val_succ] at this
        omega
      simp [this]

private theorem torusCharacter_partialProd {K : Type u} [CommRing K]
    (t : Fin (r + 1) → Kˣ) (ht : ∏ i, t i = 1) (k : Fin (r + 1)) :
    torusCharacter (fun i : Fin r ↦ Fin.partialProd t i.succ.castSucc) (weight r k) = t k := by
  rw [torusCharacter_weight]
  split_ifs with hkr hk0
  · let i : Fin r := ⟨k, hkr⟩
    let j : Fin r := ⟨k - 1, by omega⟩
    have hi : i.succ.castSucc = k.succ := Fin.ext (by simp [i])
    have hj : j.succ.castSucc = k.castSucc := Fin.ext (by simp [j]; omega)
    rw [hi, hj]
    simpa only [mul_comm] using (Fin.partialProd_right_inv t k)
  · have hkzero : (k : ℕ) = 0 := by omega
    have hkfin : k = 0 := Fin.ext hkzero
    subst k
    have hi : (⟨(0 : Fin (r + 1)), hkr⟩ : Fin r).succ.castSucc =
        (0 : Fin (r + 1)).succ := Fin.ext rfl
    rw [mul_one, hi, Fin.partialProd_succ,
      show (0 : Fin (r + 1)).castSucc = (0 : Fin (r + 2)) by rfl,
      Fin.partialProd_zero, one_mul]
  · have hkmax : (k : ℕ) = r := by omega
    have hrpos : 0 < r := by omega
    have hkfin : k = ⟨r, Nat.lt_succ_self r⟩ := Fin.ext hkmax
    subst k
    let i : Fin r := ⟨r - 1, by omega⟩
    let k : Fin (r + 1) := ⟨r, Nat.lt_succ_self r⟩
    have hi : i.succ.castSucc = k.castSucc := Fin.ext (by simp [i, k]; omega)
    rw [hi]
    have hlast : Fin.partialProd t k.succ = 1 := by
      have hk_last : k.succ = Fin.last (r + 1) := Fin.ext (by simp [k])
      rw [hk_last]
      rw [Fin.partialProd, Fin.val_last]
      have htake : (List.ofFn t).take (r + 1) = List.ofFn t :=
        (List.take_eq_self_iff _).mpr (by simp)
      rw [htake, Fin.prod_ofFn]
      exact ht
    have hright := Fin.partialProd_right_inv t k
    rw [hlast, mul_one] at hright
    simpa only [one_mul, k] using hright
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

/-- If distinct weights define distinct characters over a ring without zero divisors, a carrier
point centralizing the weight torus is diagonal. -/
theorem centralizer_range_weightTorusPoints_of_weightChar_injective
    (K : Type u) [CommRing K] [IsCancelMulZero K]
    (hchar : Function.Injective (weightChar K (κ := Fin r))) :
    Subgroup.centralizer
        ((weightTorusPoints r K).range : Set (points r K)) = diagonalPoints r K := by
  apply le_antisymm
  · intro g hg
    rw [mem_diagonalPoints_iff]
    intro i j hij
    have hweight : weight r i ≠ weight r j := fun h ↦ hij (weight_injective r h)
    have hchar_ne : weightChar K (weight r i) ≠ weightChar K (weight r j) :=
      fun h ↦ hweight (hchar h)
    have hexists : ∃ s, weightChar K (weight r i) s ≠ weightChar K (weight r j) s := by
      by_contra h
      push Not at h
      exact hchar_ne (MonoidHom.ext h)
    obtain ⟨s, hs⟩ := hexists
    let d := weightTorusPoints r K s
    have hcomm : Commute d g :=
      Subgroup.mem_centralizer_iff.mp hg d ⟨s, rfl⟩
    have hmatrix : Commute d.1.1 g.1.1 :=
      congrArg (fun x : points r K ↦ x.1.1) hcomm.eq
    have hd : d = weightTorusPoints r K s := rfl
    rw [hd] at hmatrix
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

/-- Over an infinite field, a carrier point centralizing the weight torus is diagonal. -/
theorem centralizer_range_weightTorusPoints (K : Type u) [Field K] [Infinite K] :
    Subgroup.centralizer
        ((weightTorusPoints r K).range : Set (points r K)) = diagonalPoints r K :=
  centralizer_range_weightTorusPoints_of_weightChar_injective r K weightChar_injective

/-- The standard weight-torus parametrization is injective over every commutative ring. -/
theorem weightTorusPoints_injective (K : Type u) [CommRing K] :
    Function.Injective (weightTorusPoints r K) := by
  intro s t hst
  apply eq_of_span_eq_top_of_torusCharacter_eq (span_range_weight_eq_top r)
  intro i
  have hmatrix := congrArg (fun g : points r K ↦ g.1) hst
  rw [coe_weightTorusPoints, coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] at hmatrix
  exact congrFun (diagGL_injective hmatrix) i

/-- **Over a commutative ring, the standard weight torus consists of all diagonal carrier
points.** Thus every diagonal carrier point admits a standard weight-torus parametrization. -/
theorem range_weightTorusPoints_eq_diagonalPoints (K : Type u) [CommRing K] :
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
      have hdet := det_eq_one_of_mem_points r g.property
      have hdet' := congrArg Matrix.GeneralLinearGroup.det ht
      rw [det_diagGL] at hdet'
      exact hdet'.trans hdet
    refine ⟨(fun i : Fin r ↦ Fin.partialProd t i.succ.castSucc), ?_⟩
    apply Subtype.ext
    rw [coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply]
    have hchars :
        (fun i ↦ torusCharacter (fun j : Fin r ↦ Fin.partialProd t j.succ.castSucc)
          (weight r i)) = t :=
      funext (torusCharacter_partialProd r t hprod)
    rw [hchars, ht]

/-- If its weight characters are distinct over a ring without zero divisors, the standard weight
torus is maximal among commutative subgroups of the type `A_r` carrier. -/
theorem eq_range_weightTorusPoints_of_le_of_isMulCommutative_of_weightChar_injective
    (K : Type u) [CommRing K] [IsCancelMulZero K]
    (hchar : Function.Injective (weightChar K (κ := Fin r)))
    (H : Subgroup (points r K)) [IsMulCommutative H]
    (hle : (weightTorusPoints r K).range ≤ H) :
    H = (weightTorusPoints r K).range :=
  le_antisymm
    (by
      rw [range_weightTorusPoints_eq_diagonalPoints r K,
        ← centralizer_range_weightTorusPoints_of_weightChar_injective r K hchar]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

/-- **The standard weight torus is maximal among commutative subgroups of the type `A_r`
carrier over an infinite field.** -/
theorem eq_range_weightTorusPoints_of_le_of_isMulCommutative
    (K : Type u) [Field K] [Infinite K]
    (H : Subgroup (points r K)) [IsMulCommutative H]
    (hle : (weightTorusPoints r K).range ≤ H) :
    H = (weightTorusPoints r K).range :=
  eq_range_weightTorusPoints_of_le_of_isMulCommutative_of_weightChar_injective r K
    weightChar_injective H hle

end

end TauCeti.SlStd
