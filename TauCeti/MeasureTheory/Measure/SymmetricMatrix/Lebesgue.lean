/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lebesgue measure on the symmetric subspace

`TauCeti.symmetricLebesgue p` is the pushforward of product Lebesgue measure on the
upper-triangular coordinates along `(TauCeti.symmetricCoordinates p).symm`. This is the
normalization used by the Wishart densities and the multivariate-Gamma integral of the
standard-distributions roadmap: the coordinate unit cube has measure one.

The Frobenius volume of `measureSpaceOfInnerProductSpace` is a Haar measure for the same
topology, but a different normalization: the off-diagonal coordinate directions `Eᵢⱼ + Eⱼᵢ`
have Frobenius norm `√2`, so Frobenius volume is `2 ^ (p * (p - 1) / 4)` times
`symmetricLebesgue p`, with a real exponent.

## Main declarations

* `TauCeti.symmetricLebesgue` — Lebesgue measure on the symmetric subspace, normalized by the
  upper-triangular coordinates.
* `TauCeti.measurePreserving_symmetricCoordinates_symm` — the coordinate reconstruction is
  measure preserving.
* `TauCeti.isAddHaarMeasure_symmetricLebesgue` — `symmetricLebesgue p` is an additive Haar
  measure, as required by Mathlib's Jacobian API.
* `TauCeti.volume_symmetricMatrix_eq_smul_symmetricLebesgue` — comparison with the Frobenius
  volume.
* `TauCeti.symmetricLebesgue_zero` — in dimension zero, `symmetricLebesgue` is the Dirac
  measure on the unique symmetric matrix.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 1,
  **Symmetric matrices and their Lebesgue measure**.
-/

public section

noncomputable section

open MeasureTheory Module

open scoped RealInnerProductSpace

namespace TauCeti

/-- Lebesgue measure on the symmetric subspace: the pushforward of product Lebesgue measure on
the upper-triangular coordinates along the coordinate reconstruction. The coordinate unit cube
has measure one; this is the normalization used by the Wishart densities. -/
@[expose]
def symmetricLebesgue (p : ℕ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (volume : Measure (upperTriangle p → ℝ)).map (symmetricCoordinates p).symm

theorem measurePreserving_symmetricCoordinates_symm (p : ℕ) :
    MeasurePreserving (symmetricCoordinates p).symm volume (symmetricLebesgue p) :=
  ⟨(symmetricCoordinates p).symm.continuous.measurable, rfl⟩

theorem measurePreserving_symmetricCoordinates (p : ℕ) :
    MeasurePreserving (symmetricCoordinates p) (symmetricLebesgue p) volume :=
  (measurePreserving_symmetricCoordinates_symm p).symm (symmetricCoordinatesMeasurableEquiv p).symm

instance isAddHaarMeasure_symmetricLebesgue (p : ℕ) :
    (symmetricLebesgue p).IsAddHaarMeasure :=
  ContinuousLinearEquiv.isAddHaarMeasure_map (symmetricCoordinates p).symm volume

/-! ### Comparison with the Frobenius volume

The comparison goes through the coordinate basis `TauCeti.symmetricBasis p`, whose vectors are
the symmetric matrices `Eᵢⱼ + Eⱼᵢ` and `Eᵢᵢ`. Rescaling the off-diagonal ones by `(√2)⁻¹` makes
the basis orthonormal for the Frobenius inner product, and the determinant of that rescaling is
the ratio of the two normalizations. -/

section comparison

private theorem addHaar_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).addHaar = (volume : Measure (ι → ℝ)) := by
  rw [Basis.addHaar_def, Basis.parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]

private theorem symmetricLebesgue_eq_addHaar (p : ℕ) :
    symmetricLebesgue p = (symmetricBasis p).addHaar := by
  rw [symmetricLebesgue, ← addHaar_basisFun, Basis.map_addHaar]
  rfl

private theorem inner_symmetricMatrix_eq_sum (p : ℕ)
    (A C : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ⟪A, C⟫ = ∑ a, ∑ b, (A : Matrix (Fin p) (Fin p) ℝ) a b *
      (C : Matrix (Fin p) (Fin p) ℝ) a b := rfl

private theorem sum_mul_single (p : ℕ) (A : Matrix (Fin p) (Fin p) ℝ) (k l : Fin p) :
    ∑ a, ∑ b, A a b * Matrix.single k l (1 : ℝ) a b = A k l := by
  simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- The coordinate basis vector at `kl` pairs with a symmetric matrix through its `kl` entry,
doubled off the diagonal. -/
private theorem inner_symmetricBasis (p : ℕ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (kl : upperTriangle p) :
    ⟪A, symmetricBasis p kl⟫ =
      (if kl.1.1 = kl.1.2 then 1 else 2) * (A : Matrix (Fin p) (Fin p) ℝ) kl.1.1 kl.1.2 := by
  obtain ⟨⟨k, l⟩, hkl⟩ := kl
  rw [inner_symmetricMatrix_eq_sum]
  by_cases h : k = l
  · subst h
    rw [coe_symmetricBasis_diag, sum_mul_single]
    simp
  · rw [coe_symmetricBasis_offDiag p hkl h]
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_single,
      coe_apply_comm A l k]
    rw [ite_eq_right h]
    ring

/-- The rescaling that turns the coordinate basis into an orthonormal one. -/
private def symScale (p : ℕ) (ij : upperTriangle p) : ℝˣ :=
  if ij.1.1 = ij.1.2 then 1 else Units.mk0 (Real.sqrt 2)⁻¹ (by positivity)

private theorem symScale_coe (p : ℕ) (ij : upperTriangle p) :
    ((symScale p ij : ℝˣ) : ℝ) = if ij.1.1 = ij.1.2 then 1 else (Real.sqrt 2)⁻¹ := by
  rw [symScale]
  split <;> simp

private theorem orthonormal_symScaled (p : ℕ) :
    Orthonormal ℝ ⇑((symmetricBasis p).unitsSMul (symScale p)) := by
  rw [orthonormal_iff_ite]
  intro ij kl
  obtain ⟨⟨k, l⟩, hkl⟩ := kl
  rw [Basis.unitsSMul_apply, Basis.unitsSMul_apply, Units.smul_def, Units.smul_def,
    real_inner_smul_left, real_inner_smul_right, inner_symmetricBasis,
    coe_symmetricBasis_apply_of_le p ij hkl]
  by_cases h : ij = ⟨(k, l), hkl⟩
  · subst h
    by_cases hd : k = l
    · simp [symScale_coe, hd]
    · simp only [symScale_coe, hd, ite_false, ite_true, mul_one]
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt (by norm_num), inv_mul_cancel₀ two_ne_zero]
  · simp [h]

private theorem addHaar_symScaled (p : ℕ) :
    ((symmetricBasis p).unitsSMul (symScale p)).addHaar =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) := by
  rw [← Basis.toBasis_toOrthonormalBasis _ (orthonormal_symScaled p),
    OrthonormalBasis.addHaar_eq_volume]

/-- There are `∑ i < p, i = p * (p - 1) / 2` upper-triangular positions off the diagonal. -/
private theorem card_offDiag (p : ℕ) :
    (Finset.univ.filter fun ij : upperTriangle p => ij.1.1 ≠ ij.1.2).card =
      ∑ i ∈ Finset.range p, i := by
  have hdiag : (Finset.univ.filter fun ij : upperTriangle p => ij.1.1 = ij.1.2) =
      Finset.univ.image fun i : Fin p => (⟨(i, i), le_rfl⟩ : upperTriangle p) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · exact fun h => ⟨ij.1.1, Subtype.ext (Prod.ext_iff.2 ⟨rfl, h⟩)⟩
    · rintro ⟨i, -, rfl⟩
      rfl
  have hcard : (Finset.univ.filter fun ij : upperTriangle p => ij.1.1 = ij.1.2).card = p := by
    rw [hdiag, Finset.card_image_of_injective _ fun a b hab => by
      simpa [Subtype.ext_iff, Prod.ext_iff] using hab, Finset.card_univ, Fintype.card_fin]
  have htotal := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (upperTriangle p))) fun ij => ij.1.1 = ij.1.2
  simp only [← ne_eq] at htotal
  rw [hcard, Finset.card_univ, card_upperTriangle] at htotal
  have hsum : p * (p + 1) / 2 = ∑ i ∈ Finset.range (p + 1), i := by
    rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]
  rw [hsum, Finset.sum_range_succ] at htotal
  omega

/-- The triangular number of `p` doubles to `p * (p - 1)`; stated over `ℝ` so that the real
subtraction on the right is unproblematic at `p = 0`. -/
private theorem two_mul_card_offDiag (p : ℕ) :
    2 * ((∑ i ∈ Finset.range p, i : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
  have h := Finset.sum_range_id_mul_two p
  rcases p with _ | n
  · simp
  · have hcast : ((∑ i ∈ Finset.range (n + 1), i : ℕ) : ℝ) * 2 =
        ((n + 1 : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast at hcast ⊢
    linarith

private theorem prod_symScale_inv (p : ℕ) :
    (((∏ ij, symScale p ij)⁻¹ : ℝˣ) : ℝ) =
      Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 4) := by
  set N : ℕ := ∑ i ∈ Finset.range p, i with hN
  have hprod : ((∏ ij, symScale p ij : ℝˣ) : ℝ) = (Real.sqrt 2)⁻¹ ^ N := by
    rw [← Units.coeHom_apply, map_prod]
    simp only [Units.coeHom_apply, symScale_coe]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, card_offDiag]
  rw [Units.val_inv_eq_inv_val, hprod, inv_pow, inv_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast ((2 : ℝ) ^ (1 / 2 : ℝ)) N, ← Real.rpow_mul (by norm_num)]
  congr 1
  have := two_mul_card_offDiag p
  rw [← hN] at this
  linarith

private theorem volume_parallelepiped_symmetricBasis (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)))
        (symmetricBasis p).parallelepiped =
      ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 4)) := by
  rw [Basis.coe_parallelepiped, ← addHaar_symScaled p, Measure.addHaar_parallelepiped,
    Basis.det_unitsSMul]
  simp only [AlternatingMap.smul_apply, Basis.det_self, smul_eq_mul, mul_one]
  rw [prod_symScale_inv]
  exact congrArg ENNReal.ofReal (abs_of_nonneg (Real.rpow_nonneg (by norm_num) _))

end comparison

/-- The Frobenius volume of the symmetric subspace is `2 ^ (p * (p - 1) / 4)` times
`symmetricLebesgue`, with a real exponent: each of the `p * (p - 1) / 2` off-diagonal
coordinate directions `Eᵢⱼ + Eⱼᵢ` has Frobenius norm `√2`. -/
theorem volume_symmetricMatrix_eq_smul_symmetricLebesgue (p : ℕ) :
    (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) =
      ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 4)) • symmetricLebesgue p := by
  rw [symmetricLebesgue_eq_addHaar, Basis.addHaar_def, ← volume_parallelepiped_symmetricBasis]
  exact Measure.addHaarMeasure_unique _ _

/-- In dimension zero, the symmetric subspace is a single point and `symmetricLebesgue` is the
Dirac measure there, so the dimension-zero Wishart laws need no special casing. -/
theorem symmetricLebesgue_zero : symmetricLebesgue 0 = Measure.dirac 0 := by
  have : IsEmpty (upperTriangle 0) := ⟨fun ij => ij.1.1.elim0⟩
  rw [symmetricLebesgue, volume_pi, Measure.pi_of_empty _ 0, Measure.map_dirac, map_zero]

end TauCeti
