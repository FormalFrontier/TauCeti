/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
public import TauCeti.LinearAlgebra.Matrix.SmithNormalForm
import TauCeti.Algebra.Module.Submodule.Quotient

/-!
# Smith decomposition of an integral lattice's discriminant group

Let `L` be a nondegenerate integral lattice and choose a basis `b` of its carrier. Smith
normalization of the Gram matrix gives positive invariant factors `dᵢ` in divisibility order and
an additive equivalence

```text
L.DiscriminantGroup ≃+ ∏ i, ZMod dᵢ.
```

This file exposes that decomposition at the integral-lattice interface. It records the diagonal
inclusion matrix in the chosen Smith bases, proves independence of the initial carrier basis, and
shows that the product of the cyclic-factor orders is the lattice discriminant.

## Main declarations

* `TauCeti.IntegralLattice.gramSmithInvariantFactors`: normalized positive Smith factors for a
  nondegenerate Gram matrix.
* `TauCeti.IntegralLattice.gramSmithInvariantFactors_eq`: the factors do not depend on the carrier
  basis.
* `TauCeti.IntegralLattice.gramSmithInvariantFactors_dvd`: successive invariant factors divide one
  another.
* `TauCeti.IntegralLattice.exists_gramSmithInvariantFactors_smith_normal_form`: the normalized
  invariant factors are a Smith normal form of the Gram matrix.
* `TauCeti.IntegralLattice.discriminantGroupInvariantFactorsEquiv`: the discriminant group as a
  product of cyclic groups of the normalized invariant-factor orders.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `Mathlib.LinearAlgebra.FreeModule.Finite.Quotient`, especially
  `Submodule.quotientEquivPiZMod`.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The embedded carrier and the dual carrier have the same integral rank. -/
theorem finrank_carrierInDual_eq_dualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    Module.finrank ℤ L.carrierInDual = Module.finrank ℤ L.dualCarrier := by
  rw [L.finrank_carrierInDual, L.finrank_carrier, L.finrank_dualCarrier]

open Classical in
private theorem gramSmithWitness (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    ∃ (P Q : Matrix.GeneralLinearGroup (Fin (Fintype.card ι)) ℤ)
      (d : Fin (Fintype.card ι) → ℤ), (∀ i, 0 < d i) ∧
        (∀ ⦃i j : Fin (Fintype.card ι)⦄, i ≤ j → d i ∣ d j) ∧
          (P : Matrix _ _ ℤ) * L.gramMatrix (b.reindex (Fintype.equivFin ι)) *
              (Q : Matrix _ _ ℤ) = Matrix.diagonal d := by
  apply Matrix.exists_smith_normal_form_of_det_ne_zero
  rw [← L.gramDet_def, L.gramDet_reindex, L.gramDet_ne_zero_iff]
  exact L.form_nondegenerate

open Classical in
private noncomputable def gramSmithLeftMatrix (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    Matrix.GeneralLinearGroup (Fin (Fintype.card ι)) ℤ :=
  (L.gramSmithWitness b).choose

open Classical in
private noncomputable def gramSmithRightMatrix (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    Matrix.GeneralLinearGroup (Fin (Fintype.card ι)) ℤ :=
  (L.gramSmithWitness b).choose_spec.choose

open Classical in
/-- The normalized positive Smith invariant factors of a nondegenerate Gram matrix. -/
noncomputable def gramSmithInvariantFactors (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) : Fin (Fintype.card ι) → ℤ :=
  (L.gramSmithWitness b).choose_spec.choose_spec.choose

open Classical in
/-- The normalized Gram invariant factors are positive. -/
theorem gramSmithInvariantFactors_pos (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (i) :
    0 < L.gramSmithInvariantFactors b i :=
  (L.gramSmithWitness b).choose_spec.choose_spec.choose_spec.1 i

open Classical in
/-- The normalized Gram invariant factors form a divisibility chain. -/
theorem gramSmithInvariantFactors_dvd (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L)
    {i j : Fin (Fintype.card ι)} (hij : i ≤ j) :
    L.gramSmithInvariantFactors b i ∣ L.gramSmithInvariantFactors b j :=
  (L.gramSmithWitness b).choose_spec.choose_spec.choose_spec.2.1 hij

open Classical in
/-- The normalized invariant factors are a Smith normal form of the Gram matrix: general-linear
row and column operations bring it to their diagonal. -/
theorem exists_gramSmithInvariantFactors_smith_normal_form (L : IntegralLattice V)
    [L.IsNondegenerate] {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    ∃ P Q : Matrix.GeneralLinearGroup (Fin (Fintype.card ι)) ℤ,
      (P : Matrix _ _ ℤ) * L.gramMatrix (b.reindex (Fintype.equivFin ι)) *
          (Q : Matrix _ _ ℤ) =
        Matrix.diagonal (L.gramSmithInvariantFactors b) :=
  ⟨L.gramSmithLeftMatrix b, L.gramSmithRightMatrix b,
    (L.gramSmithWitness b).choose_spec.choose_spec.choose_spec.2.2⟩

open Classical in
/-- The normalized Gram invariant factors do not depend on the chosen carrier basis with a fixed
index type. -/
theorem gramSmithInvariantFactors_eq (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b b' : Basis ι ℤ L) :
    L.gramSmithInvariantFactors b = L.gramSmithInvariantFactors b' := by
  let e := b.reindex (Fintype.equivFin ι)
  let e' := b'.reindex (Fintype.equivFin ι)
  let T : Matrix.GeneralLinearGroup (Fin (Fintype.card ι)) ℤ :=
    ⟨e'.toMatrix e, e.toMatrix e', e'.toMatrix_mul_toMatrix_flip e,
      e.toMatrix_mul_toMatrix_flip e'⟩
  let Tt : Matrix.GeneralLinearGroup (Fin (Fintype.card ι)) ℤ :=
    ⟨(e'.toMatrix e).transpose, (e.toMatrix e').transpose, by
      rw [← Matrix.transpose_mul, e.toMatrix_mul_toMatrix_flip e', Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, e'.toMatrix_mul_toMatrix_flip e, Matrix.transpose_one]⟩
  have hchange : (Tt : Matrix _ _ ℤ) * L.gramMatrix e' * (T : Matrix _ _ ℤ) =
      L.gramMatrix e := by
    rw [L.gramMatrix_eq_toMatrix, L.gramMatrix_eq_toMatrix]
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e' e L.integralForm
  obtain ⟨P, Q, hb⟩ := L.exists_gramSmithInvariantFactors_smith_normal_form b
  obtain ⟨P', Q', hb'⟩ := L.exists_gramSmithInvariantFactors_smith_normal_form b'
  refine (Matrix.smith_normal_form_unique
    (fun i ↦ (L.gramSmithInvariantFactors_pos b' i).le)
    (fun i ↦ (L.gramSmithInvariantFactors_pos b i).le)
    (fun _ _ hij ↦ L.gramSmithInvariantFactors_dvd b' hij)
    (fun _ _ hij ↦ L.gramSmithInvariantFactors_dvd b hij)
    (P * Tt * P'⁻¹) (Q'⁻¹ * T * Q) ?_).symm
  rw [← hb']
  simp only [Units.val_mul]
  calc
    ((P : Matrix _ _ ℤ) * (Tt : Matrix _ _ ℤ) * (↑P'⁻¹ : Matrix _ _ ℤ)) *
          ((P' : Matrix _ _ ℤ) * L.gramMatrix e' * (Q' : Matrix _ _ ℤ)) *
          ((↑Q'⁻¹ : Matrix _ _ ℤ) * (T : Matrix _ _ ℤ) * (Q : Matrix _ _ ℤ)) =
        (P : Matrix _ _ ℤ) *
          ((Tt : Matrix _ _ ℤ) * L.gramMatrix e' * (T : Matrix _ _ ℤ)) *
          (Q : Matrix _ _ ℤ) := by simp [Matrix.mul_assoc]
    _ = (P : Matrix _ _ ℤ) * L.gramMatrix e * (Q : Matrix _ _ ℤ) := by
      rw [hchange]
    _ = Matrix.diagonal (L.gramSmithInvariantFactors b) := hb

/-- The order of every cyclic factor in the normalized decomposition is nonzero. -/
theorem gramSmithInvariantFactors_natAbs_ne_zero
    (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (i : Fin (Fintype.card ι)) :
    (L.gramSmithInvariantFactors b i).natAbs ≠ 0 :=
  Int.natAbs_ne_zero.mpr (ne_of_gt (L.gramSmithInvariantFactors_pos b i))

/-- The orders displayed in the normalized cyclic decomposition form a divisibility chain. -/
theorem gramSmithInvariantFactors_natAbs_dvd
    (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L)
    {i j : Fin (Fintype.card ι)} (hij : i ≤ j) :
    (L.gramSmithInvariantFactors b i).natAbs ∣
      (L.gramSmithInvariantFactors b j).natAbs :=
  Int.natAbs_dvd_natAbs.mpr (L.gramSmithInvariantFactors_dvd b hij)

open Classical in
/-- The basis of the dual carrier in which the embedded carrier has normalized Smith
coordinates. -/
noncomputable def gramSmithDualBasis (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    Basis (Fin (Fintype.card ι)) ℤ L.dualCarrier :=
  let b₀ := L.dualCarrierBasis (b.reindex (Fintype.equivFin ι))
  Basis.ofEquivFun
    (b₀.equivFun.trans (Matrix.GeneralLinearGroup.toLin (L.gramSmithLeftMatrix b)).toLinearEquiv)

open Classical in
/-- The basis of the embedded carrier paired diagonally with `gramSmithDualBasis`. -/
noncomputable def gramSmithCarrierBasis (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    Basis (Fin (Fintype.card ι)) ℤ L.carrierInDual :=
  let b₀ := L.carrierInDualBasis (b.reindex (Fintype.equivFin ι))
  b₀.map (Matrix.GeneralLinearGroup.toLin' b₀ (L.gramSmithRightMatrix b)).toLinearEquiv

open Classical in
/-- The embedded carrier has the diagonal matrix of normalized invariant factors in the two Gram
Smith bases. -/
theorem gramSmithDualBasis_toMatrix_gramSmithCarrierBasis
    (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    (L.gramSmithDualBasis b).toMatrix ((↑) ∘ L.gramSmithCarrierBasis b) =
      Matrix.diagonal (L.gramSmithInvariantFactors b) := by
  let b' := b.reindex (Fintype.equivFin ι)
  let d₀ := L.dualCarrierBasis b'
  let c₀ := L.carrierInDualBasis b'
  let P := L.gramSmithLeftMatrix b
  let Q := L.gramSmithRightMatrix b
  let gQ := (Matrix.GeneralLinearGroup.toLin' c₀ Q).toLinearEquiv
  have hleft : (L.gramSmithDualBasis b).toMatrix d₀ = (P : Matrix _ _ ℤ) := by
    ext i j
    simp [gramSmithDualBasis, d₀, P, b', Basis.toMatrix_apply,
      Matrix.mulVec, dotProduct, Finsupp.single_apply]
  have hgQ : LinearMap.toMatrix c₀ c₀ gQ.toLinearMap = (Q : Matrix _ _ ℤ) := by
    ext i j
    simp [gQ, Matrix.GeneralLinearGroup.toLin'_apply, LinearMap.toMatrix_apply,
      Fintype.linearCombination_apply, Matrix.mulVec, dotProduct, Finsupp.single_apply]
  let inclusion : L.carrierInDual →ₗ[ℤ] L.dualCarrier := L.carrierInDual.subtype
  have hcarrier : d₀.toMatrix ((↑) ∘ L.gramSmithCarrierBasis b) =
      L.gramMatrix b' * (Q : Matrix _ _ ℤ) := by
    calc
      d₀.toMatrix ((↑) ∘ L.gramSmithCarrierBasis b) =
          LinearMap.toMatrix c₀ d₀ (inclusion.comp gQ.toLinearMap) := by
        rw [LinearMap.toMatrix_eq_basisToMatrix]
        -- both families list the same vectors: `gramSmithCarrierBasis` is `c₀` mapped through
        -- `gQ`, and the coercion out of `L.carrierInDual` is `inclusion`
        refine congrArg d₀.toMatrix (funext fun i ↦ ?_)
        simp [gramSmithCarrierBasis, c₀, b', Q, gQ, inclusion, Basis.map_apply]
      _ = LinearMap.toMatrix c₀ d₀ inclusion *
          LinearMap.toMatrix c₀ c₀ gQ.toLinearMap :=
        LinearMap.toMatrix_comp c₀ c₀ d₀ inclusion gQ.toLinearMap
      _ = L.gramMatrix b' * (Q : Matrix _ _ ℤ) := by
        rw [hgQ, LinearMap.toMatrix_eq_basisToMatrix]
        -- Expose the two basis-coordinate maps hidden by the inclusion abbreviation so the
        -- existing Gram-matrix identity applies directly.
        change (L.dualCarrierBasis b').toMatrix
            ((↑) ∘ L.carrierInDualBasis b') * (Q : Matrix _ _ ℤ) = _
        rw [L.dualCarrierBasis_toMatrix_carrierInDualBasis b']
  rw [← (L.gramSmithDualBasis b).toMatrix_mul_toMatrix d₀
    ((↑) ∘ L.gramSmithCarrierBasis b), hleft, hcarrier, ← Matrix.mul_assoc]
  simpa [P, Q, b', gramSmithLeftMatrix, gramSmithRightMatrix,
    gramSmithInvariantFactors] using
      (L.gramSmithWitness b).choose_spec.choose_spec.choose_spec.2.2

open Classical in
/-- In the normalized Smith bases, the embedded carrier basis vector is its positive invariant
factor times the corresponding dual-carrier basis vector. -/
@[simp]
theorem coe_gramSmithCarrierBasis_apply (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (i : Fin (Fintype.card ι)) :
    (L.gramSmithCarrierBasis b i : L.dualCarrier) =
      L.gramSmithInvariantFactors b i • L.gramSmithDualBasis b i := by
  apply (L.gramSmithDualBasis b).ext_elem
  intro j
  have h := congrFun (congrFun (L.gramSmithDualBasis_toMatrix_gramSmithCarrierBasis b) j) i
  by_cases hji : j = i
  · subst j
    simpa [Basis.toMatrix_apply, Matrix.diagonal_apply, Finsupp.single_apply] using h
  · rw [Basis.toMatrix_apply, Function.comp_apply, Matrix.diagonal_apply,
      ite_eq_right hji] at h
    rw [map_smul, Basis.repr_self, Finsupp.smul_single, Int.zsmul_eq_mul,
      Finsupp.single_apply, ite_eq_right (Ne.symm hji)]
    exact h

open Classical in
/-- The discriminant group is the product of cyclic groups with the normalized Gram invariant
factors as their orders. -/
noncomputable def discriminantGroupInvariantFactorsEquiv
    (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    L.DiscriminantGroup ≃+ ∀ i, ZMod (L.gramSmithInvariantFactors b i).natAbs :=
  L.carrierInDual.quotientEquivPiZModOfBasis (L.gramSmithDualBasis b)
    (L.gramSmithCarrierBasis b) (L.gramSmithInvariantFactors b)
    (L.coe_gramSmithCarrierBasis_apply b)

open Classical in
/-- The normalized invariant-factor equivalence sends a discriminant class to the coordinates of
its representative in the normalized dual-carrier basis. -/
@[simp]
theorem discriminantGroupInvariantFactorsEquiv_mk_apply
    (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (x : L.dualCarrier)
    (i : Fin (Fintype.card ι)) :
    L.discriminantGroupInvariantFactorsEquiv b (Submodule.Quotient.mk x) i =
      (((L.gramSmithDualBasis b).repr x i : ℤ) :
        ZMod (L.gramSmithInvariantFactors b i).natAbs) := by
  rw [discriminantGroupInvariantFactorsEquiv,
    Submodule.quotientEquivPiZModOfBasis_mk_apply]

open Classical in
/-- The product of the normalized cyclic-factor orders is the lattice discriminant. -/
theorem prod_gramSmithInvariantFactors_natAbs_eq_discriminant
    (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    ∏ i, (L.gramSmithInvariantFactors b i).natAbs = L.discriminant := by
  let (i : Fin (Fintype.card ι)) : NeZero (L.gramSmithInvariantFactors b i).natAbs :=
    ⟨L.gramSmithInvariantFactors_natAbs_ne_zero b i⟩
  rw [← L.natCard_discriminantGroup]
  symm
  rw [Nat.card_congr (L.discriminantGroupInvariantFactorsEquiv b).toEquiv, Nat.card_pi]
  simp only [Nat.card_zmod]

end TauCeti.IntegralLattice
