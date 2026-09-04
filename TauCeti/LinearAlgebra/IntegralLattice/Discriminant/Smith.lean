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

Let `L` be a nondegenerate integral lattice and choose a basis `b` of its carrier.  The basis
dual to `b` is an integral basis of `L.dualCarrier`, and the copy of `L.carrier` inside that dual
carrier has full rank.  Mathlib's full-rank Smith decomposition therefore gives nonzero diagonal
coefficients `aᵢ` and an additive equivalence

```text
L.DiscriminantGroup ≃+ ∏ i, ZMod |aᵢ|.
```

This file exposes that decomposition at the integral-lattice interface.  It also records the
diagonal inclusion matrix in the chosen Smith bases and proves that the product of the orders of
the cyclic factors is the lattice discriminant.  The current Mathlib Smith API diagonalizes a
full-rank inclusion but does not normalize its diagonal coefficients into a divisibility chain.  The
normalized branch below consumes Tau Ceti's matrix-level Smith API to expose that chain for every
nondegenerate Gram matrix and transports it to the discriminant quotient.

## Main declarations

* `TauCeti.IntegralLattice.discriminantSmithCoeff`: the nonzero integral diagonal coefficients.
* `TauCeti.IntegralLattice.discriminantSmithCoeffNatAbs`: their nonzero absolute values.
* `TauCeti.IntegralLattice.discriminantGroupSmithEquiv`: the discriminant group as a product of
  cyclic groups of those orders.
* `TauCeti.IntegralLattice.discriminantGroupSmithEquiv_mk_apply`: that equivalence reads off the
  Smith coordinates of a representative.
* `TauCeti.IntegralLattice.discriminantSmithTopBasis_toMatrix`: the inclusion is diagonal in the
  Smith bases.
* `TauCeti.IntegralLattice.prod_discriminantSmithCoeffNatAbs`: the product of the cyclic orders
  is the lattice discriminant.
* `TauCeti.IntegralLattice.gramSmithInvariantFactors`: normalized positive Smith factors for a
  nondegenerate Gram matrix.
* `TauCeti.IntegralLattice.gramSmithInvariantFactors_dvd`: successive invariant factors divide one
  another.
* `TauCeti.IntegralLattice.discriminantGroupInvariantFactorsEquiv`: the discriminant group as a
  product of cyclic groups of the normalized invariant-factor orders.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `Mathlib.LinearAlgebra.FreeModule.Finite.Quotient`, especially
  `Submodule.quotientEquivPiZMod`.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 2.
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
/-- The ambient basis of `L.dualCarrier` selected by Smith diagonalization of the full-rank
submodule `L.carrierInDual`.

The initial basis is the bilinear dual of `b`.  This basis is exposed together with
`discriminantSmithCarrierBasis` so consumers can use the diagonal inclusion equation without
unfolding Mathlib's choice-based Smith construction. -/
noncomputable def discriminantSmithTopBasis (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) : Basis ι ℤ L.dualCarrier :=
  L.carrierInDual.smithNormalFormTopBasis (L.dualCarrierBasis b)
    L.finrank_carrierInDual_eq_dualCarrier

open Classical in
/-- The basis of the embedded carrier selected by Smith diagonalization inside
`L.dualCarrier`. -/
noncomputable def discriminantSmithCarrierBasis (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) : Basis ι ℤ L.carrierInDual :=
  L.carrierInDual.smithNormalFormBotBasis (L.dualCarrierBasis b)
    L.finrank_carrierInDual_eq_dualCarrier

open Classical in
/-- A diagonal coefficient for the full-rank inclusion `L.carrierInDual ≤ L.dualCarrier`.

Its absolute value is the order of the corresponding cyclic factor in
`discriminantGroupSmithEquiv`.  No divisibility normalization between different indices is
claimed. -/
noncomputable def discriminantSmithCoeff (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) (i : ι) : ℤ :=
  L.carrierInDual.smithNormalFormCoeffs (L.dualCarrierBasis b)
    L.finrank_carrierInDual_eq_dualCarrier i

/-- Every Smith coefficient of the full-rank carrier inclusion is nonzero. -/
theorem discriminantSmithCoeff_ne_zero (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) (i : ι) :
    L.discriminantSmithCoeff b i ≠ 0 :=
  Submodule.smithNormalFormCoeffs_ne_zero (L.dualCarrierBasis b)
    L.finrank_carrierInDual_eq_dualCarrier i

/-- The absolute value of the Smith coefficient indexed by `i`, i.e. the positive order of the
cyclic discriminant-group factor it contributes. -/
noncomputable def discriminantSmithCoeffNatAbs (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) (i : ι) : ℕ :=
  (L.discriminantSmithCoeff b i).natAbs

/-- Every cyclic factor in the Smith decomposition has nonzero order. -/
theorem discriminantSmithCoeffNatAbs_ne_zero (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) (i : ι) :
    L.discriminantSmithCoeffNatAbs b i ≠ 0 :=
  Int.natAbs_ne_zero.mpr (L.discriminantSmithCoeff_ne_zero b i)

/-- The basis vector of the embedded carrier is its Smith coefficient times the corresponding
ambient Smith basis vector. -/
@[simp]
theorem coe_discriminantSmithCarrierBasis_apply (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) (i : ι) :
    (L.discriminantSmithCarrierBasis b i : L.dualCarrier) =
      L.discriminantSmithCoeff b i • L.discriminantSmithTopBasis b i :=
  Submodule.smithNormalFormBotBasis_def (L.dualCarrierBasis b)
    L.finrank_carrierInDual_eq_dualCarrier i

open Classical in
/-- In the two Smith bases, the inclusion `L.carrierInDual → L.dualCarrier` is the diagonal
matrix of `discriminantSmithCoeff`. -/
theorem discriminantSmithTopBasis_toMatrix (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) :
    (L.discriminantSmithTopBasis b).toMatrix
        ((↑) ∘ L.discriminantSmithCarrierBasis b) =
      Matrix.diagonal (L.discriminantSmithCoeff b) := by
  ext i j
  simp +contextual [Basis.toMatrix_apply, L.coe_discriminantSmithCarrierBasis_apply,
    Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]

open Classical in
/-- The discriminant group is a product of cyclic groups whose orders are the absolute values of
the Smith diagonal coefficients. -/
noncomputable def discriminantGroupSmithEquiv (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) :
    L.DiscriminantGroup ≃+ ∀ i, ZMod (L.discriminantSmithCoeffNatAbs b i) :=
  L.carrierInDual.quotientEquivPiZMod (L.dualCarrierBasis b)
    L.finrank_carrierInDual_eq_dualCarrier

open Classical in
/-- The Smith decomposition sends the class of `x` to its coordinates in the ambient Smith basis,
each read modulo the corresponding cyclic order.

This characterizes `discriminantGroupSmithEquiv` on quotient representatives, so consumers never
need to unfold Mathlib's choice-based Smith construction. -/
@[simp]
theorem discriminantGroupSmithEquiv_mk_apply (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Finite ι] (b : Basis ι ℤ L) (x : L.dualCarrier) (i : ι) :
    L.discriminantGroupSmithEquiv b (Submodule.Quotient.mk x) i =
      (((L.discriminantSmithTopBasis b).repr x i : ℤ) :
        ZMod (L.discriminantSmithCoeffNatAbs b i)) := (rfl)

open Classical in
/-- The order of the discriminant group is the product of the orders of its Smith cyclic
factors. -/
theorem natCard_discriminantGroup_eq_prod_discriminantSmithCoeffNatAbs
    (L : IntegralLattice V) [L.IsNondegenerate] {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) :
    Nat.card L.DiscriminantGroup = ∏ i, L.discriminantSmithCoeffNatAbs b i := by
  let (i : ι) : NeZero (L.discriminantSmithCoeffNatAbs b i) :=
    ⟨L.discriminantSmithCoeffNatAbs_ne_zero b i⟩
  rw [Nat.card_congr (L.discriminantGroupSmithEquiv b).toEquiv, Nat.card_pi]
  simp only [Nat.card_zmod]

open Classical in
/-- The product of the Smith cyclic-factor orders is the lattice discriminant. -/
theorem prod_discriminantSmithCoeffNatAbs (L : IntegralLattice V) [L.IsNondegenerate]
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) :
    ∏ i, L.discriminantSmithCoeffNatAbs b i = L.discriminant := by
  rw [← L.natCard_discriminantGroup_eq_prod_discriminantSmithCoeffNatAbs b,
    L.natCard_discriminantGroup]

open Classical in
/-- The product of the integral Smith coefficients is associated to the Gram determinant.

Thus the diagonal inclusion matrix supplied here is a Smith diagonalization of the Gram matrix
up to integral changes of basis, including the possible sign change in its determinant. -/
theorem associated_prod_discriminantSmithCoeff_gramDet
    (L : IntegralLattice V) [L.IsNondegenerate] {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) :
    Associated (∏ i, L.discriminantSmithCoeff b i) (L.gramDet b) := by
  apply Int.natAbs_eq_iff_associated.mp
  calc
    (∏ i, L.discriminantSmithCoeff b i).natAbs =
        ∏ i, (L.discriminantSmithCoeff b i).natAbs :=
      map_prod Int.natAbsHom _ Finset.univ
    _ = ∏ i, L.discriminantSmithCoeffNatAbs b i := rfl
    _ = L.discriminant := L.prod_discriminantSmithCoeffNatAbs b
    _ = (L.gramDet b).natAbs := L.discriminant_eq_natAbs_gramDet b

/-! ## Normalized invariant factors -/

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
        rfl
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
