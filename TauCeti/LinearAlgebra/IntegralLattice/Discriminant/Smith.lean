/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
public import TauCeti.LinearAlgebra.Matrix.SmithNormalForm

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
positive-determinant Gram-matrix branch below consumes Tau Ceti's matrix-level Smith API to expose
that chain; transporting it to the discriminant quotient and treating a negative determinant remain
later work.

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
  positive-determinant Gram matrix.
* `TauCeti.IntegralLattice.gramSmithInvariantFactors_dvd`: successive invariant factors divide one
  another.

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

/-! ## Normalized factors for positive determinant -/

open Classical in
private theorem gramSmithWitness (L : IntegralLattice V)
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (hdet : 0 < L.gramDet b) :
    ∃ (P Q : Matrix.SpecialLinearGroup (Fin (Fintype.card ι)) ℤ)
      (d : Fin (Fintype.card ι) → ℤ), (∀ i, 0 < d i) ∧
        (∀ ⦃i j : Fin (Fintype.card ι)⦄, i ≤ j → d i ∣ d j) ∧
          (P : Matrix _ _ ℤ) * L.gramMatrix (b.reindex (Fintype.equivFin ι)) *
              (Q : Matrix _ _ ℤ) = Matrix.diagonal d := by
  apply Matrix.exists_smith_normal_form_of_det_pos
    (L.gramMatrix (b.reindex (Fintype.equivFin ι))) (by
      rw [← L.gramDet_def, L.gramDet_reindex]
      exact hdet)

open Classical in
/-- The normalized Smith invariant factors of a positive-determinant Gram matrix.

The positivity and divisibility chain are supplied by the matrix Smith normal form.  The
positive-determinant hypothesis is the part of the normalization that is currently exposed here;
the general nonzero-determinant case requires a different normal-form statement for the matrix
witness, since special-linear operations preserve the sign of the determinant. -/
noncomputable def gramSmithInvariantFactors (L : IntegralLattice V)
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (hdet : 0 < L.gramDet b) :
    Fin (Fintype.card ι) → ℤ :=
  (L.gramSmithWitness b hdet).choose_spec.choose_spec.choose

open Classical in
/-- The normalized invariant factors are positive. -/
theorem gramSmithInvariantFactors_pos (L : IntegralLattice V)
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (hdet : 0 < L.gramDet b) (i) :
    0 < L.gramSmithInvariantFactors b hdet i :=
  (L.gramSmithWitness b hdet).choose_spec.choose_spec.choose_spec.1 i

open Classical in
/-- The normalized invariant factors form a divisibility chain. -/
theorem gramSmithInvariantFactors_dvd (L : IntegralLattice V)
    {ι : Type v} [Fintype ι] (b : Basis ι ℤ L) (hdet : 0 < L.gramDet b)
    {i j : Fin (Fintype.card ι)} (hij : i ≤ j) :
    L.gramSmithInvariantFactors b hdet i ∣ L.gramSmithInvariantFactors b hdet j :=
  (L.gramSmithWitness b hdet).choose_spec.choose_spec.choose_spec.2.1 hij

open Classical in
/-- The Gram matrix is diagonalized by special-linear row and column operations using the
normalized invariant factors. -/
theorem exists_gramSmithInvariantFactors_smith_normal_form (L : IntegralLattice V)
    {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) (hdet : 0 < L.gramDet b) :
    ∃ P Q : Matrix.SpecialLinearGroup (Fin (Fintype.card ι)) ℤ,
      (P : Matrix _ _ ℤ) * L.gramMatrix (b.reindex (Fintype.equivFin ι)) *
          (Q : Matrix _ _ ℤ) =
        Matrix.diagonal (L.gramSmithInvariantFactors b hdet) :=
  ⟨(L.gramSmithWitness b hdet).choose,
    (L.gramSmithWitness b hdet).choose_spec.choose,
    (L.gramSmithWitness b hdet).choose_spec.choose_spec.choose_spec.2.2⟩

open Classical in
/-- The product of the normalized invariant factors is the positive Gram determinant. -/
theorem prod_gramSmithInvariantFactors_eq_gramDet (L : IntegralLattice V)
    {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) (hdet : 0 < L.gramDet b) :
    ∏ i, L.gramSmithInvariantFactors b hdet i = L.gramDet b := by
  obtain ⟨P, Q, hPQ⟩ := L.exists_gramSmithInvariantFactors_smith_normal_form b hdet
  have hdetPQ := congrArg Matrix.det hPQ
  simp only [Matrix.det_mul, Matrix.det_diagonal] at hdetPQ
  have hgram : (L.gramMatrix (b.reindex (Fintype.equivFin ι))).det =
      (L.gramMatrix b).det := by
    calc
      (L.gramMatrix (b.reindex (Fintype.equivFin ι))).det =
          L.gramDet (b.reindex (Fintype.equivFin ι)) :=
        (L.gramDet_def _).symm
      _ = L.gramDet b := L.gramDet_reindex b (Fintype.equivFin ι)
      _ = (L.gramMatrix b).det := L.gramDet_def _
  rw [hgram] at hdetPQ
  rw [L.gramDet_def]
  have hP : (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℤ).det = 1 := P.prop
  have hQ : (Q : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℤ).det = 1 := Q.prop
  simpa only [hP, hQ, one_mul, mul_one] using hdetPQ.symm

open Classical in
/-- For a positive-determinant Gram matrix, the product of the normalized invariant factors is the
lattice discriminant. -/
theorem prod_gramSmithInvariantFactors_eq_discriminant (L : IntegralLattice V)
    {ι : Type v} [Fintype ι]
    (b : Basis ι ℤ L) (hdet : 0 < L.gramDet b) :
    ∏ i, L.gramSmithInvariantFactors b hdet i = L.discriminant := by
  rw [L.prod_gramSmithInvariantFactors_eq_gramDet b hdet,
    L.discriminant_eq_natAbs_gramDet b]
  exact (Int.natAbs_of_nonneg (le_of_lt hdet)).symm

end TauCeti.IntegralLattice
