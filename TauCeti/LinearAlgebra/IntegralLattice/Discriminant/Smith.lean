/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality

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
full-rank inclusion but does not normalize its diagonal coefficients into a divisibility chain;
the normalized invariant-factor statement is consequently later work.

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

end TauCeti.IntegralLattice
