/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry
public import TauCeti.LinearAlgebra.IntegralLattice.RadicalQuotient

/-!
# Basic examples of integral lattices

This file supplies the three acceptance examples from Layer 1 of the integral-lattices roadmap.
The hyperbolic plane is even, unimodular, and indefinite of signature `(1, 0, 1)`; the negative
rank-one root lattice has signature `(0, 0, 1)`; and the affine `A₁` lattice is even,
positive-semidefinite, and degenerate of signature `(1, 1, 0)`.  The last example is not merely
identified by its signature: its radical quotient is exhibited isometrically as the positive
rank-one `A₁` lattice.

All four lattices are constructed with `TauCeti.IntegralLattice.ofGramMatrix`, so their carriers
are genuine full `ℤ`-lattices in their displayed rational ambient spaces.  The quotient
identification uses the coordinate difference `(x₀ - x₁)`, whose kernel is exactly the radical of
the affine form.

## Main definitions

* `TauCeti.IntegralLattice.aOne`: the positive rank-one lattice with Gram matrix `[2]`.
* `TauCeti.IntegralLattice.negativeAOne`: the negative rank-one lattice with Gram matrix `[-2]`.
* `TauCeti.IntegralLattice.hyperbolicPlane`: the hyperbolic plane with Gram matrix
  `!![0, 1; 1, 0]`.
* `TauCeti.IntegralLattice.affineAOne`: the affine `A₁` lattice with Gram matrix
  `!![2, -2; -2, 2]`.
* `TauCeti.IntegralLattice.affineAOneRadicalQuotientIsometry`: the isometry from the radical
  quotient of `affineAOne` to `aOne`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1 acceptance criteria.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Module

/-! ## The four Gram lattices -/

private def aOneMatrix : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => 2

private def negativeAOneMatrix : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => -2

private def hyperbolicPlaneMatrix : Matrix (Fin 2) (Fin 2) ℤ := fun i j =>
  if i.val = j.val then 0 else 1

private def affineAOneMatrix : Matrix (Fin 2) (Fin 2) ℤ := fun i j =>
  if i.val = j.val then 2 else -2

/-- The positive rank-one root lattice `A₁`, with Gram matrix `[2]`. -/
noncomputable def aOne : IntegralLattice ℚ := by
  exact
  ofGramMatrix (Basis.singleton (Fin 1) ℚ) aOneMatrix (by
    change aOneMatrix.transpose = aOneMatrix
    ext i j
    rfl)

/-- The negative rank-one root lattice `⟨-2⟩`. -/
noncomputable def negativeAOne : IntegralLattice ℚ := by
  exact
  ofGramMatrix (Basis.singleton (Fin 1) ℚ) negativeAOneMatrix (by
    change negativeAOneMatrix.transpose = negativeAOneMatrix
    ext i j
    rfl)

/-- The hyperbolic plane, with Gram matrix `!![0, 1; 1, 0]`. -/
noncomputable def hyperbolicPlane : IntegralLattice (Fin 2 → ℚ) := by
  exact
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) hyperbolicPlaneMatrix (by
    change hyperbolicPlaneMatrix.transpose = hyperbolicPlaneMatrix
    ext i j
    simp only [hyperbolicPlaneMatrix, Matrix.transpose_apply, eq_comm])

/-- The degenerate affine `A₁` lattice, with Gram matrix `!![2, -2; -2, 2]`. -/
noncomputable def affineAOne : IntegralLattice (Fin 2 → ℚ) := by
  exact
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) affineAOneMatrix (by
    change affineAOneMatrix.transpose = affineAOneMatrix
    ext i j
    simp only [affineAOneMatrix, Matrix.transpose_apply, eq_comm])

@[simp]
theorem aOne_form_apply (x y : ℚ) : aOne.form x y = 2 * x * y := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  rw [aOne]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply]
  simp only [aOneMatrix, map_ofNat]
  simp [mul_comm]

@[simp]
theorem negativeAOne_form_apply (x y : ℚ) : negativeAOne.form x y = -2 * x * y := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  rw [negativeAOne]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply]
  simp only [negativeAOneMatrix, map_neg, map_ofNat]
  simp [mul_comm]

@[simp]
theorem hyperbolicPlane_form_apply (x y : Fin 2 → ℚ) :
    hyperbolicPlane.form x y = x 0 * y 1 + x 1 * y 0 := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [hyperbolicPlane]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp [Fin.sum_univ_two, hyperbolicPlaneMatrix]

@[simp]
theorem affineAOne_form_apply (x y : Fin 2 → ℚ) :
    affineAOne.form x y = 2 * (x 0 - x 1) * (y 0 - y 1) := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [affineAOne]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp [Fin.sum_univ_two, affineAOneMatrix]
  ring

/-! ## Norms and arithmetic invariants -/

/-- The norm on the positive rank-one lattice is twice a square. -/
@[simp]
theorem aOne_norm_apply (x : ℚ) : aOne.norm x = 2 * x ^ 2 := by
  rw [norm_apply, aOne_form_apply]
  ring

/-- The norm on the negative rank-one lattice is negative twice a square. -/
@[simp]
theorem negativeAOne_norm_apply (x : ℚ) : negativeAOne.norm x = -2 * x ^ 2 := by
  rw [norm_apply, negativeAOne_form_apply]
  ring

/-- The norm on the hyperbolic plane is twice the product of its coordinates. -/
@[simp]
theorem hyperbolicPlane_norm_apply (x : Fin 2 → ℚ) :
    hyperbolicPlane.norm x = 2 * x 0 * x 1 := by
  rw [norm_apply, hyperbolicPlane_form_apply]
  ring

/-- The norm on the affine `A₁` lattice is twice the square of the coordinate difference. -/
@[simp]
theorem affineAOne_norm_apply (x : Fin 2 → ℚ) :
    affineAOne.norm x = 2 * (x 0 - x 1) ^ 2 := by
  rw [norm_apply, affineAOne_form_apply]
  ring

/-- The positive rank-one lattice is even. -/
theorem isEven_aOne : aOne.IsEven := by
  rw [aOne, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨1, by simp [aOneMatrix]⟩

/-- The negative rank-one lattice is even. -/
theorem isEven_negativeAOne : negativeAOne.IsEven := by
  rw [negativeAOne, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨-1, by simp [negativeAOneMatrix]⟩

/-- The hyperbolic plane is even. -/
theorem isEven_hyperbolicPlane : hyperbolicPlane.IsEven := by
  rw [hyperbolicPlane, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨0, by simp [hyperbolicPlaneMatrix]⟩

/-- The affine `A₁` lattice is even. -/
theorem isEven_affineAOne : affineAOne.IsEven := by
  rw [affineAOne, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨1, by simp [affineAOneMatrix]⟩

/-- The signed determinant of the hyperbolic plane is `-1`. -/
@[simp]
theorem hyperbolicPlane_determinant : hyperbolicPlane.determinant = -1 := by
  rw [hyperbolicPlane, determinant_ofGramMatrix]
  simp [Matrix.det_fin_two, hyperbolicPlaneMatrix]

/-- The hyperbolic plane has discriminant one, the determinant form of unimodularity. -/
@[simp]
theorem hyperbolicPlane_discriminant : hyperbolicPlane.discriminant = 1 := by
  rw [hyperbolicPlane, discriminant_ofGramMatrix]
  simp [Matrix.det_fin_two, hyperbolicPlaneMatrix]

/-- The signed determinant of the affine `A₁` lattice vanishes. -/
@[simp]
theorem affineAOne_determinant : affineAOne.determinant = 0 := by
  rw [affineAOne, determinant_ofGramMatrix]
  simp [Matrix.det_fin_two, affineAOneMatrix]

/-! ## Definiteness and signatures -/

/-- The hyperbolic plane is indefinite. -/
theorem isIndefinite_hyperbolicPlane : hyperbolicPlane.IsIndefinite := by
  rw [hyperbolicPlane.isIndefinite_iff_exists_pos_and_exists_neg]
  constructor
  · refine ⟨![1, 1], ?_⟩
    norm_num
  · refine ⟨![1, -1], ?_⟩
    norm_num

/-- The hyperbolic plane has signature `(1, 0, 1)`. -/
@[simp]
theorem hyperbolicPlane_signature : hyperbolicPlane.signature = (1, 0, 1) := by
  have hnull : hyperbolicPlane.sigNull = 0 := by
    have hnondegenerate : hyperbolicPlane.form.Nondegenerate :=
      hyperbolicPlane.determinant_ne_zero_iff.mp (by simp)
    by_contra h
    have hdegenerate := hyperbolicPlane.isDegenerate_iff_sigNull_pos.mpr (Nat.pos_of_ne_zero h)
    exact hyperbolicPlane.isDegenerate_iff_not_nondegenerate.mp hdegenerate hnondegenerate
  have hsum := hyperbolicPlane.signature_sum_eq_finrank
  have hindef := isIndefinite_hyperbolicPlane
  have hnotsemidef := hyperbolicPlane.isIndefinite_iff_not_semidef.mp hindef
  have hposne : hyperbolicPlane.sigPos ≠ 0 := fun h ↦
    hnotsemidef.2 (hyperbolicPlane.isNegSemidef_iff_sigPos_eq_zero.mpr h)
  have hnegne : hyperbolicPlane.sigNeg ≠ 0 := fun h ↦
    hnotsemidef.1 (hyperbolicPlane.isPosSemidef_iff_sigNeg_eq_zero.mpr h)
  norm_num [Module.finrank_pi_fintype] at hsum
  have hpos : hyperbolicPlane.sigPos = 1 := by omega
  have hneg : hyperbolicPlane.sigNeg = 1 := by omega
  simp [signature, hpos, hnull, hneg]

/-- The negative rank-one root lattice is negative-definite. -/
theorem isNegDef_negativeAOne : negativeAOne.IsNegDef := by
  rw [negativeAOne.isNegDef_iff]
  intro x hx
  rw [negativeAOne_form_apply]
  nlinarith [sq_pos_of_ne_zero hx]

/-- The negative rank-one root lattice has signature `(0, 0, 1)`. -/
@[simp]
theorem negativeAOne_signature : negativeAOne.signature = (0, 0, 1) := by
  have hvanish := negativeAOne.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero.mp
    isNegDef_negativeAOne
  have hsum := negativeAOne.signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-- The affine `A₁` lattice is positive-semidefinite. -/
theorem isPosSemidef_affineAOne : affineAOne.IsPosSemidef := by
  rw [affineAOne.isPosSemidef_iff]
  intro x
  rw [affineAOne_form_apply]
  nlinarith [sq_nonneg (x 0 - x 1)]

/-- The affine `A₁` lattice is degenerate. -/
theorem isDegenerate_affineAOne : affineAOne.IsDegenerate := by
  rw [affineAOne.isDegenerate_iff_not_nondegenerate]
  intro h
  exact affineAOne.determinant_ne_zero_iff.mpr h affineAOne_determinant

/-- The affine `A₁` lattice has signature `(1, 1, 0)`. -/
@[simp]
theorem affineAOne_signature : affineAOne.signature = (1, 1, 0) := by
  have hneg : affineAOne.sigNeg = 0 :=
    affineAOne.isPosSemidef_iff_sigNeg_eq_zero.mp isPosSemidef_affineAOne
  have hnull : 0 < affineAOne.sigNull :=
    affineAOne.isDegenerate_iff_sigNull_pos.mp isDegenerate_affineAOne
  have hpos : 0 < affineAOne.sigPos := by
    by_contra h
    have hzero : affineAOne.sigPos = 0 := by omega
    have hnegsemi := affineAOne.isNegSemidef_iff_sigPos_eq_zero.mpr hzero
    rw [affineAOne.isNegSemidef_iff] at hnegsemi
    have := hnegsemi ![1, 0]
    norm_num at this
  have hsum := affineAOne.signature_sum_eq_finrank
  norm_num [Module.finrank_pi_fintype] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-! ## The affine radical quotient -/

/-- The coordinate difference map used to identify the affine `A₁` quotient. -/
def affineAOneDifference : (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0 -
    LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 1

/-- The affine coordinate difference map sends `x` to `x₀ - x₁`. -/
@[simp]
theorem affineAOneDifference_apply (x : Fin 2 → ℚ) :
    affineAOneDifference x = x 0 - x 1 := by
  simp [affineAOneDifference]

/-- The radical of affine `A₁` is the kernel of the coordinate difference. -/
theorem affineAOne_radical_eq_ker :
    affineAOne.radical = LinearMap.ker affineAOneDifference := by
  ext x
  rw [affineAOne.mem_radical_iff, LinearMap.mem_ker]
  constructor
  · intro hx
    have h := hx ![1, 0]
    simp only [affineAOne_form_apply] at h
    norm_num at h ⊢
    exact h
  · intro hx y
    simp only [affineAOneDifference_apply] at hx
    rw [affineAOne_form_apply, hx]
    ring

/-- The coordinate difference map is onto. -/
theorem affineAOneDifference_surjective : Function.Surjective affineAOneDifference := by
  intro x
  refine ⟨![x, 0], ?_⟩
  simp

/-- The rational radical quotient of affine `A₁`, expressed by coordinate difference. -/
noncomputable def affineAOneQuotientEquiv :
    ((Fin 2 → ℚ) ⧸ affineAOne.radical) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq affineAOne.radical (LinearMap.ker affineAOneDifference)
      affineAOne_radical_eq_ker).trans
    (affineAOneDifference.quotKerEquivOfSurjective affineAOneDifference_surjective)

/-- The quotient equivalence acts on representatives by coordinate difference. -/
@[simp]
theorem affineAOneQuotientEquiv_mk (x : Fin 2 → ℚ) :
    affineAOneQuotientEquiv (Submodule.Quotient.mk x) = x 0 - x 1 := by
  simp [affineAOneQuotientEquiv]

private theorem one_mem_aOne_carrier : (1 : ℚ) ∈ aOne.carrier := by
  classical
  rw [aOne, ofGramMatrix_carrier]
  apply Submodule.subset_span
  exact ⟨0, by simp⟩

private theorem firstBasis_mem_affineAOne_carrier :
    ![1, 0] ∈ affineAOne.carrier := by
  classical
  rw [affineAOne, ofGramMatrix_carrier]
  apply Submodule.subset_span
  exact ⟨0, by ext i; fin_cases i <;> simp⟩

private theorem affineAOneDifference_mem_carrier {x : Fin 2 → ℚ}
    (hx : x ∈ affineAOne.carrier) : affineAOneDifference x ∈ aOne.carrier := by
  classical
  rw [affineAOne, ofGramMatrix_carrier] at hx
  have hle : Submodule.span ℤ (Set.range (Pi.basisFun ℚ (Fin 2))) ≤
      aOne.carrier.comap (affineAOneDifference.restrictScalars ℤ) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa [affineAOneDifference] using one_mem_aOne_carrier
    · simpa [affineAOneDifference] using aOne.carrier.neg_mem one_mem_aOne_carrier
  exact hle hx

private def affineAOneSection : ℚ →ₗ[ℚ] (Fin 2 → ℚ) :=
  LinearMap.single ℚ (fun _ : Fin 2 ↦ ℚ) 0

@[simp]
private theorem affineAOneSection_apply (x : ℚ) : affineAOneSection x = ![x, 0] := by
  ext i
  fin_cases i <;> simp [affineAOneSection]

private theorem affineAOneSection_mem_carrier {x : ℚ} (hx : x ∈ aOne.carrier) :
    affineAOneSection x ∈ affineAOne.carrier := by
  classical
  rw [aOne, ofGramMatrix_carrier] at hx
  have hle : Submodule.span ℤ (Set.range (Basis.singleton (Fin 1) ℚ)) ≤
      affineAOne.carrier.comap (affineAOneSection.restrictScalars ℤ) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    simpa using firstBasis_mem_affineAOne_carrier
  exact hle hx

/-- The radical quotient of affine `A₁` is isometric, as an integral lattice, to `A₁`. -/
noncomputable def affineAOneRadicalQuotientIsometry :
    Isometry affineAOne.radicalQuotient aOne where
  toIsometryEquiv :=
    { toLinearEquiv := affineAOneQuotientEquiv
      map_app' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            change aOne.form (affineAOneQuotientEquiv (Submodule.Quotient.mk x))
                (affineAOneQuotientEquiv (Submodule.Quotient.mk y)) = _
            rw [affineAOneQuotientEquiv_mk, affineAOneQuotientEquiv_mk,
              aOne_form_apply, radicalQuotient_form, radicalQuotientForm_mk,
              affineAOne_form_apply] }
  map_carrier := by
    ext y
    constructor
    · rw [Submodule.mem_map]
      rintro ⟨q, hq, rfl⟩
      rw [radicalQuotient_carrier, mem_radicalQuotientCarrier_iff] at hq
      obtain ⟨x, hx, rfl⟩ := hq
      simpa using affineAOneDifference_mem_carrier hx
    · intro hy
      rw [Submodule.mem_map]
      refine ⟨Submodule.Quotient.mk (affineAOneSection y), ?_, ?_⟩
      · rw [radicalQuotient_carrier, mem_radicalQuotientCarrier_iff]
        exact ⟨affineAOneSection y, affineAOneSection_mem_carrier hy, rfl⟩
      · simp

/-- The affine `A₁` radical quotient has the positive rank-one norm under its canonical
identification. -/
@[simp]
theorem affineAOneRadicalQuotientIsometry_norm (x : (Fin 2 → ℚ) ⧸ affineAOne.radical) :
    aOne.norm (affineAOneRadicalQuotientIsometry x) = affineAOne.radicalQuotient.norm x := by
  rw [norm_apply, norm_apply, Isometry.map_app]

end IntegralLattice

end TauCeti
