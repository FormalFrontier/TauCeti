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

* `TauCeti.IntegralLattice.a1`: the positive rank-one lattice with Gram matrix `[2]`.
* `TauCeti.IntegralLattice.negativeA1`: the negative rank-one lattice with Gram matrix `[-2]`.
* `TauCeti.IntegralLattice.hyperbolicPlane`: the hyperbolic plane with Gram matrix
  `!![0, 1; 1, 0]`.
* `TauCeti.IntegralLattice.affineA1`: the affine `A₁` lattice with Gram matrix
  `!![2, -2; -2, 2]`.
* `TauCeti.IntegralLattice.affineA1RadicalQuotientIsometry`: the isometry from the radical
  quotient of `affineA1` to `a1`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1 acceptance criteria.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Module

/-! ## The four Gram lattices -/

private def a1Matrix : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => 2

private def negativeA1Matrix : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => -2

private def hyperbolicPlaneMatrix : Matrix (Fin 2) (Fin 2) ℤ := fun i j =>
  if i.val = j.val then 0 else 1

private def affineA1Matrix : Matrix (Fin 2) (Fin 2) ℤ := fun i j =>
  if i.val = j.val then 2 else -2

/-- The positive rank-one root lattice `A₁`, with Gram matrix `[2]`. -/
noncomputable def a1 : IntegralLattice ℚ := by
  exact
  ofGramMatrix (Basis.singleton (Fin 1) ℚ) a1Matrix (by
    apply Matrix.IsSymm.ext
    intro i j
    rfl)

/-- The negative rank-one root lattice `⟨-2⟩`. -/
noncomputable def negativeA1 : IntegralLattice ℚ := by
  exact
  ofGramMatrix (Basis.singleton (Fin 1) ℚ) negativeA1Matrix (by
    apply Matrix.IsSymm.ext
    intro i j
    rfl)

/-- The hyperbolic plane, with Gram matrix `!![0, 1; 1, 0]`. -/
noncomputable def hyperbolicPlane : IntegralLattice (Fin 2 → ℚ) := by
  exact
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) hyperbolicPlaneMatrix (by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [hyperbolicPlaneMatrix, eq_comm])

/-- The degenerate affine `A₁` lattice, with Gram matrix `!![2, -2; -2, 2]`. -/
noncomputable def affineA1 : IntegralLattice (Fin 2 → ℚ) := by
  exact
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) affineA1Matrix (by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [affineA1Matrix, eq_comm])

/-- Membership in the `A₁` carrier means being an integer inside `ℚ`. -/
theorem mem_a1_carrier_iff (x : ℚ) :
    x ∈ a1.carrier ↔ ∃ z : ℤ, (z : ℚ) = x := by
  classical
  rw [a1, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Basis.singleton_repr]

/-- Membership in the negative `A₁` carrier means being an integer inside `ℚ`. -/
theorem mem_negativeA1_carrier_iff (x : ℚ) :
    x ∈ negativeA1.carrier ↔ ∃ z : ℤ, (z : ℚ) = x := by
  classical
  rw [negativeA1, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Basis.singleton_repr]

/-- A vector belongs to the hyperbolic-plane carrier exactly when both coordinates are integers. -/
theorem mem_hyperbolicPlane_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ hyperbolicPlane.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  classical
  rw [hyperbolicPlane, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

/-- A vector belongs to the affine `A₁` carrier exactly when both coordinates are integers. -/
theorem mem_affineA1_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ affineA1.carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  classical
  rw [affineA1, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

/-- The `A₁` form evaluates as twice the product of its two inputs. -/
@[simp]
theorem a1_form_apply (x y : ℚ) : a1.form x y = 2 * x * y := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  rw [a1]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply]
  simp only [a1Matrix, map_ofNat]
  simp [mul_comm]

/-- The negative `A₁` form evaluates as negative twice the product of its two inputs. -/
@[simp]
theorem negativeA1_form_apply (x y : ℚ) : negativeA1.form x y = -2 * x * y := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  rw [negativeA1]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply]
  simp only [negativeA1Matrix, map_neg, map_ofNat]
  simp [mul_comm]

/-- The hyperbolic-plane form pairs opposite coordinates. -/
@[simp]
theorem hyperbolicPlane_form_apply (x y : Fin 2 → ℚ) :
    hyperbolicPlane.form x y = x 0 * y 1 + x 1 * y 0 := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [hyperbolicPlane]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp [Fin.sum_univ_two, hyperbolicPlaneMatrix]

/-- The affine `A₁` form is twice the product of the coordinate differences. -/
@[simp]
theorem affineA1_form_apply (x y : Fin 2 → ℚ) :
    affineA1.form x y = 2 * (x 0 - x 1) * (y 0 - y 1) := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [affineA1]
  rw [ofGramMatrix_form]
  rw [Matrix.toBilin_apply]
  simp [Fin.sum_univ_two, affineA1Matrix]
  ring

/-! ## Norms and arithmetic invariants -/

/-- The norm on the positive rank-one lattice is twice a square. -/
@[simp]
theorem a1_norm_apply (x : ℚ) : a1.norm x = 2 * x ^ 2 := by
  rw [norm_apply, a1_form_apply]
  ring

/-- The norm on the negative rank-one lattice is negative twice a square. -/
@[simp]
theorem negativeA1_norm_apply (x : ℚ) : negativeA1.norm x = -2 * x ^ 2 := by
  rw [norm_apply, negativeA1_form_apply]
  ring

/-- The norm on the hyperbolic plane is twice the product of its coordinates. -/
@[simp]
theorem hyperbolicPlane_norm_apply (x : Fin 2 → ℚ) :
    hyperbolicPlane.norm x = 2 * x 0 * x 1 := by
  rw [norm_apply, hyperbolicPlane_form_apply]
  ring

/-- The norm on the affine `A₁` lattice is twice the square of the coordinate difference. -/
@[simp]
theorem affineA1_norm_apply (x : Fin 2 → ℚ) :
    affineA1.norm x = 2 * (x 0 - x 1) ^ 2 := by
  rw [norm_apply, affineA1_form_apply]
  ring

/-- The positive rank-one lattice is even. -/
theorem isEven_a1 : a1.IsEven := by
  rw [a1, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨1, by simp [a1Matrix]⟩

/-- The negative rank-one lattice is even. -/
theorem isEven_negativeA1 : negativeA1.IsEven := by
  rw [negativeA1, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨-1, by simp [negativeA1Matrix]⟩

/-- The hyperbolic plane is even. -/
theorem isEven_hyperbolicPlane : hyperbolicPlane.IsEven := by
  rw [hyperbolicPlane, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨0, by simp [hyperbolicPlaneMatrix]⟩

/-- The affine `A₁` lattice is even. -/
theorem isEven_affineA1 : affineA1.IsEven := by
  rw [affineA1, isEven_ofGramMatrix_iff]
  intro i
  exact ⟨1, by simp [affineA1Matrix]⟩

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
theorem affineA1_determinant : affineA1.determinant = 0 := by
  rw [affineA1, determinant_ofGramMatrix]
  simp [Matrix.det_fin_two, affineA1Matrix]

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
theorem isNegDef_negativeA1 : negativeA1.IsNegDef := by
  rw [negativeA1.isNegDef_iff]
  intro x hx
  rw [negativeA1_form_apply]
  nlinarith [sq_pos_of_ne_zero hx]

/-- The negative rank-one root lattice has signature `(0, 0, 1)`. -/
@[simp]
theorem negativeA1_signature : negativeA1.signature = (0, 0, 1) := by
  have hvanish := negativeA1.isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero.mp
    isNegDef_negativeA1
  have hsum := negativeA1.signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-- The affine `A₁` lattice is positive-semidefinite. -/
theorem isPosSemidef_affineA1 : affineA1.IsPosSemidef := by
  rw [affineA1.isPosSemidef_iff]
  intro x
  rw [affineA1_form_apply]
  nlinarith [sq_nonneg (x 0 - x 1)]

/-- The affine `A₁` lattice is degenerate. -/
theorem isDegenerate_affineA1 : affineA1.IsDegenerate := by
  rw [affineA1.isDegenerate_iff_not_nondegenerate]
  intro h
  exact affineA1.determinant_ne_zero_iff.mpr h affineA1_determinant

/-- The affine `A₁` lattice has signature `(1, 1, 0)`. -/
@[simp]
theorem affineA1_signature : affineA1.signature = (1, 1, 0) := by
  have hneg : affineA1.sigNeg = 0 :=
    affineA1.isPosSemidef_iff_sigNeg_eq_zero.mp isPosSemidef_affineA1
  have hnull : 0 < affineA1.sigNull :=
    affineA1.isDegenerate_iff_sigNull_pos.mp isDegenerate_affineA1
  have hpos : 0 < affineA1.sigPos := by
    by_contra h
    have hzero : affineA1.sigPos = 0 := by omega
    have hnegsemi := affineA1.isNegSemidef_iff_sigPos_eq_zero.mpr hzero
    rw [affineA1.isNegSemidef_iff] at hnegsemi
    have := hnegsemi ![1, 0]
    norm_num at this
  have hsum := affineA1.signature_sum_eq_finrank
  norm_num [Module.finrank_pi_fintype] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-! ## The affine radical quotient -/

/-- The coordinate difference map used to identify the affine `A₁` quotient. -/
def affineA1Difference : (Fin 2 → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0 -
    LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 1

/-- The affine coordinate difference map sends `x` to `x₀ - x₁`. -/
@[simp]
theorem affineA1Difference_apply (x : Fin 2 → ℚ) :
    affineA1Difference x = x 0 - x 1 := by
  simp [affineA1Difference]

/-- The radical of affine `A₁` is the kernel of the coordinate difference. -/
theorem affineA1_radical_eq_ker :
    affineA1.radical = LinearMap.ker affineA1Difference := by
  ext x
  rw [affineA1.mem_radical_iff, LinearMap.mem_ker]
  constructor
  · intro hx
    have h := hx ![1, 0]
    simp only [affineA1_form_apply] at h
    norm_num at h ⊢
    exact h
  · intro hx y
    simp only [affineA1Difference_apply] at hx
    rw [affineA1_form_apply, hx]
    ring

/-- The coordinate difference map is onto. -/
theorem affineA1Difference_surjective : Function.Surjective affineA1Difference := by
  intro x
  refine ⟨![x, 0], ?_⟩
  simp

/-- The rational radical quotient of affine `A₁`, expressed by coordinate difference. -/
noncomputable def affineA1QuotientEquiv :
    ((Fin 2 → ℚ) ⧸ affineA1.radical) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq affineA1.radical (LinearMap.ker affineA1Difference)
      affineA1_radical_eq_ker).trans
    (affineA1Difference.quotKerEquivOfSurjective affineA1Difference_surjective)

/-- The quotient equivalence acts on representatives by coordinate difference. -/
@[simp]
theorem affineA1QuotientEquiv_mk (x : Fin 2 → ℚ) :
    affineA1QuotientEquiv (Submodule.Quotient.mk x) = x 0 - x 1 := by
  simp [affineA1QuotientEquiv]

private theorem affineA1Difference_mem_carrier {x : Fin 2 → ℚ}
    (hx : x ∈ affineA1.carrier) : affineA1Difference x ∈ a1.carrier := by
  rw [mem_affineA1_carrier_iff] at hx
  rw [mem_a1_carrier_iff]
  obtain ⟨z₀, hz₀⟩ := hx 0
  obtain ⟨z₁, hz₁⟩ := hx 1
  refine ⟨z₀ - z₁, ?_⟩
  simp only [Int.cast_sub, affineA1Difference_apply]
  rw [hz₀, hz₁]

private def affineA1Section : ℚ →ₗ[ℚ] (Fin 2 → ℚ) :=
  LinearMap.single ℚ (fun _ : Fin 2 ↦ ℚ) 0

@[simp]
private theorem affineA1Section_apply (x : ℚ) : affineA1Section x = ![x, 0] := by
  ext i
  fin_cases i <;> simp [affineA1Section]

private theorem affineA1Section_mem_carrier {x : ℚ} (hx : x ∈ a1.carrier) :
    affineA1Section x ∈ affineA1.carrier := by
  rw [mem_a1_carrier_iff] at hx
  rw [mem_affineA1_carrier_iff]
  obtain ⟨z, hz⟩ := hx
  intro i
  fin_cases i
  · exact ⟨z, by simpa using hz⟩
  · exact ⟨0, by simp⟩

/-- The radical quotient of affine `A₁` is isometric, as an integral lattice, to `A₁`. -/
noncomputable def affineA1RadicalQuotientIsometry :
    Isometry affineA1.radicalQuotient a1 where
  toIsometryEquiv :=
    { toLinearEquiv := affineA1QuotientEquiv
      map_app' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            calc
              _ = a1.form (affineA1QuotientEquiv (Submodule.Quotient.mk x))
                  (affineA1QuotientEquiv (Submodule.Quotient.mk y)) := rfl
              _ = a1.form (x 0 - x 1) (y 0 - y 1) := by
                rw [affineA1QuotientEquiv_mk, affineA1QuotientEquiv_mk]
              _ = affineA1.form x y := by
                rw [a1_form_apply, affineA1_form_apply]
              _ = affineA1.radicalQuotient.form (Submodule.Quotient.mk x)
                  (Submodule.Quotient.mk y) := by
                rw [radicalQuotient_form, radicalQuotientForm_mk] }
  map_carrier := by
    ext y
    constructor
    · rw [Submodule.mem_map]
      rintro ⟨q, hq, rfl⟩
      rw [radicalQuotient_carrier, mem_radicalQuotientCarrier_iff] at hq
      obtain ⟨x, hx, rfl⟩ := hq
      simpa using affineA1Difference_mem_carrier hx
    · intro hy
      rw [Submodule.mem_map]
      refine ⟨Submodule.Quotient.mk (affineA1Section y), ?_, ?_⟩
      · rw [radicalQuotient_carrier, mem_radicalQuotientCarrier_iff]
        exact ⟨affineA1Section y, affineA1Section_mem_carrier hy, rfl⟩
      · simp

/-- The affine radical-quotient isometry acts on representatives by coordinate difference. -/
@[simp]
theorem affineA1RadicalQuotientIsometry_mk (x : Fin 2 → ℚ) :
    affineA1RadicalQuotientIsometry (Submodule.Quotient.mk x) = x 0 - x 1 := by
  exact affineA1QuotientEquiv_mk x

/-- The inverse affine radical-quotient isometry sends `y` to the class of `![y, 0]`. -/
@[simp]
theorem affineA1RadicalQuotientIsometry_symm_apply (y : ℚ) :
    affineA1RadicalQuotientIsometry.symm y = Submodule.Quotient.mk ![y, 0] := by
  apply affineA1RadicalQuotientIsometry.injective
  simp

end IntegralLattice

end TauCeti
