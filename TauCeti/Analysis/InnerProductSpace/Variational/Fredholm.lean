/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.Normed.Operator.Compact.RieszTheory

/-!
# The Fredholm alternative for compact perturbations of coercive forms

Let `B` be a bounded coercive bilinear form on a real Hilbert space `V`, and let
`J : V → H` be a continuous linear map to another real Hilbert space.  Lax--Milgram turns the
quadratic form

`(u, v) ↦ ⟪J u, J v⟫`

into an operator `K : V → V`, characterized by `B (K u) v = ⟪J u, J v⟫`.  When `J` is compact,
so is `K`.  Mathlib's Fredholm alternative for compact operators can therefore be applied to
`1 - κK`: either the homogeneous compactly perturbed variational problem has a nonzero solution,
or every represented forcing has a unique solution.  Its kernel is finite dimensional in either
case.

This is the abstract functional-analytic assembly used by Lane D.18 of the PDE roadmap.  In that
application `V = H¹₀(Ω)`, `H = L²(Ω)`, and `J` is the compact Rellich inclusion.

## Main declarations

* `IsCoercive.formPerturbationOperator`: the Lax--Milgram operator representing
  `(u, v) ↦ ⟪J u, J v⟫`.
* `IsCoercive.isCompactOperator_formPerturbationOperator`: compactness when `J` is compact.
* `IsCoercive.finiteDimensional_ker_one_sub_smul_formPerturbationOperator`: finite dimensionality
  of the homogeneous solution space.
* `IsCoercive.fredholmAlternative_formPerturbation`: the variational Fredholm alternative.

The construction consumes Mathlib's `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` and
the Riesz--Schauder kernel theorem
`TauCeti.IsCompactOperator.finiteDimensional_ker_one_sub`.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.2.3; J. B. Conway, *A Course in
Functional Analysis*, Chapter VI, Section 5.
-/

public section

noncomputable section

open Module
open scoped InnerProduct InnerProductSpace

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The operator representing the form `(u, v) ↦ ⟪J u, J v⟫` relative to a coercive form `B`.
It is characterized by `IsCoercive.apply_formPerturbationOperator` without unfolding. -/
def formPerturbationOperator (hB : IsCoercive B) (J : V →L[ℝ] H) : V →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp ((J†).comp J)

/-- The form perturbation operator is the inverse Lax--Milgram operator applied to `J†J`. -/
theorem formPerturbationOperator_apply (hB : IsCoercive B) (J : V →L[ℝ] H) (u : V) :
    hB.formPerturbationOperator J u = hB.solutionOfInner ((J†) (J u)) := by
  rw [formPerturbationOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, solutionOfInner_def]
  rfl

/-- Characterization of the form perturbation operator by its variational equation. -/
@[simp]
theorem apply_formPerturbationOperator (hB : IsCoercive B) (J : V →L[ℝ] H) (u v : V) :
    B (hB.formPerturbationOperator J u) v = ⟪J u, J v⟫_ℝ := by
  rw [formPerturbationOperator_apply, apply_solutionOfInner_eq_inner,
    ContinuousLinearMap.adjoint_inner_left]

/-- If the continuous linear map `J` is compact, so is the operator representing its
inner-product form. -/
theorem isCompactOperator_formPerturbationOperator (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) : IsCompactOperator (hB.formPerturbationOperator J) := by
  rw [formPerturbationOperator]
  exact (hJ.clm_comp (J†)).clm_comp
    hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap

/-- The compactly perturbed operator equation is equivalent to its variational formulation. -/
theorem one_sub_smul_formPerturbationOperator_apply_eq_iff (hB : IsCoercive B)
    (J : V →L[ℝ] H) (kappa : ℝ) (F u : V) :
    (1 - kappa • hB.formPerturbationOperator J : V →L[ℝ] V) u = hB.solutionOfInner F ↔
      ∀ v : V, B u v - kappa * ⟪J u, J v⟫_ℝ = ⟪F, v⟫_ℝ := by
  constructor
  · intro hu v
    have h := congrArg (fun w => B w v) hu
    simpa only [sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul, smul_eq_mul,
      apply_formPerturbationOperator, apply_solutionOfInner_eq_inner] using h
  · intro hu
    apply hB.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [continuousLinearEquivOfBilin_apply, continuousLinearEquivOfBilin_solutionOfInner]
    simpa only [sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul, smul_eq_mul,
      apply_formPerturbationOperator] using hu v

/-- The compactly perturbed operator equation with an arbitrary continuous functional is
equivalent to its variational formulation. -/
theorem one_sub_smul_formPerturbationOperator_apply_eq_iff_functional (hB : IsCoercive B)
    (J : V →L[ℝ] H) (kappa : ℝ) (ell : StrongDual ℝ V) (u : V) :
    (1 - kappa • hB.formPerturbationOperator J : V →L[ℝ] V) u =
        hB.solutionOfFunctional ell ↔
      ∀ v : V, B u v - kappa * ⟪J u, J v⟫_ℝ = ell v := by
  rw [solutionOfFunctional_def,
    one_sub_smul_formPerturbationOperator_apply_eq_iff]
  simp only [InnerProductSpace.toDual_symm_apply]

/-- The homogeneous solution space of a compactly perturbed coercive variational problem is
finite dimensional. -/
theorem finiteDimensional_ker_one_sub_smul_formPerturbationOperator (hB : IsCoercive B)
    {J : V →L[ℝ] H} (hJ : IsCompactOperator J) (kappa : ℝ) :
    FiniteDimensional ℝ
      (LinearMap.ker
        ((1 - kappa • hB.formPerturbationOperator J : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
  exact TauCeti.IsCompactOperator.finiteDimensional_ker_one_sub
    ((hB.isCompactOperator_formPerturbationOperator hJ).smul kappa)

/-- **The variational Fredholm alternative.**  For a compact continuous linear map `J`, either the
homogeneous perturbation of `B` by `κ ⟪J ·, J ·⟫` has a nonzero solution, or every represented
forcing has a unique solution. -/
theorem fredholmAlternative_formPerturbation (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) (kappa : ℝ) :
    (∃ u : V, u ≠ 0 ∧ ∀ v : V, B u v - kappa * ⟪J u, J v⟫_ℝ = 0) ∨
      ∀ ell : StrongDual ℝ V, ∃! u : V,
        ∀ v : V, B u v - kappa * ⟪J u, J v⟫_ℝ = ell v := by
  let K : V →L[ℝ] V := kappa • hB.formPerturbationOperator J
  have hK : IsCompactOperator K :=
    (hB.isCompactOperator_formPerturbationOperator hJ).smul kappa
  rcases hK.hasEigenvalue_or_mem_resolventSet one_ne_zero with heigen | hresolvent
  · left
    obtain ⟨u, hu⟩ := heigen.exists_hasEigenvector
    refine ⟨u, hu.2, ?_⟩
    simpa using
      (hB.one_sub_smul_formPerturbationOperator_apply_eq_iff J kappa 0 u).mp (by
        have hKu : (kappa • hB.formPerturbationOperator J) u = u := by
          simpa only [K, one_smul, ContinuousLinearMap.coe_coe] using hu.apply_eq_smul
        rw [sub_apply, one_apply_eq_self, hKu, sub_self, solutionOfInner_def, map_zero])
  · right
    have hunit : IsUnit (1 - K : V →L[ℝ] V) := by
      simpa only [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, one_smul]
        using hresolvent
    have hbij : Function.Bijective (1 - K : V →L[ℝ] V) :=
      ContinuousLinearMap.isUnit_iff_bijective.mp hunit
    intro ell
    obtain ⟨u, hu, hunique⟩ := hbij.existsUnique (hB.solutionOfFunctional ell)
    refine ⟨u, ?_, fun y hy => hunique y ?_⟩
    · exact
        (hB.one_sub_smul_formPerturbationOperator_apply_eq_iff_functional J kappa ell u).mp <| by
        simpa only [K] using hu
    · exact
        (hB.one_sub_smul_formPerturbationOperator_apply_eq_iff_functional J kappa ell y).mpr hy

end IsCoercive
