/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.VariationalFredholm
public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.RellichKondrachov

/-!
# The Fredholm alternative for the Dirichlet problem

Let `B` be the bounded coercive energy form of a divergence-form operator on `H¹₀(Ω)`.  Shifting
its mass coefficient by a constant `-κ` changes the weak equation to

`B(u, v) - κ ⟪u, v⟫_{L²} = ⟪f, v⟫_{L²}`.

When `Ω` is bounded, Rellich--Kondrachov makes the value inclusion
`H¹₀(Ω) → L²(Ω)` compact.  The abstract variational Fredholm alternative therefore gives the
classical dichotomy: either the homogeneous shifted problem has a nonzero solution, or every
`L²` forcing has a unique weak solution.  The homogeneous solution space is always finite
dimensional.

This is the compact-resolvent step of Lane D.18 of `TauCetiRoadmap/PDE/README.md`.  The unshifted
form `B` can itself contain bounded measurable principal, drift, and mass coefficients; only the
additional perturbation is the scalar mass shift.  This is the standard reduction of a Gårding
form to a coercive form by adding a sufficiently large constant.

## Main declarations

* `TauCeti.PDE.dirichletMassOperator`: the operator representing the `L²` mass form relative to
  the coercive energy form; `TauCeti.PDE.isCompactOperator_dirichletMassOperator` proves it compact
  on bounded domains.
* `TauCeti.PDE.IsWeakSolutionDirichletMassShift`: the weak equation with scalar mass shift.
* `TauCeti.PDE.finiteDimensional_ker_one_sub_smul_dirichletMassOperator`: finite dimensionality
  of its homogeneous solution space.
* `TauCeti.PDE.fredholmAlternative_isWeakSolutionDirichletMassShift`: the Fredholm dichotomy.

## References

Lane D, item 18 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential Equations*,
Section 6.2.3; D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Chapter 8, Theorem 8.3.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProduct InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-- Shortcut normed group instance on `H¹₀(Ω)`, needed by the inherited Hilbert structure. -/
noncomputable local instance instNormedAddCommGroupH1ZeroFredholm :
    NormedAddCommGroup (W1p0 mu Omega 2) := inferInstance

/-- Shortcut inner-product instance on `H¹₀(Ω)`. -/
noncomputable local instance instInnerProductSpaceH1ZeroFredholm :
    InnerProductSpace ℝ (W1p0 mu Omega 2) := inferInstance

/-- The Lax--Milgram operator representing the `L²` mass form on `H¹₀(Ω)`.  It is characterized
by `TauCeti.PDE.energyFormH1_dirichletMassOperator`. -/
def dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2 :=
  hcoercive.formPerturbationOperator W1p0.valueL

/-- The Dirichlet mass operator represents the `L²` inner product relative to the base energy
form. -/
@[simp]
theorem energyFormH1_dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (u v : W1p0 mu Omega 2) :
    energyFormH1 a b c (dirichletMassOperator hcoeff hcoercive u : W1p mu Omega 2)
        (v : W1p mu Omega 2) =
      ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [← energyFormH1L0_apply hcoeff, dirichletMassOperator,
    hcoercive.apply_formPerturbationOperator, W1p0.valueL_apply, W1p0.valueL_apply]

/-- On a bounded domain, the Dirichlet mass operator is compact by Rellich--Kondrachov. -/
theorem isCompactOperator_dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    IsCompactOperator (dirichletMassOperator hcoeff hcoercive) := by
  apply hcoercive.isCompactOperator_formPerturbationOperator
  exact W1p0.isCompactOperator_valueL (by simp) hOmega

/-- The weak Dirichlet equation obtained by shifting the base operator's mass coefficient by the
constant `-κ`.  It says `B(u,v) - κ⟪u,v⟫_{L²} = ⟪f,v⟫_{L²}` for every
`v ∈ H¹₀(Ω)`. -/
def IsWeakSolutionDirichletMassShift (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (kappa : ℝ) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) : Prop :=
  ∀ v : W1p0 mu Omega 2,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) -
        kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
      dirichletForcing f v

/-- Being a mass-shifted weak solution, written out as the integral identity
`B(u, v) - κ⟪u, v⟫_{L²} = ∫_Ω f v`. -/
@[simp]
theorem isWeakSolutionDirichletMassShift_iff (kappa : ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b c kappa f u ↔
      ∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) -
            kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ =
          ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [IsWeakSolutionDirichletMassShift, dirichletForcing_apply_eq_setIntegral]

/-- A zero mass shift recovers the unshifted Dirichlet weak equation.

This named specialization is not a simp lemma because
`isWeakSolutionDirichletMassShift_iff` already reduces its left-hand side; registering both
lemmas would violate the `simpNF` linter. -/
theorem isWeakSolutionDirichletMassShift_zero_iff (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b c 0 f u ↔ IsWeakSolutionDirichlet a b c f u := by
  rw [isWeakSolutionDirichletMassShift_iff, isWeakSolutionDirichlet_iff]
  simp only [zero_mul, sub_zero]

/-- The mass-shifted weak equation written as an operator equation on `H¹₀(Ω)`. -/
theorem isWeakSolutionDirichletMassShift_iff_operator_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (kappa : ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b c kappa f u ↔
      (1 - kappa • dirichletMassOperator hcoeff hcoercive :
          W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) u =
        weakSolutionDirichlet hcoeff hcoercive f := by
  have habstract :
      IsWeakSolutionDirichletMassShift a b c kappa f u ↔
        (1 - kappa • dirichletMassOperator hcoeff hcoercive :
            W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) u =
          hcoercive.solutionOfFunctional (dirichletForcing f) := by
    simpa only [dirichletMassOperator, IsWeakSolutionDirichletMassShift,
      energyFormH1L0_apply, W1p0.valueL_apply] using
      (hcoercive.one_sub_smul_formPerturbationOperator_apply_eq_iff_functional
        (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) kappa (dirichletForcing f) u).symm
  have hsolution :
      weakSolutionDirichlet hcoeff hcoercive f =
        hcoercive.solutionOfFunctional (dirichletForcing f) :=
    hcoercive.eq_solutionOfFunctional fun v => by
    rw [energyFormH1L0_apply, dirichletForcing_apply_eq_setIntegral]
    exact (isWeakSolutionDirichlet_iff f _).mp
      (isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f) v
  constructor
  · exact fun h => (habstract.mp h).trans hsolution.symm
  · exact fun h => habstract.mpr (h.trans hsolution)

/-- The homogeneous solution space of a scalar mass shift of a coercive Dirichlet form is finite
dimensional on a bounded domain. -/
theorem finiteDimensional_ker_one_sub_smul_dirichletMassOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (kappa : ℝ) :
    FiniteDimensional ℝ
      (LinearMap.ker
        ((1 - kappa • dirichletMassOperator hcoeff hcoercive :
          W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) :
            W1p0 mu Omega 2 →ₗ[ℝ] W1p0 mu Omega 2)) :=
  hcoercive.finiteDimensional_ker_one_sub_smul_formPerturbationOperator
    (W1p0.isCompactOperator_valueL (by simp) hOmega) kappa

/-- **The Fredholm alternative for the mass-shifted Dirichlet problem.**  On a bounded domain,
either the homogeneous shifted problem has a nonzero weak solution, or every `L²` forcing has a
unique weak solution. -/
theorem fredholmAlternative_isWeakSolutionDirichletMassShift
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (kappa : ℝ) :
    (∃ u : W1p0 mu Omega 2, u ≠ 0 ∧ IsWeakSolutionDirichletMassShift a b c kappa 0 u) ∨
      ∀ f : Lp ℝ 2 (mu.restrict Omega),
        ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichletMassShift a b c kappa f u := by
  rcases hcoercive.fredholmAlternative_formPerturbation
      (W1p0.isCompactOperator_valueL (by simp) hOmega) kappa with hkernel | hunique
  · left
    obtain ⟨u, hune, hu⟩ := hkernel
    refine ⟨u, hune, fun v => ?_⟩
    simpa only [energyFormH1L0_apply, W1p0.valueL_apply, dirichletForcing_apply, inner_zero_left]
      using hu v
  · right
    intro f
    obtain ⟨u, hu, huniq⟩ := hunique (dirichletForcing f)
    refine ⟨u, fun v => ?_, fun y hy => huniq y fun v => ?_⟩
    · simpa only [energyFormH1L0_apply, W1p0.valueL_apply] using hu v
    · simpa only [energyFormH1L0_apply, W1p0.valueL_apply] using hy v

end PDE

end TauCeti
