/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh
public import TauCeti.Analysis.PDE.FredholmAlternative

/-!
# The Dirichlet spectrum of a divergence-form elliptic operator

For a divergence-form operator `L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u` on an open set
`Ω ⊆ ℝⁿ`, a real number `κ` is a **Dirichlet eigenvalue** when the homogeneous Dirichlet
problem `L u = κ u` in `Ω`, `u = 0` on `∂Ω`, has a nonzero weak solution: some
`u ∈ H¹₀(Ω)`, `u ≠ 0`, with

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹₀(Ω)`,

where `a` is the energy form of `L`.  This file develops that eigenvalue problem through the
**solution operator** `S : L²(Ω) → L²(Ω)`, which sends `f` to the value of the weak solution of
`L u = f`.

`S` is the inverse of `L` under the homogeneous boundary condition, and it is the object that
carries the spectral theory: it is compact for a bounded `Ω` because the inclusion
`H¹₀(Ω) → L²(Ω)` is (Rellich--Kondrachov), it is symmetric when the energy form is, and its
nonzero eigenvalues are exactly the reciprocals of the Dirichlet eigenvalues.  Mathlib's
spectral theorem for compact self-adjoint operators then applies, giving eigenvectors with dense
span in `L²(Ω)` and finite-dimensional eigenspaces at the nonzero eigenvalues; the eigenvalue `0`
is absent because the value map `H¹₀(Ω) → L²(Ω)` has dense range.  Assembling Hilbert bases of
the eigenspaces turns that density into an orthonormal basis of `L²(Ω)` of Dirichlet
eigenfunctions, in which the solution operator is diagonal.

## Hypotheses, and what each result needs

No regularity of `∂Ω` is used anywhere: the boundary condition is membership in `H¹₀(Ω)`, the
closure of `C_c^∞(Ω)`.  The hypotheses are carried separately and named at each statement.

* **Coercivity** of the energy form on `H¹₀(Ω)` is what makes the solution operator exist at
  all.  It also forces every Dirichlet eigenvalue to be *positive*, and quantitatively to be at
  least the coercivity constant, because the `L²` norm of a Sobolev jet is dominated by its
  graph norm.  For a domain inside a ball this is the explicit Poincaré constant of
  `TauCeti.PDE.UniformlyEllipticOn.mul_norm_sq_le_energyFormH1_self_of_subset_ball`, so the
  first Dirichlet eigenvalue is bounded below by the constant in the Poincaré inequality.
* **Boundedness** of `Ω` is what makes the solution operator compact, hence what gives
  finite-dimensional eigenspaces and the spectral theorem.  It is not needed for the eigenvalue
  bounds.
* **Symmetry** of the energy form is what makes the solution operator self-adjoint.  It is not
  an assumption on `Ω` either: with no drift and an almost everywhere symmetric principal
  coefficient it holds outright,
  by `TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`.
* **Dense range** of the value map `H¹₀(Ω) → L²(Ω)` rules out the eigenvalue `0` of the solution
  operator: the kernel of the solution operator is exactly the orthogonal complement of its
  range.  The density follows because the range contains all test functions and test functions
  are dense in `L²(Ω)`.

## The Fredholm alternative in eigenvalue language

Reading the Fredholm alternative for a scalar mass shift through this vocabulary gives the
familiar statement: if `κ` is *not* a Dirichlet eigenvalue, then `L u - κ u = f` has exactly one
weak solution for every `f ∈ L²(Ω)`
(`TauCeti.PDE.existsUnique_isWeakSolutionDirichletMassShift_of_not_isDirichletEigenvalue`).

## The variational characterization

The first Dirichlet eigenvalue is not only the least one: it is the minimum of the Rayleigh
quotient `a(u, u) / ‖u‖²_{L²(Ω)}` over `H¹₀(Ω)`, equivalently the largest constant `C` for which
the Poincaré-type inequality `C‖u‖²_{L²(Ω)} ≤ a(u, u)` holds.  The inequality itself needs
neither boundedness nor nonemptiness of `Ω`; boundedness together with nonemptiness makes the
minimum *attained*, through compactness of the solution operator and nonvanishing of the value
map.

## Main declarations

* `TauCeti.PDE.dirichletSolutionOperator`: the solution operator on `L²(Ω)`, with
  `TauCeti.PDE.dirichletSolutionOperator_apply` identifying it as the value of the weak
  solution, and `TauCeti.PDE.isCompactOperator_dirichletSolutionOperator`,
  `TauCeti.PDE.isSymmetric_dirichletSolutionOperator` and
  `TauCeti.PDE.inner_dirichletSolutionOperator_self_nonneg`.
* `TauCeti.PDE.IsDirichletEigenvalue`: the Dirichlet eigenvalue problem, with
  `TauCeti.PDE.isDirichletEigenvalue_iff_setIntegral` writing it as an integral identity and
  `TauCeti.PDE.isDirichletEigenvalue_iff_exists_isWeakSolutionDirichletMassShift` matching it
  with the mass-shifted weak equation.
* `TauCeti.PDE.firstDirichletEigenvalue` and `TauCeti.PDE.isDirichletEigenvalue_first`: the least
  Dirichlet eigenvalue and its attainment on a nonempty bounded domain.
* `TauCeti.PDE.pos_of_isDirichletEigenvalue` and `TauCeti.PDE.le_of_isDirichletEigenvalue`:
  every Dirichlet eigenvalue is positive, and at least the coercivity constant.
* `TauCeti.PDE.isLeast_rayleighQuotient_firstDirichletEigenvalue`: the Rayleigh principle, that
  the first Dirichlet eigenvalue is the minimum of `a(u, u) / ‖u‖²_{L²(Ω)}`, with its inequality
  half `TauCeti.PDE.firstDirichletEigenvalue_mul_norm_value_sq_le` and its reading as the optimal
  Poincaré constant `TauCeti.PDE.isGreatest_firstDirichletEigenvalue`.
* `TauCeti.PDE.isDirichletEigenvalue_iff_hasEigenvalue`: the reciprocal correspondence with the
  nonzero eigenvalues of the solution operator.
* `TauCeti.PDE.finiteDimensional_eigenspace_dirichletSolutionOperator` and
  `TauCeti.PDE.orthogonalComplement_iSup_eigenspaces_dirichletSolutionOperator_eq_bot`: the
  eigenspaces are finite dimensional and the eigenfunctions span a dense subspace of `L²(Ω)`.
* `TauCeti.PDE.exists_hilbertBasis_forall_isDirichletEigenvalue`: the Dirichlet eigenfunctions
  form an orthonormal basis of `L²(Ω)`, and the Dirichlet problem is solved in it by the
  eigenfunction expansion.
* `TauCeti.PDE.UniformlyEllipticOn.le_of_isDirichletEigenvalue_of_subset_ball` and
  `TauCeti.PDE.le_of_isDirichletEigenvalue_laplacian_of_subset_ball`: the explicit lower bound
  on the Dirichlet spectrum of a domain inside a ball, and its `-Δ` case
  `1/(2(4R² + 1)) ≤ κ`.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.5 (eigenvalues and eigenfunctions);
D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Chapter 8, Section 8.12; H. Brezis, *Functional Analysis, Sobolev Spaces and Partial
Differential Equations*, Section 9.8.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Module.End Set TopologicalSpace
open scoped ENNReal InnerProduct InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} {C : ℝ}

/-- Shortcut normed group instance on `H¹₀(Ω)`, needed by the inherited Hilbert structure. -/
noncomputable local instance instNormedAddCommGroupH1ZeroSpectrum :
    NormedAddCommGroup (W1p0 mu Omega 2) := inferInstance

/-- Shortcut inner-product instance on `H¹₀(Ω)`. -/
noncomputable local instance instInnerProductSpaceH1ZeroSpectrum :
    InnerProductSpace ℝ (W1p0 mu Omega 2) := inferInstance

/-! ### The solution operator on `L²(Ω)` -/

/-- **The solution operator of the Dirichlet problem**: the map sending `f ∈ L²(Ω)` to the
value of the unique weak solution of `L u = f` in `Ω`, `u = 0` on `∂Ω`.  It inverts the
Dirichlet problem, and it is the operator whose spectrum carries the Dirichlet eigenvalue
problem; `TauCeti.PDE.dirichletSolutionOperator_apply` identifies its value with the
Lax--Milgram solution. -/
def dirichletSolutionOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    Lp ℝ 2 (mu.restrict Omega) →L[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  hcoercive.formSolutionOperator W1p0.valueL

/-- The abstract solution map of the energy form along the value inclusion is the weak solution
of the Dirichlet problem. -/
theorem formSolutionMap_valueL_eq_weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    hcoercive.formSolutionMap W1p0.valueL f = weakSolutionDirichlet hcoeff hcoercive f := by
  refine (IsCoercive.eq_formSolutionMap hcoercive W1p0.valueL fun v => ?_).symm
  rw [energyFormH1L0_apply, W1p0.valueL_apply, ← dirichletForcing_apply f v,
    dirichletForcing_apply_eq_setIntegral]
  exact (isWeakSolutionDirichlet_iff f _).mp
    (isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f) v

/-- The solution operator returns the value component of the weak solution. -/
@[simp]
theorem dirichletSolutionOperator_apply
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    dirichletSolutionOperator hcoeff hcoercive f =
      W1p.value (weakSolutionDirichlet hcoeff hcoercive f : W1p mu Omega 2) := by
  rw [dirichletSolutionOperator, IsCoercive.formSolutionOperator_apply,
    formSolutionMap_valueL_eq_weakSolutionDirichlet hcoeff hcoercive f, W1p0.valueL_apply]

/-- **The solution operator is compact on a bounded domain**, by Rellich--Kondrachov. -/
theorem isCompactOperator_dirichletSolutionOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    IsCompactOperator (dirichletSolutionOperator hcoeff hcoercive) :=
  hcoercive.isCompactOperator_formSolutionOperator
    (W1p0.isCompactOperator_valueL (by simp) hOmega)

/-- **The solution operator is self-adjoint for a symmetric energy form.**  With no drift and an
almost everywhere symmetric principal coefficient the symmetry hypothesis is supplied by
`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`. -/
theorem isSymmetric_dirichletSolutionOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    LinearMap.IsSymmetric (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) := by
  rw [dirichletSolutionOperator]
  exact hcoercive.isSymmetric_formSolutionOperator
    (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) (energyFormH1L0_comm hcoeff hsymm)

/-- **The solution operator is positive semidefinite**: its quadratic form is the energy of the
solution it produces. -/
theorem inner_dirichletSolutionOperator_self_nonneg
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    0 ≤ ⟪f, dirichletSolutionOperator hcoeff hcoercive f⟫_ℝ :=
  hcoercive.inner_formSolutionOperator_self_nonneg W1p0.valueL f

/-! ### Dirichlet eigenvalues -/

/-- **A Dirichlet eigenvalue** of the divergence-form operator
`L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u` on `Ω`: a real number `κ` for which the homogeneous
Dirichlet problem `L u = κ u` has a nonzero weak solution `u ∈ H¹₀(Ω)`, that is

`a(u, v) = κ ∫_Ω u v` for every `v ∈ H¹₀(Ω)`.

The boundary condition is membership in `H¹₀(Ω)`, so no regularity of `∂Ω` enters, and nothing
is assumed about the coefficients here; each theorem below names the hypotheses it uses.
`TauCeti.PDE.isDirichletEigenvalue_iff_setIntegral` writes the condition out as an integral
identity. -/
def IsDirichletEigenvalue (mu : Measure (EuclideanSpace ℝ ι)) [mu.IsAddHaarMeasure]
    (Omega : Opens (EuclideanSpace ℝ ι)) (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (kappa : ℝ) : Prop :=
  ∃ u : W1p0 mu Omega 2, u ≠ 0 ∧ ∀ v : W1p0 mu Omega 2,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      kappa * ⟪W1p.value (u : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ

/-- Being a Dirichlet eigenvalue, written out as the integral identity
`a(u, v) = κ ∫_Ω u v`. -/
theorem isDirichletEigenvalue_iff_setIntegral (kappa : ℝ) :
    IsDirichletEigenvalue mu Omega a b c kappa ↔
      ∃ u : W1p0 mu Omega 2, u ≠ 0 ∧ ∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa * ∫ x in Omega, W1p.value (u : W1p mu Omega 2) x *
            W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [IsDirichletEigenvalue, W1p.inner_value_eq_setIntegral]

/-- A Dirichlet eigenvalue is exactly a scalar mass shift with a nonzero homogeneous weak
solution. -/
theorem isDirichletEigenvalue_iff_exists_isWeakSolutionDirichletMassShift (kappa : ℝ) :
    IsDirichletEigenvalue mu Omega a b c kappa ↔
      ∃ u : W1p0 mu Omega 2, u ≠ 0 ∧ IsWeakSolutionDirichletMassShift a b c kappa 0 u := by
  have hzero : ∀ v : W1p0 mu Omega 2,
      (∫ x in Omega, (0 : Lp ℝ 2 (mu.restrict Omega)) x *
        W1p.value (v : W1p mu Omega 2) x ∂mu) = 0 := fun v => by
    rw [← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply, inner_zero_left]
  simp only [IsDirichletEigenvalue, isWeakSolutionDirichletMassShift_iff, hzero, sub_eq_zero]

/-- **Every Dirichlet eigenvalue of a coercive form is positive.**  Coercivity of the energy
form on `H¹₀(Ω)` is the only hypothesis: neither boundedness nor any regularity of `Ω` is
needed. -/
theorem pos_of_isDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {kappa : ℝ}
    (h : IsDirichletEigenvalue mu Omega a b c kappa) : 0 < kappa := by
  obtain ⟨u, hu, heq⟩ := h
  refine hcoercive.pos_of_forall_apply_eq_smul_inner
    (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) hu fun v => ?_
  rw [energyFormH1L0_apply, W1p0.valueL_apply, W1p0.valueL_apply]
  exact heq v

/-- **The Dirichlet spectrum lies above the coercivity constant.**  Any diagonal lower bound
`C‖w‖²_{H¹} ≤ a(w, w)` on `H¹₀(Ω)` bounds every Dirichlet eigenvalue below by `C`.  The `C`
available on a bounded domain is a Poincaré constant, so this says that the first Dirichlet
eigenvalue is at least the Poincaré constant. -/
theorem le_of_isDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {kappa : ℝ} (h : IsDirichletEigenvalue mu Omega a b c kappa) : C ≤ kappa := by
  obtain ⟨u, hu, heq⟩ := h
  refine hcoercive.le_of_forall_apply_eq_smul_inner
    (J := W1p0.valueL (mu := mu) (Omega := Omega) (p := 2))
    (fun w => ?_) (fun w => ?_) hu fun v => ?_
  · rw [energyFormH1L0_apply]
    exact hlower w
  · rw [W1p0.valueL_apply]
    exact W1p.norm_value_le (w : W1p mu Omega 2)
  · rw [energyFormH1L0_apply, W1p0.valueL_apply, W1p0.valueL_apply]
    exact heq v

/-- The **first Dirichlet eigenvalue** is the reciprocal of the norm of the Dirichlet solution
operator.  On a nonempty bounded domain with symmetric energy form this value is attained and is
the least Dirichlet eigenvalue; see `TauCeti.PDE.isDirichletEigenvalue_first` and
`TauCeti.PDE.firstDirichletEigenvalue_le`. -/
def firstDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) : ℝ :=
  ‖dirichletSolutionOperator hcoeff hcoercive‖⁻¹

/-- The first Dirichlet eigenvalue is the reciprocal of the operator norm of the Dirichlet
solution operator. -/
theorem firstDirichletEigenvalue_def
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    firstDirichletEigenvalue hcoeff hcoercive =
      ‖dirichletSolutionOperator hcoeff hcoercive‖⁻¹ := (rfl)

/-- **Existence of a Dirichlet eigenvalue.**  On a nonempty bounded domain with a symmetric energy
form, the Dirichlet eigenvalue problem has a nonzero weak solution. -/
theorem exists_isDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    ∃ kappa : ℝ, IsDirichletEigenvalue mu Omega a b c kappa := by
  obtain ⟨kappa, -, u, hu, heq⟩ := hcoercive.exists_ne_zero_forall_apply_eq_smul_inner
    (W1p0.isCompactOperator_valueL (by simp) hOmega) (energyFormH1L0_comm hcoeff hsymm)
    (W1p0.valueL_ne_zero hOmega_nonempty)
  refine ⟨kappa, u, hu, fun v => ?_⟩
  have hv := heq v
  rwa [energyFormH1L0_apply, W1p0.valueL_apply, W1p0.valueL_apply] at hv

/-- **The Dirichlet eigenvalues are the reciprocals of the nonzero eigenvalues of the solution
operator.**  This is the passage that turns the eigenvalue problem for the unbounded operator
`L` into one for a bounded — and, on a bounded domain, compact — operator on `L²(Ω)`. -/
theorem isDirichletEigenvalue_iff_hasEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {kappa : ℝ} (hkappa : kappa ≠ 0) :
    IsDirichletEigenvalue mu Omega a b c kappa ↔
      HasEigenvalue (dirichletSolutionOperator hcoeff hcoercive :
        Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) kappa⁻¹ := by
  rw [dirichletSolutionOperator,
    hcoercive.hasEigenvalue_formSolutionOperator_iff W1p0.valueL hkappa]
  refine exists_congr fun u => and_congr_right fun _ => forall_congr' fun v => ?_
  rw [energyFormH1L0_apply, W1p0.valueL_apply, W1p0.valueL_apply]

/-- The first Dirichlet eigenvalue is attained on a nonempty bounded domain with symmetric energy
form. -/
theorem isDirichletEigenvalue_first
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsDirichletEigenvalue mu Omega a b c
      (firstDirichletEigenvalue hcoeff hcoercive) := by
  rw [firstDirichletEigenvalue_def, dirichletSolutionOperator]
  obtain ⟨u, hu, heq⟩ := hcoercive.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner
    (W1p0.isCompactOperator_valueL (by simp) hOmega) (energyFormH1L0_comm hcoeff hsymm)
    (W1p0.valueL_ne_zero hOmega_nonempty)
  refine ⟨u, hu, fun v => ?_⟩
  have hv := heq v
  rwa [energyFormH1L0_apply, W1p0.valueL_apply, W1p0.valueL_apply] at hv

/-- The first Dirichlet eigenvalue is positive. -/
theorem firstDirichletEigenvalue_pos
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    0 < firstDirichletEigenvalue hcoeff hcoercive :=
  pos_of_isDirichletEigenvalue hcoeff hcoercive
    (isDirichletEigenvalue_first hcoeff hcoercive hOmega hsymm hOmega_nonempty)

/-- The first Dirichlet eigenvalue is no greater than any Dirichlet eigenvalue. -/
theorem firstDirichletEigenvalue_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {kappa : ℝ}
    (hkappa : IsDirichletEigenvalue mu Omega a b c kappa) :
    firstDirichletEigenvalue hcoeff hcoercive ≤ kappa := by
  have hkappa_pos := pos_of_isDirichletEigenvalue hcoeff hcoercive hkappa
  have heigen : HasEigenvalue (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) kappa⁻¹ :=
    (isDirichletEigenvalue_iff_hasEigenvalue hcoeff hcoercive hkappa_pos.ne').mp hkappa
  obtain ⟨v, hv, hvne⟩ := heigen.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv
  have hmul : |kappa⁻¹| * ‖v‖ ≤ ‖dirichletSolutionOperator hcoeff hcoercive‖ * ‖v‖ := by
    calc
      |kappa⁻¹| * ‖v‖ = ‖kappa⁻¹ • v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖dirichletSolutionOperator hcoeff hcoercive v‖ := (congrArg norm hv).symm
      _ ≤ ‖dirichletSolutionOperator hcoeff hcoercive‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
  have hle : |kappa⁻¹| ≤ ‖dirichletSolutionOperator hcoeff hcoercive‖ := by
    nlinarith [norm_pos_iff.mpr hvne]
  rw [abs_of_pos (inv_pos.mpr hkappa_pos)] at hle
  have hnorm_pos : 0 < ‖dirichletSolutionOperator hcoeff hcoercive‖ :=
    (inv_pos.mpr hkappa_pos).trans_le hle
  rw [firstDirichletEigenvalue_def]
  exact (inv_le_comm₀ hnorm_pos hkappa_pos).mpr hle

/-- A diagonal lower bound for the energy form bounds the first Dirichlet eigenvalue below. -/
theorem le_firstDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2)) :
    C ≤ firstDirichletEigenvalue hcoeff hcoercive :=
  le_of_isDirichletEigenvalue hcoeff hcoercive hlower
    (isDirichletEigenvalue_first hcoeff hcoercive hOmega hsymm hOmega_nonempty)

/-! ### The Rayleigh principle -/

/-- **The quantity `firstDirichletEigenvalue` is a Poincaré constant for the energy form**:

`κ₁ ‖u‖²_{L²(Ω)} ≤ a(u, u)` for every `u ∈ H¹₀(Ω)`,

and by `TauCeti.PDE.isGreatest_firstDirichletEigenvalue` it is the largest constant for
which this holds.  Neither boundedness nor nonemptiness of `Ω` is needed here: only coercivity,
which makes the solution operator exist, and symmetry, which gives the energy form its
Cauchy--Schwarz inequality. -/
theorem firstDirichletEigenvalue_mul_norm_value_sq_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (u : W1p0 mu Omega 2) :
    firstDirichletEigenvalue hcoeff hcoercive * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) := by
  rw [firstDirichletEigenvalue_def, dirichletSolutionOperator]
  have h := hcoercive.inv_norm_formSolutionOperator_mul_norm_apply_sq_le
    (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) (energyFormH1L0_comm hcoeff hsymm) u
  rwa [energyFormH1L0_apply, W1p0.valueL_apply] at h

/-- **The Rayleigh principle for the Dirichlet problem.**  On a nonempty bounded domain with a
symmetric energy form, the first Dirichlet eigenvalue is the *minimum* of the Rayleigh quotient

`a(u, u) / ‖u‖²_{L²(Ω)}`

over the `u ∈ H¹₀(Ω)` with nonzero `L²` value; the minimum is attained at an eigenfunction.
Boundedness of `Ω` enters only through the attainment, by way of Rellich--Kondrachov: the
inequality alone is `TauCeti.PDE.firstDirichletEigenvalue_mul_norm_value_sq_le`. -/
theorem isLeast_rayleighQuotient_firstDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsLeast {r : ℝ | ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) ≠ 0 ∧
        energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) /
          ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 = r}
      (firstDirichletEigenvalue hcoeff hcoercive) := by
  have hset : {r : ℝ | ∃ u : W1p0 mu Omega 2, W1p.value (u : W1p mu Omega 2) ≠ 0 ∧
      energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2) /
        ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 = r} =
      {r : ℝ | ∃ u : W1p0 mu Omega 2, W1p0.valueL u ≠ 0 ∧
        energyFormH1L0 hcoeff u u / ‖W1p0.valueL u‖ ^ 2 = r} := by
    simp only [W1p0.valueL_apply, energyFormH1L0_apply]
  rw [hset, firstDirichletEigenvalue_def, dirichletSolutionOperator]
  exact hcoercive.isLeast_rayleighQuotient (W1p0.isCompactOperator_valueL (by simp) hOmega)
    (energyFormH1L0_comm hcoeff hsymm) (W1p0.valueL_ne_zero hOmega_nonempty)

/-- **The quantity `firstDirichletEigenvalue` is the optimal Poincaré constant** of the energy
form: it is the greatest `C` with `C ‖u‖²_{L²(Ω)} ≤ a(u, u)` for all `u ∈ H¹₀(Ω)`.  This is the
Rayleigh principle read as an inequality, and it shows that the bound
`TauCeti.PDE.firstDirichletEigenvalue_mul_norm_value_sq_le` is optimal.  Boundedness of `Ω` is
not needed because this optimal-constant characterization does not assert attainment. -/
theorem isGreatest_firstDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (hOmega_nonempty : (Omega : Set (EuclideanSpace ℝ ι)).Nonempty) :
    IsGreatest {C : ℝ | ∀ u : W1p0 mu Omega 2,
        C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
          energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2)}
      (firstDirichletEigenvalue hcoeff hcoercive) := by
  have hset : {C : ℝ | ∀ u : W1p0 mu Omega 2,
      C * ‖W1p.value (u : W1p mu Omega 2)‖ ^ 2 ≤
        energyFormH1 a b c (u : W1p mu Omega 2) (u : W1p mu Omega 2)} =
      {C : ℝ | ∀ u : W1p0 mu Omega 2,
        C * ‖W1p0.valueL u‖ ^ 2 ≤ energyFormH1L0 hcoeff u u} := by
    simp only [W1p0.valueL_apply, energyFormH1L0_apply]
  rw [hset, firstDirichletEigenvalue_def, dirichletSolutionOperator]
  exact hcoercive.isGreatest_inv_norm_formSolutionOperator
    (energyFormH1L0_comm hcoeff hsymm) (W1p0.valueL_ne_zero hOmega_nonempty)

/-- **The eigenspaces of the Dirichlet problem are finite dimensional** on a bounded domain. -/
theorem finiteDimensional_eigenspace_dirichletSolutionOperator
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) {nu : ℝ} (hnu : nu ≠ 0) :
    FiniteDimensional ℝ (eigenspace (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) nu) := by
  rw [dirichletSolutionOperator]
  exact hcoercive.finiteDimensional_eigenspace_formSolutionOperator
    (W1p0.isCompactOperator_valueL (by simp) hOmega) hnu

/-- **The spectral theorem for the Dirichlet problem**: on a bounded domain and for a symmetric
energy form, the eigenvectors of the solution operator span a dense subspace of `L²(Ω)`. -/
theorem orthogonalComplement_iSup_eigenspaces_dirichletSolutionOperator_eq_bot
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    (⨆ nu : ℝ, eigenspace (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) nu)ᗮ = ⊥ := by
  rw [dirichletSolutionOperator]
  exact hcoercive.orthogonalComplement_iSup_eigenspaces_formSolutionOperator_eq_bot
    (W1p0.isCompactOperator_valueL (by simp) hOmega) (energyFormH1L0_comm hcoeff hsymm)

/-- **The Dirichlet eigenfunctions span a dense subspace of `L²(Ω)`.**  The value map
`H¹₀(Ω) → L²(Ω)` has dense range, so the eigenvalue `0` of the solution operator is absent and
the eigenspaces at nonzero eigenvalues already have trivial orthogonal complement. -/
theorem orthogonalComplement_iSup_eigenspaces_ne_zero_dirichletSolutionOperator_eq_bot
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    (⨆ nu : ℝ, ⨆ _ : nu ≠ 0, eigenspace (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict Omega) →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) nu)ᗮ = ⊥ := by
  rw [dirichletSolutionOperator]
  exact hcoercive.orthogonalComplement_iSup_eigenspaces_ne_zero_formSolutionOperator_eq_bot
    (W1p0.isCompactOperator_valueL (by simp) hOmega) W1p0.denseRange_valueL_two
    (energyFormH1L0_comm hcoeff hsymm)

/-- **The Dirichlet eigenfunctions form an orthonormal basis of `L²(Ω)`.**  On a bounded domain
and for a symmetric energy form, `L²(Ω)` has an orthonormal basis whose vectors are the values of
weak solutions `u ∈ H¹₀(Ω)` of `L u = κ u` at positive Dirichlet eigenvalues `κ`, and the
`L²(Ω)` value of the weak solution to the Dirichlet problem has the eigenfunction expansion
`W1p.value u = ∑ κ⁻¹ ⟪eₖ, f⟫ eₖ`.  No regularity of `∂Ω` enters, and `L²(Ω)` is not assumed
separable, so the basis is indexed by a set of functions as in `exists_hilbertBasis`. -/
theorem exists_hilbertBasis_forall_isDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2)) :
    ∃ (s : Set (Lp ℝ 2 (mu.restrict Omega)))
      (basis : HilbertBasis s ℝ (Lp ℝ 2 (mu.restrict Omega))) (kappa : s → ℝ)
      (u : s → W1p0 mu Omega 2),
      ⇑basis = ((↑) : s → Lp ℝ 2 (mu.restrict Omega)) ∧ (∀ f : s, 0 < kappa f) ∧
      (∀ f : s, IsDirichletEigenvalue mu Omega a b c (kappa f)) ∧
      (∀ f : s, W1p.value (u f : W1p mu Omega 2) = (f : Lp ℝ 2 (mu.restrict Omega))) ∧
      (∀ (f : s) (v : W1p0 mu Omega 2),
        energyFormH1 a b c (u f : W1p mu Omega 2) (v : W1p mu Omega 2) =
          kappa f * ⟪W1p.value (u f : W1p mu Omega 2), W1p.value (v : W1p mu Omega 2)⟫_ℝ) ∧
      ∀ f : Lp ℝ 2 (mu.restrict Omega),
        HasSum (fun g : s => (kappa g)⁻¹ • basis.repr f g • basis g)
          (dirichletSolutionOperator hcoeff hcoercive f) := by
  obtain ⟨s, basis, kappa, u, hbasis, hpos, hune, hvalue, heq, hsum⟩ :=
    hcoercive.exists_hilbertBasis_forall_apply_eq_smul_inner
      (W1p0.isCompactOperator_valueL (by simp) hOmega) W1p0.denseRange_valueL_two
      (energyFormH1L0_comm hcoeff hsymm)
  have heq' : ∀ (f : s) (v : W1p0 mu Omega 2),
      energyFormH1 a b c (u f : W1p mu Omega 2) (v : W1p mu Omega 2) =
        kappa f * ⟪W1p.value (u f : W1p mu Omega 2),
          W1p.value (v : W1p mu Omega 2)⟫_ℝ := fun f v => by
    simpa only [energyFormH1L0_apply, W1p0.valueL_apply] using heq f v
  refine ⟨s, basis, kappa, u, hbasis, hpos, fun f => ⟨u f, hune f, heq' f⟩,
    fun f => ?_, heq', ?_⟩
  · simpa only [W1p0.valueL_apply] using hvalue f
  · rw [dirichletSolutionOperator]
    exact hsum

/-- **The Fredholm alternative in eigenvalue language.**  On a bounded domain, if `κ` is not a
Dirichlet eigenvalue then `L u - κ u = f` in `Ω`, `u = 0` on `∂Ω`, has exactly one weak solution
for every `f ∈ L²(Ω)`. -/
theorem existsUnique_isWeakSolutionDirichletMassShift_of_not_isDirichletEigenvalue
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff))
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) {kappa : ℝ}
    (hkappa : ¬ IsDirichletEigenvalue mu Omega a b c kappa) (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichletMassShift a b c kappa f u := by
  rcases fredholmAlternative_isWeakSolutionDirichletMassShift hcoeff hcoercive hOmega kappa with
    hker | hsolve
  · exact absurd
      ((isDirichletEigenvalue_iff_exists_isWeakSolutionDirichletMassShift kappa).mpr hker) hkappa
  · exact hsolve f

end Domain

/-! ### The Dirichlet spectrum of a domain inside a ball -/

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

/-- **A lower bound for the Dirichlet spectrum of a domain inside a ball.**  For
`Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` with a uniformly elliptic principal part, a drift bounded by `β`, a
bounded nonnegative mass coefficient and the smallness condition `2βR < λ`, every Dirichlet
eigenvalue satisfies

`(λ² - 4β²R²)/(2λ(4R² + 1)) ≤ κ`.

The constant is the Poincaré constant of the ball, which is positive under the smallness
condition, so in particular the Dirichlet spectrum is bounded away from `0`. -/
theorem le_of_isDirichletEigenvalue_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega)) (hbeta : 0 ≤ beta)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta * (2 * R) < lam) {kappa : ℝ}
    (hkappa : IsDirichletEigenvalue volume Omega a b c kappa) :
    (lam ^ 2 - beta ^ 2 * (2 * R) ^ 2) / (2 * lam * ((2 * R) ^ 2 + 1)) ≤ kappa := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  exact le_of_isDirichletEigenvalue hcoeff
    (isCoercive_energyFormH1L0 hcoeff
      (energyFormH1_poincare_constant_pos h.pos hbeta (by linarith) hsmall)
      (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_ball h ha hb hc hb_bound hc_bound
        hc_nonneg hball w.2))
    (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_ball h ha hb hc hb_bound hc_bound
      hc_nonneg hball w.2)
    hkappa

end UniformlyEllipticOn

/-- **The Dirichlet spectrum of `-Δ` on a domain inside a ball.**  For
`Ω ⊆ B(z, R) ⊆ ℝ^{n+1}`, every `κ` for which `-Δu = κu` in `Ω`, `u = 0` on `∂Ω`, has a nonzero
weak solution satisfies `1/(2(4R² + 1)) ≤ κ`; in particular the first Dirichlet eigenvalue of
`-Δ` is positive.  The bound is the Poincaré constant of the ball, not the sharp eigenvalue. -/
theorem le_of_isDirichletEigenvalue_laplacian_of_subset_ball
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R) {kappa : ℝ}
    (hkappa : IsDirichletEigenvalue volume Omega (fun _ => 1) 0 0 kappa) :
    1 / (2 * ((2 * R) ^ 2 + 1)) ≤ kappa := by
  have key := UniformlyEllipticOn.le_of_isDirichletEigenvalue_of_subset_ball
    (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const le_rfl (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
    (fun _ _ => le_rfl) hR hball (by simp) hkappa
  simpa using key

/-- **Every Dirichlet eigenvalue of `-Δ` is positive** on a domain inside a ball. -/
theorem pos_of_isDirichletEigenvalue_laplacian_of_subset_ball
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R) {kappa : ℝ}
    (hkappa : IsDirichletEigenvalue volume Omega (fun _ => 1) 0 0 kappa) :
    0 < kappa :=
  lt_of_lt_of_le (by positivity)
    (le_of_isDirichletEigenvalue_laplacian_of_subset_ball hR hball hkappa)

end Euclidean

end PDE

end TauCeti
