/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev

/-!
# The Dirichlet problem: existence and uniqueness of a weak solution

Lane D, item 17 of `TauCetiRoadmap/PDE/README.md` asks for the first end-to-end existence
theorem of the roadmap: for a divergence-form operator

`L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u`

whose energy form is coercive on `H¹₀(Ω)`, the homogeneous Dirichlet problem `L u = f` in `Ω`,
`u = 0` on `∂Ω`, has a unique weak solution. This file assembles that theorem out of pieces
that are already in place: the bundled energy form `TauCeti.PDE.energyFormH1L0` and its lower
bounds from `TauCeti/Analysis/PDE/EnergyForm/Sobolev.lean`, and the variational form of
Lax--Milgram `IsCoercive.existsUnique_forall_eq` from
`TauCeti/Analysis/InnerProductSpace/LaxMilgram.lean`.

## The weak formulation

A weak solution is a function `u ∈ H¹₀(Ω)` satisfying

`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,

which is `TauCeti.PDE.IsWeakSolutionDirichlet`. Two hypotheses are hidden in that sentence and
neither is a boundary-regularity assumption. The homogeneous boundary condition is carried by
membership in `H¹₀(Ω) = W^{1,2}_0(Ω)`, the closure of `C_c^∞(Ω)`, so no trace operator and no
regularity of `∂Ω` is needed to state it. The right-hand side is an `L²(Ω)` function paired
against the *value* component of the test function, which is what makes it a continuous linear
functional on `H¹₀(Ω)`: `TauCeti.PDE.dirichletForcing`, of norm at most `‖f‖_{L²}` because the
value component of a Sobolev jet is dominated by the graph norm.

## Where coercivity comes from

Lax--Milgram needs `IsCoercive`, that is `∃ C > 0, ∀ u, C‖u‖‖u‖ ≤ a(u, u)`, and the energy-form
file supplies exactly such diagonal lower bounds without packaging them.
`TauCeti.PDE.isCoercive_energyFormH1L0` converts any of them, and the two geometric routes of
that file are instantiated here: a domain trapped between two hyperplanes and a domain contained
in a ball, whose Poincaré constants are the slab width `t - s` and the diameter bound `2R`. In
both cases the drift smallness condition `βP < λ` is what makes the resulting constant positive,
and with no drift it is vacuous. This is *not* a claim that coercivity fails otherwise: when it
is genuinely unavailable the Fredholm alternative (Lane D, item 18) replaces Lax--Milgram.

## The `-Δ` payoff

Specialising to `a = 1`, `b = 0`, `c = 0` on a ball gives
`TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`: the Poisson problem
`-Δu = f` in `Ω`, `u = 0` on `∂Ω`, has a unique weak solution whenever `Ω` is contained in a
ball. Unfolded through `TauCeti.PDE.isWeakSolutionDirichlet_one_zero_zero_iff` the variational
equation reads `∫_Ω ∇v · ∇u = ∫_Ω f v`, the classical weak form of Poisson's equation. This is
the existence half of the roadmap's "end-to-end existence" acceptance criterion; the smoothness
half is Lane E and the identification with the Newtonian potential is Lane C.

## A priori bound

`TauCeti.PDE.norm_le_of_isWeakSolutionDirichlet` records the energy estimate `‖u‖_{H¹} ≤ ‖f‖/C`
attached to a coercivity constant `C`. It is proved for *every* weak solution rather than for
the constructed one, so it is available before, and independently of, uniqueness.

## Main declarations

* `TauCeti.PDE.dirichletForcing`: the `L²` right-hand side as a continuous linear functional on
  `H¹₀(Ω)`, with `TauCeti.PDE.norm_dirichletForcing_le`.
* `TauCeti.PDE.IsWeakSolutionDirichlet`: the weak formulation of `L u = f` in `Ω`, `u = 0` on
  `∂Ω`.
* `TauCeti.PDE.isCoercive_energyFormH1L0`: a diagonal lower bound packaged as `IsCoercive`.
* `TauCeti.PDE.weakSolutionDirichlet` and
  `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet`: the Lax--Milgram solution and the
  existence-and-uniqueness theorem.
* `TauCeti.PDE.norm_le_of_isWeakSolutionDirichlet`: the energy estimate `‖u‖ ≤ ‖f‖/C`.
* `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_of_subset_slab` and
  `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_of_subset_ball`: existence and uniqueness
  under the geometric hypotheses that make the energy form coercive.
* `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`: the Poisson
  problem `-Δu = f` on a ball-contained domain.

## References

Lane D, item 17 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential
Equations*, Section 6.2.2 (existence of weak solutions); D. Gilbarg and N. Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Chapter 8, Theorem 8.3.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {C : ℝ}

/-- Shortcut seminormed group instance on `H¹₀(Ω)`. The norm is inherited through two nested
closed subspaces of an `L²` space of jets, which instance search does not find on its own; the
same shortcut is used in `TauCeti/Analysis/PDE/EnergyForm/Sobolev.lean`. -/
noncomputable local instance instSeminormedAddCommGroupH1Zero :
    SeminormedAddCommGroup (W1p0 mu Omega 2) := inferInstance

/-- Shortcut normed space instance on `H¹₀(Ω)`, needed to talk about operator norms of
functionals on it. -/
noncomputable local instance instNormedSpaceH1Zero :
    NormedSpace ℝ (W1p0 mu Omega 2) := inferInstance

/-- Shortcut normed group instance on `H¹₀(Ω)`, the separated form of the seminorm above; the
inner-product shortcut below needs it and does not find it on its own. -/
noncomputable local instance instNormedAddCommGroupH1Zero :
    NormedAddCommGroup (W1p0 mu Omega 2) := inferInstance

/-- Shortcut inner-product instance on `H¹₀(Ω)`: the Hilbert structure Lax--Milgram runs on,
inherited from the `L²` jet space through the same two closed subspaces. -/
noncomputable local instance instInnerProductSpaceH1Zero :
    InnerProductSpace ℝ (W1p0 mu Omega 2) := inferInstance

/-! ### The forcing functional -/

/-- The **right-hand side of the Dirichlet problem** as a continuous linear functional on
`H¹₀(Ω)`: an `L²(Ω)` function `f` acts by `v ↦ ∫_Ω f v`, pairing against the value component of
the Sobolev jet. Continuity is automatic from the construction, the value projection
`TauCeti.W1p.valueL` being continuous and the pairing being the `L²` inner product. -/
def dirichletForcing (f : Lp ℝ 2 (mu.restrict Omega)) : StrongDual ℝ (W1p0 mu Omega 2) :=
  (innerSL ℝ f).comp (W1p.valueL.comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL)

/-- The forcing functional is the `L²` inner product against the value component. -/
@[simp] theorem dirichletForcing_apply (f : Lp ℝ 2 (mu.restrict Omega)) (v : W1p0 mu Omega 2) :
    dirichletForcing f v = ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [dirichletForcing, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, innerSL_apply_apply, W1p.valueL_apply]

/-- The forcing functional written as the integral `∫_Ω f v` it names. -/
theorem dirichletForcing_apply_eq_setIntegral (f : Lp ℝ 2 (mu.restrict Omega))
    (v : W1p0 mu Omega 2) :
    dirichletForcing f v = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  rw [dirichletForcing_apply, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [RCLike.inner_apply, mul_comm])

/-- The forcing functional is bounded by the `L²` norm of its density, because the value
component of a Sobolev jet is dominated by the graph norm. -/
theorem norm_dirichletForcing_apply_le (f : Lp ℝ 2 (mu.restrict Omega))
    (v : W1p0 mu Omega 2) : ‖dirichletForcing f v‖ ≤ ‖f‖ * ‖v‖ := by
  rw [dirichletForcing_apply]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (W1p.norm_value_le (v : W1p mu Omega 2)) (norm_nonneg f)

/-- The operator norm of the forcing functional is at most `‖f‖_{L²(Ω)}`. -/
theorem norm_dirichletForcing_le (f : Lp ℝ 2 (mu.restrict Omega)) :
    ‖dirichletForcing f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (norm_dirichletForcing_apply_le f)

/-! ### The weak formulation -/

/-- **The weak formulation of the homogeneous Dirichlet problem.** `u ∈ H¹₀(Ω)` is a weak
solution of `L u = f` in `Ω`, `u = 0` on `∂Ω`, for
`L u = -∂ⱼ(aⁱʲ ∂ᵢu) + bⁱ ∂ᵢu + c u`, when

`a(u, v) = ∫_Ω f v` for every test function `v ∈ H¹₀(Ω)`.

The boundary condition is not a side condition here: it is membership of `u` in `H¹₀(Ω)`, the
closure of `C_c^∞(Ω)`, so no regularity of `∂Ω` and no trace operator enters the statement.
Nothing is assumed about the coefficients; each theorem below names the hypotheses it uses. -/
def IsWeakSolutionDirichlet (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) : Prop :=
  ∀ v : W1p0 mu Omega 2,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = dirichletForcing f v

/-- Being a weak solution, written out as the integral identity `a(u, v) = ∫_Ω f v`. -/
@[simp] theorem isWeakSolutionDirichlet_iff (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet a b c f u ↔
      ∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2)
          = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [IsWeakSolutionDirichlet, dirichletForcing_apply_eq_setIntegral]

/-- **The energy estimate.** Any weak solution is bounded in `H¹` by the `L²` norm of the data,
with the coercivity constant as the only other ingredient. The estimate is stated for every
weak solution, so it does not presuppose uniqueness. -/
theorem norm_le_of_isWeakSolutionDirichlet (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) : ‖u‖ ≤ ‖f‖ / C := by
  have hkey : C * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ :=
    ((hlower u).trans_eq (hu u)).trans ((le_abs_self _).trans (norm_dirichletForcing_apply_le f u))
  rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (norm_nonneg f) hC.le
  · rw [le_div_iff₀ hC]
    nlinarith [hkey, hpos]

/-! ### Coercivity and Lax--Milgram -/

/-- **A diagonal lower bound is coercivity.** The energy-form file proves bounds of the shape
`C‖u‖² ≤ a(u, u)`; this packages one, together with positivity of its constant, as the
`IsCoercive` hypothesis of Mathlib's Lax--Milgram theorem. -/
theorem isCoercive_energyFormH1L0
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2)) :
    IsCoercive (energyFormH1L0 hcoeff) := by
  refine ⟨C, hC, fun w => ?_⟩
  rw [energyFormH1L0_apply]
  calc C * ‖w‖ * ‖w‖ = C * ‖w‖ ^ 2 := by ring
    _ ≤ _ := hlower w

/-- **The weak solution of the Dirichlet problem**, produced by Lax--Milgram from coercivity of
the energy form. It is characterised by
`TauCeti.PDE.isWeakSolutionDirichlet_weakSolutionDirichlet` together with
`TauCeti.PDE.eq_weakSolutionDirichlet`. -/
def weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    W1p0 mu Omega 2 :=
  hcoercive.solutionOfFunctional (dirichletForcing f)

/-- The Lax--Milgram solution is a weak solution of the Dirichlet problem. -/
theorem isWeakSolutionDirichlet_weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    IsWeakSolutionDirichlet a b c f (weakSolutionDirichlet hcoeff hcoercive f) := by
  intro v
  rw [← energyFormH1L0_apply hcoeff]
  exact hcoercive.apply_solutionOfFunctional_eq (dirichletForcing f) v

/-- A weak solution of the Dirichlet problem is *the* Lax--Milgram solution. -/
theorem eq_weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} (hu : IsWeakSolutionDirichlet a b c f u) :
    u = weakSolutionDirichlet hcoeff hcoercive f :=
  hcoercive.eq_solutionOfFunctional fun v => by
    rw [energyFormH1L0_apply hcoeff]; exact hu v

/-- **Existence and uniqueness of the weak solution of the Dirichlet problem.** For a
divergence-form operator whose energy form is bounded and coercive on `H¹₀(Ω)`, and for every
`f ∈ L²(Ω)`, there is exactly one `u ∈ H¹₀(Ω)` with

`a(u, v) = ∫_Ω f v` for all `v ∈ H¹₀(Ω)`.

This is Lane D, item 17 of the PDE roadmap: the energy method's existence theorem, obtained by
consuming Mathlib's Lax--Milgram theorem through the variational interface. -/
theorem existsUnique_isWeakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u :=
  ⟨weakSolutionDirichlet hcoeff hcoercive f,
    isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f,
    fun _ hu => eq_weakSolutionDirichlet hcoeff hcoercive hu⟩

/-- Existence and uniqueness of the weak solution, stated from a diagonal lower bound on the
energy form instead of a packaged `IsCoercive` hypothesis. -/
theorem existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u :=
  existsUnique_isWeakSolutionDirichlet hcoeff (isCoercive_energyFormH1L0 hcoeff hC hlower) f

/-! ### The Laplacian model -/

/-- The energy form of the Laplacian model `-Δ` (`a = 1`, no drift, no mass) is the Dirichlet
form `∫_Ω ∇v · ∇u`. -/
@[simp] theorem energyFormH1_one_zero_zero_apply [DecidableEq ι] (u v : W1p mu Omega 2) :
    energyFormH1 (fun _ => 1) 0 0 u v =
      ∫ x in Omega, W1p.gradient v x ⬝ᵥ W1p.gradient u x ∂mu := by
  rw [energyFormH1_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp)

/-- The weak formulation of the Laplacian model `-Δ` is the classical one: `u ∈ H¹₀(Ω)` solves
`-Δu = f` weakly exactly when `∫_Ω ∇v · ∇u = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. -/
theorem isWeakSolutionDirichlet_one_zero_zero_iff [DecidableEq ι]
    (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u ↔
      ∀ v : W1p0 mu Omega 2,
        ∫ x in Omega, W1p.gradient (v : W1p mu Omega 2) x ⬝ᵥ
            W1p.gradient (u : W1p mu Omega 2) x ∂mu
          = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [isWeakSolutionDirichlet_iff, energyFormH1_one_zero_zero_apply]

end Domain

/-! ### Existence on a slab- or ball-contained domain -/

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

/-- **Existence and uniqueness for a domain trapped in a slab.** If `Ω ⊆ ℝ^{n+1}` lies between
the hyperplanes `xᵢ = s` and `xᵢ = t`, the principal part is uniformly elliptic with constants
`λ ≤ Λ`, the drift is bounded by `β`, the mass coefficient is bounded by `γ` and nonnegative,
and the drift is small in the sense `β(t - s) < λ`, then the Dirichlet problem has exactly one
weak solution for every `f ∈ L²(Ω)`. The Poincaré constant of the slab is its width, and the
domain need not be bounded: boundedness in one direction is enough. -/
theorem existsUnique_isWeakSolutionDirichlet_of_subset_slab
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega)) (hbeta : 0 ≤ beta)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {i : Fin (n + 1)} {s t : ℝ} (hst : s ≤ t)
    (hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc s t)
    (hsmall : beta * (t - s) < lam)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet a b c f u :=
  existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (energyFormH1_poincare_constant_pos h.pos hbeta (by linarith) hsmall)
    (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_slab h ha hb hc hb_bound hc_bound
      hc_nonneg hst hslab w.2) f

/-- **Existence and uniqueness for a domain inside a ball.** For `Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` with a
uniformly elliptic principal part, a drift bounded by `β`, a bounded nonnegative mass
coefficient and the smallness condition `2βR < λ`, the Dirichlet problem has exactly one weak
solution for every `f ∈ L²(Ω)`. The Poincaré constant used is the diameter bound `2R`, not the
sharp one, so the smallness condition is not sharp either. -/
theorem existsUnique_isWeakSolutionDirichlet_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega)) (hbeta : 0 ≤ beta)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta * (2 * R) < lam)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet a b c f u :=
  existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (energyFormH1_poincare_constant_pos h.pos hbeta (by linarith) hsmall)
    (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_ball h ha hb hc hb_bound hc_bound
      hc_nonneg hball w.2) f

end UniformlyEllipticOn

/-! ### The Poisson problem -/

/-- **The Poisson problem on a ball-contained domain.** For `Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` and every
`f ∈ L²(Ω)` there is exactly one `u ∈ H¹₀(Ω)` solving `-Δu = f` in `Ω`, `u = 0` on `∂Ω`,
weakly. This is the constant-coefficient case `a = 1`, `b = 0`, `c = 0` of
`TauCeti.PDE.UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball`, where the
drift smallness condition is vacuous; unfolded through
`TauCeti.PDE.isWeakSolutionDirichlet_one_zero_zero_iff` the equation reads
`∫_Ω ∇v · ∇u = ∫_Ω f v`. It is the existence half of the roadmap's end-to-end acceptance
criterion for the Dirichlet problem on a ball. -/
theorem existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u :=
  UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball
    (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const le_rfl (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
    (fun _ _ => le_rfl) hR hball (by simp) f

end Euclidean

end PDE

end TauCeti
