/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Cycle
public import TauCeti.Analysis.Contour.Argument.CyclePV
public import TauCeti.Analysis.Contour.Cauchy.HomologyFormula
public import TauCeti.Analysis.Contour.Cycle.HungerbuhlerWasem
public import TauCeti.Analysis.Contour.Cycle.Residue
public import TauCeti.Analysis.Contour.Winding.HalfPlane

/-!
# Contour integration in a convex domain

Layer 3 of the contour integration roadmap proves the homology Cauchy theorem, and Layers 2 and 4
state the residue theorems, for a cycle that is **null-homologous** in the domain of holomorphy.
That hypothesis is the right one — it is exactly what the proofs need — but it is not the one an
application arrives with. An application arrives with a disc, a half-plane, a strip, a rectangle,
or a triangle, and a contour drawn inside it.

`TauCeti.Contour.isNullHomologous_of_convex` closes that gap: a closed curve in a **convex open**
set is null-homologous there. This file records the resulting hypothesis-free statements, one per
theorem of the null-homologous tower, for a single closed curve and for a contour cycle:

* Cauchy's theorem `∮_γ f = 0` and Cauchy's integral formula `n_z(γ) · f(z) = (2πi)⁻¹ ∮_γ f/(· − z)`
  in every derivative order;
* the classical residue theorem `∮_γ f = 2πi · Σ_s n_s(γ) · Res_s f` for poles off the curve;
* the argument principle, in the ordinary and the principal-value (zeros **on** the curve) forms;
* the Hungerbühler–Wasem generalized residue theorem in its unconditional simple-pole regime,
  singularities on the curve included.

In each the hypothesis `IsNullHomologous` disappears, replaced by convexity and openness of the
ambient domain. The disc case, which reconciles this development with Mathlib's disc Cauchy
theory, is the specialisation to `Metric.ball`, recorded here for Cauchy's theorem and the integral
formula.

Convexity is genuinely a hypothesis on the *domain*, not on the curve: nothing is asked of `γ`
beyond the piecewise-`C¹` regularity (or, where a principal value is taken, the immersion
regularity) that every statement of the tower already carries. The other route to null-homology,
`TauCeti.Contour.isNullHomologous_of_pathHomotopy_refl`, instead asks the caller to exhibit a
contracting homotopy; the two are incomparable in strength, since a convex domain need not come
with a distinguished loop and a null-homotopic loop need not lie in a convex domain.

## Main results

* `TauCeti.Contour.cauchyTheorem_convex`, `TauCeti.Contour.cauchyIntegralFormula_convex` — Cauchy's
  theorem and integral formula on a convex open set.
* `TauCeti.Contour.classicalResidueTheorem_convex`, `TauCeti.Contour.argumentPrinciple_convex` —
  the residue theorem and the argument principle there.
* `TauCeti.Contour.hasCauchyPV_logDeriv_convex`,
  `TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles_convex` — the principal-value
  statements, whose singularities may lie on the curve.
* `TauCeti.Contour.Cycle.cauchyTheorem_convex`,
  `TauCeti.Contour.Cycle.classicalResidueTheorem_convex`,
  `TauCeti.Contour.Cycle.hungerbuhlerWasem_residueTheorem_of_simple_poles_convex` — the cycle
  forms.

## Provenance

No formalization is vendored: each statement is its null-homologous counterpart with the
null-homology discharged by `TauCeti.Contour.isNullHomologous_of_convex`.

## References

* S. Lang, *Complex Analysis* (GTM 103), Ch. IV — Cauchy's theorem on a convex (indeed, on a
  star-shaped) set.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Theorem 3.3, the principal-value statements below.
-/

public section

open Complex MeasureTheory Set

open scoped Interval Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {Ω : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}

/-- **Cauchy's theorem on a convex open set.** A holomorphic function integrates to zero along
every closed piecewise-`C¹` curve contained in a convex open set.

This is the homology Cauchy theorem `TauCeti.Contour.homologyCauchyTheorem` with its
null-homology hypothesis discharged by convexity, and it is the form in which Cauchy's theorem
is usually applied: on a disc, a half-plane, a strip, or a rectangle. -/
theorem cauchyTheorem_convex (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : IsPiecewiseC1On γ a b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 :=
  homologyCauchyTheorem hopen γ a b hγ hγΩ hclosed hf
    (isNullHomologous_of_convex hconv hopen hγ hclosed hγΩ)

/-- **Cauchy's theorem on a disc** — the specialisation of
`TauCeti.Contour.cauchyTheorem_convex` to `Metric.ball`, reconciling the raw-curve development
with Mathlib's disc Cauchy theory: a function holomorphic on a disc integrates to zero along every
closed piecewise-`C¹` curve inside it, not only along the boundary circles. -/
theorem cauchyTheorem_ball {c : ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hγ : IsPiecewiseC1On γ a b) (hγr : ∀ t ∈ uIcc a b, γ t ∈ Metric.ball c r)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 :=
  cauchyTheorem_convex (convex_ball c r) Metric.isOpen_ball hf hγ hγr hclosed

/-- **Cauchy's integral formula on a convex open set, for the `k`-th derivative.** For `f`
holomorphic on a convex open `Ω`, a closed piecewise-`C¹` curve `γ` in `Ω`, and `z ∈ Ω` off the
curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`. -/
theorem cauchyIntegralFormula_iteratedDeriv_convex {z : ℂ} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : IsPiecewiseC1On γ a b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b) (hz : z ∈ Ω)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) (k : ℕ) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ (k + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z *
          (iteratedDeriv k f z / (k.factorial : ℂ)) :=
  cauchyIntegralFormula_iteratedDeriv_nullHomologous hopen hf hγ hγΩ hclosed
    (isNullHomologous_of_convex hconv hopen hγ hclosed hγΩ) hz hoff k

/-- **Cauchy's integral formula on a convex open set.** For `f` holomorphic on a convex open `Ω`,
a closed piecewise-`C¹` curve `γ` in `Ω`, and `z ∈ Ω` off the curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z)) = 2πi · n_z(γ) · f z`. -/
theorem cauchyIntegralFormula_convex {z : ℂ} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : IsPiecewiseC1On γ a b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b) (hz : z ∈ Ω)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z :=
  cauchyIntegralFormula_nullHomologous hopen hf hγ hγΩ hclosed
    (isNullHomologous_of_convex hconv hopen hγ hclosed hγΩ) hz hoff

/-- **Cauchy's integral formula on a disc** — the `Metric.ball` case of
`TauCeti.Contour.cauchyIntegralFormula_convex`. -/
theorem cauchyIntegralFormula_ball {c : ℂ} {r : ℝ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hγ : IsPiecewiseC1On γ a b)
    (hγr : ∀ t ∈ uIcc a b, γ t ∈ Metric.ball c r) (hclosed : γ a = γ b)
    (hz : z ∈ Metric.ball c r) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z :=
  cauchyIntegralFormula_convex (convex_ball c r) Metric.isOpen_ball hf hγ hγr hclosed hz hoff

/-- **The classical residue theorem on a convex open set.** Let `Ω` be convex and open, `S` a
finite set, `f` holomorphic on `Ω ∖ S` and meromorphic at each point of `S` lying in `Ω`, and let
`γ` be a closed piecewise-`C¹` curve in `Ω` avoiding `S`. Then

`∫ t in a..b, γ' t • f (γ t) = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`.

Unlike `TauCeti.Contour.classicalResidueTheorem_circle`, the curve is arbitrary and the poles need
not be enclosed: a pole in a component of the complement that `γ` does not wind around simply gets
weight `0`. -/
theorem classicalResidueTheorem_convex {S : Finset ℂ} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hf : DifferentiableOn ℂ f (Ω \ (↑S : Set ℂ))) (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hγ : IsPiecewiseC1On γ a b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s :=
  classicalResidueTheorem_nullHomologous hopen hf hmero hγ hγΩ hclosed hoff
    (isNullHomologous_of_convex hconv hopen hγ hclosed hγΩ)

/-- **The argument principle on a convex open set.** For `f` analytic and non-vanishing on a
convex open `Ω` off a finite `S`, meromorphic of order `ord` at each point of `S` lying in `Ω`,
and a closed piecewise-`C¹` curve `γ` in `Ω` avoiding `S`,

`∫ t in a..b, γ' t • (f'/f) (γ t) = 2πi · ∑_{z ∈ S} n_z(γ) · ord z`,

the winding-weighted count of the zeros and poles of `f`. -/
theorem argumentPrinciple_convex {S : Finset ℂ} {ord : ℂ → ℤ} (hconv : Convex ℝ Ω)
    (hopen : IsOpen Ω) (hoffS : ∀ z ∈ Ω, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ Ω → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hγ : IsPiecewiseC1On γ a b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ) :=
  argumentPrinciple_nullHomologous hopen hoffS hmero hord hγ hγΩ hclosed hγoff
    (isNullHomologous_of_convex hconv hopen hγ hclosed hγΩ)

/-- **The generalized residue theorem on a convex open set, simple-pole regime.** Let `Ω` be
convex and open, `S ⊆ Ω` finite, `f` holomorphic on `Ω ∖ S` with at worst a simple pole at each
point of `S`, and `γ` a closed piecewise-`C¹` immersion in `Ω` based off `S`. Then the Cauchy
principal value of the contour integral is

`p.v. ∮_γ f = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`,

with the generalized, possibly non-integer, winding numbers as weights. The curve is free to pass
**through** the singularities; conditions (A′) and (B) of Hungerbühler–Wasem are automatic in this
regime, and null-homology is automatic by convexity, so no hypothesis beyond the immersion
survives. -/
theorem hungerbuhlerWasem_residueTheorem_of_simple_poles_convex (S : Finset ℂ)
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSΩ : (S : Set ℂ) ⊆ Ω) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hf : DifferentiableOn ℂ f (Ω \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) :=
  hungerbuhlerWasem_residueTheorem_of_simple_poles hopen S γ a b hγ_imm hSΩ hclosed hγa hγΩ hf
    hmero (isNullHomologous_of_convex hconv hopen hγ_imm.isPiecewiseC1On hclosed hγΩ) h_simple

/-- **The half-residue on a convex open set.** An on-curve simple pole about which the immersion
has generalized winding number `½` contributes `πi · Res_s f` to the principal value — the
`S = {s}` case of `TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles_convex`. -/
theorem hasCauchyPV_half_residue_of_simple_pole_convex {s : ℂ} (hconv : Convex ℝ Ω)
    (hopen : IsOpen Ω) (hγ_imm : IsPwC1ImmersionOn γ a b) (hsΩ : s ∈ Ω) (hclosed : γ a = γ b)
    (hγa : γ a ≠ s) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hf : DifferentiableOn ℂ f (Ω \ {s}))
    (hmero : MeromorphicAt f s)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s)
    (hwind : windingNumber γ a b s = 1 / 2) :
    HasCauchyPV γ a b f ((Real.pi : ℂ) * Complex.I * residue f s) :=
  hasCauchyPV_half_residue_of_simple_pole hopen γ a b s hγ_imm hsΩ hclosed hγa hγΩ hf hmero
    (isNullHomologous_of_convex hconv hopen hγ_imm.isPiecewiseC1On hclosed hγΩ) h_simple hwind

/-- **The argument principle on a convex open set, for a curve running through the zeros.** With
`f` analytic and non-vanishing on a convex open `Ω` off a finite `S`, meromorphic of order `ord` at
each point of `S` lying in `Ω`, and `γ` a closed piecewise-`C¹` immersion in `Ω` based off `S`,

`p.v. ∮_γ f'/f = 2πi · ∑_{z ∈ S} n_z(γ) · ord z`.

The curve may pass through the zeros and poles of `f`; each such point contributes its order
weighted by a generalized winding number, `½` in the standard configuration of a positively
oriented curve with a single smooth branch through the point. -/
theorem hasCauchyPV_logDeriv_convex {S : Finset ℂ} {ord : ℂ → ℤ} (hconv : Convex ℝ Ω)
    (hopen : IsOpen Ω) (hoffS : ∀ z ∈ Ω, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ Ω → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hγ_imm : IsPwC1ImmersionOn γ a b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hγa : γ a ∉ (S : Set ℂ)) :
    HasCauchyPV γ a b (logDeriv f)
      (2 * (Real.pi : ℂ) * Complex.I * ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ)) :=
  hasCauchyPV_logDeriv_nullHomologous hopen hoffS hmero hord hγ_imm hγΩ hclosed hγa
    (isNullHomologous_of_convex hconv hopen hγ_imm.isPiecewiseC1On hclosed hγΩ)

namespace Cycle

variable {C : Cycle}

/-- **Cauchy's theorem for a cycle in a convex open set.** A holomorphic function integrates to
zero along every contour cycle contained in a convex open set. -/
theorem cauchyTheorem_convex (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (hCΩ : IsIn C Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    integral f C = 0 :=
  homologyCauchyTheorem hopen hCΩ hf (isNullHomologous_of_convex hconv hopen hCΩ)

/-- **The classical residue theorem for a cycle in a convex open set.** For `f` holomorphic on
`Ω ∖ S` and meromorphic at each point of `S` lying in the convex open `Ω`, and a contour cycle `C`
in `Ω` whose trace avoids `S`,

`∮_C f = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`. -/
theorem classicalResidueTheorem_convex {S : Finset ℂ} (hconv : Convex ℝ Ω) (hopen : IsOpen Ω)
    (hf : DifferentiableOn ℂ f (Ω \ (↑S : Set ℂ))) (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hCΩ : IsIn C Ω) (hoff : ∀ s ∈ S, s ∉ trace C) :
    integral f C = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s :=
  TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous hopen hf hmero hCΩ hoff
    (isNullHomologous_of_convex hconv hopen hCΩ)

/-- **The generalized residue theorem for a cycle in a convex open set, simple-pole regime.** Each
curve of the cycle may run through the singularities, which are at worst simple poles; the Cauchy
principal value of the cycle integral is the winding-weighted residue sum. Null-homology,
condition (A′) and condition (B) are all discharged. -/
theorem hungerbuhlerWasem_residueTheorem_of_simple_poles_convex {S : Finset ℂ}
    (hconv : Convex ℝ Ω) (hopen : IsOpen Ω) (hSΩ : (S : Set ℂ) ⊆ Ω)
    (hf : DifferentiableOn ℂ f (Ω \ (S : Set ℂ))) (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hCΩ : IsIn C Ω)
    (h_imm : ∀ δ ∈ FreeAbelianGroup.support C, IsPwC1ImmersionOn (⇑δ) δ.a δ.b)
    (hbase : ∀ δ ∈ FreeAbelianGroup.support C, δ δ.a ∉ (S : Set ℂ))
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV C f
      (2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s) :=
  hungerbuhlerWasem_residueTheorem_of_simple_poles hopen S hSΩ hf hmero hCΩ h_imm hbase
    (isNullHomologous_of_convex hconv hopen hCΩ) h_simple

end Cycle

end TauCeti.Contour

end
