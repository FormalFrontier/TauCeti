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
public import TauCeti.Analysis.Contour.Winding.StarConvex

/-!
# Contour integration in a star-shaped domain

Layer 3 of the contour integration roadmap proves the homology Cauchy theorem, and Layers 2 and 4
state the residue theorems, for a cycle that is **null-homologous** in the domain of holomorphy.
That hypothesis is the right one — it is exactly what the proofs need — but it is not the one an
application arrives with. An application arrives with an open disc, half-plane, strip, open
rectangle or slit plane, or with a convex open neighborhood of a rectangle or triangle, and a
contour drawn inside it.

`TauCeti.Contour.isNullHomologous_of_starConvex` closes that gap: a closed curve in a set that is
star-shaped about some point is null-homologous there. This file records the resulting
hypothesis-free statements:

* Cauchy's theorem `∮_γ f = 0`, for a curve and for a cycle, and its `Metric.ball` case;
* Cauchy's integral formula `n_z(γ) · f(z) = (2πi)⁻¹ ∮_γ f/(· − z)` in every derivative order, for
  a curve, and its `Metric.ball` case;
* the classical residue theorem `∮_γ f = 2πi · Σ_s n_s(γ) · Res_s f` for poles off the curve, for a
  curve and for a cycle;
* the argument principle, in the ordinary and the principal-value (zeros **on** the curve) forms,
  for a curve;
* the Hungerbühler–Wasem generalized residue theorem in its unconditional simple-pole regime,
  singularities on the curve included, for a curve and for a cycle, together with the half-residue
  case.

In each the hypothesis `IsNullHomologous` disappears, replaced by star-shapedness and openness of
the ambient domain. Star-shapedness is genuinely a hypothesis on the *domain*, not on the curve:
nothing is asked of `γ` beyond the piecewise-`C¹` regularity (or, where a principal value is taken,
the immersion regularity) that every statement of the tower already carries.

The relation to the other route to null-homology,
`TauCeti.Contour.isNullHomologous_of_pathHomotopy_refl`, is one-way: a star-shaped domain
contracts, so every loop in it is null-homotopic there and the homotopy hypothesis is implied. The
value of the statements below is that the caller never has to build that homotopy. Conversely the
homotopy route reaches strictly more domains, at the cost of exhibiting the contraction.

A convex `Ω` is star-shaped about any of its points; a caller holding `hconv : Convex ℝ Ω` and a
curve in `Ω` supplies `hconv.starConvex (hγΩ a left_mem_uIcc)`, and the `Metric.ball` statements
below do exactly that.

## Roadmap

The disc statements `TauCeti.Contour.cauchyTheorem_ball` and
`TauCeti.Contour.cauchyIntegralFormula_ball`, with the star-shaped statements they specialise, are
Layer 2's "Cauchy's theorem for a contractible contour as a corollary (reconciled with Mathlib's
disc statements)": Mathlib's disc Cauchy theory integrates over the bounding circle, and these
extend it to an arbitrary closed piecewise-`C¹` curve inside the disc. The residue and argument
statements are what makes the rest of the tower applicable at all: Layer 2's classical residue
theorem and argument principle, and Layer 4's Hungerbühler–Wasem theorem, are all stated for a
null-homologous cycle, and the roadmap's acceptance criteria — poles inside a circle, a simple pole
*on* the contour contributing the half-residue, an improper integral along the real axis — are
posed on a disc or a half-plane, which are star-shaped. The roadmap's first client, the valence
formula, integrates `logDeriv f` around a contour in the upper half-plane, which is star-shaped
too, and passes through the elliptic points, so it consumes
`TauCeti.Contour.hasCauchyPV_logDeriv_starConvex`.

## Main results

* `TauCeti.Contour.cauchyTheorem_starConvex`, `TauCeti.Contour.cauchyIntegralFormula_starConvex` —
  Cauchy's theorem and integral formula on a star-shaped open set.
* `TauCeti.Contour.classicalResidueTheorem_starConvex`,
  `TauCeti.Contour.argumentPrinciple_starConvex` — the residue theorem and the argument principle
  there.
* `TauCeti.Contour.hasCauchyPV_logDeriv_starConvex`,
  `TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles_starConvex` — the
  principal-value statements, whose singularities may lie on the curve.
* `TauCeti.Contour.Cycle.cauchyTheorem_starConvex`,
  `TauCeti.Contour.Cycle.classicalResidueTheorem_starConvex`,
  `TauCeti.Contour.Cycle.hungerbuhlerWasem_residueTheorem_of_simple_poles_starConvex` — the cycle
  forms.

## Provenance

No formalization is vendored: each statement is its null-homologous counterpart with the
null-homology discharged by `TauCeti.Contour.isNullHomologous_of_starConvex`.

## References

* S. Lang, *Complex Analysis* (GTM 103), Ch. IV — Cauchy's theorem on a convex, indeed on a
  star-shaped, set.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Theorem 3.3, the principal-value statements below.
-/

public section

open Complex MeasureTheory Set

open scoped Interval Real

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {Ω : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {x : ℂ}

/-- **Cauchy's theorem on a star-shaped open set.** A holomorphic function integrates to zero along
every closed piecewise-`C¹` curve contained in an open set that is star-shaped about some point.

This is the homology Cauchy theorem `TauCeti.Contour.homologyCauchyTheorem` with its
null-homology hypothesis discharged by star-shapedness, and it is the form in which Cauchy's
theorem is usually applied: on an open disc, half-plane, strip, open rectangle, or slit plane. -/
theorem cauchyTheorem_starConvex (hstar : StarConvex ℝ x Ω) (hopen : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : IsPiecewiseC1On γ a b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 :=
  homologyCauchyTheorem hopen γ a b hγ hγΩ hclosed hf
    (isNullHomologous_of_starConvex hstar hγ hclosed hγΩ)

/-- **Cauchy's theorem on a disc** — the `Metric.ball` case of
`TauCeti.Contour.cauchyTheorem_starConvex`: a function holomorphic on a disc integrates to zero
along every closed piecewise-`C¹` curve inside it, not only along the boundary circles. -/
theorem cauchyTheorem_ball {c : ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hγ : IsPiecewiseC1On γ a b) (hγr : ∀ t ∈ uIcc a b, γ t ∈ Metric.ball c r)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 :=
  cauchyTheorem_starConvex ((convex_ball c r).starConvex (hγr a left_mem_uIcc))
    Metric.isOpen_ball hf hγ hγr hclosed

/-- **Cauchy's integral formula on a star-shaped open set, for the `k`-th derivative.** For `f`
holomorphic on an open `Ω` star-shaped about `x`, a closed piecewise-`C¹` curve `γ` in `Ω`, and
`z ∈ Ω` off the curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`. -/
theorem cauchyIntegralFormula_iteratedDeriv_starConvex {z : ℂ} (hstar : StarConvex ℝ x Ω)
    (hopen : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) (hγ : IsPiecewiseC1On γ a b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b) (hz : z ∈ Ω)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) (k : ℕ) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ (k + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z *
          (iteratedDeriv k f z / (k.factorial : ℂ)) :=
  cauchyIntegralFormula_iteratedDeriv_nullHomologous hopen hf hγ hγΩ hclosed
    (isNullHomologous_of_starConvex hstar hγ hclosed hγΩ) hz hoff k

/-- **Cauchy's integral formula on a star-shaped open set.** For `f` holomorphic on an open `Ω`
star-shaped about `x`, a closed piecewise-`C¹` curve `γ` in `Ω`, and `z ∈ Ω` off the curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z)) = 2πi · n_z(γ) · f z`. -/
theorem cauchyIntegralFormula_starConvex {z : ℂ} (hstar : StarConvex ℝ x Ω) (hopen : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (hγ : IsPiecewiseC1On γ a b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b) (hz : z ∈ Ω)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z :=
  cauchyIntegralFormula_nullHomologous hopen hf hγ hγΩ hclosed
    (isNullHomologous_of_starConvex hstar hγ hclosed hγΩ) hz hoff

/-- **Cauchy's integral formula on a disc, for the `k`-th derivative** — the `Metric.ball` case of
`TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_starConvex`. -/
theorem cauchyIntegralFormula_iteratedDeriv_ball {c : ℂ} {r : ℝ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hγ : IsPiecewiseC1On γ a b)
    (hγr : ∀ t ∈ uIcc a b, γ t ∈ Metric.ball c r) (hclosed : γ a = γ b)
    (hz : z ∈ Metric.ball c r) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) (k : ℕ) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ (k + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z *
          (iteratedDeriv k f z / (k.factorial : ℂ)) :=
  cauchyIntegralFormula_iteratedDeriv_starConvex
    ((convex_ball c r).starConvex (hγr a left_mem_uIcc)) Metric.isOpen_ball hf hγ hγr hclosed hz
    hoff k

/-- **Cauchy's integral formula on a disc** — the `Metric.ball` case of
`TauCeti.Contour.cauchyIntegralFormula_starConvex`. -/
theorem cauchyIntegralFormula_ball {c : ℂ} {r : ℝ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hγ : IsPiecewiseC1On γ a b)
    (hγr : ∀ t ∈ uIcc a b, γ t ∈ Metric.ball c r) (hclosed : γ a = γ b)
    (hz : z ∈ Metric.ball c r) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z :=
  cauchyIntegralFormula_starConvex ((convex_ball c r).starConvex (hγr a left_mem_uIcc))
    Metric.isOpen_ball hf hγ hγr hclosed hz hoff

/-- **The classical residue theorem on a star-shaped open set.** Let `Ω` be open and star-shaped
about `x`, `S` a finite set, `f` holomorphic on `Ω ∖ S` and meromorphic at each point of `S` lying
in `Ω`, and let `γ` be a closed piecewise-`C¹` curve in `Ω` avoiding `S`. Then

`∫ t in a..b, γ' t • f (γ t) = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`.

Unlike `TauCeti.Contour.classicalResidueTheorem_circle`, the curve is arbitrary and the poles need
not be enclosed: a pole in a component of the complement that `γ` does not wind around simply gets
weight `0`. -/
theorem classicalResidueTheorem_starConvex {S : Finset ℂ} (hstar : StarConvex ℝ x Ω)
    (hopen : IsOpen Ω) (hf : DifferentiableOn ℂ f (Ω \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hγ : IsPiecewiseC1On γ a b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s :=
  classicalResidueTheorem_nullHomologous hopen hf hmero hγ hγΩ hclosed hoff
    (isNullHomologous_of_starConvex hstar hγ hclosed hγΩ)

/-- **The argument principle on a star-shaped open set.** For `f` analytic and non-vanishing on an
open `Ω` star-shaped about `x`, off a finite `S`, meromorphic of order `ord` at each point of `S`
lying in `Ω`, and a closed piecewise-`C¹` curve `γ` in `Ω` avoiding `S`,

`∫ t in a..b, γ' t • (f'/f) (γ t) = 2πi · ∑_{z ∈ S} n_z(γ) · ord z`,

the winding-weighted count of the zeros and poles of `f`. -/
theorem argumentPrinciple_starConvex {S : Finset ℂ} {ord : ℂ → ℤ} (hstar : StarConvex ℝ x Ω)
    (hopen : IsOpen Ω) (hoffS : ∀ z ∈ Ω, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ Ω → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hγ : IsPiecewiseC1On γ a b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) :
    ∫ t in a..b, deriv γ t • logDeriv f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ) :=
  argumentPrinciple_nullHomologous hopen hoffS hmero hord hγ hγΩ hclosed hγoff
    (isNullHomologous_of_starConvex hstar hγ hclosed hγΩ)

/-- **The generalized residue theorem on a star-shaped open set, simple-pole regime.** Let `Ω` be
open and star-shaped about `x`, `S ⊆ Ω` finite, `f` holomorphic on `Ω ∖ S` with at worst a simple
pole at each point of `S`, and `γ` a closed piecewise-`C¹` immersion in `Ω` based off `S`. Then the
Cauchy principal value of the contour integral is

`p.v. ∮_γ f = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`,

with the generalized, possibly non-integer, winding numbers as weights. The curve is free to pass
**through** the singularities; conditions (A′) and (B) of Hungerbühler–Wasem are automatic in this
regime, while null-homology is automatic by star-shapedness. Thus null-homology and conditions (A′)
and (B) require no additional hypotheses in this regime. -/
theorem hungerbuhlerWasem_residueTheorem_of_simple_poles_starConvex {S : Finset ℂ}
    (hstar : StarConvex ℝ x Ω) (hopen : IsOpen Ω) (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSΩ : (S : Set ℂ) ⊆ Ω) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hf : DifferentiableOn ℂ f (Ω \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) :=
  hungerbuhlerWasem_residueTheorem_of_simple_poles hopen S γ a b hγ_imm hSΩ hclosed hγa hγΩ hf
    hmero (isNullHomologous_of_starConvex hstar hγ_imm.isPiecewiseC1On hclosed hγΩ) h_simple

/-- **The half-residue on a star-shaped open set.** An on-curve simple pole about which the
immersion has generalized winding number `½` contributes `πi · Res_s f` to the principal value —
the `S = {s}` case of
`TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles_starConvex`. -/
theorem hasCauchyPV_half_residue_of_simple_pole_starConvex {s : ℂ} (hstar : StarConvex ℝ x Ω)
    (hopen : IsOpen Ω) (hγ_imm : IsPwC1ImmersionOn γ a b) (hsΩ : s ∈ Ω) (hclosed : γ a = γ b)
    (hγa : γ a ≠ s) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hf : DifferentiableOn ℂ f (Ω \ {s}))
    (hmero : MeromorphicAt f s)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s)
    (hwind : windingNumber γ a b s = 1 / 2) :
    HasCauchyPV γ a b f ((Real.pi : ℂ) * Complex.I * residue f s) :=
  hasCauchyPV_half_residue_of_simple_pole hopen γ a b s hγ_imm hsΩ hclosed hγa hγΩ hf hmero
    (isNullHomologous_of_starConvex hstar hγ_imm.isPiecewiseC1On hclosed hγΩ) h_simple hwind

/-- **The argument principle on a star-shaped open set, for a curve running through the zeros.**
With `f` analytic and non-vanishing on an open `Ω` star-shaped about `x`, off a finite `S`,
meromorphic of order `ord` at each point of `S` lying in `Ω`, and `γ` a closed piecewise-`C¹`
immersion in `Ω` based off `S`,

`p.v. ∮_γ f'/f = 2πi · ∑_{z ∈ S} n_z(γ) · ord z`.

The curve may pass through the zeros and poles of `f`; each such point contributes its order
weighted by a generalized winding number, `½` in the standard configuration of a positively
oriented curve with a single smooth branch through the point. -/
theorem hasCauchyPV_logDeriv_starConvex {S : Finset ℂ} {ord : ℂ → ℤ} (hstar : StarConvex ℝ x Ω)
    (hopen : IsOpen Ω) (hoffS : ∀ z ∈ Ω, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ Ω → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hγ_imm : IsPwC1ImmersionOn γ a b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hγa : γ a ∉ (S : Set ℂ)) :
    HasCauchyPV γ a b (logDeriv f)
      (2 * (Real.pi : ℂ) * Complex.I * ∑ z ∈ S, windingNumber γ a b z * (ord z : ℂ)) :=
  hasCauchyPV_logDeriv_nullHomologous hopen hoffS hmero hord hγ_imm hγΩ hclosed hγa
    (isNullHomologous_of_starConvex hstar hγ_imm.isPiecewiseC1On hclosed hγΩ)

namespace Cycle

variable {C : Cycle}

/-- **Cauchy's theorem for a cycle in a star-shaped open set.** A holomorphic function integrates
to zero along every contour cycle contained in an open set star-shaped about some point. -/
theorem cauchyTheorem_starConvex (hstar : StarConvex ℝ x Ω) (hopen : IsOpen Ω) (hCΩ : IsIn C Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    integral f C = 0 :=
  homologyCauchyTheorem hopen hCΩ hf (isNullHomologous_of_starConvex hstar hCΩ)

/-- **The classical residue theorem for a cycle in a star-shaped open set.** For `f` holomorphic on
`Ω ∖ S` and meromorphic at each point of `S` lying in the open, star-shaped `Ω`, and a contour
cycle `C` in `Ω` whose trace avoids `S`,

`∮_C f = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`. -/
theorem classicalResidueTheorem_starConvex {S : Finset ℂ} (hstar : StarConvex ℝ x Ω)
    (hopen : IsOpen Ω) (hf : DifferentiableOn ℂ f (Ω \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ Ω → MeromorphicAt f s)
    (hCΩ : IsIn C Ω) (hoff : ∀ s ∈ S, s ∉ trace C) :
    integral f C = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s :=
  TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous hopen hf hmero hCΩ hoff
    (isNullHomologous_of_starConvex hstar hCΩ)

/-- **The generalized residue theorem for a cycle in a star-shaped open set, simple-pole regime.**
Each curve of the cycle may run through the singularities, which are at worst simple poles; the
Cauchy principal value of the cycle integral is the winding-weighted residue sum. Null-homology,
condition (A′) and condition (B) are all discharged. -/
theorem hungerbuhlerWasem_residueTheorem_of_simple_poles_starConvex {S : Finset ℂ}
    (hstar : StarConvex ℝ x Ω) (hopen : IsOpen Ω) (hSΩ : (S : Set ℂ) ⊆ Ω)
    (hf : DifferentiableOn ℂ f (Ω \ (S : Set ℂ))) (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hCΩ : IsIn C Ω)
    (h_imm : ∀ δ ∈ FreeAbelianGroup.support C, IsPwC1ImmersionOn (⇑δ) δ.a δ.b)
    (hbase : ∀ δ ∈ FreeAbelianGroup.support C, δ δ.a ∉ (S : Set ℂ))
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV C f
      (2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s) :=
  hungerbuhlerWasem_residueTheorem_of_simple_poles hopen S hSΩ hf hmero hCΩ h_imm hbase
    (isNullHomologous_of_starConvex hstar hCΩ) h_simple

end Cycle

end TauCeti.Contour

end
