/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Cycle
public import TauCeti.Analysis.Contour.Winding.Number.Circle

/-!
# Cauchy's integral formula in homology form, for all derivatives

For `f` holomorphic on an open `U`, a closed piecewise-`C¹` curve `γ` in `U` that is
**null-homologous** there, and a point `z ∈ U` off the curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`

for every `k : ℕ`, with `n_z(γ)` the generalized winding number. The case `k = 0` is the second
bullet of the roadmap's Layer 3 — the identity `f(z) · n_z(C) = (2πi)⁻¹ ∮_C f(w)/(w − z) dw` that
accompanies the homology Cauchy theorem — and the general `k` is its derivative form.

The proof is a single application of the residue theorem for a null-homologous cycle
(`TauCeti.Contour.classicalResidueTheorem_nullHomologous`) to the Cauchy kernel
`w ↦ f w / (w − z) ^ (k + 1)`, whose only singularity in `U` is the pole at `z`, together with the
residue computation `TauCeti.Contour.residue_div_sub_pow_of_analyticAt` reading the residue there as
the Taylor coefficient `f⁽ᵏ⁾(z) / k !`. Holomorphy on the *open* `U` is what turns
`DifferentiableOn` into analyticity at `z` (`DifferentiableOn.analyticOnNhd`), so the Taylor
coefficient exists at all.

## Main results

* `TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous` — the formula above, for
  every order `k`.
* `TauCeti.Contour.cauchyIntegralFormula_nullHomologous` — its `k = 0` case, the roadmap's Layer-3
  Cauchy integral formula `∮_γ f(w)/(w − z) dw = 2πi · n_z(γ) · f z`.
* `TauCeti.Contour.cauchyIntegralFormula_deriv_nullHomologous` — its `k = 1` case, stated with
  `deriv f z`.
* `TauCeti.Contour.circleIntegral_div_sub_pow_of_differentiableOn` — the round-circle corollary
  `∮_{C(c,R)} f(w)/(w − z) ^ (k + 1) dw = 2πi · f⁽ᵏ⁾(z) / k !` at an arbitrary `z` **inside** the
  circle.

## Relation to Mathlib

Mathlib's higher-derivative Cauchy integral formulas
(`Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable` and its
`DiffContOnCl` / `DifferentiableOn` variants) evaluate the circle integral of
`(w − c)^{−(k+1)} • f w` at the **centre** `c` of the circle only, and the file recording them
carries an explicit `TODO: add a version for w ∈ Metric.ball c R`. The circle corollary here is that
off-centre version, obtained for free from the null-homologous statement; only its `k = 0` case is
already upstream, as `Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`. The price
of the extra generality in `k` is holomorphy on an open neighbourhood of the closed disc, where
Mathlib asks only for continuity up to the boundary.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 (the index of a point and the homology form of Cauchy's
  theorem and integral formula).
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.

## Provenance

No formal source is vendored: the statements are assembled here from the repository's residue
theorem for a null-homologous cycle and its residue API, which are themselves migrated from the
AINTLIB `LeanModularForms` development.
-/

public section

open Complex MeasureTheory Metric Set

open scoped Interval Real

namespace TauCeti.Contour

/-- **Cauchy's integral formula for the `k`-th derivative, homology form.** Let `f` be holomorphic
on an open `U`, let `γ` be a closed piecewise-`C¹` curve in `U` that is null-homologous there, and
let `z ∈ U` lie off the curve. Then for every `k`,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`,

the `k`-th Taylor coefficient of `f` at `z` weighted by the generalized winding number of `γ` about
`z`. Only the pole at `z` contributes: the residue theorem for a null-homologous cycle applied to
the Cauchy kernel `w ↦ f w / (w − z) ^ (k + 1)` leaves the single residue
`iteratedDeriv k f z / k !`. -/
theorem cauchyIntegralFormula_iteratedDeriv_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U)
    (hz : z ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) (k : ℕ) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ (k + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z *
          (iteratedDeriv k f z / (k.factorial : ℂ)) := by
  have hfz : AnalyticAt ℂ f z := hf.analyticOnNhd hU z hz
  have hker := classicalResidueTheorem_nullHomologous (f := fun w => f w / (w - z) ^ (k + 1))
    (S := {z}) hU ?_ ?_ hγ hγU hclosed ?_ hnull
  · rw [hker, Finset.sum_singleton, residue_div_sub_pow_of_analyticAt hfz k]
    ring
  · -- Off `z` the kernel is a quotient of holomorphic functions with non-vanishing denominator.
    rw [Finset.coe_singleton]
    intro w hw
    exact ((hf w hw.1).mono Set.sdiff_subset).div (by fun_prop)
      (pow_ne_zero _ (sub_ne_zero.mpr hw.2))
  · -- At `z` it is meromorphic, `f` being analytic there.
    intro s hs _
    rw [Finset.mem_singleton] at hs
    subst hs
    exact hfz.meromorphicAt.div (by fun_prop)
  · intro t ht
    rw [Finset.coe_singleton]
    exact hoff t ht

/-- **Cauchy's integral formula, homology form** (roadmap Layer 3). For `f` holomorphic on an open
`U`, `γ` a closed piecewise-`C¹` curve in `U` that is null-homologous there, and `z ∈ U` off the
curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z)) = 2πi · n_z(γ) · f z`,

so that `f z · n_z(γ) = (2πi)⁻¹ ∮_γ f(w)/(w − z) dw`: the Cauchy-type integral recovers the value of
`f` at `z`, counted with the multiplicity with which `γ` winds around it. The `S = ∅` companion of
this statement is the homology Cauchy theorem `TauCeti.Contour.homologyCauchyTheorem`. -/
theorem cauchyIntegralFormula_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U)
    (hz : z ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * f z := by
  simpa using cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hγ hγU hclosed hnull hz
    hoff 0

/-- **Cauchy's integral formula for the first derivative, homology form.** The `k = 1` case of
`TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous`, stated with `deriv f z`:

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ 2) = 2πi · n_z(γ) · f' z`. -/
theorem cauchyIntegralFormula_deriv_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U)
    (hz : z ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ 2)
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * deriv f z := by
  simpa [iteratedDeriv_one] using
    cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hγ hγU hclosed hnull hz hoff 1

/-- **Cauchy's integral formula for derivatives at an off-centre point of a disc.** If `f` is
holomorphic on an open `U` containing the closed disc `closedBall c R` and `z` lies strictly inside
that disc, then

`∮_{C(c, R)} f(w) / (w − z) ^ (k + 1) dw = 2πi · f⁽ᵏ⁾(z) / k !`.

The counterclockwise circle is null-homologous in `U` — a point outside `U` lies outside the closed
disc, hence has winding number `0` (`TauCeti.Contour.windingNumber_circleMap_eq_zero_of_lt_dist`) —
and it winds once about `z` (`TauCeti.Contour.windingNumber_circleMap_eq_one_of_dist_lt`), so
`TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous` applies with weight `1`.

Mathlib's higher-derivative circle formulas are stated at the centre of the circle only; this is the
`w ∈ Metric.ball c R` version their file leaves as a TODO. For `k = 0`,
`Complex.circleIntegral_div_sub_of_differentiable_on_off_countable` is upstream and asks less
regularity (continuity on the closed disc, differentiability off a countable subset of the open
one). -/
theorem circleIntegral_div_sub_pow_of_differentiableOn {f : ℂ → ℂ} {U : Set ℂ} {c z : ℂ} {R : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hUR : closedBall c R ⊆ U) (hz : dist z c < R)
    (k : ℕ) :
    (∮ w in C(c, R), f w / (w - z) ^ (k + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * (iteratedDeriv k f z / (k.factorial : ℂ)) := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg hz
  have hclosed : circleMap c R 0 = circleMap c R (2 * Real.pi) := by
    simpa using (periodic_circleMap c R 0).symm
  have hnull : IsNullHomologous (circleMap c R) 0 (2 * Real.pi) U := by
    rw [isNullHomologous_iff]
    intro w hw
    exact windingNumber_circleMap_eq_zero_of_lt_dist hR.le
      (not_le.mp fun hle => hw (hUR (mem_closedBall.mpr hle)))
  rw [circleIntegral, cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf
      (IsPiecewiseC1On.of_contDiffOn (contDiff_circleMap c R).contDiffOn)
      (fun θ _ => hUR (circleMap_mem_closedBall c hR.le θ)) hclosed hnull
      (hUR (mem_closedBall.mpr hz.le))
      (fun θ _ => circleMap_ne_mem_ball (mem_ball.mpr hz) θ) k,
    windingNumber_circleMap_eq_one_of_dist_lt hz, mul_one]

end TauCeti.Contour

end
