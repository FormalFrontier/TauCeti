/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Residue.SimplePole
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The residue of a quotient at a simple zero of the denominator

For `g, h` analytic at `z₀` with `h z₀ = 0` and `h' z₀ ≠ 0`, the quotient `g / h` has at worst a
simple pole at `z₀` and

`Res_{z₀} (g / h) = g z₀ / h' z₀`.

This is the textbook recipe for the residue of a quotient — the one used to evaluate essentially
every concrete residue of a rational or meromorphic function, and hence the computational input to
the roadmap's applications: the classical residue theorem
(`TauCeti.Contour.classicalResidueTheorem_circle`) and the improper integrals reached by the
Hungerbühler–Wasem generalized residue theorem
(`TauCeti.Contour.hungerbuhlerWasem_residueTheorem`) both reduce an integral to a sum of residues,
which then have to be *computed*.

The mechanism is the simple-pole limit rule
`TauCeti.Contour.residue_eq_of_tendsto_sub_mul`: since `h z₀ = 0`, the difference quotient
`slope h z₀ z` *is* `h z / (z − z₀)`, so its reciprocal `(z − z₀) / h z` tends to `(h' z₀)⁻¹` by
the very definition of the derivative (`hasDerivAt_iff_tendsto_slope`). Multiplying by the
continuous factor `g` gives `(z − z₀) · (g z / h z) → g z₀ / h' z₀`, and that limit is the residue.
No Laurent expansion of `h` is needed: only the first-order information `h z₀ = 0`, `h' z₀ ≠ 0`.

The companion order computation is recorded alongside, because the Hungerbühler–Wasem hypotheses
are stated in terms of pole orders: a simple zero of the denominator drops the order by exactly
one (`meromorphicOrderAt_div_of_deriv_ne_zero`), so `g / h` has an *exactly* simple pole as soon as
`g z₀ ≠ 0` (`meromorphicOrderAt_div_eq_neg_one`). That is precisely the shape of hypothesis that
`TauCeti.Contour.hasCauchyPV_half_residue_of_simple_pole` and
`TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles` consume.

## Main results

* `TauCeti.Contour.residue_div_of_deriv_ne_zero` — `residue (g / h) z₀ = g z₀ / deriv h z₀` at a
  simple zero `z₀` of `h`.
* `TauCeti.Contour.residue_inv_of_deriv_ne_zero` — the numerator-free case
  `residue (fun z => (h z)⁻¹) z₀ = (deriv h z₀)⁻¹`.
* `TauCeti.Contour.meromorphicOrderAt_div_of_deriv_ne_zero` — a simple zero of the denominator
  lowers the meromorphic order by one.
* `TauCeti.Contour.meromorphicOrderAt_div_eq_neg_one` — the pole is *exactly* simple when the
  numerator does not vanish, the `meromorphicOrderAt … = −1` hypothesis of the simple-pole
  residue theorems.
* `TauCeti.Contour.residue_inv_pow_sub_one` — the worked example
  `residue (fun z => (z ^ n − 1)⁻¹) ζ = ζ / n` at an `n`-th root of unity `ζ`, and
  `TauCeti.Contour.residue_inv_sq_add_one_I` — `residue (fun z => (z ^ 2 + 1)⁻¹) I = −(I / 2)`, the
  residue behind the improper integral `∫ dx / (1 + x²)`.

These are Layer 2 results of the contour-integration roadmap: the residue against Mathlib's
`meromorphicOrderAt` API, in the form the residue theorems' right-hand sides are evaluated with.

## Implementation notes

The derivative hypothesis is phrased with Mathlib's `deriv` rather than a bundled `HasDerivAt`
witness, so that the statement reads as the textbook formula `g z₀ / h'(z₀)`; `AnalyticAt`
supplies differentiability, so a `HasDerivAt` witness converts with `HasDerivAt.deriv`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 (the residue at a simple pole of a quotient).
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Filter Topology Complex

namespace TauCeti.Contour

variable {g h : ℂ → ℂ} {z₀ : ℂ}

/-- At a zero of `h` with derivative `c ≠ 0`, the reciprocal difference quotient `(z − z₀) / h z`
tends to `c⁻¹`. Since `h z₀ = 0`, the quotient `h z / (z − z₀)` is literally `slope h z₀ z`, so
this is the definition of the derivative (`hasDerivAt_iff_tendsto_slope`) followed by inversion. -/
private theorem tendsto_sub_div_of_hasDerivAt {c : ℂ} (hd : HasDerivAt h c z₀)
    (hh0 : h z₀ = 0) (hc : c ≠ 0) :
    Tendsto (fun z => (z - z₀) / h z) (𝓝[≠] z₀) (𝓝 c⁻¹) := by
  refine Tendsto.congr' (Eventually.of_forall fun z => ?_) (hd.tendsto_slope.inv₀ hc)
  rw [slope_def_field, hh0, sub_zero, inv_div]

/-- **The residue of a quotient at a simple zero of the denominator.** If `g` and `h` are analytic
at `z₀` with `h z₀ = 0` and `deriv h z₀ ≠ 0`, then

`residue (fun z => g z / h z) z₀ = g z₀ / deriv h z₀`.

This is the textbook computation rule for residues of quotients; it needs only the first-order
data `h z₀ = 0` and `deriv h z₀ ≠ 0` at the denominator's zero, no Laurent expansion. -/
theorem residue_div_of_deriv_ne_zero (hg : AnalyticAt ℂ g z₀) (hh : AnalyticAt ℂ h z₀)
    (hh0 : h z₀ = 0) (hh' : deriv h z₀ ≠ 0) :
    residue (fun z => g z / h z) z₀ = g z₀ / deriv h z₀ := by
  have hquot : Tendsto (fun z => (z - z₀) / h z) (𝓝[≠] z₀) (𝓝 (deriv h z₀)⁻¹) :=
    tendsto_sub_div_of_hasDerivAt hh.differentiableAt.hasDerivAt hh0 hh'
  have hgc : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hkey : Tendsto (fun z => g z * ((z - z₀) / h z)) (𝓝[≠] z₀) (𝓝 (g z₀ / deriv h z₀)) := by
    rw [div_eq_mul_inv]
    exact hgc.mul hquot
  have hmero : MeromorphicAt (fun z => g z / h z) z₀ :=
    hg.meromorphicAt.fun_div hh.meromorphicAt
  exact residue_eq_of_tendsto_sub_mul hmero
    (Tendsto.congr' (Eventually.of_forall fun z => by ring) hkey)

/-- **The residue of a reciprocal at a simple zero.** The numerator-free case of
`TauCeti.Contour.residue_div_of_deriv_ne_zero`: at a zero of `h` with non-vanishing derivative,
`residue (fun z => (h z)⁻¹) z₀ = (deriv h z₀)⁻¹`. -/
theorem residue_inv_of_deriv_ne_zero (hh : AnalyticAt ℂ h z₀) (hh0 : h z₀ = 0)
    (hh' : deriv h z₀ ≠ 0) :
    residue (fun z => (h z)⁻¹) z₀ = (deriv h z₀)⁻¹ := by
  simpa only [one_div] using
    residue_div_of_deriv_ne_zero (g := fun _ => 1) analyticAt_const hh hh0 hh'

/-- A simple zero of the denominator lowers the meromorphic order by one: if `g` is meromorphic at
`z₀` and `h` is analytic at `z₀` with `h z₀ = 0` and `deriv h z₀ ≠ 0`, then

`meromorphicOrderAt (fun z => g z / h z) z₀ = meromorphicOrderAt g z₀ − 1`.

The denominator's analytic order at a zero with non-vanishing derivative is `1`
(`AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`), and orders subtract across a quotient
(`fun_meromorphicOrderAt_div`). -/
theorem meromorphicOrderAt_div_of_deriv_ne_zero (hg : MeromorphicAt g z₀) (hh : AnalyticAt ℂ h z₀)
    (hh0 : h z₀ = 0) (hh' : deriv h z₀ ≠ 0) :
    meromorphicOrderAt (fun z => g z / h z) z₀ = meromorphicOrderAt g z₀ - 1 := by
  have hord : meromorphicOrderAt h z₀ = 1 := by
    rw [hh.meromorphicOrderAt_eq, hh.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hh0 hh']
    simp
  rw [fun_meromorphicOrderAt_div hg hh.meromorphicAt, hord]

/-- **A non-vanishing numerator over a simple zero is an exactly simple pole.** If `g` and `h` are
analytic at `z₀` with `g z₀ ≠ 0`, `h z₀ = 0` and `deriv h z₀ ≠ 0`, then
`meromorphicOrderAt (fun z => g z / h z) z₀ = −1`. This is the `order = −1` hypothesis consumed by
the simple-pole residue theorems
(`TauCeti.Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles`,
`TauCeti.Contour.hasCauchyPV_half_residue_of_simple_pole`), whose residue is then
`g z₀ / deriv h z₀` by `TauCeti.Contour.residue_div_of_deriv_ne_zero`. -/
theorem meromorphicOrderAt_div_eq_neg_one (hg : AnalyticAt ℂ g z₀) (hgne : g z₀ ≠ 0)
    (hh : AnalyticAt ℂ h z₀) (hh0 : h z₀ = 0) (hh' : deriv h z₀ ≠ 0) :
    meromorphicOrderAt (fun z => g z / h z) z₀ = -1 := by
  rw [meromorphicOrderAt_div_of_deriv_ne_zero hg.meromorphicAt hh hh0 hh',
    hg.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hgne)]
  simp

/-! ### Worked examples

Two concrete residues that the quotient rule reads off in a few lines, and that the classical
residue theorem's right-hand side needs in order to produce a number. -/

/-- **The residue of `(z ^ n − 1)⁻¹` at an `n`-th root of unity** is `ζ / n`. The denominator has a
simple zero at `ζ` with derivative `n · ζ ^ (n − 1) = n · ζ⁻¹`, so the residue is `ζ / n`;
summing
over the `n`-th roots of unity recovers the familiar partial-fraction coefficients of
`(z ^ n − 1)⁻¹`. -/
theorem residue_inv_pow_sub_one {n : ℕ} (hn : n ≠ 0) {ζ : ℂ} (hζ : ζ ^ n = 1) :
    residue (fun z => (z ^ n - 1)⁻¹) ζ = ζ / n := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hζ
    exact zero_ne_one hζ
  -- `ζ ^ (n − 1) = ζ⁻¹`, since `ζ ^ (n − 1) · ζ = ζ ^ n = 1`.
  have hpred : ζ ^ (n - 1) = ζ⁻¹ := by
    have hmul : ζ ^ (n - 1) * ζ = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      exact hζ
    rw [inv_eq_one_div, eq_div_iff hζ0]
    exact hmul
  have hda : HasDerivAt (fun z : ℂ => z ^ n - 1) ((n : ℂ) * ζ⁻¹) ζ := by
    simpa [hpred] using (hasDerivAt_pow n ζ).sub_const 1
  have hd0 : deriv (fun z : ℂ => z ^ n - 1) ζ ≠ 0 := by
    rw [hda.deriv]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (inv_ne_zero hζ0)
  rw [residue_inv_of_deriv_ne_zero (h := fun z : ℂ => z ^ n - 1) (by fun_prop)
    (by rw [hζ, sub_self]) hd0, hda.deriv, mul_inv, inv_inv]
  ring

/-- **The residue of `(z ^ 2 + 1)⁻¹` at `I`** is `−(I / 2)`: the denominator has a simple zero at
`I` with derivative `2 I`, so the residue is `(2 I)⁻¹ = −(I / 2)`. This is the residue behind the
classical evaluation of the improper integral `∫ dx / (1 + x ^ 2) = π`. -/
theorem residue_inv_sq_add_one_I : residue (fun z => (z ^ 2 + 1)⁻¹) I = -(I / 2) := by
  have hda : HasDerivAt (fun z : ℂ => z ^ 2 + 1) (2 * I) I := by
    simpa using (hasDerivAt_pow 2 I).add_const 1
  have hd0 : deriv (fun z : ℂ => z ^ 2 + 1) I ≠ 0 := by
    rw [hda.deriv]
    exact mul_ne_zero two_ne_zero I_ne_zero
  rw [residue_inv_of_deriv_ne_zero (h := fun z : ℂ => z ^ 2 + 1) (by fun_prop)
    (by rw [I_sq]; ring) hd0, hda.deriv, mul_inv, inv_I]
  ring

end TauCeti.Contour

end
