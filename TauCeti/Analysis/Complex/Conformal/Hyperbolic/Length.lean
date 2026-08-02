/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.ClosedForm
public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.SpecialFunctions.Artanh
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Poincaré metric is the length metric of its density

`Hyperbolic/Distance.lean` defines the hyperbolic distance on the complex open unit disc by the
closed formula `hyperbolicDist z w = Real.artanh (pseudoHyperbolicExpr z w)`, and
`Hyperbolic/Density.lean` shows that its infinitesimal density is `(1 - ‖z‖ ^ 2)⁻¹` and that the
distance from the origin along a *radius* is the integral of that density along the radius. The
latter file records, in so many words, what was still missing: "the density-weighted length of a
general curve is not defined here, so this does not identify `hyperbolicDist` with the length
metric of the density between arbitrary points". This file supplies the definition and the
identification.

The definition is the obvious one: for a path `γ : ℝ → ℂ` in the disc,

`TauCeti.hyperbolicLength γ a b = ∫ t in a..b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)`,

the Euclidean speed integrated against the Poincaré density. The theorem is that
`hyperbolicDist z w` is the **least** such length over `C¹` paths from `z` to `w`
(`TauCeti.isLeast_hyperbolicLength`): no path is shorter
(`TauCeti.hyperbolicDist_le_hyperbolicLength`), and one path realises the value
(`TauCeti.exists_hyperbolicLength_eq_hyperbolicDist`).

## The proof

Both halves rest on one algebraic fact, the **conformal invariance of the density**
(`TauCeti.norm_deriv_unitDiscMoebiusFormula_div_one_sub_sq`): for the disc Moebius factor
`M z = (z - c) / (1 - conj c * z)`,

`‖M ′ z‖ / (1 - ‖M z‖ ^ 2) = (1 - ‖z‖ ^ 2)⁻¹`.

Indeed `‖M ′ z‖ = (1 - ‖c‖ ^ 2) / ‖1 - conj c * z‖ ^ 2`, while the defect identity
`TauCeti.one_sub_pseudoHyperbolicExpr_sq` evaluates the denominator as
`(1 - ‖z‖ ^ 2) (1 - ‖c‖ ^ 2) / ‖1 - conj c * z‖ ^ 2`; the Moebius denominator and the factor
`1 - ‖c‖ ^ 2` both cancel. Integrating this along a path gives
`TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp`: hyperbolic length is unchanged by
post-composition with a disc Moebius factor. That is what moves an arbitrary path to one starting
at the origin.

*The lower bound.* For a path with `γ a = 0` the estimate is a one-variable calculus argument.
Choosing the unit vector `v = conj (γ b) / ‖γ b‖`, the real function `ψ t = (v * γ t).re` runs
from `0` to `‖γ b‖` and satisfies `|ψ| ≤ ‖γ‖` and `|ψ ′| ≤ ‖γ ′‖`. Hence, pointwise,

`(Real.artanh ∘ ψ) ′ = ψ ′ / (1 - ψ ^ 2) ≤ ‖γ ′‖ / (1 - ‖γ‖ ^ 2)`,

the first inequality being `1 - ‖γ‖ ^ 2 ≤ 1 - ψ ^ 2` in the denominator, and the fundamental
theorem of calculus turns the left-hand integral into `Real.artanh ‖γ b‖ = hyperbolicDist (γ a)
(γ b)`. Projecting on a *linear* functional rather than on the norm is what keeps the comparison
function differentiable where the path crosses the origin.

*The bound is attained.* By the same invariance it suffices to exhibit a shortest path from the
origin, and the Euclidean radius `t ↦ u * t` is one: its hyperbolic length over `[0, r]` is
`∫ t in (0)..r, (1 - t ^ 2)⁻¹ = Real.artanh r` (`TauCeti.hyperbolicLength_ray`), which is
`Real.integral_one_sub_sq_inv_eq_artanh`, the same input the radial statement of
`Hyperbolic/Density.lean` spends. Transporting the radius by the Moebius factor centred at `-z`
joins `z` to `w` with length `hyperbolicDist z w`. So the radii through the origin and their Moebius
images — the hyperbolic geodesics classified in `Conformal/Poincare/Betweenness.lean` — are
exactly the paths that realise the distance.

## Relation to Mathlib's `Manifold.pathELength`

Mathlib's `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean` defines `Manifold.pathELength`
and `Manifold.riemannianEDist`, the infimum of path lengths, for a charted space each of whose
tangent spaces carries an `ENorm`. Routing this file through it would first require equipping the
open unit disc with a manifold structure and its tangent spaces with the Poincaré `ENorm`, none of
which exists in this tree; and it would state the result in `ℝ≥0∞`, whereas `hyperbolicDist` and
the entire disc development are real-valued. `hyperbolicLength` is therefore the elementary
interval integral rather than a `pathELength` specialisation. Should the Poincaré disc later be
given a Riemannian structure, `TauCeti.isLeast_hyperbolicLength` is precisely the input needed to
identify `hyperbolicDist` with `Manifold.riemannianEDist`, and this file should be refactored onto
that API at that point.

## Main declarations

* `TauCeti.hyperbolicLength` — the density-weighted length of a path in the disc, with
  `TauCeti.hyperbolicLength_eq_integral` rewriting it against an explicit derivative and
  `TauCeti.hyperbolicLength_nonneg`, `TauCeti.hyperbolicLength_const` the basic evaluations.
* `TauCeti.norm_deriv_unitDiscMoebiusFormula_div_one_sub_sq` — the conformal invariance of the
  Poincaré density, and `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp` its integrated
  form: hyperbolic length is a Moebius invariant.
* `TauCeti.hyperbolicLength_ray` — the hyperbolic length of a Euclidean radius is `Real.artanh`
  of its Euclidean length.
* `TauCeti.hyperbolicDist_le_hyperbolicLength` — **no `C¹` path in the disc is hyperbolically
  shorter than the hyperbolic distance between its endpoints.**
* `TauCeti.exists_hyperbolicLength_eq_hyperbolicDist` — the bound is attained.
* `TauCeti.isLeast_hyperbolicLength` — **the Poincaré metric is the length metric of its
  density**: `hyperbolicDist z w` is the least hyperbolic length of a `C¹` path from `z` to `w`.

## Coordination with upstream Mathlib

As with the rest of the L2 material of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), this file is coordinated with the in-progress
human-curated Riemann-mapping effort [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
which contains no hyperbolic metric on the disc; Mathlib has the hyperbolic metric on the upper
half-plane (`Analysis/Complex/UpperHalfPlane/Metric.lean`) but neither a disc version nor a
length-metric characterisation of it. Should a human-curated Poincaré metric land upstream, this
file should be refactored onto it.

## References

* L. V. Ahlfors, *Conformal Invariants*, Ch. 1 (the Poincaré metric as a length metric).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {γ γ' : ℝ → ℂ} {a b : ℝ} {c z w : ℂ}

/-! ## The hyperbolic length of a path -/

/-- The **hyperbolic length** of the path `γ` over the parameter interval from `a` to `b`: the
Euclidean speed `‖deriv γ t‖` integrated against the Poincaré density `(1 - ‖γ t‖ ^ 2)⁻¹` of
`Conformal/Hyperbolic/Density.lean`.

The definition is stated for an arbitrary `γ : ℝ → ℂ`; it is the intended notion of length only
when `γ` is differentiable and takes its values in the open unit disc, and every theorem below
assumes as much. -/
@[expose] noncomputable def hyperbolicLength (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)

/-- The defining formula for the hyperbolic length of a path. -/
theorem hyperbolicLength_def (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ a b = ∫ t in a..b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2) :=
  rfl

@[simp]
theorem hyperbolicLength_same (γ : ℝ → ℂ) (a : ℝ) : hyperbolicLength γ a a = 0 :=
  intervalIntegral.integral_same

/-- Reversing the parameter interval reverses the sign, as for any oriented integral. -/
theorem hyperbolicLength_symm (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ b a = -hyperbolicLength γ a b :=
  intervalIntegral.integral_symm _ _

@[simp]
theorem hyperbolicLength_const (c : ℂ) (a b : ℝ) :
    hyperbolicLength (fun _ => c) a b = 0 := by
  simp [hyperbolicLength]

/-- The hyperbolic length computed from an explicit derivative rather than from `deriv`. -/
theorem hyperbolicLength_eq_integral (hderiv : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t) :
    hyperbolicLength γ a b = ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) :=
  intervalIntegral.integral_congr fun t ht => by rw [(hderiv t ht).deriv]

/-- A path running through the open unit disc has nonnegative hyperbolic length. -/
theorem hyperbolicLength_nonneg (hab : a ≤ b) (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    0 ≤ hyperbolicLength γ a b :=
  intervalIntegral.integral_nonneg hab fun t ht =>
    div_nonneg (norm_nonneg _) (by nlinarith [norm_nonneg (γ t), hmem t ht])

/-- **The hyperbolic length of a Euclidean radius.** For a unit vector `u` and `0 ≤ r < 1`, the
path `t ↦ u * t` has hyperbolic length `Real.artanh r` over `[0, r]`, which by
`TauCeti.hyperbolicDist_zero_right` is the hyperbolic distance from `0` to its endpoint. This is
the radial computation of `Conformal/Hyperbolic/Density.lean` read as a statement about lengths. -/
theorem hyperbolicLength_ray {u : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    hyperbolicLength (fun t : ℝ => u * (t : ℂ)) 0 r = Real.artanh r := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u * (s : ℂ)) u t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul u
  rw [hyperbolicLength_eq_integral (γ' := fun _ => u) fun t _ => hderiv t,
    ← Real.integral_one_sub_sq_inv_eq_artanh ⟨by linarith, hr1⟩]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hr] at ht
  have hnorm : ‖u * (t : ℂ)‖ = t := by
    rw [norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  rw [hnorm, hu, one_div]

/-! ## Conformal invariance of the density -/

/-- **The Poincaré density is invariant under the disc Moebius factors.** For `‖c‖ < 1` the
derivative of `z ↦ (z - c) / (1 - conj c * z)` computed in
`TauCeti.hasDerivAt_unitDiscMoebiusFormula`, weighted by the density at the image point, is the
density at the source point.

The two ingredients cancel each other exactly: the derivative has norm
`(1 - ‖c‖ ^ 2) / ‖1 - conj c * z‖ ^ 2`, and the defect identity
`TauCeti.one_sub_pseudoHyperbolicExpr_sq` evaluates `1 - ‖(z - c) / (1 - conj c * z)‖ ^ 2` as
`(1 - ‖z‖ ^ 2) * (1 - ‖c‖ ^ 2) / ‖1 - conj c * z‖ ^ 2`. -/
theorem norm_deriv_unitDiscMoebiusFormula_div_one_sub_sq (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    ‖(1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * z) ^ 2‖ /
        (1 - ‖(z - c) / (1 - (starRingEnd ℂ) c * z)‖ ^ 2) = (1 - ‖z‖ ^ 2)⁻¹ := by
  have hden : (1 : ℂ) - (starRingEnd ℂ) c * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hz hc
  have hN : (0 : ℝ) < ‖1 - (starRingEnd ℂ) c * z‖ := norm_pos_iff.mpr hden
  have hA : (0 : ℝ) < 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  have hB : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hcc : (1 : ℂ) - (starRingEnd ℂ) c * c = ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [← pseudoHyperbolicExpr_def z c, one_sub_pseudoHyperbolicExpr_sq hz hc, hcc, norm_div,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  field_simp

/-- **Hyperbolic length is a Moebius invariant.** Post-composing a `C¹` path in the disc with the
Moebius factor `z ↦ (z - c) / (1 - conj c * z)` leaves its hyperbolic length unchanged: this is
`TauCeti.norm_deriv_unitDiscMoebiusFormula_div_one_sub_sq` integrated along the path. It is the
tool that moves the starting point of a path to the origin. -/
theorem hyperbolicLength_unitDiscMoebiusFormula_comp (hc : ‖c‖ < 1)
    (hderiv : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicLength (fun t => (γ t - c) / (1 - (starRingEnd ℂ) c * γ t)) a b
      = hyperbolicLength γ a b := by
  have key : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => (γ s - c) / (1 - (starRingEnd ℂ) c * γ s))
        (γ' t * ((1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * γ t) ^ 2)) t := by
    intro t ht
    have hden : (1 : ℂ) - (starRingEnd ℂ) c * γ t ≠ 0 :=
      one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t ht) hc
    simpa [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_unitDiscMoebiusFormula c (γ t) hden).scomp t (hderiv t ht)
  rw [hyperbolicLength_eq_integral key, hyperbolicLength_eq_integral hderiv]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [norm_mul, mul_div_assoc,
    norm_deriv_unitDiscMoebiusFormula_div_one_sub_sq hc (hmem t ht), ← div_eq_mul_inv]

/-! ## The distance is a lower bound for the length -/

/-- The lower bound for a path issued from the origin, where the hyperbolic distance to the
endpoint is `Real.artanh` of its Euclidean norm. Comparing with the real function
`t ↦ (v * γ t).re` for a suitable unit vector `v` — rather than with `t ↦ ‖γ t‖`, which need not
be differentiable — turns the estimate into the fundamental theorem of calculus for
`Real.artanh`. -/
private theorem artanh_norm_le_integral (hab : a ≤ b)
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) (hcont : ContinuousOn γ' (Icc a b))
    (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) (h0 : γ a = 0) :
    Real.artanh ‖γ b‖ ≤ ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hγcont : ContinuousOn γ (Icc a b) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have hpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - ‖γ t‖ ^ 2 := fun t ht => by
    nlinarith [norm_nonneg (γ t), hmem t ht]
  have hint2 : IntervalIntegrable (fun t => ‖γ' t‖ / (1 - ‖γ t‖ ^ 2)) MeasureTheory.volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]
    exact hcont.norm.div (continuousOn_const.sub (hγcont.norm.pow 2)) fun t ht => (hpos t ht).ne'
  rcases eq_or_ne (γ b) 0 with hb | hb
  · rw [hb, norm_zero, Real.artanh_zero]
    exact intervalIntegral.integral_nonneg hab fun t ht =>
      div_nonneg (norm_nonneg _) (hpos t ht).le
  · have hR0 : 0 < ‖γ b‖ := norm_pos_iff.mpr hb
    set v : ℂ := (starRingEnd ℂ) (γ b) / ((‖γ b‖ : ℝ) : ℂ) with hvdef
    have hvnorm : ‖v‖ = 1 := by
      rw [hvdef, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR0, div_self hR0.ne']
    set ψ : ℝ → ℝ := fun t => (v * γ t).re with hψdef
    have hψa : ψ a = 0 := by simp [hψdef, h0]
    have hψb : ψ b = ‖γ b‖ := by
      have hmul : v * γ b = ((‖γ b‖ : ℝ) : ℂ) := by
        rw [hvdef, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq]
        push_cast
        field_simp
      change (v * γ b).re = ‖γ b‖
      rw [hmul, Complex.ofReal_re]
    have hψbound : ∀ t : ℝ, |ψ t| ≤ ‖γ t‖ := fun t =>
      (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hvnorm, one_mul])
    have hψmem : ∀ t ∈ Icc a b, ψ t ∈ Ioo (-1 : ℝ) 1 := fun t ht =>
      abs_lt.mp ((hψbound t).trans_lt (hmem t ht))
    have hψderiv : ∀ t ∈ Icc a b, HasDerivAt ψ ((v * γ' t).re) t := fun t ht => by
      simpa [hψdef, Function.comp_def] using
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hderiv t ht).const_mul v)
    have hψcont : ContinuousOn ψ (Icc a b) :=
      Complex.reCLM.continuous.comp_continuousOn (continuousOn_const.mul hγcont)
    have hψ'cont : ContinuousOn (fun t => (v * γ' t).re) (Icc a b) :=
      Complex.reCLM.continuous.comp_continuousOn (continuousOn_const.mul hcont)
    have hPpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - ψ t ^ 2 := fun t ht => by
      have := hψmem t ht
      nlinarith [this.1, this.2]
    have hint1 : IntervalIntegrable (fun t => (1 - ψ t ^ 2)⁻¹ * (v * γ' t).re)
        MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [huIcc]
      exact ((continuousOn_const.sub (hψcont.pow 2)).inv₀ fun t ht => (hPpos t ht).ne').mul hψ'cont
    have hFTC : ∫ t in a..b, (1 - ψ t ^ 2)⁻¹ * (v * γ' t).re
        = Real.artanh (ψ b) - Real.artanh (ψ a) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => (hψderiv t (huIcc ▸ ht)).artanh (hψmem t (huIcc ▸ ht))) hint1
    have hmono : ∫ t in a..b, (1 - ψ t ^ 2)⁻¹ * (v * γ' t).re
        ≤ ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := by
      refine intervalIntegral.integral_mono_on hab hint1 hint2 fun t ht => ?_
      have hQ : (0 : ℝ) < 1 - ‖γ t‖ ^ 2 := hpos t ht
      have hPQ : 1 - ‖γ t‖ ^ 2 ≤ 1 - ψ t ^ 2 := by
        nlinarith [hψbound t, abs_nonneg (ψ t), sq_abs (ψ t), norm_nonneg (γ t)]
      have hnum : (v * γ' t).re ≤ ‖γ' t‖ :=
        (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans_eq
          (by rw [norm_mul, hvnorm, one_mul]))
      have h1 : (1 - ψ t ^ 2)⁻¹ * (v * γ' t).re ≤ (1 - ψ t ^ 2)⁻¹ * ‖γ' t‖ :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr (hPpos t ht).le)
      have h2 : (1 - ψ t ^ 2)⁻¹ * ‖γ' t‖ ≤ (1 - ‖γ t‖ ^ 2)⁻¹ * ‖γ' t‖ := by
        gcongr
      rw [div_eq_inv_mul]
      exact h1.trans h2
    rw [← hψb, ← sub_zero (Real.artanh (ψ b)), ← Real.artanh_zero, ← hψa, ← hFTC]
    exact hmono

/-- **No path in the disc is hyperbolically shorter than the hyperbolic distance between its
endpoints.** For a `C¹` path `γ` staying in the open unit disc,
`hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b`.

The starting point is moved to the origin by the Moebius factor centred at `γ a`, which changes
neither side: the left-hand side because the factor is a hyperbolic isometry, the right-hand side
by `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp`. -/
theorem hyperbolicDist_le_hyperbolicLength (hab : a ≤ b)
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) (hcont : ContinuousOn γ' (Icc a b))
    (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hc : ‖γ a‖ < 1 := hmem a ⟨le_rfl, hab⟩
  have hden : ∀ t ∈ Icc a b, (1 : ℂ) - (starRingEnd ℂ) (γ a) * γ t ≠ 0 := fun t ht =>
    one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t ht) hc
  have hγcont : ContinuousOn γ (Icc a b) := fun t ht =>
    (hderiv t ht).continuousAt.continuousWithinAt
  have hσderiv : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (γ s - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ s))
        (γ' t * ((1 - (starRingEnd ℂ) (γ a) * γ a) /
          (1 - (starRingEnd ℂ) (γ a) * γ t) ^ 2)) t := fun t ht => by
    simpa [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_unitDiscMoebiusFormula (γ a) (γ t) (hden t ht)).scomp t (hderiv t ht)
  have hσ'cont : ContinuousOn (fun t => γ' t * ((1 - (starRingEnd ℂ) (γ a) * γ a) /
      (1 - (starRingEnd ℂ) (γ a) * γ t) ^ 2)) (Icc a b) :=
    hcont.mul (continuousOn_const.div
      ((continuousOn_const.sub (continuousOn_const.mul hγcont)).pow 2)
      fun t ht => pow_ne_zero 2 (hden t ht))
  have hσmem : ∀ t ∈ Icc a b,
      ‖(γ t - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ t)‖ < 1 := fun t ht => by
    rw [← pseudoHyperbolicExpr_def]
    exact pseudoHyperbolicExpr_lt_one_of_norm_lt_one (hmem t ht) hc
  have hσa : (γ a - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ a) = 0 := by
    rw [sub_self, zero_div]
  have key := artanh_norm_le_integral hab hσderiv hσ'cont hσmem hσa
  rw [← hyperbolicLength_eq_integral (fun t ht => hσderiv t (huIcc ▸ ht)),
    hyperbolicLength_unitDiscMoebiusFormula_comp hc (fun t ht => hderiv t (huIcc ▸ ht))
      (fun t ht => hmem t (huIcc ▸ ht))] at key
  refine le_trans (le_of_eq ?_) key
  rw [hyperbolicDist_comm, hyperbolicDist_def, pseudoHyperbolicExpr_def]

/-! ## The bound is attained -/

/-- **The hyperbolic distance is realised by a path.** Any two points of the open unit disc are
joined by a `C¹` path in the disc whose hyperbolic length is exactly their hyperbolic distance,
namely the Moebius image of a Euclidean radius. -/
theorem exists_hyperbolicLength_eq_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ∃ (r : ℝ) (γ γ' : ℝ → ℂ), 0 ≤ r ∧ (∀ t ∈ Icc 0 r, HasDerivAt γ (γ' t) t) ∧
      ContinuousOn γ' (Icc 0 r) ∧ (∀ t ∈ Icc 0 r, ‖γ t‖ < 1) ∧ γ 0 = z ∧ γ r = w ∧
      hyperbolicLength γ 0 r = hyperbolicDist z w := by
  have hp0 : 0 ≤ pseudoHyperbolicExpr w z := pseudoHyperbolicExpr_nonneg w z
  have hp1 : pseudoHyperbolicExpr w z < 1 := pseudoHyperbolicExpr_lt_one_of_norm_lt_one hw hz
  set p : ℝ := pseudoHyperbolicExpr w z with hpdef
  set m : ℂ := (w - z) / (1 - (starRingEnd ℂ) z * w) with hmdef
  have hmnorm : ‖m‖ = p := by rw [hpdef, pseudoHyperbolicExpr_def, hmdef]
  set u : ℂ := if p = 0 then 1 else m / (p : ℂ) with hudef
  have hunorm : ‖u‖ = 1 := by
    by_cases h : p = 0
    · simp [hudef, h]
    · rw [hudef, if_neg h, norm_div, hmnorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hp0, div_self h]
  have hup : u * (p : ℂ) = m := by
    by_cases h : p = 0
    · have hm0 : m = 0 := norm_eq_zero.mp (by rw [hmnorm, h])
      rw [hudef, if_pos h, h, hm0]
      simp
    · rw [hudef, if_neg h, div_mul_cancel₀]
      exact_mod_cast h
  have hρderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u * (s : ℂ)) u t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul u
  have hρmem : ∀ t ∈ Icc (0 : ℝ) p, ‖u * (t : ℂ)‖ < 1 := fun t ht => by
    rw [norm_mul, hunorm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 hp1
  have hnz : ‖(-z)‖ < 1 := by rwa [norm_neg]
  have hden : ∀ t ∈ Icc (0 : ℝ) p, (1 : ℂ) - (starRingEnd ℂ) (-z) * (u * (t : ℂ)) ≠ 0 :=
    fun t ht => one_sub_conj_mul_ne_zero_of_norm_lt_one (hρmem t ht) hnz
  have huIcc : uIcc (0 : ℝ) p = Icc 0 p := uIcc_of_le hp0
  refine ⟨p, fun t => (u * (t : ℂ) - -z) / (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))),
    fun t => u * ((1 - (starRingEnd ℂ) (-z) * -z) /
      (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))) ^ 2),
    hp0, fun t ht => ?_, ?_, fun t ht => ?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_def, smul_eq_mul, mul_comm] using
      (hasDerivAt_unitDiscMoebiusFormula (-z) (u * (t : ℂ)) (hden t ht)).scomp t (hρderiv t)
  · exact continuousOn_const.mul (continuousOn_const.div
      ((continuousOn_const.sub (continuousOn_const.mul
        (Continuous.continuousOn (by fun_prop)))).pow 2)
      fun t ht => pow_ne_zero 2 (hden t ht))
  · exact mem_ball_zero_iff.mp (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hnz
      (mem_ball_zero_iff.mpr (hρmem t ht)))
  · simp
  · have hinv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hz (mem_ball_zero_iff.mpr hw)
    change (u * (p : ℂ) - -z) / (1 - (starRingEnd ℂ) (-z) * (u * (p : ℂ))) = w
    rw [hup, hmdef]
    simpa using hinv
  · rw [hyperbolicLength_unitDiscMoebiusFormula_comp hnz (γ' := fun _ => u)
      (fun t _ => hρderiv t) (fun t ht => hρmem t (huIcc ▸ ht)),
      hyperbolicLength_ray hunorm hp0 hp1, hpdef, ← hyperbolicDist_def, hyperbolicDist_comm]

/-- **The Poincaré metric is the length metric of the Poincaré density.** For two points of the
open unit disc, `hyperbolicDist z w` is the least hyperbolic length of a `C¹` path in the disc
running from `z` to `w`.

Together with the classification of the hyperbolic geodesics in
`Conformal/Poincare/Betweenness.lean` this closes the circle of descriptions of the Poincaré
metric: the closed formula of `Hyperbolic/Distance.lean`, the infinitesimal density of
`Hyperbolic/Density.lean`, and the induced length metric all agree. -/
theorem isLeast_hyperbolicLength (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    IsLeast {L : ℝ | ∃ (r : ℝ) (γ γ' : ℝ → ℂ), 0 ≤ r ∧ (∀ t ∈ Icc 0 r, HasDerivAt γ (γ' t) t) ∧
      ContinuousOn γ' (Icc 0 r) ∧ (∀ t ∈ Icc 0 r, ‖γ t‖ < 1) ∧ γ 0 = z ∧ γ r = w ∧
      hyperbolicLength γ 0 r = L} (hyperbolicDist z w) := by
  constructor
  · exact exists_hyperbolicLength_eq_hyperbolicDist hz hw
  · rintro L ⟨r, γ, γ', hr, hderiv, hcont, hmem, h0, hr', rfl⟩
    have := hyperbolicDist_le_hyperbolicLength hr hderiv hcont hmem
    rwa [h0, hr'] at this

end TauCeti
