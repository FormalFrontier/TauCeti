/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.ClosedForm
public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.AutomorphismIsometry
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

`TauCeti.hyperbolicLength γ a b = ∫ t in uIcc a b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)`,

the Euclidean speed integrated against the Poincaré density over the *unordered* parameter
interval, as for Mathlib's `Manifold.pathELength`: the length of a path does not depend on the
orientation of its parameter interval, and is nonnegative. The theorem is that
`hyperbolicDist z w` is the **least** such length over `C¹` paths from `z` to `w`
(`TauCeti.isLeast_hyperbolicLength`): no path is shorter
(`TauCeti.hyperbolicDist_le_hyperbolicLength`), and one path realises the value
(`TauCeti.exists_hyperbolicLength_eq_hyperbolicDist`). Regularity is always asked of the path
*relative to its parameter interval*: continuity on the closed interval, an ordinary derivative
at its interior points, and a derivative that extends continuously to the closed interval.

## The proof

Both halves rest on one algebraic fact, which `Conformal/SchwarzPick/AutomorphismIsometry.lean`
already supplies as the equality case of the infinitesimal Schwarz--Pick lemma
(`TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one`): the disc
Moebius factor `M z = (z - c) / (1 - conj c * z)` preserves the Poincaré density,

`‖M ′ z‖ / (1 - ‖M z‖ ^ 2) = 1 / (1 - ‖z‖ ^ 2)`.

Integrating it along a path gives `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp`:
hyperbolic length is unchanged by post-composition with a disc Moebius factor. That is what moves
an arbitrary path to one starting at the origin.

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
joins `z` to `w` with length `hyperbolicDist z w`. The minimisers exhibited here are therefore
the radii through the origin and their Moebius images, the hyperbolic geodesics classified in
`Conformal/Poincare/Betweenness.lean`; the converse — that a path of least length is a
reparametrisation of one of them — is an equality case that this file does not prove.

## Relation to Mathlib's `Manifold.pathELength`

Mathlib's `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean` defines `Manifold.pathELength`
and `Manifold.riemannianEDist`, the infimum of path lengths, for a charted space each of whose
tangent spaces carries an `ENorm`. Routing this file through it would first require equipping the
open unit disc with a manifold structure and its tangent spaces with the Poincaré `ENorm`, none of
which exists in this tree; and it would state the result in `ℝ≥0∞`, whereas `hyperbolicDist` and
the entire disc development are real-valued. `hyperbolicLength` is therefore the elementary
integral over the parameter interval rather than a `pathELength` specialisation. Should the
Poincaré disc later be given a Riemannian structure, `TauCeti.isLeast_hyperbolicLength` is
precisely the input needed to identify `hyperbolicDist` with `Manifold.riemannianEDist`, and this
file should be refactored onto that API at that point.

## Main declarations

* `TauCeti.hyperbolicLength` — the density-weighted length of a path in the disc, with
  `TauCeti.hyperbolicLength_eq_integral` rewriting it against an explicit derivative and
  `TauCeti.hyperbolicLength_symm`, `TauCeti.hyperbolicLength_nonneg`,
  `TauCeti.hyperbolicLength_const`, `TauCeti.hyperbolicLength_add` the basic evaluations and
  operations.
* `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp` — hyperbolic length is a Moebius
  invariant, the integrated form of the infinitesimal isometry
  `TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one`.
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

/-- The **hyperbolic length** of the path `γ` over the parameter interval with endpoints `a` and
`b`: the Euclidean speed `‖deriv γ t‖` integrated over the unordered interval `uIcc a b` against
the Poincaré density `(1 - ‖γ t‖ ^ 2)⁻¹` of `Conformal/Hyperbolic/Density.lean`.

Taking the integral over the unordered interval, as Mathlib's `Manifold.pathELength` does, makes
the length independent of the orientation of the parameter interval
(`TauCeti.hyperbolicLength_symm`) and nonnegative for a path in the disc whichever way round its
endpoints are (`TauCeti.hyperbolicLength_nonneg`).

The definition is stated for an arbitrary `γ : ℝ → ℂ`, and only the derivative at the interior
parameters enters (`TauCeti.hyperbolicLength_eq_integral`). It is the intended notion of length
when `γ` is a `C¹` path with values in the open unit disc, which is what the comparison with
`TauCeti.hyperbolicDist` below assumes; the evaluations of the length itself need no such
hypothesis. -/
noncomputable def hyperbolicLength (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ t in uIcc a b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2)

/-- The defining formula for the hyperbolic length of a path. -/
theorem hyperbolicLength_def (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ a b = ∫ t in uIcc a b, ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2) := by
  rw [hyperbolicLength]

@[simp]
theorem hyperbolicLength_same (γ : ℝ → ℂ) (a : ℝ) : hyperbolicLength γ a a = 0 := by
  rw [hyperbolicLength_def, uIcc_self]
  simp

/-- Hyperbolic length does not depend on the orientation of the parameter interval. -/
theorem hyperbolicLength_symm (γ : ℝ → ℂ) (a b : ℝ) :
    hyperbolicLength γ b a = hyperbolicLength γ a b := by
  rw [hyperbolicLength_def, hyperbolicLength_def, uIcc_comm]

@[simp]
theorem hyperbolicLength_const (c : ℂ) (a b : ℝ) :
    hyperbolicLength (fun _ => c) a b = 0 := by
  rw [hyperbolicLength_def]
  simp

/-- The hyperbolic length computed from an explicit derivative rather than from `deriv`. The
derivative is only asked for at the interior parameters, the two endpoints forming a null set. -/
theorem hyperbolicLength_eq_integral (hab : a ≤ b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) :
    hyperbolicLength γ a b = ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := by
  have hEq : EqOn (fun t => ‖deriv γ t‖ / (1 - ‖γ t‖ ^ 2))
      (fun t => ‖γ' t‖ / (1 - ‖γ t‖ ^ 2)) (Ioo a b) := fun t ht => by
    simp only [(hderiv t ht).deriv]
  rw [hyperbolicLength_def, uIcc_of_le hab,
    ← MeasureTheory.restrict_Ioo_eq_restrict_Icc,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hEq,
    MeasureTheory.restrict_Ioo_eq_restrict_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- A path running through the open unit disc has nonnegative hyperbolic length, whichever way
round its endpoints are. -/
theorem hyperbolicLength_nonneg (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    0 ≤ hyperbolicLength γ a b := by
  rw [hyperbolicLength_def]
  exact MeasureTheory.setIntegral_nonneg measurableSet_uIcc fun t ht =>
    div_nonneg (norm_nonneg _) (by nlinarith [norm_nonneg (γ t), hmem t ht])

/-- For a `C¹` path in the disc the density-weighted speed is interval integrable, which is what
lets its length be split along the parameter interval. -/
private theorem intervalIntegrable_norm_div_one_sub_norm_sq (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hγ' : ContinuousOn γ' (Icc a b))
    (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    IntervalIntegrable (fun t => ‖γ' t‖ / (1 - ‖γ t‖ ^ 2)) MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact hγ'.norm.div (continuousOn_const.sub (hγ.norm.pow 2)) fun t ht =>
    (show (0 : ℝ) < 1 - ‖γ t‖ ^ 2 by nlinarith [norm_nonneg (γ t), hmem t ht]).ne'

/-- **Hyperbolic length is additive along the parameter interval**: the lengths of the two halves
of a path add up to the length of the whole. -/
theorem hyperbolicLength_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hγ : ContinuousOn γ (Icc a c)) (hderiv : ∀ t ∈ Ioo a c, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc a c)) (hmem : ∀ t ∈ Icc a c, ‖γ t‖ < 1) :
    hyperbolicLength γ a b + hyperbolicLength γ b c = hyperbolicLength γ a c := by
  have hsub₁ : Icc a b ⊆ Icc a c := Icc_subset_Icc le_rfl hbc
  have hsub₂ : Icc b c ⊆ Icc a c := Icc_subset_Icc hab le_rfl
  rw [hyperbolicLength_eq_integral (γ' := γ') hab fun t ht =>
      hderiv t (Ioo_subset_Ioo le_rfl hbc ht),
    hyperbolicLength_eq_integral (γ' := γ') hbc fun t ht =>
      hderiv t (Ioo_subset_Ioo hab le_rfl ht),
    hyperbolicLength_eq_integral (hab.trans hbc) hderiv]
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_norm_div_one_sub_norm_sq hab (hγ.mono hsub₁) (hγ'.mono hsub₁)
      fun t ht => hmem t (hsub₁ ht))
    (intervalIntegrable_norm_div_one_sub_norm_sq hbc (hγ.mono hsub₂) (hγ'.mono hsub₂)
      fun t ht => hmem t (hsub₂ ht))

/-- **The hyperbolic length of a Euclidean radius.** For a unit vector `u` and `0 ≤ r < 1`, the
path `t ↦ u * t` has hyperbolic length `Real.artanh r` over `[0, r]`, which by
`TauCeti.hyperbolicDist_zero_right` is the hyperbolic distance from `0` to its endpoint. This is
the radial computation of `Conformal/Hyperbolic/Density.lean` read as a statement about lengths. -/
theorem hyperbolicLength_ray {u : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    hyperbolicLength (fun t : ℝ => u * (t : ℂ)) 0 r = Real.artanh r := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u * (s : ℂ)) u t := fun t => by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul u
  rw [hyperbolicLength_eq_integral (γ' := fun _ => u) hr fun t _ => hderiv t,
    ← Real.integral_one_sub_sq_inv_eq_artanh ⟨by linarith, hr1⟩]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hr] at ht
  have hnorm : ‖u * (t : ℂ)‖ = t := by
    rw [norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  rw [hnorm, hu, one_div]

/-! ## Conformal invariance of the density -/

/-- The Moebius invariance of hyperbolic length over an ordered parameter interval; the general
case follows by symmetry. -/
private theorem hyperbolicLength_unitDiscMoebiusFormula_comp_of_le (hc : ‖c‖ < 1) (hab : a ≤ b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    hyperbolicLength (fun t => (γ t - c) / (1 - (starRingEnd ℂ) c * γ t)) a b
      = hyperbolicLength γ a b := by
  have key : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => (γ s - c) / (1 - (starRingEnd ℂ) c * γ s))
        (γ' t * ((1 - (starRingEnd ℂ) c * c) / (1 - (starRingEnd ℂ) c * γ t) ^ 2)) t := by
    intro t ht
    have hden : (1 : ℂ) - (starRingEnd ℂ) c * γ t ≠ 0 :=
      one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t (Ioo_subset_Icc_self ht)) hc
    simpa [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_unitDiscMoebiusFormula c (γ t) hden).scomp t (hderiv t ht)
  rw [hyperbolicLength_eq_integral hab key, hyperbolicLength_eq_integral hab hderiv]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  have hden : (1 : ℂ) - (starRingEnd ℂ) c * γ t ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t ht) hc
  rw [norm_mul, mul_div_assoc, ← (hasDerivAt_unitDiscMoebiusFormula c (γ t) hden).deriv,
    norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one hc (hmem t ht),
    mul_one_div]

/-- **Hyperbolic length is a Moebius invariant.** Post-composing a path in the disc with the
Moebius factor `z ↦ (z - c) / (1 - conj c * z)` leaves its hyperbolic length unchanged: this is
the infinitesimal Poincaré isometry
`TauCeti.norm_deriv_div_one_sub_norm_sq_unitDiscMoebiusFormula_of_norm_lt_one` integrated along
the path. It is the tool that moves the starting point of a path to the origin. -/
theorem hyperbolicLength_unitDiscMoebiusFormula_comp (hc : ‖c‖ < 1)
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicLength (fun t => (γ t - c) / (1 - (starRingEnd ℂ) c * γ t)) a b
      = hyperbolicLength γ a b := by
  rcases le_total a b with hab | hab
  · rw [uIoo_of_le hab] at hderiv
    rw [uIcc_of_le hab] at hmem
    exact hyperbolicLength_unitDiscMoebiusFormula_comp_of_le hc hab hderiv hmem
  · rw [uIoo_comm, uIoo_of_le hab] at hderiv
    rw [uIcc_comm, uIcc_of_le hab] at hmem
    rw [hyperbolicLength_symm _ b a, hyperbolicLength_symm γ b a]
    exact hyperbolicLength_unitDiscMoebiusFormula_comp_of_le hc hab hderiv hmem

/-! ## The distance is a lower bound for the length -/

/-- The lower bound for a path issued from the origin, where the hyperbolic distance to the
endpoint is `Real.artanh` of its Euclidean norm. Comparing with the real function
`t ↦ (v * γ t).re` for a suitable unit vector `v` — rather than with `t ↦ ‖γ t‖`, which need not
be differentiable — turns the estimate into the fundamental theorem of calculus for
`Real.artanh`. -/
private theorem artanh_norm_le_integral (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) (h0 : γ a = 0) :
    Real.artanh ‖γ b‖ ≤ ∫ t in a..b, ‖γ' t‖ / (1 - ‖γ t‖ ^ 2) := by
  have hpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - ‖γ t‖ ^ 2 := fun t ht => by
    nlinarith [norm_nonneg (γ t), hmem t ht]
  have hint2 : IntervalIntegrable (fun t => ‖γ' t‖ / (1 - ‖γ t‖ ^ 2)) MeasureTheory.volume a b :=
    intervalIntegrable_norm_div_one_sub_norm_sq hab hγ hγ' hmem
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
      simp only [hψdef, hmul, Complex.ofReal_re]
    have hψbound : ∀ t : ℝ, |ψ t| ≤ ‖γ t‖ := fun t =>
      (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hvnorm, one_mul])
    have hψmem : ∀ t ∈ Icc a b, ψ t ∈ Ioo (-1 : ℝ) 1 := fun t ht =>
      abs_lt.mp ((hψbound t).trans_lt (hmem t ht))
    have hψderiv : ∀ t ∈ Ioo a b, HasDerivAt ψ ((v * γ' t).re) t := fun t ht => by
      simpa [hψdef, Function.comp_def] using
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hderiv t ht).const_mul v)
    have hψcont : ContinuousOn ψ (Icc a b) :=
      Complex.reCLM.continuous.comp_continuousOn (continuousOn_const.mul hγ)
    have hψ'cont : ContinuousOn (fun t => (v * γ' t).re) (Icc a b) :=
      Complex.reCLM.continuous.comp_continuousOn (continuousOn_const.mul hγ')
    have hPpos : ∀ t ∈ Icc a b, (0 : ℝ) < 1 - ψ t ^ 2 := fun t ht => by
      have := hψmem t ht
      nlinarith [this.1, this.2]
    have hint1 : IntervalIntegrable (fun t => (1 - ψ t ^ 2)⁻¹ * (v * γ' t).re)
        MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      exact ((continuousOn_const.sub (hψcont.pow 2)).inv₀ fun t ht => (hPpos t ht).ne').mul hψ'cont
    have hFTC : ∫ t in a..b, (1 - ψ t ^ 2)⁻¹ * (v * γ' t).re
        = Real.artanh (ψ b) - Real.artanh (ψ a) :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
        (Real.continuousOn_artanh.comp hψcont fun t ht => hψmem t ht)
        (fun t ht => ((hψderiv t ht).artanh
          (hψmem t (Ioo_subset_Icc_self ht))).hasDerivWithinAt) hint1
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

/-- The lower bound over an ordered parameter interval; the general case follows by symmetry. -/
private theorem hyperbolicDist_le_hyperbolicLength_of_le (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hderiv : ∀ t ∈ Ioo a b, HasDerivAt γ (γ' t) t)
    (hγ' : ContinuousOn γ' (Icc a b)) (hmem : ∀ t ∈ Icc a b, ‖γ t‖ < 1) :
    hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b := by
  have hc : ‖γ a‖ < 1 := hmem a ⟨le_rfl, hab⟩
  have hden : ∀ t ∈ Icc a b, (1 : ℂ) - (starRingEnd ℂ) (γ a) * γ t ≠ 0 := fun t ht =>
    one_sub_conj_mul_ne_zero_of_norm_lt_one (hmem t ht) hc
  have hσderiv : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s => (γ s - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ s))
        (γ' t * ((1 - (starRingEnd ℂ) (γ a) * γ a) /
          (1 - (starRingEnd ℂ) (γ a) * γ t) ^ 2)) t := fun t ht => by
    simpa [Function.comp_def, smul_eq_mul] using
      (hasDerivAt_unitDiscMoebiusFormula (γ a) (γ t)
        (hden t (Ioo_subset_Icc_self ht))).scomp t (hderiv t ht)
  have hσcont : ContinuousOn (fun s => (γ s - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ s))
      (Icc a b) :=
    (hγ.sub continuousOn_const).div (continuousOn_const.sub (continuousOn_const.mul hγ)) hden
  have hσ'cont : ContinuousOn (fun t => γ' t * ((1 - (starRingEnd ℂ) (γ a) * γ a) /
      (1 - (starRingEnd ℂ) (γ a) * γ t) ^ 2)) (Icc a b) :=
    hγ'.mul (continuousOn_const.div
      ((continuousOn_const.sub (continuousOn_const.mul hγ)).pow 2)
      fun t ht => pow_ne_zero 2 (hden t ht))
  have hσmem : ∀ t ∈ Icc a b,
      ‖(γ t - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ t)‖ < 1 := fun t ht => by
    rw [← pseudoHyperbolicExpr_def]
    exact pseudoHyperbolicExpr_lt_one_of_norm_lt_one (hmem t ht) hc
  have hσa : (γ a - γ a) / (1 - (starRingEnd ℂ) (γ a) * γ a) = 0 := by
    rw [sub_self, zero_div]
  have key := artanh_norm_le_integral hab hσcont hσderiv hσ'cont hσmem hσa
  rw [← hyperbolicLength_eq_integral hab hσderiv,
    hyperbolicLength_unitDiscMoebiusFormula_comp_of_le hc hab hderiv hmem] at key
  refine le_trans (le_of_eq ?_) key
  rw [hyperbolicDist_comm, hyperbolicDist_def, pseudoHyperbolicExpr_def]

/-- **No path in the disc is hyperbolically shorter than the hyperbolic distance between its
endpoints.** For a path `γ` staying in the open unit disc, continuous on its parameter interval
and continuously differentiable inside it,
`hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b`.

The starting point is moved to the origin by the Moebius factor centred at `γ a`, which changes
neither side: the left-hand side because the factor is a hyperbolic isometry, the right-hand side
by `TauCeti.hyperbolicLength_unitDiscMoebiusFormula_comp`. -/
theorem hyperbolicDist_le_hyperbolicLength (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : ∀ t ∈ uIoo a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (uIcc a b))
    (hmem : ∀ t ∈ uIcc a b, ‖γ t‖ < 1) :
    hyperbolicDist (γ a) (γ b) ≤ hyperbolicLength γ a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hγ hγ' hmem
    rw [uIoo_of_le hab] at hderiv
    exact hyperbolicDist_le_hyperbolicLength_of_le hab hγ hderiv hγ' hmem
  · rw [uIcc_comm, uIcc_of_le hab] at hγ hγ' hmem
    rw [uIoo_comm, uIoo_of_le hab] at hderiv
    have key := hyperbolicDist_le_hyperbolicLength_of_le hab hγ hderiv hγ' hmem
    rwa [hyperbolicDist_comm, hyperbolicLength_symm] at key

/-! ## The bound is attained -/

/-- **The hyperbolic distance is realised by a path.** Any two points of the open unit disc are
joined by a `C¹` path in the disc whose hyperbolic length is exactly their hyperbolic distance,
namely the Moebius image of a Euclidean radius. -/
theorem exists_hyperbolicLength_eq_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ∃ (r : ℝ) (γ γ' : ℝ → ℂ), 0 ≤ r ∧ ContinuousOn γ (Icc 0 r) ∧
      (∀ t ∈ Ioo 0 r, HasDerivAt γ (γ' t) t) ∧ ContinuousOn γ' (Icc 0 r) ∧
      (∀ t ∈ Icc 0 r, ‖γ t‖ < 1) ∧ γ 0 = z ∧ γ r = w ∧
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
  have hσderiv : ∀ t ∈ Icc (0 : ℝ) p,
      HasDerivAt (fun s : ℝ => (u * (s : ℂ) - -z) / (1 - (starRingEnd ℂ) (-z) * (u * (s : ℂ))))
        (u * ((1 - (starRingEnd ℂ) (-z) * -z) /
          (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))) ^ 2)) t := fun t ht => by
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using
      (hasDerivAt_unitDiscMoebiusFormula (-z) (u * (t : ℂ)) (hden t ht)).scomp t (hρderiv t)
  have huIcc : uIcc (0 : ℝ) p = Icc 0 p := uIcc_of_le hp0
  refine ⟨p, fun t => (u * (t : ℂ) - -z) / (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))),
    fun t => u * ((1 - (starRingEnd ℂ) (-z) * -z) /
      (1 - (starRingEnd ℂ) (-z) * (u * (t : ℂ))) ^ 2),
    hp0, fun t ht => (hσderiv t ht).continuousAt.continuousWithinAt,
    fun t ht => hσderiv t (Ioo_subset_Icc_self ht), ?_, fun t ht => ?_, ?_, ?_, ?_⟩
  · exact continuousOn_const.mul (continuousOn_const.div
      ((continuousOn_const.sub (continuousOn_const.mul
        (Continuous.continuousOn (by fun_prop)))).pow 2)
      fun t ht => pow_ne_zero 2 (hden t ht))
  · exact mem_ball_zero_iff.mp (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hnz
      (mem_ball_zero_iff.mpr (hρmem t ht)))
  · simp
  · have hinv := leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hz (mem_ball_zero_iff.mpr hw)
    -- the goal is the path exhibited above applied at the endpoint `p`; `dsimp only`
    -- beta-reduces that application, after which `u * p` is the Moebius image of `w`
    dsimp only
    rw [hup, hmdef]
    simpa using hinv
  · rw [hyperbolicLength_unitDiscMoebiusFormula_comp hnz (γ' := fun _ => u)
      (fun t _ => hρderiv t) (fun t ht => hρmem t (huIcc ▸ ht)),
      hyperbolicLength_ray hunorm hp0 hp1, hpdef, ← hyperbolicDist_def, hyperbolicDist_comm]

/-- **The Poincaré metric is the length metric of the Poincaré density.** For two points of the
open unit disc, `hyperbolicDist z w` is the least hyperbolic length of a path in the disc running
from `z` to `w` that is continuous on its parameter interval and continuously differentiable
inside it.

Together with the classification of the hyperbolic geodesics in
`Conformal/Poincare/Betweenness.lean` this closes the circle of descriptions of the Poincaré
metric: the closed formula of `Hyperbolic/Distance.lean`, the infinitesimal density of
`Hyperbolic/Density.lean`, and the induced length metric all agree. -/
theorem isLeast_hyperbolicLength (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    IsLeast {L : ℝ | ∃ (r : ℝ) (γ γ' : ℝ → ℂ), 0 ≤ r ∧ ContinuousOn γ (Icc 0 r) ∧
      (∀ t ∈ Ioo 0 r, HasDerivAt γ (γ' t) t) ∧ ContinuousOn γ' (Icc 0 r) ∧
      (∀ t ∈ Icc 0 r, ‖γ t‖ < 1) ∧ γ 0 = z ∧ γ r = w ∧
      hyperbolicLength γ 0 r = L} (hyperbolicDist z w) := by
  constructor
  · exact exists_hyperbolicLength_eq_hyperbolicDist hz hw
  · rintro L ⟨r, γ, γ', hr, hγ, hderiv, hγ', hmem, h0, hr', rfl⟩
    have := hyperbolicDist_le_hyperbolicLength_of_le hr hγ hderiv hγ' hmem
    rwa [h0, hr'] at this

end TauCeti
