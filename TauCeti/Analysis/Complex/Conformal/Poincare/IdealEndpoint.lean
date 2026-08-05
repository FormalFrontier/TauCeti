/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Poincare.Geodesic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The ideal endpoints of a Poincaré geodesic

`Poincare/Geodesic.lean` builds the unit-speed geodesic lines of the Poincaré disc:
`TauCeti.PoincareDisc.radialGeodesic u`, the Euclidean diameter in direction `u : Circle`
parametrised as `t ↦ u * Real.tanh t`, and `TauCeti.PoincareDisc.geodesicLine a u`, its transport
to an arbitrary base point `a` by the Moebius isometry that sends `a` to the origin. Those lines
are complete — they are isometric embeddings of the whole real line — so they never leave the disc
at any finite time. This file describes where they go anyway: **as `t → ±∞` a geodesic line
converges, in the ambient plane, to a point of the unit circle**, and the two limits it has are
distinct. Those limits are the geodesic's *ideal endpoints*, the points at infinity of the
hyperbolic plane.

## What the computation is

For a radial geodesic there is nothing to do: `Real.tanh t → 1` as `t → ∞`, so `u * Real.tanh t`
tends to `u` itself, and to `-u` in the other direction. Off the origin the line is that radial
picture pushed forward by the Moebius factor centred at `-a`, whose formula
`z ↦ (z + a) / (1 + conj a * z)` extends past the open disc: it is continuous at every point of
the unit circle, because `‖conj a * z‖ = ‖a‖ < 1` keeps its denominator away from zero. So the
limit exists and is the value of that formula at `u`, which is
`TauCeti.PoincareDisc.idealEndpoint a u`. That value lies on the unit circle by
`TauCeti.pseudoHyperbolicExpr_eq_one_of_norm_eq_one`, the boundary form of the estimate that makes
the same formula map the open disc to itself — one identity governing both the interior and the
boundary behaviour of a disc automorphism.

## The rays out of a point

Fixing the base point `a` and varying the direction, `u ↦ idealEndpoint a u` is a **bijection of
the circle**: injective because the Moebius formula is, and surjective because
`ξ ↦ (ξ - a) / (1 - conj a * ξ)` inverts it, again by the same boundary norm identity. Read
geometrically that is `TauCeti.PoincareDisc.existsUnique_idealEndpoint_eq`: *from every point of
the disc there is exactly one geodesic ray to each ideal point*. Together with
`TauCeti.PoincareDisc.geodesicLine_injective`, which says distinct directions give distinct lines,
it identifies the directions at `a` with the ideal points, and it gives at once that the forward
and backward endpoints of one line differ (`TauCeti.PoincareDisc.idealEndpoint_neg_ne`), since
`u` and `-u` are distinct directions.

Two small reversal lemmas relate the two ends: negating the direction of a geodesic line is the
same as reversing its time (`TauCeti.PoincareDisc.radialGeodesic_neg`,
`TauCeti.PoincareDisc.geodesicLine_neg`), so the backward endpoint of `geodesicLine a u` is the
forward endpoint of `geodesicLine a (-u)` and no limit has to be computed twice.

## Main declarations

* `TauCeti.PoincareDisc.coe_geodesicLine` — the geodesic line through `a` in direction `u`, read
  as a complex number: the Moebius formula evaluated at `u * Real.tanh t`.
* `TauCeti.PoincareDisc.radialGeodesic_neg`, `TauCeti.PoincareDisc.geodesicLine_neg` — reversing
  the direction of a geodesic reverses its time parameter.
* `TauCeti.PoincareDisc.idealEndpoint` — the forward ideal endpoint of `geodesicLine a u`, a point
  of `Circle`, with its defining formula `TauCeti.PoincareDisc.coe_idealEndpoint` and its value
  `u` at the origin.
* `TauCeti.PoincareDisc.tendsto_coe_geodesicLine_atTop`,
  `TauCeti.PoincareDisc.tendsto_coe_geodesicLine_atBot` — **a geodesic line converges to its two
  ideal endpoints**, `idealEndpoint a u` forwards and `idealEndpoint a (-u)` backwards; for the
  lines through the origin these read `TauCeti.PoincareDisc.tendsto_coe_radialGeodesic_atTop` and
  `TauCeti.PoincareDisc.tendsto_coe_radialGeodesic_atBot`, with limits `u` and `-u`.
* `TauCeti.PoincareDisc.idealEndpoint_injective`,
  `TauCeti.PoincareDisc.idealEndpoint_surjective` and
  `TauCeti.PoincareDisc.existsUnique_idealEndpoint_eq` — **from each point of the disc there is
  exactly one geodesic ray to each ideal point**.
* `TauCeti.PoincareDisc.idealEndpoint_neg_ne` — the two ends of a geodesic line are distinct ideal
  points.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
the conformal layers, everything below is about the complex unit disc. The ideal boundary is taken
to be Mathlib's `Circle`, the unit circle of `ℂ`, rather than an abstract compactification: that
is the concrete model the disc automorphisms already act on, and the one the boundary layers
compare against.

This advances the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on `𝔻`"
(see `ConformalMapping/README.md`), extending the geodesic API of `Poincare/Geodesic.lean` to the
boundary behaviour of those geodesics. It reuses Tau Ceti's pseudo-hyperbolic, Moebius and
geodesic API and adds no new analytic input. As with the rest of the L0--L3 conformal-mapping
material it is coordinated with the upstream Mathlib Riemann-mapping effort
leanprover-community/mathlib4#33505, whose human-curated work in
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean` this file
duplicates nothing of; should a human-curated Poincaré-disc metric land upstream, this material
should be refactored onto it. Mathlib has the hyperbolic metric on the upper half-plane
(`Analysis/Complex/UpperHalfPlane`), but no Poincaré metric on the disc, no geodesics for it and
no ideal boundary.

## References

* L. V. Ahlfors, *Conformal Invariants*, Ch. 1.
* A. F. Beardon, *The Geometry of Discrete Groups* (GTM 91), §7.
-/

public section

namespace TauCeti

open Filter Metric Set Topology
open _root_.Complex
open scoped ComplexConjugate

namespace PoincareDisc

/-! ### The hyperbolic tangent at infinity -/

/-- `Real.tanh` written so that its limits at `±∞` are visible:
`tanh t = (1 - e ^ (-t) * e ^ (-t)) / (1 + e ^ (-t) * e ^ (-t))`, the quotient
`(e ^ t - e ^ (-t)) / (e ^ t + e ^ (-t))` with numerator and denominator divided by `e ^ t`.

Mathlib's `Analysis/SpecialFunctions/Artanh.lean` records that `Real.tanh` is a bijection onto
`Ioo (-1) 1` but not its limits, so they are proved here. Kept private: this is a real-analysis
rearrangement, not part of the Poincaré-disc API. -/
private lemma tanh_eq_div_exp_neg (t : ℝ) :
    Real.tanh t =
      (1 - Real.exp (-t) * Real.exp (-t)) / (1 + Real.exp (-t) * Real.exp (-t)) := by
  have hpos : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hneg : Real.exp (-t) = 1 / Real.exp t := by rw [Real.exp_neg, one_div]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hneg]
  field_simp

/-- The hyperbolic tangent tends to `1` at `+∞`. -/
private lemma tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  have hs : Tendsto (fun t : ℝ => Real.exp (-t) * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul Real.tendsto_exp_neg_atTop_nhds_zero
  have hnum : Tendsto (fun t : ℝ => 1 - Real.exp (-t) * Real.exp (-t)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hs
  have hden : Tendsto (fun t : ℝ => 1 + Real.exp (-t) * Real.exp (-t)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hs
  have h : Tendsto (fun t : ℝ => (1 - Real.exp (-t) * Real.exp (-t)) /
      (1 + Real.exp (-t) * Real.exp (-t))) atTop (𝓝 (1 / 1)) := hnum.div hden one_ne_zero
  rw [div_one] at h
  exact h.congr fun t => (tanh_eq_div_exp_neg t).symm

/-- The hyperbolic tangent tends to `-1` at `-∞`, by oddness. -/
private lemma tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  have h : Tendsto (fun t : ℝ => -(Real.tanh ∘ fun s : ℝ => -s) t) atBot (𝓝 (-1)) :=
    (tendsto_tanh_atTop.comp tendsto_neg_atBot_atTop).neg
  simpa [Function.comp_def, Real.tanh_neg] using h

/-- The direction `u` scaled by `Real.tanh`, the complex-number form of a radial geodesic, tends
to `u` at `+∞`. -/
private lemma tendsto_coe_mul_tanh_atTop (u : Circle) :
    Tendsto (fun t : ℝ => (u : ℂ) * ((Real.tanh t : ℝ) : ℂ)) atTop (𝓝 (u : ℂ)) := by
  simpa using
    (((Complex.continuous_ofReal.tendsto 1).comp tendsto_tanh_atTop).const_mul (u : ℂ))

/-- The direction `u` scaled by `Real.tanh` tends to `-u` at `-∞`. -/
private lemma tendsto_coe_mul_tanh_atBot (u : Circle) :
    Tendsto (fun t : ℝ => (u : ℂ) * ((Real.tanh t : ℝ) : ℂ)) atBot (𝓝 (-(u : ℂ))) := by
  simpa using
    (((Complex.continuous_ofReal.tendsto (-1)).comp tendsto_tanh_atBot).const_mul (u : ℂ))

/-! ### Reversing a geodesic -/

/-- **Reversing a radial geodesic.** Negating the direction of a radial geodesic reverses its time
parameter, `Real.tanh` being odd. So the backward half of `radialGeodesic u` is the forward half
of `radialGeodesic (-u)`. -/
lemma radialGeodesic_neg (u : Circle) (t : ℝ) :
    radialGeodesic (-u) t = radialGeodesic u (-t) :=
  toUnitDisc.injective <| Complex.UnitDisc.coe_injective <| by
    rw [coe_radialGeodesic, coe_radialGeodesic, Circle.coe_neg, Real.tanh_neg]
    push_cast
    ring

/-- **Reversing a geodesic line.** The base-point version of
`TauCeti.PoincareDisc.radialGeodesic_neg`: the line through `a` in direction `-u` is the line
through `a` in direction `u` run backwards. -/
lemma geodesicLine_neg (a : PoincareDisc) (u : Circle) (t : ℝ) :
    geodesicLine a (-u) t = geodesicLine a u (-t) := by
  rw [geodesicLine_def, geodesicLine_def, radialGeodesic_neg]

/-! ### The geodesic line as a complex number -/

/-- The geodesic line through `a` in direction `u`, read in the ambient plane: it is the Moebius
formula centred at `-a` evaluated at the radial point `u * Real.tanh t`.

This is what `TauCeti.PoincareDisc.geodesicLine` unfolds to on the underlying complex numbers, and
the form in which the limits at `±∞` are taken. -/
lemma coe_geodesicLine (a : PoincareDisc) (u : Circle) (t : ℝ) :
    ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ) =
      ((u : ℂ) * ((Real.tanh t : ℝ) : ℂ) + (toUnitDisc a : ℂ)) /
        (1 + conj (toUnitDisc a : ℂ) * ((u : ℂ) * ((Real.tanh t : ℝ) : ℂ))) := by
  rw [geodesicLine_def]
  simp only [unitDiscMoebiusIsometryEquiv_symm, unitDiscMoebiusIsometryEquiv_apply,
    toUnitDisc_toPoincare, coe_unitDiscMoebius, coe_radialGeodesic, Complex.UnitDisc.coe_neg,
    map_neg, sub_neg_eq_add, neg_mul]

/-! ### The ideal endpoint -/

/-- **The forward ideal endpoint of a Poincaré geodesic.** For a base point `a` of the Poincaré
disc and a direction `u : Circle`, this is the point of the unit circle that the geodesic line
`TauCeti.PoincareDisc.geodesicLine a u` converges to as `t → ∞`
(`TauCeti.PoincareDisc.tendsto_coe_geodesicLine_atTop`): the Moebius formula centred at `-a`,
which carries the open disc to itself, evaluated at `u`.

The backward endpoint of the same line is `idealEndpoint a (-u)`, by
`TauCeti.PoincareDisc.tendsto_coe_geodesicLine_atBot`. -/
noncomputable def idealEndpoint (a : PoincareDisc) (u : Circle) : Circle where
  val := ((u : ℂ) + (toUnitDisc a : ℂ)) / (1 + conj (toUnitDisc a : ℂ) * (u : ℂ))
  property := mem_sphere_zero_iff_norm.2 <| by
    have h := pseudoHyperbolicExpr_eq_one_of_norm_eq_one (z := (u : ℂ))
      (w := -(toUnitDisc a : ℂ)) (Circle.norm_coe u)
      (by simpa using (toUnitDisc a).norm_lt_one)
    rw [pseudoHyperbolicExpr_def] at h
    simpa only [map_neg, sub_neg_eq_add, neg_mul] using h

/-- The defining formula for the ideal endpoint. -/
@[simp]
lemma coe_idealEndpoint (a : PoincareDisc) (u : Circle) :
    (idealEndpoint a u : ℂ) =
      ((u : ℂ) + (toUnitDisc a : ℂ)) / (1 + conj (toUnitDisc a : ℂ) * (u : ℂ)) := by
  rw [idealEndpoint]

/-- At the origin the Moebius formula is the identity, so the ideal endpoint of the radial
geodesic in direction `u` is `u` itself. -/
@[simp]
lemma idealEndpoint_toPoincare_zero (u : Circle) :
    idealEndpoint (Complex.UnitDisc.toPoincare 0) u = u :=
  Circle.ext <| by simp

/-- The denominator of the Moebius formula does not vanish at a point of the unit circle: it is
`1` plus something of norm `‖a‖ < 1`. -/
private lemma one_add_conj_mul_ne_zero (a : PoincareDisc) {z : ℂ} (hz : ‖z‖ = 1) :
    1 + conj (toUnitDisc a : ℂ) * z ≠ 0 := by
  have hlt : ‖-(conj (toUnitDisc a : ℂ) * z)‖ < 1 := by
    rw [norm_neg, norm_mul, norm_conj, hz, mul_one]
    exact (toUnitDisc a).norm_lt_one
  simpa using (isUnit_one_sub_of_norm_lt_one hlt).ne_zero

/-- The Moebius defect `1 - a * conj a = 1 - ‖a‖ ^ 2` of an interior point, as a nonzero complex
number. It is the factor that the injectivity of `idealEndpoint a` cancels by. -/
private lemma one_sub_mul_conj_ne_zero (a : PoincareDisc) :
    (1 : ℂ) - (toUnitDisc a : ℂ) * conj (toUnitDisc a : ℂ) ≠ 0 := by
  have hlt : ‖(toUnitDisc a : ℂ)‖ ^ 2 < 1 := by
    nlinarith [(toUnitDisc a).norm_lt_one, norm_nonneg (toUnitDisc a : ℂ)]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, sub_ne_zero, ← Complex.ofReal_one]
  exact fun h => hlt.ne' (Complex.ofReal_inj.mp h)

/-! ### Convergence to the ideal endpoints -/

/-- A radial geodesic converges to its direction `u` as `t → ∞`. -/
theorem tendsto_coe_radialGeodesic_atTop (u : Circle) :
    Tendsto (fun t : ℝ => ((toUnitDisc (radialGeodesic u t) : Complex.UnitDisc) : ℂ)) atTop
      (𝓝 (u : ℂ)) := by
  simpa only [coe_radialGeodesic] using tendsto_coe_mul_tanh_atTop u

/-- A radial geodesic converges to `-u`, the direction it came from, as `t → -∞`. -/
theorem tendsto_coe_radialGeodesic_atBot (u : Circle) :
    Tendsto (fun t : ℝ => ((toUnitDisc (radialGeodesic u t) : Complex.UnitDisc) : ℂ)) atBot
      (𝓝 (-(u : ℂ))) := by
  simpa only [coe_radialGeodesic] using tendsto_coe_mul_tanh_atBot u

/-- **A geodesic line converges to its forward ideal endpoint.** As `t → ∞` the point
`geodesicLine a u t` tends, in the plane, to `idealEndpoint a u` on the unit circle.

The Moebius formula centred at `-a` is continuous at `u`, its denominator being nonzero there, so
the limit is obtained by evaluating it at the limit `u` of the radial geodesic. -/
theorem tendsto_coe_geodesicLine_atTop (a : PoincareDisc) (u : Circle) :
    Tendsto (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ)) atTop
      (𝓝 (idealEndpoint a u : ℂ)) := by
  have hnum := (tendsto_coe_mul_tanh_atTop u).add
    (tendsto_const_nhds (x := (toUnitDisc a : ℂ)) (f := atTop))
  have hden := (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop)).add
    ((tendsto_coe_mul_tanh_atTop u).const_mul (conj (toUnitDisc a : ℂ)))
  have h := hnum.div hden (one_add_conj_mul_ne_zero a (Circle.norm_coe u))
  rw [coe_idealEndpoint]
  exact h.congr fun t => (coe_geodesicLine a u t).symm

/-- **A geodesic line converges to its backward ideal endpoint.** As `t → -∞` the point
`geodesicLine a u t` tends to `idealEndpoint a (-u)`, the forward endpoint of the same line run in
the other direction (`TauCeti.PoincareDisc.geodesicLine_neg`). -/
theorem tendsto_coe_geodesicLine_atBot (a : PoincareDisc) (u : Circle) :
    Tendsto (fun t : ℝ => ((toUnitDisc (geodesicLine a u t) : Complex.UnitDisc) : ℂ)) atBot
      (𝓝 (idealEndpoint a (-u) : ℂ)) := by
  have h := (tendsto_coe_geodesicLine_atTop a (-u)).comp tendsto_neg_atBot_atTop
  refine h.congr fun t => ?_
  rw [Function.comp_apply, geodesicLine_neg, neg_neg]

/-! ### The rays out of a point -/

/-- Distinct directions at `a` have distinct ideal endpoints: cross-multiplying the two Moebius
values leaves `(u - v) * (1 - ‖a‖ ^ 2)`, and the Moebius defect `1 - ‖a‖ ^ 2` is nonzero. -/
theorem idealEndpoint_injective (a : PoincareDisc) : Function.Injective (idealEndpoint a) := by
  intro u v huv
  have h : ((u : ℂ) + (toUnitDisc a : ℂ)) * (1 + conj (toUnitDisc a : ℂ) * (v : ℂ)) =
      ((v : ℂ) + (toUnitDisc a : ℂ)) * (1 + conj (toUnitDisc a : ℂ) * (u : ℂ)) := by
    have hcoe := congrArg (fun z : Circle => (z : ℂ)) huv
    rwa [coe_idealEndpoint, coe_idealEndpoint,
      div_eq_div_iff (one_add_conj_mul_ne_zero a (Circle.norm_coe u))
        (one_add_conj_mul_ne_zero a (Circle.norm_coe v))] at hcoe
  have hfac : ((u : ℂ) - (v : ℂ)) *
      (1 - (toUnitDisc a : ℂ) * conj (toUnitDisc a : ℂ)) = 0 := by linear_combination h
  exact Circle.ext
    (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (one_sub_mul_conj_ne_zero a)))

/-- Every ideal point is the endpoint of a geodesic ray out of `a`: the direction to take is
`(ξ - a) / (1 - conj a * ξ)`, which lies on the unit circle by
`TauCeti.pseudoHyperbolicExpr_eq_one_of_norm_eq_one`. -/
theorem idealEndpoint_surjective (a : PoincareDisc) : Function.Surjective (idealEndpoint a) := by
  intro ξ
  have hden : (1 : ℂ) - conj (toUnitDisc a : ℂ) * (ξ : ℂ) ≠ 0 := by
    refine (isUnit_one_sub_of_norm_lt_one ?_).ne_zero
    rw [norm_mul, norm_conj, Circle.norm_coe, mul_one]
    exact (toUnitDisc a).norm_lt_one
  have hnorm : ‖((ξ : ℂ) - (toUnitDisc a : ℂ)) /
      (1 - conj (toUnitDisc a : ℂ) * (ξ : ℂ))‖ = 1 := by
    have h := pseudoHyperbolicExpr_eq_one_of_norm_eq_one (z := (ξ : ℂ))
      (w := (toUnitDisc a : ℂ)) (Circle.norm_coe ξ) (toUnitDisc a).norm_lt_one
    rwa [pseudoHyperbolicExpr_def] at h
  -- Name the direction as an element of `Circle`, rather than leaving the anonymous constructor
  -- in the goal, where its `Submonoid.unitSphere` membership proof would block rewriting.
  obtain ⟨u, hu⟩ : ∃ u : Circle, (u : ℂ) =
      ((ξ : ℂ) - (toUnitDisc a : ℂ)) / (1 - conj (toUnitDisc a : ℂ) * (ξ : ℂ)) :=
    ⟨⟨_, mem_sphere_zero_iff_norm.2 hnorm⟩, rfl⟩
  refine ⟨u, Circle.ext ?_⟩
  have hden' : (1 : ℂ) - (ξ : ℂ) * conj (toUnitDisc a : ℂ) ≠ 0 := by
    rwa [mul_comm (ξ : ℂ) (conj (toUnitDisc a : ℂ))]
  -- Both the numerator and the denominator of `idealEndpoint` at this direction collapse to a
  -- multiple of the Moebius defect `1 - ‖a‖ ^ 2`, and the quotient of the two multiples is `ξ`.
  rw [coe_idealEndpoint, div_eq_iff (one_add_conj_mul_ne_zero a (Circle.norm_coe u)), hu]
  field_simp
  ring

/-- **From every point of the Poincaré disc there is exactly one geodesic ray to each ideal
point.** Directions at `a` and ideal points correspond, and by
`TauCeti.PoincareDisc.geodesicLine_injective` distinct directions carry distinct geodesic
lines. -/
theorem existsUnique_idealEndpoint_eq (a : PoincareDisc) (ξ : Circle) :
    ∃! u : Circle, idealEndpoint a u = ξ :=
  (Function.Bijective.existsUnique
    ⟨idealEndpoint_injective a, idealEndpoint_surjective a⟩ ξ)

/-- **The two ends of a geodesic line are distinct ideal points**, `u` and `-u` being distinct
directions. -/
theorem idealEndpoint_neg_ne (a : PoincareDisc) (u : Circle) :
    idealEndpoint a (-u) ≠ idealEndpoint a u :=
  fun h => u.neg_ne_self (idealEndpoint_injective a h)

end PoincareDisc

end TauCeti
