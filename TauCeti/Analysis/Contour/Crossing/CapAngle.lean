/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.Excision
public import TauCeti.Analysis.Contour.RegularityConditions
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Chord.QuotientAsymptotics

/-!
# The capping angle at a crossing

Hungerbühler–Wasem Proposition 2.2 replaces a small window around a crossing of a curve through
`s` by a circular cap.  The local loop is the original crossing window followed by the reverse of
that cap.  Its winding number is the crossing angle divided by `2π`.

This file identifies the angle through which the cap must run.  If `L_L`, `L_R` are the incoming
and outgoing tangent limits and `w_L`, `w_R` are the two endpoint chords, put

`δ = arg (-L_L / w_L) + arg (w_R / L_R) - crossingAngle γ t₀`.

The angle identity behind the per-window principal-value calculation says that `δ` is the angle
from `w_L` to `w_R`, modulo `2π`.  Thus, when the endpoint chords have equal norm, the circular arc
starting at `w_L` and sweeping through `δ` ends at `w_R`.  Moreover `δ` tends to
`-crossingAngle γ t₀` as the endpoints tend to the crossing from their respective sides.  This is
the branch control needed to ensure that a sufficiently local cap is the reverse of the model
sector arc, rather than that arc with an unnoticed extra turn.

The final theorem records the exact local accounting.  Its chord identities, equal-radius
condition, and tangent-limit hypotheses prove that the cap has the same endpoints as the crossing
window.  Whenever the principal value on that window has the standard boundary-argument value
supplied by the per-window calculation, subtracting the winding number of the cap leaves exactly
`crossingAngle γ t₀ / 2π`.  This is the geometric bridge from that analytic calculation to the
excision identity in `TauCeti.Analysis.Contour.Crossing.Excision`.

## Main definitions and results

* `TauCeti.Contour.crossingCapSweep` — the signed angular sweep of the cap from the incoming chord
  to the outgoing chord.
* `TauCeti.Contour.coe_crossingCapSweep_eq_arg_div` — this sweep is the endpoint-chord angle modulo
  `2π`.
* `TauCeti.Contour.circleMap_crossingCapSweep_endpoints` — at equal endpoint radii it gives a
  circular cap with the required endpoints.
* `TauCeti.Contour.tendsto_crossingCapSweep` — the sweep converges to the negative crossing angle.
* `TauCeti.Contour.windingNumber_sub_circleCap_eq_crossingAngle_div_two_pi` — the local loop has
  winding number `crossingAngle / 2π` once the standard per-window principal value is known.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.2.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {s L_R L_L w_L w_R : ℂ} {t₀ l u : ℝ}

/-- **The signed sweep of the circular cap at a crossing.**  The two argument terms are exactly
the boundary arguments in the principal value over the crossing window.  Subtracting the crossing
angle leaves the angle swept from the left endpoint chord `w_L` to the right endpoint chord `w_R`.

For endpoints sufficiently close to the crossing this tends to `-crossingAngle γ t₀`, because the
cap runs from the reversed incoming ray to the outgoing ray, opposite to the model-sector arc. -/
def crossingCapSweep (γ : ℝ → ℂ) (t₀ : ℝ) (L_R L_L w_L w_R : ℂ) : ℝ :=
  ((-L_L) / w_L).arg + (w_R / L_R).arg - crossingAngle γ t₀

/-- **The cap sweep joins the two endpoint directions.**  Modulo `2π`, `crossingCapSweep` is the
argument of `w_R / w_L`.  This is the exact angle identity: no small-window assumption is needed
until one wants to select the representative with no extra full turn. -/
theorem coe_crossingCapSweep_eq_arg_div (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0)
    (hw_L : w_L ≠ 0) (hw_R : w_R ≠ 0)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    (crossingCapSweep γ t₀ L_R L_L w_L w_R : Real.Angle) =
      ((w_R / w_L).arg : Real.Angle) := by
  have h := coe_crossingAngle_eq_arg_neg_div_add_arg_div_sub_arg_div
    hL_L hL_R hw_L hw_R h_R h_L
  rw [crossingCapSweep, Real.Angle.coe_sub, Real.Angle.coe_add, h]
  abel

/-- The exponential of the cap sweep is the unit endpoint ratio.  Equal endpoint norms turn this
into the endpoint ratio itself. -/
theorem exp_crossingCapSweep_mul_I (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0)
    (hw_L : w_L ≠ 0) (hnorm : ‖w_L‖ = ‖w_R‖)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    Complex.exp ((crossingCapSweep γ t₀ L_R L_L w_L w_R : ℂ) * Complex.I) = w_R / w_L := by
  have hw_R : w_R ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [← hnorm]
    exact norm_ne_zero_iff.mpr hw_L
  rw [exp_mul_I_congr_angle
    (coe_crossingCapSweep_eq_arg_div hL_L hL_R hw_L hw_R h_R h_L)]
  have hratio_norm : ‖w_R / w_L‖ = 1 := by
    rw [norm_div, ← hnorm, div_self (norm_ne_zero_iff.mpr hw_L)]
  calc
    Complex.exp (((w_R / w_L).arg : ℂ) * Complex.I) =
        (‖w_R / w_L‖ : ℂ) * Complex.exp (((w_R / w_L).arg : ℂ) * Complex.I) := by
          rw [hratio_norm]
          simp
    _ = w_R / w_L := Complex.norm_mul_exp_arg_mul_I _

/-- **The cap has the prescribed endpoints.**  If the endpoint chords have equal norm, the circle
of that radius about `s`, starting at the principal argument of `w_L` and sweeping through
`crossingCapSweep`, starts at `s + w_L` and ends at `s + w_R`. -/
theorem circleMap_crossingCapSweep_endpoints (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0)
    (hnorm : ‖w_L‖ = ‖w_R‖)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    circleMap s ‖w_L‖ w_L.arg = s + w_L ∧
      circleMap s ‖w_L‖
          (w_L.arg + crossingCapSweep γ t₀ L_R L_L w_L w_R) = s + w_R := by
  by_cases hw_L : w_L = 0
  · have hw_R : w_R = 0 := by
      apply norm_eq_zero.mp
      rw [← hnorm, hw_L, norm_zero]
    simp [circleMap, hw_L, hw_R]
  constructor
  · rw [circleMap, Complex.norm_mul_exp_arg_mul_I]
  · rw [circleMap, Complex.ofReal_add, add_mul, Complex.exp_add,
      exp_crossingCapSweep_mul_I hL_L hL_R hw_L hnorm h_R h_L]
    have hwL_norm : (‖w_L‖ : ℂ) * Complex.exp ((w_L.arg : ℂ) * Complex.I) = w_L :=
      Complex.norm_mul_exp_arg_mul_I w_L
    calc
      s + (‖w_L‖ : ℂ) *
          (Complex.exp ((w_L.arg : ℂ) * Complex.I) * (w_R / w_L)) =
          s + ((‖w_L‖ : ℂ) * Complex.exp ((w_L.arg : ℂ) * Complex.I)) *
            (w_R / w_L) := by ring
      _ = s + w_R := by rw [hwL_norm]; field_simp

/-- **A local cap approaches the reverse model-sector arc.**  As its left and right endpoint
parameters tend independently to `t₀`, `crossingCapSweep` tends to the negative crossing angle.
Thus for a small window it chooses the local representative of the endpoint angle, not a cap with
an additional full turn. -/
theorem tendsto_crossingCapSweep (h_at : γ t₀ = s) (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0)
    (h_deriv_L : HasDerivWithinAt γ L_L (Iio t₀) t₀)
    (h_deriv_R : HasDerivWithinAt γ L_R (Ioi t₀) t₀) :
    Tendsto (fun p : ℝ × ℝ => crossingCapSweep γ t₀ L_R L_L
        (γ p.1 - s) (γ p.2 - s))
      ((𝓝[<] t₀) ×ˢ (𝓝[>] t₀)) (𝓝 (-crossingAngle γ t₀)) := by
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) ((𝓝[<] t₀) ×ˢ (𝓝[>] t₀)) (𝓝[<] t₀) :=
    tendsto_fst
  have hsnd : Tendsto (fun p : ℝ × ℝ => p.2) ((𝓝[<] t₀) ×ˢ (𝓝[>] t₀)) (𝓝[>] t₀) :=
    tendsto_snd
  have hleft := (tendsto_arg_neg_tangent_div_chord_nhdsLT h_at hL_L h_deriv_L).comp hfst
  have hright := (tendsto_arg_chord_div_tangent_nhdsGT h_at hL_R h_deriv_R).comp hsnd
  simpa only [crossingCapSweep, Function.comp_apply, zero_add, zero_sub] using
    (hleft.add hright).sub tendsto_const_nhds

/-- **The local crossing loop contributes exactly the crossing angle.**  Suppose `w_L` and `w_R`
are the endpoint chords of `[l, u]`, have equal norm, and the one-sided tangent limits are nonzero.
Then the circular cap with sweep `crossingCapSweep` joins `γ l` to `γ u`.  If the principal value
on the window is the standard pure-imaginary boundary-argument value
`i · (arg (-L_L / w_L) + arg (w_R / L_R))`, as supplied by the separate per-window calculation,
the winding number of the crossing window minus that of the cap is exactly
`crossingAngle γ t₀ / 2π`.  Thus the window followed by the reversed cap is the one-window local
loop contribution in Hungerbühler–Wasem Proposition 2.2. -/
theorem windingNumber_sub_circleCap_eq_crossingAngle_div_two_pi
    (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0) (hw_L : w_L ≠ 0) (hlu : l ≠ u)
    (hw_l : w_L = γ l - s) (hw_u : w_R = γ u - s) (hnorm : ‖w_L‖ = ‖w_R‖)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (hpv : HasCauchyPVAt γ l u (fun z => (z - s)⁻¹) s
      (((((-L_L) / w_L).arg + (w_R / L_R).arg : ℝ) : ℂ) * Complex.I)) :
    let cap := circleCap s ‖w_L‖ l u w_L.arg
      (w_L.arg + crossingCapSweep γ t₀ L_R L_L w_L w_R)
    cap l = γ l ∧ cap u = γ u ∧
      windingNumber γ l u s - windingNumber cap l u s
        = (crossingAngle γ t₀ : ℂ) / (2 * (Real.pi : ℂ)) := by
  dsimp only
  have hends := circleMap_crossingCapSweep_endpoints (s := s) hL_L hL_R hnorm h_R h_L
  constructor
  · rw [circleCap_left, hends.1, hw_l]
    ring
  constructor
  · rw [circleCap_right s ‖w_L‖ hlu w_L.arg, hends.2, hw_u]
    ring
  · rw [windingNumber_eq_of_hasCauchyPVAt hpv,
      windingNumber_circleCap (norm_ne_zero_iff.mpr hw_L) hlu w_L.arg
        (w_L.arg + crossingCapSweep γ t₀ L_R L_L w_L w_R)]
    simp only [add_sub_cancel_left, crossingCapSweep]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    push_cast
    ring

end TauCeti.Contour

end

end
