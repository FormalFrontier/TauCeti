/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Winding.Number.Circle
import TauCeti.Analysis.Contour.Winding.Number.Reparam

/-!
# Excising a crossing window and capping it with a circular arc

Hungerbühler–Wasem Proposition 2.2 decomposes a closed piecewise-`C¹` immersion `Λ` that meets a
point `s` finitely often as `Λ = \tilde{\Lambda} + Γ₁ + ⋯ + Γₙ`, where `\tilde{\Lambda}` avoids `s`
and each `Γ_ℓ` is a local loop at a crossing, and concludes
`n_s(Λ) = n_s(\tilde{\Lambda}) + ∑_ℓ α_ℓ / 2π`. The identity *modulo an integer* is
`TauCeti.Contour.IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_sum_crossingAngle`, whose
integer is produced abstractly because the surgered curve `\tilde{\Lambda}` is never built. This
file builds it.

The surgery is the obvious one. A parameter window `[l, u]` containing the crossing is chosen so
that the curve sits on the circle `|z - s| = |r|` at both ends, `γ l = circleMap s r θ` and
`γ u = circleMap s r θ'`. The window is then deleted and replaced by the arc of that circle running
from angle `θ` to angle `θ'` (`TauCeti.Contour.circleCap`), giving `exciseCrossing γ s r l u θ θ'`,
a curve that agrees with `γ` outside the window. Each further property it has comes with its own
hypotheses:

* it is again piecewise `C¹` on `[a, b]` (`IsPiecewiseC1On.exciseCrossing`) provided `γ` is and the
  window sits strictly inside with `a < l < u < b`, the two endpoint conditions being what glues the
  cap to `γ`;
* it is again closed (`exciseCrossing_closed`) provided `γ a = γ b` and the window misses the two
  endpoints, `a < l` and `u < b`;
* and — this is the point — it **avoids `s`** (`exciseCrossing_ne_center`) provided the signed
  radial scale is nonzero, `r ≠ 0`, and `γ` itself meets `s` only strictly inside the window.

Under all of these together its winding number about `s` is an integer.

`Crossing.Decomposition` builds on this surgery to prove the exact finite-window winding-number
accounting identity and its one-window specialization.

What remains of HW Proposition 2.2 is the identification of the local contribution with the crossing
angle `α_ℓ / 2π` for a general immersion. It is congruent to `α_ℓ / 2π` modulo `1` — that is exactly
the content of the modulo-an-integer theorem cited above — and the outstanding step is the estimate
that pins the representative, namely that the local loop over a small enough window winds less than
once.

## Main definitions

* `TauCeti.Contour.circleCap` — for a nondegenerate window `l ≠ u`, the arc with signed radial scale
  `r` about `s` sweeping from angle `θ` to angle `θ'`, parametrised affinely over `[l, u]`; when
  `l = u` the affine change of parameter degenerates and the arc is constantly `circleMap s r θ`.
* `TauCeti.Contour.exciseCrossing` — the curve `γ` with the window `[l, u]` replaced by that cap.

## Main results

* `TauCeti.Contour.windingNumber_circleCap` — the cap has winding number `(θ' - θ) / 2π` about `s`.
* `TauCeti.Contour.IsPiecewiseC1On.exciseCrossing` — the excised curve is piecewise `C¹`,
  `TauCeti.Contour.exciseCrossing_closed` — it is closed if `γ` is, and
  `TauCeti.Contour.exciseCrossing_ne_center` — it avoids `s`.

## Provenance

Independently reconstructed; no formalization is vendored. The `ContourIntegration` roadmap
designates the AINTLIB `LeanModularForms` development
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), Apache-2.0) as the existing
source for this area, and assigns `LeanModularForms/ForMathlib/HungerbuhlerWasem/Crossing.lean` to
"Prop 2.2 / sector geometry". That file was consulted and carries no excise-and-cap construction:
at revision `340875a` it is the per-pole principal-value composition (`HasCauchyPV.add`,
`HasCauchyPV.finset_sum`, `cpv_polarPart_at_pole_under_conditions`) together with the crossing
angle-compatibility lemmas, and the surgered curve `\tilde{Λ}` is never built there either. The
one place AINTLIB names this excision, `ForMathlib/ExitTime.lean`, constructs only the exit-time
parameters bounding the window (`firstExitTimeLeft`, `firstExitTimeRight`), not the spliced curve.
So the definitions and proofs below are new, assembled from Tau Ceti's existing winding-number API
for reparametrisation and circles.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Proposition 2.2.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ : ℝ → ℂ} {s : ℂ} {a b l u r θ θ' t : ℝ}

/-! ### The circular cap -/

/-- **The circular cap** with signed radial scale `r` about `s`: the arc of the circle
`|z - s| = |r|` parametrised affinely over the window `[l, u]`, running from angle `θ` at `l`
(`circleCap_left`) to angle `θ'` at `u` (`circleCap_right`) whenever the window is nondegenerate,
`l ≠ u`. For `l = u` the affine
change of parameter divides by zero, so the cap is constantly `circleMap s r θ` and does not reach
angle `θ'`; every result below that needs the far endpoint assumes `l < u` or `l ≠ u`.

It is written as `circleMap s r` precomposed with an affine change of parameter, which is the shape
the reparametrisation and principal-value lemmas for circular arcs consume. -/
def circleCap (s : ℂ) (r l u θ θ' : ℝ) : ℝ → ℂ :=
  circleMap s r ∘ fun t => (θ' - θ) / (u - l) * t + (θ - (θ' - θ) / (u - l) * l)

/-- **Characteristic value lemma** for the circular cap: at parameter `t` it is the point of the
circle at angle `θ` advanced by the fraction `(t - l) / (u - l)` of the sweep `θ' - θ`.

Deliberately not `@[simp]`: it rewrites the left-hand sides of the endpoint lemmas `circleCap_left`
and `circleCap_right`, which are the simp-normal forms this file's consumers actually meet. -/
theorem circleCap_apply (s : ℂ) (r l u θ θ' t : ℝ) :
    circleCap s r l u θ θ' t = circleMap s r (θ + (θ' - θ) / (u - l) * (t - l)) := by
  simp only [circleCap, Function.comp_apply]
  congr 1
  ring

/-- The cap starts at the point of angle `θ`. -/
@[simp]
theorem circleCap_left (s : ℂ) (r l u θ θ' : ℝ) :
    circleCap s r l u θ θ' l = circleMap s r θ := by
  rw [circleCap_apply]
  congr 1
  ring

/-- The cap ends at the point of angle `θ'`, the window being nondegenerate. -/
@[simp]
theorem circleCap_right (s : ℂ) (r : ℝ) (hlu : l ≠ u) (θ θ' : ℝ) :
    circleCap s r l u θ θ' u = circleMap s r θ' := by
  have hul : u - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlu)
  rw [circleCap_apply]
  congr 1
  field_simp
  ring

/-- The cap is `C¹` (indeed smooth): the circle map is, and the change of parameter is affine. -/
theorem contDiff_circleCap (s : ℂ) (r l u θ θ' : ℝ) : ContDiff ℝ 1 (circleCap s r l u θ θ') :=
  (contDiff_circleMap s r).comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- The cap misses the centre when its signed radial scale is nonzero. -/
theorem circleCap_ne_center (hr : r ≠ 0) : circleCap s r l u θ θ' t ≠ s :=
  circleMap_ne_center hr

/-- The index principal value along the cap exists, the cap being an affinely reparametrised
circular arc. -/
theorem cauchyPVExistsAt_circleCap (s : ℂ) (r l u θ θ' a b : ℝ) :
    CauchyPVExistsAt (circleCap s r l u θ θ') a b (fun z => (z - s)⁻¹) s :=
  cauchyPVExistsAt_circleMap_comp_affine _ _ a b

/-- **The winding number of the cap is its angular extent over `2π`.** The arc misses `s`, so the
principal value collapses to the ordinary index integral, and the affine change of parameter carries
`[l, u]` onto `[θ, θ']`. -/
theorem windingNumber_circleCap (hr : r ≠ 0) (hlu : l ≠ u) (θ θ' : ℝ) :
    windingNumber (circleCap s r l u θ θ') l u s
      = ((θ' - θ : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hul : u - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlu)
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (circleMap s r) x := differentiable_circleMap s r
  have hderiv : ∀ S : Set ℝ, ContinuousOn (deriv (circleMap s r)) S := by
    intro S
    rw [funext (deriv_circleMap s r)]
    exact ((continuous_circleMap 0 r).mul continuous_const).continuousOn
  have hleft : (θ' - θ) / (u - l) * l + (θ - (θ' - θ) / (u - l) * l) = θ := by ring
  have hright : (θ' - θ) / (u - l) * u + (θ - (θ' - θ) / (u - l) * l) = θ' := by
    field_simp
    ring
  rw [circleCap, windingNumber_comp_mul_add (γ := circleMap s r) (z₀ := s)
      (fun x _ => hdiff x) (hderiv _) (fun x _ => circleMap_ne_center hr),
    hleft, hright, windingNumber_circleMap_center hr]

/-! ### The excised curve -/

/-- **The excised curve**: `γ` with the parameter window `[l, u]` deleted and replaced by the
circular cap with signed radial scale `r` about `s` running from angle `θ` to angle `θ'`. This is
the curve HW Proposition 2.2 calls `\tilde{\Lambda}`.

The definition itself assumes nothing; the properties that make it a surgery each need hypotheses.
If `γ` is continuous (indeed piecewise `C¹`) on `[a, b]`, the window is nondegenerate and strictly
inside, `a < l < u < b`, and the two endpoint conditions `γ l = circleMap s r θ` and
`γ u = circleMap s r θ'` hold, then the replacement glues continuously and the result is again
piecewise `C¹` (`IsPiecewiseC1On.exciseCrossing`). If moreover `γ a = γ b` it is again closed
(`exciseCrossing_closed`). And if the signed radial scale is nonzero, `r ≠ 0`, and `γ` meets `s`
only inside the open window, then the excised curve misses `s` altogether
(`exciseCrossing_ne_center`). -/
def exciseCrossing (γ : ℝ → ℂ) (s : ℂ) (r l u θ θ' : ℝ) : ℝ → ℂ :=
  fun t => if l ≤ t ∧ t ≤ u then circleCap s r l u θ θ' t else γ t

/-- **Characteristic value lemma** inside the window: there the excised curve is the cap. -/
@[simp]
theorem exciseCrossing_of_mem (ht : t ∈ Icc l u) :
    exciseCrossing γ s r l u θ θ' t = circleCap s r l u θ θ' t :=
  ite_eq_left (mem_Icc.mp ht)

/-- **Characteristic value lemma** outside the window: there the excised curve is `γ`. -/
@[simp]
theorem exciseCrossing_of_notMem (ht : t ∉ Icc l u) :
    exciseCrossing γ s r l u θ θ' t = γ t :=
  ite_eq_right fun h => ht (mem_Icc.mpr h)

/-- Left of the window the excised curve is `γ`, including at the left endpoint, where the cap
starts at `γ l`. -/
theorem exciseCrossing_eqOn_Iic (hlu : l ≤ u) (hθ : γ l = circleMap s r θ) (θ' : ℝ) :
    EqOn (exciseCrossing γ s r l u θ θ') γ (Iic l) := by
  intro t ht
  rcases eq_or_lt_of_le (mem_Iic.mp ht) with rfl | hlt
  · rw [exciseCrossing_of_mem ⟨le_refl _, hlu⟩, circleCap_left, hθ]
  · exact exciseCrossing_of_notMem fun h => absurd h.1 (not_le.mpr hlt)

/-- Right of the window the excised curve is `γ`, including at the right endpoint, where the cap
ends at `γ u`. -/
theorem exciseCrossing_eqOn_Ici (hlu : l < u) (θ : ℝ) (hθ' : γ u = circleMap s r θ') :
    EqOn (exciseCrossing γ s r l u θ θ') γ (Ici u) := by
  intro t ht
  rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | hlt
  · rw [exciseCrossing_of_mem ⟨hlu.le, le_refl _⟩, circleCap_right s r hlu.ne, hθ']
  · exact exciseCrossing_of_notMem fun h => absurd h.2 (not_le.mpr hlt)

/-- Inside the window the excised curve is the cap. -/
theorem exciseCrossing_eqOn_Icc (γ : ℝ → ℂ) (s : ℂ) (r l u θ θ' : ℝ) :
    EqOn (exciseCrossing γ s r l u θ θ') (circleCap s r l u θ θ') (Icc l u) :=
  fun _ ht => exciseCrossing_of_mem ht

/-- **The excised curve is closed** whenever `γ` is: the window `[l, u]` lies strictly inside
`[a, b]`, so both endpoints of `[a, b]` fall outside it and the excised curve takes the values of
`γ` there. -/
theorem exciseCrossing_closed (hal : a < l) (hub : u < b) (hclosed : γ a = γ b) (θ θ' : ℝ) :
    exciseCrossing γ s r l u θ θ' a = exciseCrossing γ s r l u θ θ' b := by
  rw [exciseCrossing_of_notMem fun h => absurd h.1 (not_le.mpr hal),
    exciseCrossing_of_notMem fun h => absurd h.2 (not_le.mpr hub), hclosed]

/-- **The excised curve avoids `s`.** Inside the window it runs along a circle with nonzero signed
radial scale about `s`, and outside it agrees with `γ`, which by hypothesis meets `s` only strictly
inside the window. -/
theorem exciseCrossing_ne_center (hr : r ≠ 0) (θ θ' : ℝ)
    (havoid : ∀ t ∈ Icc a b, t ∉ Ioo l u → γ t ≠ s) :
    ∀ t ∈ Icc a b, exciseCrossing γ s r l u θ θ' t ≠ s := by
  intro t ht
  by_cases hw : t ∈ Icc l u
  · rw [exciseCrossing_of_mem hw]
    exact circleCap_ne_center hr
  · rw [exciseCrossing_of_notMem hw]
    exact havoid t ht fun h => hw (Ioo_subset_Icc_self h)

/-- **The excised curve is piecewise `C¹`.** The two window endpoints join a piecewise-`C¹` curve to
a smooth arc, so they are the only new breakpoints. -/
theorem IsPiecewiseC1On.exciseCrossing (hγ : IsPiecewiseC1On γ a b) (hal : a < l) (hlu : l < u)
    (hub : u < b) (hθ : γ l = circleMap s r θ) (hθ' : γ u = circleMap s r θ') :
    IsPiecewiseC1On (TauCeti.Contour.exciseCrossing γ s r l u θ θ') a b := by
  have hab : a ≤ b := by linarith
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hleft := exciseCrossing_eqOn_Iic hlu.le hθ θ'
  have hright := exciseCrossing_eqOn_Ici hlu θ hθ'
  have hmid := exciseCrossing_eqOn_Icc γ s r l u θ θ'
  -- continuity, by gluing the three closed pieces
  have hcont : ContinuousOn (TauCeti.Contour.exciseCrossing γ s r l u θ θ') (uIcc a b) := by
    have hγ_cont : ContinuousOn γ (Icc a b) := hIcc ▸ hγ.continuousOn
    have h₁ : ContinuousOn (TauCeti.Contour.exciseCrossing γ s r l u θ θ') (Icc a l) :=
      (hγ_cont.mono (Icc_subset_Icc_right (by linarith))).congr
        fun x hx => hleft (mem_Iic.mpr hx.2)
    have h₂ : ContinuousOn (TauCeti.Contour.exciseCrossing γ s r l u θ θ') (Icc l u) :=
      ((contDiff_circleCap s r l u θ θ').continuous.continuousOn).congr fun x hx => hmid hx
    have h₃ : ContinuousOn (TauCeti.Contour.exciseCrossing γ s r l u θ θ') (Icc u b) :=
      (hγ_cont.mono (Icc_subset_Icc_left (by linarith))).congr
        fun x hx => hright (mem_Ici.mpr hx.1)
    rw [hIcc, ← Icc_union_Icc_eq_Icc (by linarith : a ≤ u) (by linarith : u ≤ b),
      ← Icc_union_Icc_eq_Icc (by linarith : a ≤ l) hlu.le]
    exact ((h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc).union_of_isClosed h₃
      (isClosed_Icc.union isClosed_Icc) isClosed_Icc)
  obtain ⟨p, hp, hC1⟩ := hγ.exists_breakpoints
  refine IsPiecewiseC1On.of_breakpoints hcont (insert l (insert u p)) ?_ ?_
  · have hmin : min a b = a := min_eq_left hab
    have hmax : max a b = b := max_eq_right hab
    intro x hx
    simp only [Finset.coe_insert, mem_insert_iff] at hx
    rw [hmin, hmax]
    rcases hx with rfl | rfl | hx
    · exact ⟨hal, by linarith⟩
    · exact ⟨by linarith, hub⟩
    · have hx' := hp hx
      rwa [hmin, hmax] at hx'
  · intro c d hcd hdis
    rcases lt_or_ge d c with hdc | -
    · rw [Icc_eq_empty (not_le.mpr hdc)]
      exact contDiffOn_empty
    have hlmem : l ∉ Ioo c d := disjoint_left.mp hdis (by simp)
    have humem : u ∉ Ioo c d := disjoint_left.mp hdis (by simp)
    have hdisp : Disjoint (↑p : Set ℝ) (Ioo c d) :=
      disjoint_left.mpr fun x hx => disjoint_left.mp hdis (by simp [hx])
    have hl' : l ≤ c ∨ d ≤ l := by
      rcases le_or_gt l c with h | h
      · exact Or.inl h
      · exact Or.inr (not_lt.mp fun hcon => hlmem ⟨h, hcon⟩)
    have hu' : u ≤ c ∨ d ≤ u := by
      rcases le_or_gt u c with h | h
      · exact Or.inl h
      · exact Or.inr (not_lt.mp fun hcon => humem ⟨h, hcon⟩)
    rcases hl' with hlc | hdl
    · rcases hu' with huc | hdu
      · -- the subinterval lies to the right of the window
        exact (hC1 c d hcd hdisp).congr fun x hx => hright (mem_Ici.mpr (huc.trans hx.1))
      · -- the subinterval lies inside the window
        exact ((contDiff_circleCap s r l u θ θ').contDiffOn).congr
          fun x hx => hmid ⟨hlc.trans hx.1, hx.2.trans hdu⟩
    · -- the subinterval lies to the left of the window
      exact (hC1 c d hcd hdisp).congr fun x hx => hleft (mem_Iic.mpr (hx.2.trans hdl))

end TauCeti.Contour

end

end
