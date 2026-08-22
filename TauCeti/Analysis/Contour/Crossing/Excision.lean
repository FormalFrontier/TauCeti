/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.ModelSector.Closed
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Winding.Number.Circle
import TauCeti.Analysis.Contour.Winding.Number.Concat
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
that the curve sits on the circle `|z - s| = r` at both ends, `γ l = circleMap s r θ` and
`γ u = circleMap s r θ'`. The window is then deleted and replaced by the arc of that circle running
from angle `θ` to angle `θ'` (`TauCeti.Contour.circleCap`), giving `exciseCrossing γ s r l u θ θ'`:
a curve that agrees with `γ` outside the window, is again closed and piecewise `C¹`, and — this is
the point — **avoids `s`**, so its winding number is an integer.

What the surgery buys is an exact accounting of the crossing
(`windingNumber_eq_exciseCrossing_add`):

`n_s(γ) = n_s(\tilde{γ}) + (n_s(γ|[l,u]) - (θ' - θ) / 2π)`,

the bracket being the winding number of the local loop `Γ` that runs along `γ` across the window and
returns along the cap reversed. Since `n_s(\tilde{γ}) ∈ ℤ`, this says the generalized winding
number of `γ` is an integer plus the crossing's own local contribution — HW Proposition 2.2 with the
integer no longer abstract. On the model sector, where the curve crosses along two straight radii,
the local contribution is exactly the opening angle over `2π` and the excised curve has winding
number `0` (`windingNumber_exciseCrossing_modelSector`).

What remains of HW Proposition 2.2 is the identification of the local contribution with the crossing
angle `α_ℓ / 2π` for a general immersion. It is congruent to `α_ℓ / 2π` modulo `1` — that is exactly
the content of the modulo-an-integer theorem cited above — and the outstanding step is the estimate
that pins the representative, namely that the local loop over a small enough window winds less than
once.

## Main definitions

* `TauCeti.Contour.circleCap` — the arc of the circle of radius `r` about `s` sweeping from angle
  `θ` to angle `θ'`, parametrised affinely over `[l, u]`.
* `TauCeti.Contour.exciseCrossing` — the curve `γ` with the window `[l, u]` replaced by that cap.

## Main results

* `TauCeti.Contour.windingNumber_circleCap` — the cap has winding number `(θ' - θ) / 2π` about `s`.
* `TauCeti.Contour.IsPiecewiseC1On.exciseCrossing` — the excised curve is piecewise `C¹`, and
  `TauCeti.Contour.exciseCrossing_ne` — it avoids `s`.
* `TauCeti.Contour.windingNumber_eq_exciseCrossing_add` — the winding number of `γ` is that of the
  excised curve plus the local contribution of the window.
* `TauCeti.Contour.exists_int_windingNumber_eq_add_crossing_excess` — hence it is an integer plus
  that local contribution.
* `TauCeti.Contour.windingNumber_exciseCrossing_modelSector` — excising the corner of a model sector
  leaves winding number `0`, the sector's whole index `α / 2π` being its local contribution.

## Provenance

No formalization is vendored. The excise-and-cap surgery is the construction behind
Hungerbühler–Wasem Proposition 2.2; everything here is assembled from Tau Ceti's existing winding
number API (concatenation, reparametrisation, the circle, the model sector) and its integrality
theorem for closed avoiding curves.

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

/-- **The circular cap** of radius `r` about `s`: the arc of the circle `|z - s| = r` running from
angle `θ` to angle `θ'`, parametrised affinely over the window `[l, u]`.

It is written as `circleMap s r` precomposed with an affine change of parameter, which is the shape
the reparametrisation and principal-value lemmas for circular arcs consume. -/
def circleCap (s : ℂ) (r l u θ θ' : ℝ) : ℝ → ℂ :=
  circleMap s r ∘ fun t => (θ' - θ) / (u - l) * t + (θ - (θ' - θ) / (u - l) * l)

/-- **Characteristic value lemma** for the circular cap: at parameter `t` it is the point of the
circle at angle `θ` advanced by the fraction `(t - l) / (u - l)` of the sweep `θ' - θ`. -/
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

/-- The cap misses the centre, its radius being nonzero. -/
theorem circleCap_ne (hr : r ≠ 0) : circleCap s r l u θ θ' t ≠ s :=
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
circular cap of radius `r` about `s` running from angle `θ` to angle `θ'`.

When the two endpoint conditions `γ l = circleMap s r θ` and `γ u = circleMap s r θ'` hold the
replacement is continuous, and if `γ` meets `s` only inside the open window then the excised curve
misses `s` altogether. This is the curve HW Proposition 2.2 calls `\tilde{\Lambda}`. -/
def exciseCrossing (γ : ℝ → ℂ) (s : ℂ) (r l u θ θ' : ℝ) : ℝ → ℂ :=
  fun t => if l ≤ t ∧ t ≤ u then circleCap s r l u θ θ' t else γ t

/-- **Characteristic value lemma** inside the window: there the excised curve is the cap. -/
theorem exciseCrossing_of_mem (ht : t ∈ Icc l u) :
    exciseCrossing γ s r l u θ θ' t = circleCap s r l u θ θ' t :=
  ite_eq_left (mem_Icc.mp ht)

/-- **Characteristic value lemma** outside the window: there the excised curve is `γ`. -/
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

/-- **The excised curve avoids `s`.** Inside the window it runs along a circle of nonzero radius
about `s`, and outside it agrees with `γ`, which by hypothesis meets `s` only strictly inside the
window. -/
theorem exciseCrossing_ne (hr : r ≠ 0) (θ θ' : ℝ)
    (havoid : ∀ t ∈ Icc a b, t ∉ Ioo l u → γ t ≠ s) :
    ∀ t ∈ Icc a b, exciseCrossing γ s r l u θ θ' t ≠ s := by
  intro t ht
  by_cases hw : t ∈ Icc l u
  · rw [exciseCrossing_of_mem hw]
    exact circleCap_ne hr
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

/-! ### The winding number across an excised crossing -/

/-- **Excising a crossing decomposes the winding number.** Let `γ` be piecewise `C¹` on `[a, b]`,
let `[l, u]` be a window strictly inside it whose endpoints sit on the circle of radius `r ≠ 0`
about `s`, at angles `θ` and `θ'`, and suppose `γ` meets `s` only strictly inside that window. Then

`n_s(γ) = n_s(\tilde{γ}) + (n_s(γ|[l,u]) - (θ' - θ) / 2π)`,

where `\tilde{γ}` is the excised curve. The bracket is the winding number of the local loop that
runs along `γ` across the window and returns along the cap reversed — the `Γ_ℓ` of
Hungerbühler–Wasem Proposition 2.2 — and the identity is exact, no smallness of the window is used.

Only the index principal value on the window is assumed; off the window the curve avoids `s`, so
there the principal values are ordinary integrals. -/
theorem windingNumber_eq_exciseCrossing_add (hγ : IsPiecewiseC1On γ a b) (hal : a < l)
    (hlu : l < u) (hub : u < b) (hr : r ≠ 0) (hθ : γ l = circleMap s r θ)
    (hθ' : γ u = circleMap s r θ') (havoid : ∀ t ∈ Icc a b, t ∉ Ioo l u → γ t ≠ s)
    (hpv : CauchyPVExistsAt γ l u (fun z => (z - s)⁻¹) s) :
    windingNumber γ a b s
      = windingNumber (exciseCrossing γ s r l u θ θ') a b s
        + (windingNumber γ l u s - ((θ' - θ : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) := by
  have hab : a ≤ b := by linarith
  have hleft := exciseCrossing_eqOn_Iic hlu.le hθ θ'
  have hright := exciseCrossing_eqOn_Ici hlu θ hθ'
  have hmid := exciseCrossing_eqOn_Icc γ s r l u θ θ'
  -- the principal values on the two point-avoiding flanks are ordinary integrals
  have hflank : ∀ c d : ℝ, uIcc c d ⊆ uIcc a b → (∀ t ∈ uIcc c d, γ t ≠ s) →
      CauchyPVExistsAt γ c d (fun z => (z - s)⁻¹) s := by
    intro c d hsub havd
    have hcd : IsPiecewiseC1On γ c d := hγ.mono hsub
    exact cauchyPVExistsAt_of_avoidance hcd.continuousOn havd
      (intervalIntegrable_inv_sub_mul_deriv hcd.continuousOn havd hcd.intervalIntegrable_deriv)
  have hIab : uIcc a b = Icc a b := uIcc_of_le hab
  have hpv_al : CauchyPVExistsAt γ a l (fun z => (z - s)⁻¹) s := by
    refine hflank a l ?_ ?_
    · rw [hIab, uIcc_of_le (by linarith : a ≤ l)]
      exact Icc_subset_Icc_right (by linarith)
    · rw [uIcc_of_le (by linarith : a ≤ l)]
      intro t ht
      exact havoid t ⟨ht.1, by linarith [ht.2]⟩ fun h => absurd ht.2 (not_le.mpr h.1)
  have hpv_ub : CauchyPVExistsAt γ u b (fun z => (z - s)⁻¹) s := by
    refine hflank u b ?_ ?_
    · rw [hIab, uIcc_of_le (by linarith : u ≤ b)]
      exact Icc_subset_Icc_left (by linarith)
    · rw [uIcc_of_le (by linarith : u ≤ b)]
      intro t ht
      exact havoid t ⟨by linarith [ht.1], ht.2⟩ fun h => absurd ht.1 (not_le.mpr h.2)
  -- the same three principal values along the excised curve
  have heq_al : EqOn γ (exciseCrossing γ s r l u θ θ') (uIoo a l) := by
    intro t ht
    rw [uIoo_of_le (by linarith : a ≤ l)] at ht
    exact (hleft (mem_Iic.mpr ht.2.le)).symm
  have heq_ub : EqOn γ (exciseCrossing γ s r l u θ θ') (uIoo u b) := by
    intro t ht
    rw [uIoo_of_le (by linarith : u ≤ b)] at ht
    exact (hright (mem_Ici.mpr ht.1.le)).symm
  have heq_lu : EqOn (circleCap s r l u θ θ') (exciseCrossing γ s r l u θ θ') (uIoo l u) := by
    intro t ht
    rw [uIoo_of_le hlu.le] at ht
    exact (hmid ⟨ht.1.le, ht.2.le⟩).symm
  have hpvE_al := hpv_al.congr_curve heq_al
  have hpvE_ub := hpv_ub.congr_curve heq_ub
  have hpvE_lu := (cauchyPVExistsAt_circleCap s r l u θ θ' l u).congr_curve heq_lu
  -- additivity over the three pieces, for both curves
  have hsplit : ∀ (c : ℝ → ℂ), CauchyPVExistsAt c a l (fun z => (z - s)⁻¹) s →
      CauchyPVExistsAt c l u (fun z => (z - s)⁻¹) s →
      CauchyPVExistsAt c u b (fun z => (z - s)⁻¹) s →
      windingNumber c a b s
        = windingNumber c a l s + windingNumber c l u s + windingNumber c u b s := by
    intro c h₁ h₂ h₃
    rw [windingNumber_eq_add_of_hasCauchyPVAt h₁.hasCauchyPVAt_cauchyPVAt
        (h₂.hasCauchyPVAt_cauchyPVAt.concat h₃.hasCauchyPVAt_cauchyPVAt),
      windingNumber_eq_add_of_hasCauchyPVAt h₂.hasCauchyPVAt_cauchyPVAt
        h₃.hasCauchyPVAt_cauchyPVAt, add_assoc]
  rw [hsplit γ hpv_al hpv hpv_ub, hsplit _ hpvE_al hpvE_lu hpvE_ub,
    ← windingNumber_congr_curve heq_al, ← windingNumber_congr_curve heq_ub,
    ← windingNumber_congr_curve heq_lu, windingNumber_circleCap hr hlu.ne θ θ']
  ring

/-- **Hungerbühler–Wasem Proposition 2.2 with the integer identified, for one crossing window.**
Under the hypotheses of `windingNumber_eq_exciseCrossing_add` on a *closed* curve, the winding
number of `γ` about `s` is an integer plus the local contribution of the window, the integer being
the winding number of the excised curve — which is an integer precisely because the surgery has
pushed the curve off `s`.

What is still missing for HW Proposition 2.2 is the evaluation of the local contribution as
`crossingAngle γ t₀ / 2π`; combined with
`TauCeti.Contour.IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_sum_crossingAngle` this statement
already gives that the two agree modulo `1`. -/
theorem exists_int_windingNumber_eq_add_crossing_excess (hγ : IsPiecewiseC1On γ a b) (hal : a < l)
    (hlu : l < u) (hub : u < b) (hr : r ≠ 0) (hclosed : γ a = γ b) (hθ : γ l = circleMap s r θ)
    (hθ' : γ u = circleMap s r θ') (havoid : ∀ t ∈ Icc a b, t ∉ Ioo l u → γ t ≠ s)
    (hpv : CauchyPVExistsAt γ l u (fun z => (z - s)⁻¹) s) :
    ∃ k : ℤ, windingNumber γ a b s
      = k + (windingNumber γ l u s - ((θ' - θ : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) := by
  have hab : a ≤ b := by linarith
  have hE := hγ.exciseCrossing hal hlu hub hθ hθ'
  have hEclosed : exciseCrossing γ s r l u θ θ' a = exciseCrossing γ s r l u θ θ' b := by
    rw [exciseCrossing_of_notMem fun h => absurd h.1 (not_le.mpr hal),
      exciseCrossing_of_notMem fun h => absurd h.2 (not_le.mpr hub), hclosed]
  obtain ⟨k, hk⟩ := hE.exists_int_windingNumber hEclosed
    (fun t ht => exciseCrossing_ne hr θ θ' havoid t ((uIcc_of_le hab) ▸ ht))
  exact ⟨k, by rw [windingNumber_eq_exciseCrossing_add hγ hal hlu hub hr hθ hθ' havoid hpv, hk]⟩

/-! ### The model sector, excised -/

/-- **Excising the corner of a model sector leaves nothing.** The model sector of radius `r` and
opening angle `α` crosses its own corner along two straight radii; deleting the window `[-ε, ε]` and
capping it with the arc from angle `φ + α` back to angle `φ` produces a closed curve of winding
number `0`.

Equivalently, the sector's entire index `α / 2π` is the local contribution of its crossing, which is
the model case of the identification that HW Proposition 2.2 asserts for a general immersion. -/
theorem windingNumber_exciseCrossing_modelSector {z₀ : ℂ} {ε φ α : ℝ} (hε : 0 < ε) (hεr : ε < r)
    (hα : 0 ≤ α) :
    windingNumber (exciseCrossing (modelSector z₀ r φ α) z₀ ε (-ε) ε (φ + α) φ)
      (-r) (r + α) z₀ = 0 := by
  have hr : 0 < r := hε.trans hεr
  set U : ℂ := Complex.exp ((φ + α : ℝ) * Complex.I) with hU
  set V : ℂ := Complex.exp ((φ : ℝ) * Complex.I) with hV
  have hVnorm : ‖V‖ = 1 := by rw [hV, Complex.norm_exp_ofReal_mul_I]
  have hUnorm : ‖U‖ = 1 := by rw [hU, Complex.norm_exp_ofReal_mul_I]
  have hUV : ‖U‖ = ‖V‖ := by rw [hUnorm, hVnorm]
  -- on the corner interval the sector is its two-ray corner
  have hcorner : EqOn (twoRayCorner z₀ U V) (modelSector z₀ r φ α) (uIoo (-ε) ε) := by
    intro t ht
    refine modelSector_eqOn_corner z₀ hr.le φ α ?_
    rw [uIoo_of_le (by linarith : -ε ≤ ε)] at ht
    rw [uIoo_of_le (by linarith : -r ≤ r)]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the two window endpoints lie on the circle of radius `ε`
  have hθ : modelSector z₀ r φ α (-ε) = circleMap z₀ ε (φ + α) := by
    rw [modelSector_of_le (by linarith : -ε ≤ r), twoRayCorner_of_neg (by linarith : -ε < 0),
      circleMap]
    push_cast
    ring
  have hθ' : modelSector z₀ r φ α ε = circleMap z₀ ε φ := by
    rw [modelSector_of_le (by linarith : ε ≤ r), twoRayCorner_of_nonneg hε.le, circleMap]
  -- off the window the sector misses its corner
  have havoid : ∀ t ∈ Icc (-r) (r + α), t ∉ Ioo (-ε) ε → modelSector z₀ r φ α t ≠ z₀ := by
    intro t _ ht
    have habs : ε ≤ |t| := by
      rcases le_or_gt t 0 with h | h
      · rw [abs_of_nonpos h]
        by_contra hcon
        exact ht ⟨by linarith [not_le.mp hcon], by linarith⟩
      · rw [abs_of_pos h]
        by_contra hcon
        exact ht ⟨by linarith, not_le.mp hcon⟩
    rcases le_or_gt t r with hle | hgt
    · rw [modelSector_of_le hle, ← sub_ne_zero, ← norm_ne_zero_iff, norm_twoRayCorner_sub hUV,
        hVnorm, mul_one]
      exact fun h => absurd (h ▸ habs) (by simpa using hε)
    · rw [modelSector_of_lt hgt]
      exact circleMap_ne_center hr.ne'
  -- the corner's own index vanishes, and its principal value exists
  have hpv : CauchyPVExistsAt (modelSector z₀ r φ α) (-ε) ε (fun z => (z - z₀)⁻¹) z₀ :=
    (cauchyPVExistsAt_inv_sub_twoRayCorner hUV ε).congr_curve hcorner
  have hzero : windingNumber (modelSector z₀ r φ α) (-ε) ε z₀ = 0 := by
    rw [← windingNumber_congr_curve hcorner]
    exact windingNumber_eq_zero_twoRayCorner hUV ε
  have hmain := windingNumber_eq_exciseCrossing_add
    (isPiecewiseC1On_modelSector hr.le φ α) (by linarith : -r < -ε) (by linarith : -ε < ε)
    (by linarith : ε < r + α) hε.ne' hθ hθ' havoid hpv
  rw [windingNumber_closedModelSector hr φ hα, hzero] at hmain
  have hcast : ((φ - (φ + α) : ℝ) : ℂ) = -(α : ℂ) := by push_cast; ring
  rw [hcast] at hmain
  linear_combination -hmain

end TauCeti.Contour

end

end
