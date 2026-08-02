/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.CrossingValue.Curvature
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Boundedness of the real winding integrand at crossings

For a `C²` immersed plane curve `γ` and a point `w`, the real winding integrand

`realWindingIntegrand (γ t - w) (deriv γ t)`

is bounded on every compact parameter set, even when `γ` passes through `w`.  This is the
smooth case of the bounded-integrand assertion in Hungerbühler--Wasem Proposition 2.3.  At a
crossing the displayed function is defined to be zero, while its punctured limit is half the
signed curvature times speed.  The proof fills in the crossing values by those finite limits,
obtains a continuous auxiliary function, and then uses compactness.

The full proposition only needs `C^{1,1}` regularity.  The `C²` result here is the direct global
companion to the existing pointwise `C²` crossing-value theorem; weakening the regularity requires
the corresponding almost-everywhere second-order crossing analysis.

As in the crossing-value modules, the value is written using the explicit coordinate formula
because Mathlib has no signed-curvature API for plane curves.

## Main result

* `TauCeti.Contour.isBounded_image_realWindingIntegrand` -- the real winding integrand of a `C²`
  immersion has bounded image on a compact parameter set, without an avoidance hypothesis.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Complex Filter Set Topology

/-- The removable extension of the real winding integrand at crossings.  At `γ t = w` it takes
the crossing value `(x' y'' - y' x'') / (2 (x'² + y'²))`; away from crossings it is the ordinary
real winding integrand. -/
private def realWindingIntegrandExtension (γ : ℝ → ℂ) (w : ℂ) (t : ℝ) : ℝ :=
  if γ t = w then
    ((deriv γ t).re * (deriv (deriv γ) t).im
          - (deriv γ t).im * (deriv (deriv γ) t).re) /
      (2 * ((deriv γ t).re ^ 2 + (deriv γ t).im ^ 2))
  else
    realWindingIntegrand (γ t - w) (deriv γ t)

/-- The curvature-speed expression used to fill the crossings is continuous wherever `γ` is
`C²` and its velocity is nonzero. -/
private theorem continuousAt_crossingValue {γ : ℝ → ℂ} {t : ℝ}
    (hγ : ContDiffAt ℝ 2 γ t) (hvel : deriv γ t ≠ 0) :
    ContinuousAt (fun s ↦
      ((deriv γ s).re * (deriv (deriv γ) s).im
            - (deriv γ s).im * (deriv (deriv γ) s).re) /
        (2 * ((deriv γ s).re ^ 2 + (deriv γ s).im ^ 2))) t := by
  have hD : ContinuousAt (deriv γ) t :=
    (ContDiffAt.derivWithin (m := 0) hγ (by norm_num)).continuousAt
  have hA : ContinuousAt (deriv (deriv γ)) t :=
    (ContDiffAt.derivWithin (m := 0)
      (ContDiffAt.derivWithin (m := 1) hγ (by norm_num)) (by norm_num)).continuousAt
  have hden : 2 * ((deriv γ t).re ^ 2 + (deriv γ t).im ^ 2) ≠ 0 := by
    have hnorm : 0 < Complex.normSq (deriv γ t) := Complex.normSq_pos.mpr hvel
    rw [Complex.normSq_apply] at hnorm
    nlinarith
  exact (((Complex.continuous_re.continuousAt.comp hD).mul
      (Complex.continuous_im.continuousAt.comp hA)).sub
    ((Complex.continuous_im.continuousAt.comp hD).mul
      (Complex.continuous_re.continuousAt.comp hA))).div
    (continuousAt_const.mul
      (((Complex.continuous_re.continuousAt.comp hD).pow 2).add
        ((Complex.continuous_im.continuousAt.comp hD).pow 2))) hden

/-- Away from a crossing, the ordinary real winding integrand is continuous. -/
private theorem continuousAt_realWindingIntegrand {γ : ℝ → ℂ} {w : ℂ} {t : ℝ}
    (hγ : ContDiffAt ℝ 2 γ t) (havoid : γ t ≠ w) :
    ContinuousAt (fun s ↦ realWindingIntegrand (γ s - w) (deriv γ s)) t := by
  simp_rw [realWindingIntegrand_def]
  exact Complex.continuous_im.continuousAt.comp
    (((hγ.continuousAt.sub continuousAt_const).inv₀ (sub_ne_zero.mpr havoid)).mul
      ((ContDiffAt.derivWithin (m := 0) hγ (by norm_num)).continuousAt))

/-- Filling each crossing with its curvature-speed value makes the real winding integrand
continuous on any set where the curve is pointwise `C²` and immersed. -/
private theorem continuousOn_realWindingIntegrandExtension {γ : ℝ → ℂ} {w : ℂ} {K : Set ℝ}
    (hγ : ∀ t ∈ K, ContDiffAt ℝ 2 γ t)
    (hvel : ∀ t ∈ K, deriv γ t ≠ 0) :
    ContinuousOn (realWindingIntegrandExtension γ w) K := by
  intro t ht
  have hγt : ContDiffAt ℝ 2 γ t := hγ t ht
  have hcurv := continuousAt_crossingValue hγt (hvel t ht)
  apply ContinuousAt.continuousWithinAt
  by_cases hcross : γ t = w
  · rw [continuousAt_iff_punctured_nhds]
    rw [realWindingIntegrandExtension, if_pos hcross]
    exact (hcurv.tendsto.mono_left nhdsWithin_le_nhds).if'
      (tendsto_realWindingIntegrand_at_crossing_of_contDiffAt hγt hcross (hvel t ht))
  · apply (continuousAt_realWindingIntegrand hγt hcross).congr_of_eventuallyEq
    filter_upwards [hγt.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds hcross)] with s hs
    simp only [mem_singleton_iff] at hs
    simp only [realWindingIntegrandExtension, if_neg hs]

/-- **Hungerbühler--Wasem Proposition 2.3, bounded-integrand assertion in the `C²` case.**
Let `γ` be pointwise `C²` with nonzero velocity on a compact parameter set `K`. For every `w : ℂ`,
the image of

`t ↦ realWindingIntegrand (γ t - w) (deriv γ t)`

on `K` is bounded.  No avoidance hypothesis is imposed: at parameters where `γ t = w`,
the real integrand is defined to be zero, and near each such parameter its finite punctured limit
is the explicit half-curvature-times-speed value from
`tendsto_realWindingIntegrand_at_crossing_of_contDiffAt`. -/
theorem isBounded_image_realWindingIntegrand {γ : ℝ → ℂ} {w : ℂ} {K : Set ℝ}
    (hK : IsCompact K) (hγ : ∀ t ∈ K, ContDiffAt ℝ 2 γ t)
    (hvel : ∀ t ∈ K, deriv γ t ≠ 0) :
    Bornology.IsBounded
      ((fun t ↦ realWindingIntegrand (γ t - w) (deriv γ t)) '' K) := by
  have hext_cont : ContinuousOn (realWindingIntegrandExtension γ w) K :=
    continuousOn_realWindingIntegrandExtension hγ hvel
  have hext_bdd : Bornology.IsBounded
      (realWindingIntegrandExtension γ w '' K) :=
    (hK.image_of_continuousOn hext_cont).isBounded
  refine (hext_bdd.union (Set.finite_singleton (0 : ℝ)).isBounded).subset ?_
  rintro y ⟨t, ht, rfl⟩
  by_cases hcross : γ t = w
  · right
    simp [hcross]
  · left
    exact ⟨t, ht, by simp [realWindingIntegrandExtension, hcross]⟩

end TauCeti.Contour

end
