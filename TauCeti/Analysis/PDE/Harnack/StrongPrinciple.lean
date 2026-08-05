/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.Harnack.Planar

/-!
# The strong maximum principle for planar harmonic functions

This file globalizes the zero case of the planar Harnack inequality from a disk to a preconnected
set containing a neighborhood of the distinguished point.  The local disk result gives vanishing
on a neighborhood, and Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` propagates
that equality throughout the preconnected set.

Applying this zero-propagation result to differences gives the strong comparison principle and
the strong maximum and minimum principles: two ordered harmonic functions that meet at an
interior point agree everywhere, and a harmonic function with a local extremum there is constant
on the preconnected set.  For the latter, the comparison principle first gives constancy on a disk.

This is the planar harmonic case of Lane C, item 13 in the PDE roadmap.  The local vanishing input
is the zero case of Harnack's inequality; see Evans, *Partial Differential Equations*, Chapter 2,
Section 2.2.

## Main declarations

* `TauCeti.eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero`: a nonnegative harmonic function
  on a preconnected set that vanishes at an interior point vanishes everywhere on the set.
* `TauCeti.eqOn_of_harmonicOnNhd_of_le_of_eq`: the strong comparison principle for planar
  harmonic functions.
* `TauCeti.eqOn_const_of_harmonicOnNhd_of_isLocalMax`: the local strong maximum principle.
* `TauCeti.eqOn_const_of_harmonicOnNhd_of_isLocalMin`: the local strong minimum principle.
* `TauCeti.eqOn_const_of_harmonicOnNhd_of_isMaxOn`: the strong maximum principle.
* `TauCeti.eqOn_const_of_harmonicOnNhd_of_isMinOn`: the strong minimum principle.
-/

public section

noncomputable section

namespace TauCeti

open Function InnerProductSpace Metric Set Topology

variable {f g : ℂ → ℝ} {Ω : Set ℂ} {a : ℂ}

/-- A nonnegative harmonic function on a preconnected planar set that vanishes at an interior
point vanishes throughout the set.

The neighborhood hypothesis places a disk around the vanishing point.  The conclusion can fail
on a disconnected set, where a harmonic function may vanish on one component and be positive on
another. -/
theorem eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero
    (hΩa : Ω ∈ 𝓝 a) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hnonneg : ∀ z ∈ Ω, 0 ≤ f z) (hfa : f a = 0) :
    EqOn f 0 Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hΩa
  have hzero : EqOn f 0 (ball a r) :=
    eq_zero_on_ball_of_harmonicOnNhd_of_nonneg_of_eq_zero
      (hf.mono hball) (fun z hz ↦ hnonneg z (hball hz)) (mem_ball_self hr) hfa
  have hfanalytic : AnalyticOnNhd ℝ f Ω := fun z hz ↦ HarmonicAt.analyticAt (hf z hz)
  apply hfanalytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩconn
    (mem_of_mem_nhds hΩa)
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact hzero hz

/-- **Strong comparison principle for planar harmonic functions.**

Let `f` and `g` be harmonic on a preconnected set that is a neighborhood of `a`.  If `f ≤ g`
throughout the set and they agree at `a`, then they agree throughout the set. -/
theorem eqOn_of_harmonicOnNhd_of_le_of_eq
    (hΩa : Ω ∈ 𝓝 a) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hg : HarmonicOnNhd g Ω) (hfg : ∀ z ∈ Ω, f z ≤ g z) (hfg_a : f a = g a) :
    EqOn f g Ω := by
  have hdiff : HarmonicOnNhd (g - f) Ω := hg.sub hf
  have hdiff_nonneg : ∀ z ∈ Ω, 0 ≤ (g - f) z := by
    intro z hz
    simpa only [Pi.sub_apply, sub_nonneg] using hfg z hz
  have hdiff_a : (g - f) a = 0 := by
    simp only [Pi.sub_apply, sub_eq_zero]
    exact hfg_a.symm
  have hzero := eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero hΩa hΩconn hdiff
    hdiff_nonneg hdiff_a
  intro z hz
  have hz_zero := hzero hz
  exact (sub_eq_zero.mp (by simpa only [Pi.sub_apply, Pi.zero_apply] using hz_zero)).symm

/-- **Local strong maximum principle for planar harmonic functions.**

A real-valued harmonic function on a preconnected planar set that contains a neighborhood of a
local maximum point is constant throughout the set. -/
theorem eqOn_const_of_harmonicOnNhd_of_isLocalMax
    (hΩa : Ω ∈ 𝓝 a) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hmax : IsLocalMax f a) : EqOn f (const ℂ (f a)) Ω := by
  have hΩeventually : ∀ᶠ z in 𝓝 a, z ∈ Ω := hΩa
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hΩeventually.and hmax)
  have hconst : EqOn f (const ℂ (f a)) (ball a r) :=
    eqOn_of_harmonicOnNhd_of_le_of_eq (ball_mem_nhds a hr)
      (convex_ball a r).isPreconnected
      (hf.mono fun _ hz ↦ (hball hz).1) (harmonicOnNhd_const (f a))
      (fun _ hz ↦ (hball hz).2) rfl
  have hfanalytic : AnalyticOnNhd ℝ f Ω := fun z hz ↦ HarmonicAt.analyticAt (hf z hz)
  apply hfanalytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩconn
    (mem_of_mem_nhds hΩa)
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact hconst hz

/-- **Local strong minimum principle for planar harmonic functions.**

A real-valued harmonic function on a preconnected planar set that contains a neighborhood of a
local minimum point is constant throughout the set. -/
theorem eqOn_const_of_harmonicOnNhd_of_isLocalMin
    (hΩa : Ω ∈ 𝓝 a) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hmin : IsLocalMin f a) : EqOn f (const ℂ (f a)) Ω := by
  have hneg := eqOn_const_of_harmonicOnNhd_of_isLocalMax hΩa hΩconn hf.neg hmin.neg
  intro z hz
  simpa only [Pi.neg_apply, Function.const_apply, neg_inj] using hneg hz

/-- **Strong maximum principle for planar harmonic functions, global-extremum form.**

A real-valued harmonic function on a preconnected planar set that contains a neighborhood of an
attained maximum point is constant throughout the set. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMaxOn
    (hΩa : Ω ∈ 𝓝 a) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hmax : IsMaxOn f Ω a) : EqOn f (const ℂ (f a)) Ω := by
  exact eqOn_const_of_harmonicOnNhd_of_isLocalMax hΩa hΩconn hf
    (hmax.isLocalMax hΩa)

/-- **Strong minimum principle for planar harmonic functions, global-extremum form.**

A real-valued harmonic function on a preconnected planar set that contains a neighborhood of an
attained minimum point is constant throughout the set. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMinOn
    (hΩa : Ω ∈ 𝓝 a) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hmin : IsMinOn f Ω a) : EqOn f (const ℂ (f a)) Ω := by
  exact eqOn_const_of_harmonicOnNhd_of_isLocalMin hΩa hΩconn hf
    (hmin.isLocalMin hΩa)

end TauCeti

end

end
