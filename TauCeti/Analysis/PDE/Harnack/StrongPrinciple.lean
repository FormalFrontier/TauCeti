/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.Harnack.Planar

/-!
# The strong maximum principle for planar harmonic functions

This file globalizes the zero case of the planar Harnack inequality from a disk to an arbitrary
open preconnected domain.  The local disk result gives vanishing on a neighborhood, and Mathlib's
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` propagates that equality throughout the
preconnected domain.

Applying this zero-propagation result to differences gives the strong comparison principle and
the strong maximum and minimum principles: two ordered harmonic functions that meet at an
interior point agree everywhere, and a harmonic function with a local extremum in the domain is
constant there.  For the latter, the comparison principle first gives constancy on a disk.

This is the planar harmonic case of Lane C, item 13 in the PDE roadmap.  The local vanishing input
is the zero case of Harnack's inequality; see Evans, *Partial Differential Equations*, Chapter 2,
Section 2.2.

## Main declarations

* `TauCeti.eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero`: a nonnegative harmonic function
  on an open preconnected domain that vanishes once vanishes everywhere.
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

/-- A nonnegative harmonic function on an open preconnected planar domain that vanishes at one
point vanishes throughout the domain.

The openness of the domain is needed to place a disk around each of its points.  The conclusion
can fail on a disconnected domain, where a harmonic function may vanish on one component and be
positive on another. -/
theorem eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hnonneg : ∀ z ∈ Ω, 0 ≤ f z) (ha : a ∈ Ω) (hfa : f a = 0) :
    EqOn f 0 Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ a ha
  have hzero : EqOn f 0 (ball a r) :=
    eq_zero_on_ball_of_harmonicOnNhd_of_nonneg_of_eq_zero
      (hf.mono hball) (fun z hz ↦ hnonneg z (hball hz)) (mem_ball_self hr) hfa
  have hfanalytic : AnalyticOnNhd ℝ f Ω := fun z hz ↦ HarmonicAt.analyticAt (hf z hz)
  apply hfanalytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩconn ha
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact hzero hz

/-- **Strong comparison principle for planar harmonic functions.**

Let `f` and `g` be harmonic on an open preconnected domain.  If `f ≤ g` throughout the
domain and they agree at one point of it, then they agree throughout the domain. -/
theorem eqOn_of_harmonicOnNhd_of_le_of_eq
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hg : HarmonicOnNhd g Ω) (hfg : ∀ z ∈ Ω, f z ≤ g z) (ha : a ∈ Ω)
    (hfg_a : f a = g a) : EqOn f g Ω := by
  have hdiff : HarmonicOnNhd (g - f) Ω := hg.sub hf
  have hdiff_nonneg : ∀ z ∈ Ω, 0 ≤ (g - f) z := by
    intro z hz
    simpa only [Pi.sub_apply, sub_nonneg] using hfg z hz
  have hdiff_a : (g - f) a = 0 := by
    simp only [Pi.sub_apply, sub_eq_zero]
    exact hfg_a.symm
  have hzero := eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero hΩ hΩconn hdiff
    hdiff_nonneg ha hdiff_a
  intro z hz
  have hz_zero := hzero hz
  exact (sub_eq_zero.mp (by simpa only [Pi.sub_apply, Pi.zero_apply] using hz_zero)).symm

/-- **Local strong maximum principle for planar harmonic functions.**

A real-valued harmonic function on an open preconnected planar domain that has a local maximum
at a point of the domain is constant throughout the domain. -/
theorem eqOn_const_of_harmonicOnNhd_of_isLocalMax
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (ha : a ∈ Ω) (hmax : IsLocalMax f a) : EqOn f (const ℂ (f a)) Ω := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((show ∀ᶠ z in 𝓝 a, z ∈ Ω from hΩ.mem_nhds ha).and hmax)
  have hconst : EqOn f (const ℂ (f a)) (ball a r) :=
    eqOn_of_harmonicOnNhd_of_le_of_eq isOpen_ball (convex_ball a r).isPreconnected
      (hf.mono fun _ hz ↦ (hball hz).1) (harmonicOnNhd_const (f a))
      (fun _ hz ↦ (hball hz).2) (mem_ball_self hr) rfl
  have hfanalytic : AnalyticOnNhd ℝ f Ω := fun z hz ↦ HarmonicAt.analyticAt (hf z hz)
  apply hfanalytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩconn ha
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact hconst hz

/-- **Local strong minimum principle for planar harmonic functions.**

A real-valued harmonic function on an open preconnected planar domain that has a local minimum
at a point of the domain is constant throughout the domain. -/
theorem eqOn_const_of_harmonicOnNhd_of_isLocalMin
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (ha : a ∈ Ω) (hmin : IsLocalMin f a) : EqOn f (const ℂ (f a)) Ω := by
  have hneg := eqOn_const_of_harmonicOnNhd_of_isLocalMax hΩ hΩconn hf.neg ha hmin.neg
  intro z hz
  simpa only [Pi.neg_apply, Function.const_apply, neg_inj] using hneg hz

/-- **Strong maximum principle for planar harmonic functions, global-extremum form.**

A real-valued harmonic function on an open preconnected planar domain that attains its maximum
at a point of the domain is constant throughout the domain. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMaxOn
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (ha : a ∈ Ω) (hmax : IsMaxOn f Ω a) : EqOn f (const ℂ (f a)) Ω := by
  exact eqOn_const_of_harmonicOnNhd_of_isLocalMax hΩ hΩconn hf ha
    (hmax.isLocalMax (hΩ.mem_nhds ha))

/-- **Strong minimum principle for planar harmonic functions, global-extremum form.**

A real-valued harmonic function on an open preconnected planar domain that attains its minimum
at a point of the domain is constant throughout the domain. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMinOn
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (ha : a ∈ Ω) (hmin : IsMinOn f Ω a) : EqOn f (const ℂ (f a)) Ω := by
  exact eqOn_const_of_harmonicOnNhd_of_isLocalMin hΩ hΩconn hf ha
    (hmin.isLocalMin (hΩ.mem_nhds ha))

end TauCeti

end

end
