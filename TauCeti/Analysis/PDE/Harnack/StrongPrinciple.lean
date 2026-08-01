/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.Harnack.Planar

/-!
# The strong maximum principle for planar harmonic functions

This file globalizes the zero case of the planar Harnack inequality from a disk to an arbitrary
open preconnected domain.  For a nonnegative harmonic function, the zero set is open by the local
disk result and its complement is open by continuity.  Preconnectedness therefore propagates one
zero throughout the domain.

Applying this zero-propagation result to differences gives the strong comparison principle and
the strong maximum and minimum principles: two ordered harmonic functions that meet at an
interior point agree everywhere, and a harmonic function attaining an extremum in the domain is
constant there.

This is the planar harmonic case of Lane C, item 13 in the PDE roadmap.  The argument is the
standard Harnack proof of the strong principle; see Evans, *Partial Differential Equations*,
Chapter 2, Section 2.2.

## Main declarations

* `TauCeti.eq_zero_on_of_harmonicOnNhd_of_nonneg_of_eq_zero`: a nonnegative harmonic function
  on an open preconnected domain that vanishes once vanishes everywhere.
* `TauCeti.eqOn_of_harmonicOnNhd_of_le_of_eq`: the strong comparison principle for planar
  harmonic functions.
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
  let V := Ω ∩ {z | f z = 0}
  have hVopen : IsOpen V := by
    refine Metric.isOpen_iff.mpr fun z hz ↦ ?_
    obtain ⟨hzΩ, hfz⟩ := hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ z hzΩ
    have hzero : EqOn f 0 (ball z r) :=
      eq_zero_on_ball_of_harmonicOnNhd_of_nonneg_of_eq_zero
        (hf.mono hball) (fun y hy ↦ hnonneg y (hball hy)) (mem_ball_self hr) hfz
    exact ⟨r, hr, fun y hy ↦ ⟨hball hy, hzero hy⟩⟩
  let W := Ω ∩ {z | f z = 0}ᶜ
  have hWopen : IsOpen W := by
    exact hf.continuousOn.isOpen_inter_preimage hΩ isOpen_ne
  have hVW : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hcover : Ω ⊆ V ∪ W := fun z hz ↦
    (eq_or_ne (f z) 0).imp (.intro hz) (.intro hz)
  have hVnonempty : (Ω ∩ V).Nonempty :=
    ⟨a, ha, ha, hfa⟩
  have hsub : Ω ⊆ V :=
    hΩconn.subset_left_of_subset_union hVopen hWopen hVW hcover hVnonempty
  intro z hz
  exact (hsub hz).2

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

/-- **Strong maximum principle for planar harmonic functions.**

A real-valued harmonic function on an open preconnected planar domain that attains its maximum
at a point of the domain is constant throughout the domain. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMaxOn
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (ha : a ∈ Ω) (hmax : IsMaxOn f Ω a) : EqOn f (const ℂ (f a)) Ω := by
  apply eqOn_of_harmonicOnNhd_of_le_of_eq hΩ hΩconn hf (harmonicOnNhd_const (f a))
      (fun z hz ↦ hmax hz) ha
  rfl

/-- **Strong minimum principle for planar harmonic functions.**

A real-valued harmonic function on an open preconnected planar domain that attains its minimum
at a point of the domain is constant throughout the domain. -/
theorem eqOn_const_of_harmonicOnNhd_of_isMinOn
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (ha : a ∈ Ω) (hmin : IsMinOn f Ω a) : EqOn f (const ℂ (f a)) Ω := by
  exact (eqOn_of_harmonicOnNhd_of_le_of_eq hΩ hΩconn (harmonicOnNhd_const (f a)) hf
    (fun z hz ↦ hmin hz) ha rfl).symm

end TauCeti

end

end
