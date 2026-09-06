/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Archon Horizon (claude+codex), Axel Delaval,
  Chunlei Liu, Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Inverses of primitives of positive functions

The primitive of a continuous positive real function is strictly increasing, and its inverse is
continuously differentiable on the interval between the primitive's endpoint values. This is the
parameter-side inverse result used by the regular Riemannian reparametrization theorem.

The result supplies the interval-integral and inverse-function input for constructing arclength
parametrizations of regular curves.
-/

public section

open Filter Set

namespace TauCeti

noncomputable section

/-- The primitive of a continuous positive real function on `[a, b]` has a
`C¹` inverse on the interval between the primitive's endpoint values.

The conclusion records both interval inverse identities, the endpoint values,
strict monotonicity, and the derivative of the inverse. Values of the inverse outside
the primitive's interval image are intentionally left unspecified. -/
theorem exists_contDiffOn_intervalIntegral_inverse_of_pos {v : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hv_cont : ContinuousOn v (Icc a b))
    (hv_pos : ∀ t ∈ Icc a b, 0 < v t) :
    ∃ L : ℝ, ∃ psi : ℝ → ℝ,
      L = ∫ t in a..b, v t ∧
      0 < L ∧
      MapsTo psi (Icc 0 L) (Icc a b) ∧
      StrictMonoOn psi (Icc 0 L) ∧
      psi 0 = a ∧
      psi L = b ∧
      (∀ t ∈ Icc a b, psi (∫ s in a..t, v s) = t) ∧
      (∀ s ∈ Icc 0 L, ∫ t in a..psi s, v t = s) ∧
      ContDiffOn ℝ 1 psi (Icc 0 L) ∧
      (∀ s ∈ Icc 0 L, HasDerivAt psi (v (psi s))⁻¹ s) := by
  -- Clamp the integrand to `[a, b]`; this is an internal device for applying
  -- the global inverse-function theorem and is invisible in the public API.
  let p : ℝ → Icc a b := projIcc a b hab.le
  let w : ℝ → ℝ := (Icc a b).domRestrict v ∘ p
  have hw_cont : Continuous w := hv_cont.domRestrict.comp continuous_projIcc
  have hw_eq : ∀ t ∈ Icc a b, w t = v t := by
    intro t ht
    simp only [w, p, Function.comp_apply, Set.domRestrict_apply,
      projIcc_of_mem hab.le ht]
  have hw_pos : ∀ t, 0 < w t := by
    intro t
    simpa only [w, Function.comp_apply, Set.domRestrict_apply] using
      hv_pos (p t) (p t).property
  have hintegral_eq : ∀ t ∈ Icc a b,
      (∫ s in a..t, w s) = ∫ s in a..t, v s := by
    intro t ht
    refine intervalIntegral.integral_congr fun r hr ↦ hw_eq r ?_
    rw [uIcc_of_le ht.1] at hr
    exact ⟨hr.1, hr.2.trans ht.2⟩
  -- Build the primitive of the clamped extension and prove its derivative,
  -- additivity, and strict monotonicity from positivity.
  let phi : ℝ → ℝ := fun t ↦ ∫ s in a..t, w s
  have hphi_strict : ∀ t, HasStrictDerivAt phi (w t) t := by
    intro t
    simpa only [phi] using hw_cont.integral_hasStrictDerivAt a t
  have hphi_add : ∀ s t, phi t = phi s + ∫ r in s..t, w r := by
    intro s t
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hw_cont.intervalIntegrable a s) (hw_cont.intervalIntegrable s t)
    simpa only [phi] using hadd.symm
  have hphi_mono : StrictMono phi := by
    intro s t hst
    have hpos : 0 < ∫ r in s..t, w r :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        (hw_cont.intervalIntegrable s t) (fun r _ ↦ hw_pos r) hst
    rw [hphi_add s t]
    linarith
  have hphi_cont : Continuous phi :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hphi_strict t).hasDerivAt.continuousAt
  have hphi_inj : Function.Injective phi := hphi_mono.injective
  -- Construct the global inverse and obtain its derivative on the primitive's
  -- open range from the strict inverse-function theorem.
  let psi : ℝ → ℝ := Function.invFun phi
  have hleft : ∀ t, psi (phi t) = t :=
    Function.leftInverse_invFun hphi_inj
  let W : Set ℝ := Set.range phi
  have hphi_open : IsOpenMap phi :=
    isOpenMap_of_hasStrictDerivAt hphi_strict (fun t ↦ (hw_pos t).ne')
  have hpsi_deriv_local : ∀ t, HasDerivAt psi (w t)⁻¹ (phi t) := by
    intro t
    have hstrict : HasStrictDerivAt (Function.invFun phi) (w t)⁻¹ (phi t) :=
      (hphi_strict t).to_local_left_inverse (hw_pos t).ne'
        (Filter.Eventually.of_forall (Function.leftInverse_invFun hphi_inj))
    simpa only [psi] using hstrict.hasDerivAt
  have hW_open : IsOpen W := by
    simpa only [W] using hphi_open.isOpen_range
  have hright : ∀ s ∈ W, phi (psi s) = s := by
    rintro s ⟨t, rfl⟩
    rw [hleft t]
  have hpsi_hasDeriv : ∀ s ∈ W, HasDerivAt psi (w (psi s))⁻¹ s := by
    rintro s ⟨t, rfl⟩
    rw [hleft t]
    exact hpsi_deriv_local t
  have hpsi_diff : DifferentiableOn ℝ psi W := fun s hs ↦
    (hpsi_hasDeriv s hs).differentiableAt.differentiableWithinAt
  have hpsi_cont : ContinuousOn psi W := fun s hs ↦
    (hpsi_hasDeriv s hs).continuousAt.continuousWithinAt
  have hpsi_deriv_eq : EqOn (deriv psi) (fun s ↦ (w (psi s))⁻¹) W :=
    fun s hs ↦ (hpsi_hasDeriv s hs).deriv
  -- Upgrade the pointwise inverse derivative to `C¹` regularity on the open
  -- range before restricting to the compact endpoint interval.
  have hpsi_C1 : ContDiffOn ℝ 1 psi W := by
    rw [contDiffOn_one_iff_derivWithin hW_open.uniqueDiffOn]
    refine ⟨hpsi_diff, ?_⟩
    have hc : ContinuousOn (fun s ↦ (w (psi s))⁻¹) W :=
      (hw_cont.comp_continuousOn hpsi_cont).inv₀ fun s _ ↦ (hw_pos (psi s)).ne'
    refine hc.congr fun s hs ↦ ?_
    rw [derivWithin_of_isOpen hW_open hs, hpsi_deriv_eq hs]
  -- Identify the endpoint image, then package the inverse, monotonicity,
  -- endpoint, regularity, and derivative conclusions on `Icc 0 L`.
  let L : ℝ := ∫ t in a..b, v t
  have hphi_a : phi a = 0 := by
    simp only [phi, intervalIntegral.integral_same]
  have hphi_b : phi b = L := by
    simpa only [phi, L] using hintegral_eq b (right_mem_Icc.mpr hab.le)
  have hL_pos : 0 < L := by
    have hlt := hphi_mono hab
    rwa [hphi_a, hphi_b] at hlt
  have himage : phi '' Icc a b = Icc 0 L := by
    rw [hphi_cont.continuousOn.image_Icc_of_monotoneOn hab.le
      (hphi_mono.monotone.monotoneOn (Icc a b)), hphi_a, hphi_b]
  have hIccW : Icc 0 L ⊆ W := by
    rw [← himage]
    rintro _ ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩
  have hmaps : MapsTo psi (Icc 0 L) (Icc a b) := by
    intro s hs
    rw [← himage] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [hleft t]
    exact ht
  have hpsi_strict : StrictMonoOn psi (Icc 0 L) := by
    intro x hx y hy hxy
    rw [← himage] at hx hy
    obtain ⟨tx, _, rfl⟩ := hx
    obtain ⟨ty, _, rfl⟩ := hy
    rw [hleft tx, hleft ty]
    by_contra hnot
    exact (not_lt_of_ge (hphi_mono.monotone (le_of_not_gt hnot))) hxy
  have hpsi_zero : psi 0 = a := by
    rw [← hphi_a, hleft a]
  have hpsi_L : psi L = b := by
    rw [← hphi_b, hleft b]
  have hleft_Icc : ∀ t ∈ Icc a b, psi (∫ s in a..t, v s) = t := by
    intro t ht
    rw [← hintegral_eq t ht]
    simpa only [phi] using hleft t
  have hright_Icc : ∀ s ∈ Icc 0 L, ∫ t in a..psi s, v t = s := by
    intro s hs
    rw [← hintegral_eq (psi s) (hmaps hs)]
    simpa only [phi] using hright s (hIccW hs)
  refine ⟨L, psi, ?_, hL_pos, hmaps, hpsi_strict, hpsi_zero, hpsi_L,
    hleft_Icc, hright_Icc, hpsi_C1.mono hIccW, ?_⟩
  · simp only [L]
  · intro s hs
    simpa only [hw_eq (psi s) (hmaps hs)] using hpsi_hasDeriv s (hIccW hs)

end

end TauCeti
