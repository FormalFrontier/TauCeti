/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Topology.Homotopy.Path
import TauCeti.Analysis.Contour.NullHomologous
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Homotopy invariance of the winding number

The winding number of a closed path about `w` is invariant under a twice continuously
differentiable path homotopy through `ℂ \ {w}`. The proof represents the Cauchy kernel as the closed
complex-linear `1`-form `z ↦ (z - w)⁻¹ dz`, then applies Mathlib's Poincaré theorem for curve
integrals on the compact image of the homotopy.

## Main results

* `windingNumber_eq_two_pi_I_inv_mul_curveIntegral` identifies Tau Ceti's raw-function winding
  number of a piecewise-`C¹` path with Mathlib's curve integral of the Cauchy-kernel `1`-form.
* `isPiecewiseC1On_eval_of_smoothPathHomotopy` supplies piecewise-`C¹` regularity for every path
  in a smooth homotopy.
* `windingNumber_eq_of_pathHomotopy` proves the Layer 0 homotopy invariance result.
* `isNullHomologous_iff_of_pathHomotopy` transfers null-homology across a homotopy in the ambient
  set.

## Provenance

The homotopy step reuses Mathlib's
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`; no formal source
is vendored. Homotopy invariance of the classical winding number is standard complex analysis; see
the references in the Contour Integration roadmap.
-/

public section

noncomputable section

open scoped unitInterval
open MeasureTheory Set

namespace TauCeti.Contour

private def indexForm (w : ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z => (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ

private def indexFormDeriv (w z : ℂ) : ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  ((1 : ℂ →L[ℂ] ℂ).smulRight (-((z - w) ^ 2)⁻¹) |>.smulRight
    (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ

private theorem hasFDerivAt_indexForm {w z : ℂ} (hzw : z ≠ w) :
    HasFDerivAt (indexForm w) (indexFormDeriv w z) z := by
  have hscalar : HasDerivAt (fun y : ℂ => (y - w)⁻¹) (-((z - w) ^ 2)⁻¹) z := by
    convert ((hasDerivAt_id z).sub_const w).inv (sub_ne_zero.mpr hzw) using 1
    · rfl
    · rfl
    · rfl
    · simp [div_eq_mul_inv]
  exact (hscalar.hasFDerivAt.smul_const (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ

private theorem indexFormDeriv_apply_comm (w z u v : ℂ) :
    indexFormDeriv w z u v = indexFormDeriv w z v u := by
  have happly (x y : ℂ) : indexFormDeriv w z x y = x * (-((z - w) ^ 2)⁻¹) * y := by
    simp [indexFormDeriv, mul_assoc]
  rw [happly, happly]
  ring

/-- For a piecewise-`C¹` path avoiding `w`, its winding number about `w` is the normalized curve
integral of the closed `1`-form `z ↦ (z - w)⁻¹ dz`. This is the bridge from Tau Ceti's raw-function
winding number to Mathlib's path-based curve integral. -/
theorem windingNumber_eq_two_pi_I_inv_mul_curveIntegral {x y w : ℂ} {p : Path x y}
    (hp : IsPiecewiseC1On p.extend 0 1) (havoid : ∀ t : Set.Icc (0 : ℝ) 1, p t ≠ w) :
    windingNumber p.extend 0 1 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ᶜ z in p, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
  have havoid_extend : ∀ t ∈ Set.uIcc (0 : ℝ) 1, p.extend t ≠ w := by
    rw [Set.uIcc_of_le zero_le_one]
    intro t ht
    rw [Path.extend_apply p ht]
    exact havoid ⟨t, ht⟩
  rw [windingNumber_eq_integral_of_avoidance hp.continuousOn havoid_extend
      (intervalIntegrable_inv_sub_mul_deriv hp.continuousOn havoid_extend
        hp.intervalIntegrable_deriv),
    curveIntegral_eq_intervalIntegral_deriv]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- If the extension of a path homotopy is `C²` on the unit square, then every intermediate
path, extended constantly from the unit interval to `ℝ`, is piecewise `C¹` on `[0, 1]`. -/
theorem isPiecewiseC1On_eval_of_smoothPathHomotopy {x y : ℂ} {p q : Path x y} (φ : p.Homotopy q)
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2) (Set.Icc 0 1))
    (s : I) :
    IsPiecewiseC1On (φ.eval s).extend 0 1 := by
  apply IsPiecewiseC1On.of_contDiffOn
  rw [Set.uIcc_of_le zero_le_one]
  have hs : ContDiffOn ℝ 1
      ((fun st : ℝ × ℝ ↦
        Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2) ∘
        fun t : ℝ => ((s, t) : ℝ × ℝ)) (Set.Icc 0 1) :=
    (hφsmooth.of_le (by norm_num)).comp (by fun_prop)
      (fun t ht => by
        simpa [Prod.le_def] using ⟨⟨s.2.1, ht.1⟩, ⟨s.2.2, ht.2⟩⟩)
  exact hs.congr fun _ _ => by simp [Path.extend, Path.Homotopy.eval]

/-- **Homotopy invariance of the winding number off the curve.** Two closed paths joined through
`ℂ \ {w}` by a path homotopy whose extension to the unit square is `C²` have the same winding number
about `w`. -/
theorem windingNumber_eq_of_pathHomotopy {x w : ℂ} {p q : Path x x} (φ : p.Homotopy q)
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2) (Set.Icc 0 1))
    (havoid : ∀ st : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, φ st ≠ w) :
    windingNumber p.extend 0 1 w = windingNumber q.extend 0 1 w := by
  have hrange : IsClosed (Set.range φ) :=
    (isCompact_range φ.toHomotopy.continuous).isClosed
  have haway {z : ℂ} (hz : z ∈ Set.range φ) : z ≠ w := by
    obtain ⟨st, rfl⟩ := hz
    exact havoid st
  have hclosedForm : ∀ z ∈ Set.range φ,
      HasFDerivWithinAt (indexForm w) (indexFormDeriv w z) (Set.range φ) z :=
    fun z hz ↦ (hasFDerivAt_indexForm (haway hz)).hasFDerivWithinAt
  have hcontinuousForm : ContinuousOn (indexForm w) (closure (Set.range φ)) := by
    rw [hrange.closure_eq]
    exact fun z hz ↦ (hasFDerivAt_indexForm (haway hz)).continuousAt.continuousWithinAt
  have hboundary :=
    φ.toHomotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
      (t := Set.range φ) (ω := indexForm w) (dω := indexFormDeriv w)
      (fun s _ t _ ↦ Set.mem_range_self (s, t)) hclosedForm hcontinuousForm
      (fun z _ u _ v _ ↦ indexFormDeriv_apply_comm w z u v) hφsmooth
  have heval_zero :
      φ.toHomotopy.evalAt 0 = (Path.refl x).cast p.source q.source := by
    ext t
    exact φ.source t
  have heval_one :
      φ.toHomotopy.evalAt 1 = (Path.refl x).cast p.target q.target := by
    ext t
    exact φ.target t
  rw [heval_zero, heval_one] at hboundary
  have hcurve : (∫ᶜ z in p, indexForm w z) = ∫ᶜ z in q, indexForm w z := by
    simpa only [curveIntegral_cast, curveIntegral_refl, add_zero] using hboundary
  have hcurve' :
      (∫ᶜ z in p, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ) =
        ∫ᶜ z in q, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
    simpa only [indexForm] using hcurve
  have hp : IsPiecewiseC1On p.extend 0 1 := by
    simpa using isPiecewiseC1On_eval_of_smoothPathHomotopy φ hφsmooth (0 : I)
  have hq : IsPiecewiseC1On q.extend 0 1 := by
    simpa using isPiecewiseC1On_eval_of_smoothPathHomotopy φ hφsmooth (1 : I)
  rw [windingNumber_eq_two_pi_I_inv_mul_curveIntegral
      hp
      (fun t ↦ haway ⟨(0, t), by simp⟩),
    windingNumber_eq_two_pi_I_inv_mul_curveIntegral
      hq
      (fun t ↦ haway ⟨(1, t), by simp⟩),
    hcurve']

/-- Null-homology in `Ω` is invariant under a `C²` path homotopy whose image lies in `Ω`. -/
theorem isNullHomologous_iff_of_pathHomotopy {x : ℂ} {p q : Path x x} {Ω : Set ℂ} (φ : p.Homotopy q)
    (hφsmooth : ContDiffOn ℝ 2
      (fun st : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend st.1) st.2) (Set.Icc 0 1))
    (hφΩ : ∀ st : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1, φ st ∈ Ω) :
    IsNullHomologous p.extend 0 1 Ω ↔ IsNullHomologous q.extend 0 1 Ω := by
  constructor
  · intro h
    exact h.congr_windingNumber fun z hz ↦
      (windingNumber_eq_of_pathHomotopy φ hφsmooth
        (fun st (hst : φ st = z) ↦ hz (hst ▸ hφΩ st))).symm
  · intro h
    exact h.congr_windingNumber fun z hz ↦
      windingNumber_eq_of_pathHomotopy φ hφsmooth
        (fun st (hst : φ st = z) ↦ hz (hst ▸ hφΩ st))

end TauCeti.Contour

end
