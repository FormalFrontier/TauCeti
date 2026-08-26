/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Differentiating along a curve in a manifold

A curve `γ : 𝕜 → M` in a manifold has a one-dimensional parameter, so a function on `M`
restricted along it has an honest `HasDerivWithinAt` derivative rather than only a manifold
differential.  Mathlib's composition lemmas for `mvfderiv` are stated for a manifold source, and
its `deriv` composition lemmas for a normed-space source, so neither directly produces that
derivative.  This file records the resulting chain rule, and the special case of reading the
curve in the extended chart centred at the current point, where the derivative is the velocity
itself.

Following Mathlib's `IsIntegralCurveOn`, the velocity `w : TangentSpace I (γ t)` is presented
through `HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)`, since
`TangentSpace 𝓘(𝕜, 𝕜) t` carries no `One` instance and `mfderivWithin ... 1` therefore does not
elaborate.

## Main results

* `TauCeti.Manifold.hasDerivWithinAt_comp_curve`: the chain rule
  `(g ∘ γ)' (t) = d g (γ t) (γ' t)` for a function `g` from the manifold to a normed space,
  with `TauCeti.Manifold.hasDerivAt_comp_curve` its unrestricted case.
* `TauCeti.Manifold.hasDerivWithinAt_extChartAt_comp_curve`: reading the curve in the chart
  centred at the current point differentiates it to the velocity itself, with
  `TauCeti.Manifold.hasDerivAt_extChartAt_comp_curve` its unrestricted case.
-/

public section

open scoped Manifold Topology

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {γ : 𝕜 → M} {s : Set 𝕜} {t : 𝕜} {w : TangentSpace I (γ t)}

/-- **The chain rule along a curve.** If `g` is a normed-space-valued function which is
differentiable at `γ t`, and the curve `γ` has velocity `w` at `t` within the parameter set `s`,
then `g ∘ γ` has derivative `d g (γ t) w` there.  The velocity is presented as in Mathlib's
integral-curve API, as the value of the manifold derivative on the unit tangent vector. -/
theorem hasDerivWithinAt_comp_curve {g : M → F} (hg : MDifferentiableAt I 𝓘(𝕜, F) g (γ t))
    (hγ : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)) :
    HasDerivWithinAt (g ∘ γ) (mvfderiv I g (γ t) w) s t := by
  -- Composing the two manifold derivatives gives a continuous linear map out of the tangent
  -- space to `𝕜` at `t`; rewriting it as a `smulRight` is what turns it into a `HasDerivWithinAt`.
  have hcomp : (mfderiv I 𝓘(𝕜, F) g (γ t)).comp ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)
      = (1 : 𝕜 →L[𝕜] 𝕜).smulRight (mfderiv I 𝓘(𝕜, F) g (γ t) w) :=
    ContinuousLinearMap.ext fun _ ↦ by simp
  have hmf : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) 𝓘(𝕜, F) (g ∘ γ) s t
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (mfderiv I 𝓘(𝕜, F) g (γ t) w)) :=
    (hg.hasMFDerivAt.comp_hasMFDerivWithinAt t hγ).congr_mfderiv hcomp
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  exact hmf.hasFDerivWithinAt

/-- The unrestricted case of `TauCeti.Manifold.hasDerivWithinAt_comp_curve`. -/
theorem hasDerivAt_comp_curve {g : M → F} (hg : MDifferentiableAt I 𝓘(𝕜, F) g (γ t))
    (hγ : HasMFDerivAt 𝓘(𝕜, 𝕜) I γ t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)) :
    HasDerivAt (g ∘ γ) (mvfderiv I g (γ t) w) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_comp_curve hg hγ.hasMFDerivWithinAt

variable [IsManifold I 1 M]

/-- Reading the curve in the extended chart centred at the *current* point differentiates it to
the velocity itself: the derivative of that chart at its own centre is the identity. -/
theorem hasDerivWithinAt_extChartAt_comp_curve
    (hγ : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)) :
    HasDerivWithinAt (extChartAt I (γ t) ∘ γ) w s t := by
  have h := hasDerivWithinAt_comp_curve
    (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (γ t))) hγ
  have hv : mvfderiv I (extChartAt I (γ t)) (γ t) w = w := by
    simp only [mvfderiv, mfderiv_extChartAt_self]
    rfl
  rwa [hv] at h

/-- The unrestricted case of `TauCeti.Manifold.hasDerivWithinAt_extChartAt_comp_curve`. -/
theorem hasDerivAt_extChartAt_comp_curve
    (hγ : HasMFDerivAt 𝓘(𝕜, 𝕜) I γ t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)) :
    HasDerivAt (extChartAt I (γ t) ∘ γ) w t :=
  hasDerivWithinAt_univ.mp (hasDerivWithinAt_extChartAt_comp_curve hγ.hasMFDerivWithinAt)

end TauCeti.Manifold
