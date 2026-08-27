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

The velocity itself is named here: `TauCeti.Manifold.curveVelocityWithin` reads the derivative
within a parameter set on the unit tangent vector, so that a statement about the velocity of a
curve need not carry a `HasMFDerivWithinAt` witness for it.

## Main definitions and results

* `TauCeti.Manifold.hasDerivWithinAt_comp_curve`: the chain rule
  `(g ∘ γ)' (t) = d g (γ t) (γ' t)` for a function `g` from the manifold to a normed space,
  with `TauCeti.Manifold.hasDerivAt_comp_curve` its unrestricted case.
* `TauCeti.Manifold.curveVelocityWithin` and `TauCeti.Manifold.curveVelocity`: the velocity of a
  curve within a parameter set and its unrestricted case, computed by
  `TauCeti.Manifold.curveVelocityWithin_apply` and `TauCeti.Manifold.curveVelocity_apply` and
  related by `TauCeti.Manifold.curveVelocityWithin_univ`.
* `TauCeti.Manifold.hasMFDerivWithinAt_curveVelocityWithin` and
  `TauCeti.Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt`: the two directions relating the
  named velocity to a `HasMFDerivWithinAt` witness.
* `TauCeti.Manifold.hasDerivWithinAt_extChartAt_comp_curve`: reading the curve in the chart
  centred at the current point differentiates it to the velocity itself, with
  `TauCeti.Manifold.hasDerivAt_extChartAt_comp_curve` its unrestricted case and
  `TauCeti.Manifold.derivWithin_extChartAt_comp_curve` its form for the named velocity.
-/

public section

open scoped Manifold Topology

noncomputable section

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

/-! ### The velocity of a curve -/

variable (I) in
/-- The velocity of the curve `γ` at the parameter `t`, taken within the parameter set `s`: the
value at the unit tangent vector of the manifold derivative of `γ` within `s`.  Where `γ` is not
differentiable within `s` at `t`, this carries Mathlib's junk value `0`; where the derivative
within `s` is not unique it need not be the velocity of any parametrization. -/
def curveVelocityWithin (γ : 𝕜 → M) (s : Set 𝕜) (t : 𝕜) : TangentSpace I (γ t) :=
  mfderivWithin 𝓘(𝕜, 𝕜) I γ s t (1 : 𝕜)

variable (I) in
/-- The velocity of the curve `γ` at the parameter `t`, with unrestricted derivative.  This is the
`s = Set.univ` case of `TauCeti.Manifold.curveVelocityWithin`. -/
def curveVelocity (γ : 𝕜 → M) (t : 𝕜) : TangentSpace I (γ t) :=
  curveVelocityWithin I γ Set.univ t

@[simp]
theorem curveVelocityWithin_univ : curveVelocityWithin I γ Set.univ = curveVelocity I γ :=
  (rfl)

/-- The velocity within `s` is the derivative within `s` evaluated at the unit tangent vector.
This restates the definition, whose body is not exposed across the module boundary. -/
theorem curveVelocityWithin_apply :
    curveVelocityWithin I γ s t = mfderivWithin 𝓘(𝕜, 𝕜) I γ s t (1 : 𝕜) :=
  (rfl)

/-- The unrestricted velocity is the unrestricted derivative evaluated at the unit tangent
vector. -/
theorem curveVelocity_apply : curveVelocity I γ t = mfderiv 𝓘(𝕜, 𝕜) I γ t (1 : 𝕜) := by
  rw [← curveVelocityWithin_univ, curveVelocityWithin_apply, mfderivWithin_univ]

/-- Evaluating the `smulRight` presentation of a velocity at the unit tangent vector returns that
velocity.  The tangent space of the scalar model is definitionally `𝕜`, but its instances block
rewriting by `ContinuousLinearMap.smulRight_apply` until that identification is exposed, which is
what the `change` below does. -/
private theorem smulRight_one_apply_one {x : M} (v : TangentSpace I x) :
    ((1 : 𝕜 →L[𝕜] 𝕜).smulRight v) (1 : 𝕜) = v := by
  change (1 : 𝕜) • v = v
  rw [one_smul]

/-- A continuous linear map out of the scalar model is determined by its value at `1`; this is the
shape in which Mathlib's integral-curve API presents the velocity of a curve. -/
private theorem mfderivWithin_eq_smulRight_curveVelocityWithin (γ : 𝕜 → M) (s : Set 𝕜) (t : 𝕜) :
    mfderivWithin 𝓘(𝕜, 𝕜) I γ s t = (1 : 𝕜 →L[𝕜] 𝕜).smulRight (curveVelocityWithin I γ s t) :=
  -- Reducing to the value at `1` needs `TangentSpace 𝓘(𝕜, 𝕜) t` to unfold to `𝕜`.
  ContinuousLinearMap.ext_ring (smulRight_one_apply_one _).symm

/-- A curve differentiable within `s` at `t` has `TauCeti.Manifold.curveVelocityWithin` as its
velocity there. -/
theorem hasMFDerivWithinAt_curveVelocityWithin (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t) :
    HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (curveVelocityWithin I γ s t)) :=
  hγ.hasMFDerivWithinAt.congr_mfderiv (mfderivWithin_eq_smulRight_curveVelocityWithin γ s t)

/-- The unrestricted case of `TauCeti.Manifold.hasMFDerivWithinAt_curveVelocityWithin`. -/
theorem hasMFDerivAt_curveVelocity (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t) :
    HasMFDerivAt 𝓘(𝕜, 𝕜) I γ t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (curveVelocity I γ t)) :=
  hasMFDerivWithinAt_univ.mp (hasMFDerivWithinAt_curveVelocityWithin hγ.mdifferentiableWithinAt)

/-- A velocity witnessed by a `HasMFDerivWithinAt` statement is *the* velocity, as soon as the
derivative within the parameter set is unique. -/
theorem curveVelocityWithin_eq_of_hasMFDerivWithinAt
    (hγ : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w))
    (hs : UniqueDiffWithinAt 𝕜 s t) : curveVelocityWithin I γ s t = w := by
  rw [curveVelocityWithin_apply,
    hγ.mfderivWithin (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr hs)]
  exact smulRight_one_apply_one w

/-- On a parameter set which is a neighbourhood of `t`, the restricted velocity is the
unrestricted one. -/
theorem curveVelocityWithin_of_mem_nhds (hs : s ∈ 𝓝 t) :
    curveVelocityWithin I γ s t = curveVelocity I γ t := by
  rw [curveVelocityWithin_apply, curveVelocity_apply, mfderivWithin_of_mem_nhds hs]

/-- A constant curve has zero velocity within any parameter set. -/
@[simp]
theorem curveVelocityWithin_const (x : M) : curveVelocityWithin I (fun _ : 𝕜 ↦ x) s t = 0 := by
  rw [curveVelocityWithin_apply, mfderivWithin_const]
  exact zero_apply _

/-- A constant curve has zero velocity.  This is the unrestricted case of
`TauCeti.Manifold.curveVelocityWithin_const`, which `TauCeti.Manifold.curveVelocityWithin_univ`
would otherwise keep `simp` from reaching. -/
@[simp]
theorem curveVelocity_const (x : M) : curveVelocity I (fun _ : 𝕜 ↦ x) t = 0 := by
  rw [← curveVelocityWithin_univ, curveVelocityWithin_const]

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


/-- The derivative within `s` of a differentiable curve read in the chart centred at the current
point is its velocity within `s`. -/
theorem derivWithin_extChartAt_comp_curve (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hs : UniqueDiffWithinAt 𝕜 s t) :
    derivWithin (extChartAt I (γ t) ∘ γ) s t = curveVelocityWithin I γ s t :=
  (hasDerivWithinAt_extChartAt_comp_curve
    (hasMFDerivWithinAt_curveVelocityWithin hγ)).derivWithin hs

end TauCeti.Manifold

end
