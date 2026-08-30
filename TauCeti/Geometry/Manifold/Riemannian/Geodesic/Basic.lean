/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Existence

/-!
# Geodesics of a Riemannian manifold

A curve in a Riemannian manifold is a geodesic when its velocity is parallel along it: the
derivative of the velocity field along the curve, taken for the Levi-Civita connection of the
manifold's Riemannian bundle instance, vanishes.  This file introduces that predicate, carrying
the parameter set on which it is asserted, and identifies it with the classical second-order
geodesic ODE in a chart.

The derivative along the curve is the moving-chart candidate
`CovariantDerivative.alongCurveWithin`.  That candidate is identified with the ambient covariant
derivative for fields pulled back from an ambient vector field, by
`CovariantDerivative.alongCurveWithin_pullback`; the velocity field of a curve is not such a
pullback, so for it the identification — and with it the chart independence of the predicate —
remains open, exactly as the definition of the operator records.

The predicate is stated *within* a parameter set `s`, so that a geodesic segment on a closed
interval and an all-time geodesic are the same notion at two values of `s`; the all-time
predicate is the `s = Set.univ` case.  Both the velocity `TauCeti.Manifold.curveVelocityWithin`
and the along-curve derivative `CovariantDerivative.alongCurveWithin` are then read within `s`,
and the predicate carries `UniqueDiffOn ℝ s` — satisfied by the nondegenerate intervals and by
`Set.univ` which the theory uses — because that is the hypothesis under which a derivative within
`s` is determined by the curve.  Together with the `C²` regularity it is the hypothesis under
which the equation is intended to be read as one between honest derivatives; that the two of them
do make the chart reading of the curve twice differentiable within `s` is not yet formalized, so
the `derivWithin`s below may still carry the junk value `0`.

Reading the curve in the extended chart centred at the current point turns the definition into
the second-order equation

`u'' + Γ_{γ t} (u', u') = 0`,

where `u = extChartAt I (γ t) ∘ γ` and `Γ` is the model-space Christoffel map of the Levi-Civita
connection.  That is `TauCeti.Manifold.isGeodesicCurveOn_iff_chart`.  Chart-reading the curve at
its *current* point, rather than in one fixed chart, is what makes this a statement about the
whole parameter set at once.  The bridge lemmas doing the work,
`TauCeti.Manifold.sectionCoord_curveVelocityWithin_eventuallyEq` and
`CovariantDerivative.alongCurveWithin_curveVelocityWithin_eq_zero_iff`, hold for an arbitrary
connection and live with the rest of the along-curve API in
`TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/AlongCurve/Pullback.lean`.

## Main definitions and results

* `TauCeti.Manifold.IsGeodesicCurveOn`: the geodesic equation on a parameter set, and
  `TauCeti.Manifold.IsGeodesicCurve` its all-time case, related by
  `TauCeti.Manifold.isGeodesicCurveOn_univ` and unfolded by
  `TauCeti.Manifold.isGeodesicCurve_iff`.
* `TauCeti.Manifold.IsGeodesicCurveOnFrom`: a geodesic together with its initial data, the point
  and velocity at parameter `0`, read off by `TauCeti.Manifold.IsGeodesicCurveOnFrom.base_eq` and
  `TauCeti.Manifold.IsGeodesicCurveOnFrom.velocity_eq`.
* `TauCeti.Manifold.isGeodesicCurveOn_iff_chart`: **the geodesic equation in a chart**, the
  second-order ODE `u'' + Γ (u', u') = 0`.
* `TauCeti.Manifold.isGeodesicCurveOn_iff_of_isOpen`: on an open parameter set the equation is
  the unrestricted one.
* `TauCeti.Manifold.isGeodesicCurveOn_const`: a constant curve is a geodesic.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "`IsGeodesicCurveOn γ s`" and "Initial data".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle CovariantDerivative Set
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-! ### The geodesic equation -/

variable (I γ s) in
/-- **A geodesic on a parameter set**: a `C²` curve whose velocity within `s` is annihilated by
the moving-chart candidate for the derivative along the curve, taken for the Levi-Civita
connection of the ambient Riemannian bundle instance.

The velocity is `TauCeti.Manifold.curveVelocityWithin` and the candidate for its derivative along
the curve is `CovariantDerivative.alongCurveWithin`, both taken within `s`.  The candidate is
identified with the ambient covariant derivative only for pulled-back fields, which the velocity
field is not. -/
structure IsGeodesicCurveOn : Prop where
  /-- The parameter set has unique derivatives.  Without this the derivatives within `s` are not
  determined by the curve, and the geodesic equation below does not say what it should. -/
  uniqueDiffOn : UniqueDiffOn ℝ s
  /-- A geodesic is `C²` on its parameter set: this is the regularity under which the geodesic
  equation is intended to be an equation between honest derivatives.  That it does make the chart
  reading of the curve twice differentiable within `s` is not yet formalized, so the equation may
  still read the junk values of `CovariantDerivative.alongCurveInChartWithin`. -/
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s
  /-- **The geodesic equation**: the along-curve candidate annihilates the velocity field at every
  parameter of `s`. -/
  alongCurveWithin_curveVelocityWithin_eq_zero : ∀ r ∈ s,
    alongCurveWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s r = 0

variable (I γ) in
/-- **A geodesic**, defined at every real parameter.  This is the `s = Set.univ` case of
`TauCeti.Manifold.IsGeodesicCurveOn`. -/
def IsGeodesicCurve : Prop := IsGeodesicCurveOn I γ univ

/-- Asserting the geodesic equation on the whole parameter space gives the all-time predicate. -/
theorem isGeodesicCurveOn_univ : IsGeodesicCurveOn I γ univ ↔ IsGeodesicCurve I γ := Iff.rfl

/-- A geodesic is differentiable on its parameter set. -/
theorem IsGeodesicCurveOn.mdifferentiableOn (h : IsGeodesicCurveOn I γ s) :
    MDifferentiableOn 𝓘(ℝ, ℝ) I γ s :=
  h.contMDiffOn.mdifferentiableOn (by norm_num)

/-- A geodesic is continuous on its parameter set. -/
theorem IsGeodesicCurveOn.continuousOn (h : IsGeodesicCurveOn I γ s) : ContinuousOn γ s :=
  h.contMDiffOn.continuousOn

variable (I γ s) in
/-- **A geodesic with prescribed initial data**: a geodesic on a parameter set containing `0`
which starts at `p` with velocity `v`.  The two pieces of initial data are packaged as a single
equality of points of the tangent bundle, which avoids transporting `v` along `γ 0 = p` and is
the form in which the geodesic flow on `TM` will consume them. -/
structure IsGeodesicCurveOnFrom (p : M) (v : TangentSpace I p) : Prop where
  /-- The curve is a geodesic on `s`. -/
  isGeodesicCurveOn : IsGeodesicCurveOn I γ s
  /-- The initial parameter belongs to the parameter set. -/
  zero_mem : (0 : ℝ) ∈ s
  /-- The curve leaves `p` with velocity `v`. -/
  initial_eq :
    TotalSpace.mk' E (γ 0) (curveVelocityWithin I γ s 0) = TotalSpace.mk' E p v

variable {p : M} {v : TangentSpace I p}

/-- A geodesic with initial data starts at the prescribed point. -/
theorem IsGeodesicCurveOnFrom.base_eq (h : IsGeodesicCurveOnFrom I γ s p v) : γ 0 = p :=
  congrArg TotalSpace.proj h.initial_eq

/-- A geodesic with initial data leaves with the prescribed velocity.  The equality is
heterogeneous because the two sides live in the tangent spaces at `γ 0` and at `p`. -/
theorem IsGeodesicCurveOnFrom.velocity_heq (h : IsGeodesicCurveOnFrom I γ s p v) :
    HEq (curveVelocityWithin I γ s 0) v :=
  (TotalSpace.ext_iff.mp h.initial_eq).2

/-- A geodesic with initial data leaves with the prescribed velocity, transported to
`TangentSpace I p` along `TauCeti.Manifold.IsGeodesicCurveOnFrom.base_eq`. -/
theorem IsGeodesicCurveOnFrom.velocity_eq (h : IsGeodesicCurveOnFrom I γ s p v) :
    cast (congrArg (TangentSpace I) h.base_eq) (curveVelocityWithin I γ s 0) = v :=
  eq_of_heq ((cast_heq _ _).trans h.velocity_heq)

/-- A geodesic on a parameter set containing `0` is a geodesic with the initial data it has
there. -/
theorem IsGeodesicCurveOn.isGeodesicCurveOnFrom (h : IsGeodesicCurveOn I γ s) (h0 : (0 : ℝ) ∈ s) :
    IsGeodesicCurveOnFrom I γ s (γ 0) (curveVelocityWithin I γ s 0) :=
  ⟨h, h0, rfl⟩

/-! ### The geodesic equation in a chart -/

/-- **The geodesic equation in a chart.**  A `C²` curve is a geodesic on a parameter set with
unique derivatives exactly when, at every parameter of that set, the curve read in the extended
chart centred at the *current* point solves `u'' + Γ (u', u') = 0`, with `Γ` the model-space
Christoffel map of the Levi-Civita connection in the tangent-bundle trivialization there. -/
theorem isGeodesicCurveOn_iff_chart (hs : UniqueDiffOn ℝ s) :
    IsGeodesicCurveOn I γ s ↔ ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s ∧ ∀ r ∈ s,
      derivWithin (derivWithin (extChartAt I (γ r) ∘ γ) s) s r +
        christoffelMap (Module.finBasis ℝ E)
          ((leviCivita I M).isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) (γ r)).baseSet)) (γ r)
          (derivWithin (extChartAt I (γ r) ∘ γ) s r)
          (derivWithin (extChartAt I (γ r) ∘ γ) s r) = 0 := by
  constructor
  · intro h
    exact ⟨h.contMDiffOn, fun r hr ↦ (alongCurveWithin_curveVelocityWithin_eq_zero_iff
      (leviCivita I M) γ h.uniqueDiffOn h.mdifferentiableOn hr).mp
      (h.alongCurveWithin_curveVelocityWithin_eq_zero r hr)⟩
  · rintro ⟨hc, hchart⟩
    exact ⟨hs, hc, fun r hr ↦ (alongCurveWithin_curveVelocityWithin_eq_zero_iff (leviCivita I M) γ
      hs (hc.mdifferentiableOn (by norm_num)) hr).mpr (hchart r hr)⟩

/-! ### Open parameter sets -/

/-- On an open parameter set, the geodesic equation is the unrestricted one. -/
theorem isGeodesicCurveOn_iff_of_isOpen (hs : IsOpen s) :
    IsGeodesicCurveOn I γ s ↔ ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s ∧
      ∀ r ∈ s, alongCurve (leviCivita I M) γ (curveVelocity I γ) r = 0 := by
  constructor
  · intro h
    exact ⟨h.contMDiffOn, fun r hr ↦ by
      rw [← alongCurveWithin_curveVelocityWithin_of_isOpen (leviCivita I M) γ hs hr]
      exact h.alongCurveWithin_curveVelocityWithin_eq_zero r hr⟩
  · rintro ⟨hc, hzero⟩
    exact ⟨hs.uniqueDiffOn, hc, fun r hr ↦ by
      rw [alongCurveWithin_curveVelocityWithin_of_isOpen (leviCivita I M) γ hs hr]
      exact hzero r hr⟩

/-- The all-time geodesic equation, spelled out. -/
theorem isGeodesicCurve_iff :
    IsGeodesicCurve I γ ↔ ContMDiff 𝓘(ℝ, ℝ) I 2 γ ∧
      ∀ t : ℝ, alongCurve (leviCivita I M) γ (curveVelocity I γ) t = 0 := by
  rw [← isGeodesicCurveOn_univ, isGeodesicCurveOn_iff_of_isOpen isOpen_univ, contMDiffOn_univ]
  simp

/-! ### Constant curves -/

/-- **A constant curve is a geodesic.**  Its velocity field is the zero section, which the
along-curve candidate annihilates. -/
theorem isGeodesicCurveOn_const (hs : UniqueDiffOn ℝ s) (x : M) :
    IsGeodesicCurveOn I (fun _ : ℝ ↦ x) s where
  uniqueDiffOn := hs
  contMDiffOn := contMDiffOn_const
  alongCurveWithin_curveVelocityWithin_eq_zero r _ := by
    have hzero : curveVelocityWithin I (fun _ : ℝ ↦ x) s =
        fun r : ℝ ↦ (0 : TangentSpace I ((fun _ : ℝ ↦ x) r)) :=
      funext fun _ ↦ curveVelocityWithin_const x
    rw [hzero, alongCurveWithin_zero]

/-- A constant curve is an all-time geodesic. -/
theorem isGeodesicCurve_const (x : M) : IsGeodesicCurve I (fun _ : ℝ ↦ x) :=
  isGeodesicCurveOn_const uniqueDiffOn_univ x

end TauCeti.Manifold

end
