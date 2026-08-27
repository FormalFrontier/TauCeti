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
covariant derivative of the velocity field along the curve, taken for the Levi-Civita connection
of the manifold's Riemannian bundle instance, vanishes.  This file introduces that predicate,
carrying the parameter set on which it is asserted, and identifies it with the classical
second-order geodesic ODE in a chart.

The predicate is stated *within* a parameter set `s`, so that a geodesic segment on a closed
interval and an all-time geodesic are the same notion at two values of `s`; the all-time
predicate is the `s = Set.univ` case.  Both the velocity `TauCeti.Manifold.curveVelocityWithin`
and the along-curve derivative `CovariantDerivative.alongCurveWithin` are then read within `s`,
and the predicate carries `UniqueDiffOn ℝ s` — satisfied by the nondegenerate intervals and by
`Set.univ` which the theory uses — because that is what makes those within-derivatives the
honest ones rather than junk values.

Reading the curve in the extended chart centred at the current point turns the definition into
the second-order equation

`u'' + Γ_{γ t} (u', u') = 0`,

where `u = extChartAt I (γ t) ∘ γ` and `Γ` is the model-space Christoffel map of the Levi-Civita
connection.  That is `TauCeti.Manifold.isGeodesicCurveOn_iff_chart`.  Chart-reading the curve at
its *current* point, rather than in one fixed chart, is what makes this a statement about the
whole parameter set at once.

## Main definitions and results

* `TauCeti.Manifold.IsGeodesicCurveOn`: the geodesic equation on a parameter set, and
  `TauCeti.Manifold.IsGeodesicCurve` its all-time case, unfolded by
  `TauCeti.Manifold.isGeodesicCurve_iff`.
* `TauCeti.Manifold.IsGeodesicCurveOnFrom`: a geodesic together with its initial data, the point
  and velocity at parameter `0`.
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

open Bundle CovariantDerivative Filter Set
open scoped Manifold Topology

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
/-- **A geodesic on a parameter set**: a `C²` curve whose velocity within `s` is parallel along
it for the Levi-Civita connection of the ambient Riemannian bundle instance.

The velocity is `TauCeti.Manifold.curveVelocityWithin` and its derivative along the curve is
`CovariantDerivative.alongCurveWithin`, both taken within `s`. -/
structure IsGeodesicCurveOn : Prop where
  /-- The parameter set has unique derivatives.  Without this the derivatives within `s` are not
  determined by the curve, and the geodesic equation below does not say what it should. -/
  uniqueDiffOn : UniqueDiffOn ℝ s
  /-- A geodesic is `C²` on its parameter set: this is what makes its velocity field
  differentiable, so that the geodesic equation is an equation between honest derivatives. -/
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s
  /-- **The geodesic equation**: the velocity field is parallel along the curve. -/
  alongCurveWithin_curveVelocityWithin_eq_zero : ∀ r ∈ s,
    alongCurveWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s r = 0

variable (I γ) in
/-- **A geodesic**, defined at every real parameter.  This is the `s = Set.univ` case of
`TauCeti.Manifold.IsGeodesicCurveOn`. -/
def IsGeodesicCurve : Prop := IsGeodesicCurveOn I γ univ

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

/-! ### The geodesic equation in a chart -/

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- Along a curve differentiable within `s`, the coordinate reading of the velocity field in the
tangent-bundle trivialization centred at `x` is the derivative within `s` of the curve read in the
extended chart at `x`, at every nearby parameter of `s` at which the curve is still in that
chart. -/
theorem sectionCoord_curveVelocityWithin_eventuallyEq {x : M} (hs : UniqueDiffOn ℝ s)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s) (ht : t ∈ s)
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    sectionCoord (F := E) γ (curveVelocityWithin I γ s) x =ᶠ[𝓝[s] t]
      derivWithin (extChartAt I x ∘ γ) s := by
  have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    (hγ t ht).continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx)
  filter_upwards [hbase, self_mem_nhdsWithin] with r hr hrs
  rw [sectionCoord_apply, derivWithin_extChartAt_comp γ hr (hs r hrs)
    (hasMFDerivWithinAt_curveVelocityWithin (hγ r hrs))]

/-- The moving-chart coordinate formula applied to the velocity field is the classical
second-order expression `u'' + Γ (u', u')`, for `u` the curve read in the extended chart at `x`.
The chart need not be the one centred at the current point of the curve. -/
theorem alongCurveInChartWithin_curveVelocityWithin {x : M} (hs : UniqueDiffOn ℝ s)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s) (ht : t ∈ s)
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    alongCurveInChartWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s x t =
      derivWithin (derivWithin (extChartAt I x ∘ γ) s) s t +
        christoffelMap (Module.finBasis ℝ E)
          ((leviCivita I M).isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) x).baseSet)) (γ t)
          (derivWithin (extChartAt I x ∘ γ) s t) (derivWithin (extChartAt I x ∘ γ) s t) := by
  have hEq := sectionCoord_curveVelocityWithin_eventuallyEq hs hγ ht hx
  have hpoint : sectionCoord (F := E) γ (curveVelocityWithin I γ s) x t =
      derivWithin (extChartAt I x ∘ γ) s t := hEq.self_of_nhdsWithin ht
  rw [alongCurveInChartWithin_apply, hEq.derivWithin_eq hpoint, hpoint]

/-- The along-curve derivative of the velocity field vanishes exactly when the curve read in the
extended chart at the current point solves the second-order geodesic ODE there.  The moving-chart
formula is transported by a fibrewise linear equivalence, so vanishing may be tested in the
chart. -/
theorem alongCurveWithin_curveVelocityWithin_eq_zero_iff (hs : UniqueDiffOn ℝ s)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s) (ht : t ∈ s) :
    alongCurveWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s t = 0 ↔
      derivWithin (derivWithin (extChartAt I (γ t) ∘ γ) s) s t +
        christoffelMap (Module.finBasis ℝ E)
          ((leviCivita I M).isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
          (derivWithin (extChartAt I (γ t) ∘ γ) s t)
          (derivWithin (extChartAt I (γ t) ∘ γ) s t) = 0 := by
  set e := trivializationAt E (TangentSpace I) (γ t)
  have hmem : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  rw [alongCurveWithin_apply, alongCurveInChartWithin_curveVelocityWithin hs hγ ht hmem]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  have h' := congrArg (e.continuousLinearMapAt ℝ (γ t)) h
  rwa [e.continuousLinearMapAt_symmL (R := ℝ) hmem, map_zero] at h'

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
      h.uniqueDiffOn h.mdifferentiableOn hr).mp
      (h.alongCurveWithin_curveVelocityWithin_eq_zero r hr)⟩
  · rintro ⟨hc, hchart⟩
    exact ⟨hs, hc, fun r hr ↦ (alongCurveWithin_curveVelocityWithin_eq_zero_iff hs
      (hc.mdifferentiableOn (by norm_num)) hr).mpr (hchart r hr)⟩

/-! ### Open parameter sets -/

/-- On an open parameter set, the restricted velocity field and the restricted along-curve
derivative are the unrestricted ones. -/
theorem alongCurveWithin_curveVelocityWithin_of_isOpen (hs : IsOpen s) (ht : t ∈ s) :
    alongCurveWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s t =
      alongCurve (leviCivita I M) γ (curveVelocity I γ) t := by
  have hcongr : ∀ᶠ r in 𝓝[s] t, curveVelocityWithin I γ s r = curveVelocity I γ r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact curveVelocityWithin_of_mem_nhds (hs.mem_nhds hr)
  rw [alongCurveWithin_congr (leviCivita I M) γ (curveVelocityWithin I γ s) hcongr
      (curveVelocityWithin_of_mem_nhds (hs.mem_nhds ht)),
    alongCurveWithin_of_mem_nhds (leviCivita I M) γ (curveVelocity I γ) (hs.mem_nhds ht)]

/-- On an open parameter set, the geodesic equation is the unrestricted one. -/
theorem isGeodesicCurveOn_iff_of_isOpen (hs : IsOpen s) :
    IsGeodesicCurveOn I γ s ↔ ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s ∧
      ∀ r ∈ s, alongCurve (leviCivita I M) γ (curveVelocity I γ) r = 0 := by
  constructor
  · intro h
    exact ⟨h.contMDiffOn, fun r hr ↦ by
      rw [← alongCurveWithin_curveVelocityWithin_of_isOpen hs hr]
      exact h.alongCurveWithin_curveVelocityWithin_eq_zero r hr⟩
  · rintro ⟨hc, hzero⟩
    exact ⟨hs.uniqueDiffOn, hc, fun r hr ↦ by
      rw [alongCurveWithin_curveVelocityWithin_of_isOpen hs hr]
      exact hzero r hr⟩

/-- The all-time geodesic equation, spelled out. -/
theorem isGeodesicCurve_iff :
    IsGeodesicCurve I γ ↔ ContMDiff 𝓘(ℝ, ℝ) I 2 γ ∧
      ∀ t : ℝ, alongCurve (leviCivita I M) γ (curveVelocity I γ) t = 0 := by
  rw [IsGeodesicCurve, isGeodesicCurveOn_iff_of_isOpen isOpen_univ, contMDiffOn_univ]
  simp

/-! ### Constant curves -/

/-- **A constant curve is a geodesic.**  Its velocity field is the zero section, which is
parallel. -/
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
