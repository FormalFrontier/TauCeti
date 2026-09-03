/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# The geodesic spray

The geodesic equation `u'' + Γ (u', u') = 0` is a second-order equation on the manifold; as usual
it becomes a first-order equation on the tangent bundle, for the vector field

`S (x, v) = (v, -Γ_x (v, v))`

on `TM` called the **geodesic spray**.  This file constructs `S` for the Levi-Civita connection of
the ambient Riemannian bundle instance and identifies its integral curves with the velocity lifts
of geodesics.

A vector field on a manifold assigns to a point a vector of the model space, read in the chart at
that point; the tangent-bundle chart at `z = (x, v)` reads the base direction in the extended
chart of `M` at `x` and the fibre direction in the tangent-bundle trivialization at `x`, over
which `v` is its own coordinate.  So the displayed formula *is* the definition of
`TauCeti.Manifold.geodesicSpray`, with `Γ` the model-space Christoffel map
`TauCeti.Manifold.christoffelMap` of the Levi-Civita connection in the trivialization at the base
point of the argument — the same moving-chart convention as
`CovariantDerivative.alongCurveWithin` and `TauCeti.Manifold.IsGeodesicCurveOn`.  What has to be
proved is that this formula solves the intended problem, and that is the content of
`TauCeti.Manifold.isMIntegralCurveOn_curveVelocityLiftWithin_iff` and
`TauCeti.Manifold.eq_curveVelocityLiftWithin_of_isMIntegralCurveOn`: on a parameter set with
unique derivatives, the integral curves of `S` are exactly the velocity lifts

`t ↦ (γ t, γ' t) : ℝ → TM`

of the geodesics of `M`.  The two statements are read in one direction each: the velocity lift of
a `C²` curve is an integral curve of `S` exactly when the curve is a geodesic, and conversely
every integral curve of `S` is the velocity lift of the curve it lies over, whose base curve is a
geodesic as soon as it is `C²`.  The `C²` hypothesis on the base curve is not yet removable: it
would follow from smoothness of `S`, which is the next step of the roadmap and is not proved here.

The unpacking of a curve into `TM` into its base curve and its fibre coordinate is
`TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff`, proved for an arbitrary fibre bundle.

## Main definitions and results

* `TauCeti.Manifold.geodesicSpray`: **the geodesic spray** of the ambient Riemannian bundle
  instance, a vector field on the tangent bundle, with `TauCeti.Manifold.geodesicSpray_apply` its
  chart formula and `TauCeti.Manifold.isMIntegralCurveOn_curveVelocityLiftWithin_const` the
  constant-curve check.
* `TauCeti.Manifold.curveVelocityLiftWithin` and `TauCeti.Manifold.curveVelocityLift`: the
  velocity lift of a curve to the tangent bundle, within a parameter set and unrestricted.
* `TauCeti.Manifold.hasMFDerivWithinAt_curveVelocityLiftWithin_iff`: at one parameter, the
  velocity lift of a `C²` curve solves the spray equation exactly when the covariant derivative of
  the velocity along the curve vanishes.
* `TauCeti.Manifold.isMIntegralCurveOn_curveVelocityLiftWithin_iff`: **the velocity lift of a `C²`
  curve is an integral curve of the geodesic spray exactly when the curve is a geodesic**, with
  `TauCeti.Manifold.isMIntegralCurve_curveVelocityLift_iff` its all-time case.
* `TauCeti.Manifold.eq_curveVelocityLiftWithin_of_isMIntegralCurveOn`: **an integral curve of the
  geodesic spray is a velocity lift**, and
  `TauCeti.Manifold.isGeodesicCurveOn_proj_of_isMIntegralCurveOn`: the curve it lies over is a
  geodesic once it is `C²`.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The geodesic spray".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

public section

open Bundle CovariantDerivative Filter Module Set
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-! ### The velocity lift of a curve -/

variable (I) in
/-- **The velocity lift** of a curve to the tangent bundle: the curve `t ↦ (γ t, γ' t)`, with the
velocity taken within the parameter set `s`.  It inherits the junk values of
`TauCeti.Manifold.curveVelocityWithin` where `γ` is not differentiable within `s`. -/
def curveVelocityLiftWithin (γ : ℝ → M) (s : Set ℝ) (t : ℝ) : TangentBundle I M :=
  TotalSpace.mk' E (γ t) (curveVelocityWithin I γ s t)

variable (I) in
/-- The velocity lift of a curve, with unrestricted velocity.  This is the `s = Set.univ` case of
`TauCeti.Manifold.curveVelocityLiftWithin`. -/
def curveVelocityLift (γ : ℝ → M) : ℝ → TangentBundle I M :=
  curveVelocityLiftWithin I γ univ

/-- The defining formula for the velocity lift. -/
theorem curveVelocityLiftWithin_apply (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    curveVelocityLiftWithin I γ s t =
      TotalSpace.mk' E (γ t) (curveVelocityWithin I γ s t) := (rfl)

/-- The unrestricted velocity lift is the lift taken within the whole parameter space. -/
@[simp]
theorem curveVelocityLift_eq_curveVelocityLiftWithin_univ (γ : ℝ → M) :
    curveVelocityLift I γ = curveVelocityLiftWithin I γ univ := (rfl)

/-- The velocity lift lies over the curve. -/
@[simp]
theorem curveVelocityLiftWithin_proj (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    (curveVelocityLiftWithin I γ s t).proj = γ t := (rfl)

/-- The fibre component of the velocity lift is the velocity of the curve. -/
@[simp]
theorem curveVelocityLiftWithin_snd (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    (curveVelocityLiftWithin I γ s t).2 = curveVelocityWithin I γ s t := (rfl)

/-! ### The spray -/

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- **The geodesic spray** of the ambient Riemannian bundle instance: the vector field
`(x, v) ↦ (v, -Γ_x (v, v))` on the tangent bundle, where `Γ` is the model-space Christoffel map of
the Levi-Civita connection in the tangent-bundle trivialization at `x`.  Both components are read
in the tangent-bundle chart centred at the argument, in which the base direction is read in the
extended chart of `M` at `x` and the fibre direction in the trivialization at `x`. -/
def geodesicSpray (z : TangentBundle I M) : TangentSpace I.tangent z :=
  (z.2, -christoffelMap (finBasis ℝ E)
    ((leviCivita I M).isCovariantDerivativeOn
      (s := (trivializationAt E (TangentSpace I) z.proj).baseSet)) z.proj z.2 z.2)

/-- **The chart formula for the geodesic spray**, restating the definition, whose body is not
exposed across the module boundary. -/
theorem geodesicSpray_apply (z : TangentBundle I M) :
    geodesicSpray I M z =
      (z.2, -christoffelMap (finBasis ℝ E)
        ((leviCivita I M).isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) z.proj).baseSet)) z.proj z.2 z.2) :=
  (rfl)

/-- **The geodesic equation as an integral-curve equation.**  The velocity lift of a `C²` curve
solves the equation of the geodesic spray at a parameter of its set exactly when the derivative of
its velocity along it vanishes there. -/
theorem hasMFDerivWithinAt_curveVelocityLiftWithin_iff
    (hs : UniqueDiffOn ℝ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) (ht : t ∈ s) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I.tangent (curveVelocityLiftWithin I γ s) s t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (geodesicSpray I M (curveVelocityLiftWithin I γ s t))) ↔
      alongCurveWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s t = 0 := by
  have hxbase : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hγd : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s := hγ.mdifferentiableOn (by norm_num)
  have hw : derivWithin (extChartAt I (γ t) ∘ γ) s t = curveVelocityWithin I γ s t :=
    derivWithin_extChartAt_comp_curve (hγd t ht) (hs t ht)
  -- the fibre reading of the velocity lift is the coordinate velocity of the curve
  have hcoord : (fun r ↦ (trivializationAt E (TangentSpace I) (γ t)
      (curveVelocityLiftWithin I γ s r)).2) =ᶠ[𝓝[s] t]
      sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ t) := by
    have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
      (hγd t ht).continuousWithinAt.preimage_mem_nhdsWithin
        ((trivializationAt E (TangentSpace I) (γ t)).open_baseSet.mem_nhds hxbase)
    filter_upwards [hbase] with r hr
    rw [sectionCoord_apply]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hr _).symm
  have hsec : (fun r ↦ (trivializationAt E (TangentSpace I) (γ t)
      (curveVelocityLiftWithin I γ s r)).2) =ᶠ[𝓝[s] t]
      derivWithin (extChartAt I (γ t) ∘ γ) s :=
    hcoord.trans (sectionCoord_curveVelocityWithin_eventuallyEq γ hs hγd ht hxbase)
  have hdiff : DifferentiableWithinAt ℝ (derivWithin (extChartAt I (γ t) ∘ γ) s) s t :=
    ((sectionCoord_curveVelocityWithin_eventuallyEq γ hs hγd ht
      hxbase).differentiableWithinAt_iff_of_mem ht).1
      (differentiableWithinAt_sectionCoord_curveVelocityWithin γ hs hγ ht hxbase)
  have hcont : ContinuousWithinAt (curveVelocityLiftWithin I γ s) s t := by
    rw [FiberBundle.continuousWithinAt_totalSpace E (curveVelocityLiftWithin I γ s)]
    exact ⟨(hγd t ht).continuousWithinAt,
      ((hcoord.differentiableWithinAt_iff_of_mem ht).2
        (differentiableWithinAt_sectionCoord_curveVelocityWithin γ hs hγ ht
          hxbase)).continuousWithinAt⟩
  -- the Christoffel term of the spray, read through the two presentations of the velocity
  have hchris : christoffelMap (finBasis ℝ E)
        ((leviCivita I M).isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
        (derivWithin (extChartAt I (γ t) ∘ γ) s t)
        (derivWithin (extChartAt I (γ t) ∘ γ) s t) =
      christoffelMap (finBasis ℝ E)
        ((leviCivita I M).isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
        (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t) :=
    congrArg (fun v : E ↦ christoffelMap (finBasis ℝ E)
      ((leviCivita I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t) v v) hw
  rw [alongCurveWithin_curveVelocityWithin_eq_zero_iff (leviCivita I M) γ hs hγd ht]
  refine Iff.trans (hasMFDerivWithinAt_totalSpace_curve_iff_of_continuousWithinAt
    (F := E) (V := fun x : M ↦ TangentSpace I x) (IB := I)
    (z := curveVelocityLiftWithin I γ s)
    (a := curveVelocityWithin I γ s t)
    (b := -christoffelMap (finBasis ℝ E)
      ((leviCivita I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
      (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) hcont) ?_
  refine Iff.trans (and_iff_right (hasDerivWithinAt_extChartAt_comp_curve
    (hasMFDerivWithinAt_curveVelocityWithin (hγd t ht)))) ?_
  refine Iff.trans (hsec.hasDerivWithinAt_iff_of_mem ht) ?_
  constructor
  · intro h
    rw [h.derivWithin (hs t ht), hchris, neg_add_cancel]
  · intro h
    have h1 : derivWithin (derivWithin (extChartAt I (γ t) ∘ γ) s) s t =
        -christoffelMap (finBasis ℝ E)
          ((leviCivita I M).isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
          (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t) := by
      rw [← hchris]
      exact eq_neg_of_add_eq_zero_left h
    rw [← h1]
    exact hdiff.hasDerivWithinAt

/-- **Geodesics are the base curves of the spray.**  The velocity lift of a `C²` curve is an
integral curve of the geodesic spray on a parameter set with unique derivatives exactly when the
curve is a geodesic there. -/
theorem isMIntegralCurveOn_curveVelocityLiftWithin_iff
    (hs : UniqueDiffOn ℝ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) :
    IsMIntegralCurveOn (curveVelocityLiftWithin I γ s) (geodesicSpray I M) s ↔
      IsGeodesicCurveOn I γ s := by
  refine ⟨fun h ↦ ⟨hs, hγ, fun r hr ↦
      (hasMFDerivWithinAt_curveVelocityLiftWithin_iff hs hγ hr).1 (h r hr)⟩, fun h r hr ↦ ?_⟩
  exact (hasMFDerivWithinAt_curveVelocityLiftWithin_iff hs hγ hr).2
    (h.alongCurveWithin_curveVelocityWithin_eq_zero r hr)

/-- A point at rest stays at rest: the velocity lift of a constant curve is an integral curve of
the geodesic spray. -/
theorem isMIntegralCurveOn_curveVelocityLiftWithin_const (hs : UniqueDiffOn ℝ s) (x : M) :
    IsMIntegralCurveOn (curveVelocityLiftWithin I (fun _ : ℝ ↦ x) s) (geodesicSpray I M) s :=
  (isMIntegralCurveOn_curveVelocityLiftWithin_iff hs contMDiffOn_const).2
    (isGeodesicCurveOn_const hs x)

/-- Being an integral curve of the geodesic spray on a parameter set only depends on the curve
along that set. -/
theorem isMIntegralCurveOn_geodesicSpray_congr {z z' : ℝ → TangentBundle I M}
    (h : IsMIntegralCurveOn z (geodesicSpray I M) s) (heq : EqOn z' z s) :
    IsMIntegralCurveOn z' (geodesicSpray I M) s := by
  intro r hr
  refine ((h r hr).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heq) (heq hr)).congr_mfderiv ?_
  exact congrArg (fun w : E × E ↦ (1 : ℝ →L[ℝ] ℝ).smulRight w)
    (congrArg (fun w ↦ (geodesicSpray I M w : E × E)) (heq hr).symm)

/-- **An integral curve of the spray is a velocity lift.**  On a parameter set with unique
derivatives, an integral curve of the geodesic spray is the velocity lift of the curve it lies
over. -/
theorem eq_curveVelocityLiftWithin_of_isMIntegralCurveOn {z : ℝ → TangentBundle I M}
    (hs : UniqueDiffOn ℝ s) (h : IsMIntegralCurveOn z (geodesicSpray I M) s) (ht : t ∈ s) :
    z t = curveVelocityLiftWithin I (fun r ↦ (z r).proj) s t := by
  have hproj : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun r ↦ (z r).proj) s t :=
    (Bundle.mdifferentiableAt_proj (fun x : M ↦ TangentSpace I x)).comp_mdifferentiableWithinAt t
      (h t ht).mdifferentiableWithinAt
  have hd := (hasMFDerivWithinAt_totalSpace_curve_iff_of_continuousWithinAt
    (F := E) (V := fun x : M ↦ TangentSpace I x) (IB := I) (z := z)
    (a := (z t).2)
    (b := -christoffelMap (finBasis ℝ E)
      ((leviCivita I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (z t).proj).baseSet)) (z t).proj
      (z t).2 (z t).2) (h t ht).continuousWithinAt).1 (h t ht)
  have hvel : curveVelocityWithin I (fun r ↦ (z r).proj) s t = (z t).2 :=
    (derivWithin_extChartAt_comp_curve hproj (hs t ht)).symm.trans (hd.1.derivWithin (hs t ht))
  rw [curveVelocityLiftWithin_apply, hvel]

/-- **The base curve of an integral curve of the spray is a geodesic**, as soon as it is `C²` on a
parameter set with unique derivatives. -/
theorem isGeodesicCurveOn_proj_of_isMIntegralCurveOn {z : ℝ → TangentBundle I M}
    (hs : UniqueDiffOn ℝ s) (h : IsMIntegralCurveOn z (geodesicSpray I M) s)
    (hz : ContMDiffOn 𝓘(ℝ, ℝ) I 2 (fun r ↦ (z r).proj) s) :
    IsGeodesicCurveOn I (fun r ↦ (z r).proj) s :=
  (isMIntegralCurveOn_curveVelocityLiftWithin_iff hs hz).1
    (isMIntegralCurveOn_geodesicSpray_congr h fun _r hr ↦
      (eq_curveVelocityLiftWithin_of_isMIntegralCurveOn hs h hr).symm)

/-! ### All-time geodesics and the spray -/

/-- The all-time case of `TauCeti.Manifold.isMIntegralCurveOn_curveVelocityLiftWithin_iff`: the
velocity lift of a `C²` curve is an integral curve of the geodesic spray exactly when the curve is
an all-time geodesic. -/
theorem isMIntegralCurve_curveVelocityLift_iff (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    IsMIntegralCurve (curveVelocityLift I γ) (geodesicSpray I M) ↔ IsGeodesicCurve I γ := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← isGeodesicCurveOn_univ]
  exact isMIntegralCurveOn_curveVelocityLiftWithin_iff uniqueDiffOn_univ
    (contMDiffOn_univ.2 hγ)

end TauCeti.Manifold

end
