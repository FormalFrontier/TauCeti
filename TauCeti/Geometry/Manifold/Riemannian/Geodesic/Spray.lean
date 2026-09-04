/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.CoordinateChange

/-!
# The geodesic spray

The geodesic equation `u'' + Γ (u', u') = 0` is a second-order equation on the manifold; as usual
it becomes a first-order equation on the tangent bundle, for the vector field

`S (x, v) = (v, -Γ_x (v, v))`

on `TM` called the **geodesic spray**.  This file constructs `S` for the Levi-Civita connection of
the ambient Riemannian bundle instance, identifies velocity lifts of `C²` geodesics with integral
curves of `S`, and shows that every integral curve is a velocity lift.

A vector field on a manifold assigns to a point a vector of the model space, read in the chart at
that point; the tangent-bundle chart at `z = (x, v)` reads the base direction in the extended
chart of `M` at `x` and the fibre direction in the tangent-bundle trivialization at `x`, over
which `v` is its own coordinate.  So the displayed formula *is* the definition of
`TauCeti.Manifold.geodesicSpray`, with `Γ` the model-space Christoffel map
`TauCeti.Manifold.christoffelMap` of the Levi-Civita connection in the trivialization at the base
point of the argument — the same moving-chart convention as
`CovariantDerivative.alongCurveWithin` and `TauCeti.Manifold.IsGeodesicCurveOn`.  Its compatibility
on overlapping tangent-bundle charts is `TauCeti.Manifold.tangentCoordChange_geodesicSpray`; the
derivative term in the tangent lift cancels the inhomogeneous term in
`TauCeti.Manifold.christoffelMap_coordChange`.  That this formula solves the intended problem is
the content of
`TauCeti.Manifold.isMIntegralCurveOn_curveVelocityLiftWithin_iff` and
`TauCeti.Manifold.eq_curveVelocityLiftWithin_of_isMIntegralCurveOn`: on a parameter set with
unique derivatives, velocity lifts of `C²` geodesics are integral curves of `S`, while arbitrary
integral curves of `S` are velocity lifts of their projected curves:

`t ↦ (γ t, γ' t) : ℝ → TM`

The two statements are read in one direction each: the velocity lift of a `C²` curve is an integral
curve of `S` exactly when the curve is a geodesic, and conversely every integral curve of `S` is the
velocity lift of the curve it lies over, whose base curve is a geodesic as soon as it is `C²`. The
`C²` hypothesis on the base curve is not yet removable: it would follow from smoothness of `S`,
which is not proved here.

The unpacking of a curve into `TM` into its base curve and its fibre coordinate is
`TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff`, proved for an arbitrary fibre bundle.

## Main definitions and results

* `TauCeti.Manifold.geodesicSpray`: **the geodesic spray** of the ambient Riemannian bundle
  instance, a vector field on the tangent bundle, with `TauCeti.Manifold.geodesicSpray_apply` its
  preferred-chart formula and `TauCeti.Manifold.tangentCoordChange_geodesicSpray` its formula in
  every overlapping tangent-bundle chart.
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

/-! ### The spray -/

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

-- The geodesic-spray construction below, and the identification of its integral curves with the
-- velocity lifts of geodesics, follow the geodesic-spray development of the Tau Ceti Hopf--Rinow
-- roadmap, https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md
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

/- **Chart independence of the spray formula.**  On the overlap of the preferred charts at `x`
and `x₀`, the tangent lift of the coordinate change sends the second-order vector
`(u, -Γˣ(u, u))` to `(A u, -Γˣ⁰(A u, A u))`.  Its vertical component is the derivative of
`y ↦ A_y u` in the base direction `u`, plus `A` applied to the old vertical component. -/
private theorem geodesicSpray_coordChange {x x₀ : M}
    (hx₀ : x ∈ (extChartAt I x₀).source) (u : TangentSpace I x) :
    let A := tangentCoordChange I x x₀ x
    let Γ := christoffelMap (finBasis ℝ E)
      ((leviCivita I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x).baseSet)) x
    let Γ₀ := christoffelMap (finBasis ℝ E)
      ((leviCivita I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x
    (A u, mvfderiv I (fun y ↦ tangentCoordChange I x x₀ y u) x u - A (Γ u u)) =
      (A u, -Γ₀ (A u) (A u)) := by
  dsimp only
  have h := christoffelMap_coordChange (finBasis ℝ E) hx₀ u u
    ((leviCivita I M).isCovariantDerivativeOn
      (s := (trivializationAt E (TangentSpace I) x₀).baseSet))
    ((leviCivita I M).isCovariantDerivativeOn
      (s := (trivializationAt E (TangentSpace I) x).baseSet))
  rw [h]
  simp only [neg_sub]

/-- **The geodesic spray has the same formula in every overlapping tangent-bundle chart.**
Transporting the value defined in the preferred chart at `(x, u)` to the chart based at `x₀`
sends `(v, -Γ(v, v))` to `(v₀, -Γ₀(v₀, v₀))`, where `v₀` is the fibre coordinate in the latter
chart. -/
theorem tangentCoordChange_geodesicSpray {x x₀ : M}
    (hx₀ : x ∈ (extChartAt I x₀).source) (u : TangentSpace I x) :
    tangentCoordChange I.tangent (TotalSpace.mk' E x u) (TotalSpace.mk' E x₀ 0)
        (TotalSpace.mk' E x u) (geodesicSpray I M (TotalSpace.mk' E x u)) =
      let v := tangentCoordChange I x x₀ x u
      (v, -christoffelMap (finBasis ℝ E)
        ((leviCivita I M).isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) x₀).baseSet)) x v v) := by
  rw [geodesicSpray_apply]
  have hT := tangentCoordChange_tangent_apply (I := I) (M := M) hx₀ u
    (-christoffelMap (finBasis ℝ E)
      ((leviCivita I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) x).baseSet)) x u u)
  simp only [continuousLinearMapAt_trivializationAt_self] at hT
  -- Reduce the projections of the displayed total-space point so that the general tangent-chart
  -- formula applies; these projections have no separate rewriting lemma.
  change tangentCoordChange I.tangent (TotalSpace.mk' E x u) (TotalSpace.mk' E x₀ 0)
      (TotalSpace.mk' E x u)
        (u, -christoffelMap (finBasis ℝ E)
          ((leviCivita I M).isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) x).baseSet)) x u u) = _
  rw [hT]
  simpa only [map_neg, ← sub_eq_add_neg] using
    geodesicSpray_coordChange (I := I) (M := M) hx₀ u

/-- **The geodesic equation as an integral-curve equation.**  The velocity lift of a `C²` curve
solves the equation of the geodesic spray at a parameter of its set exactly when the derivative of
its velocity along it vanishes there. -/
theorem hasMFDerivWithinAt_curveVelocityLiftWithin_iff
    (hs : UniqueDiffOn ℝ s) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s) (ht : t ∈ s) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I.tangent (curveVelocityLiftWithin I γ s) s t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (geodesicSpray I M (curveVelocityLiftWithin I γ s t))) ↔
      alongCurveWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s t = 0 := by
  rw [geodesicSpray_apply, curveVelocityLiftWithin_snd, curveVelocityLiftWithin_proj]
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
    rw [curveVelocityLiftWithin_apply, sectionCoord_apply]
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
    simp only [curveVelocityLiftWithin_proj]
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
  have htotal := hasMFDerivWithinAt_totalSpace_curve_iff_of_continuousWithinAt
    (F := E) (V := fun x : M ↦ TangentSpace I x) (IB := I)
    (z := curveVelocityLiftWithin I γ s)
    (a := curveVelocityWithin I γ s t)
    (b := -christoffelMap (finBasis ℝ E)
      ((leviCivita I M).isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t)
      (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)) hcont
  simp only [curveVelocityLiftWithin_proj] at htotal
  refine Iff.trans htotal ?_
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
    (h.congr fun _r hr ↦
      (eq_curveVelocityLiftWithin_of_isMIntegralCurveOn hs h hr).symm)

/-! ### All-time geodesics and the spray -/

/-- The all-time case of `TauCeti.Manifold.isMIntegralCurveOn_curveVelocityLiftWithin_iff`: the
velocity lift of a `C²` curve is an integral curve of the geodesic spray exactly when the curve is
an all-time geodesic. -/
theorem isMIntegralCurve_curveVelocityLift_iff (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) :
    IsMIntegralCurve (curveVelocityLift I γ) (geodesicSpray I M) ↔ IsGeodesicCurve I γ := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← isGeodesicCurveOn_univ]
  rw [← curveVelocityLiftWithin_univ]
  exact isMIntegralCurveOn_curveVelocityLiftWithin_iff uniqueDiffOn_univ
    (contMDiffOn_univ.2 hγ)

end TauCeti.Manifold

end
