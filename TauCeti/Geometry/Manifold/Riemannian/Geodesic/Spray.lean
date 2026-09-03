/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CurveInTotalSpace
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.CoordinateChange

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
`CovariantDerivative.alongCurveWithin` and `TauCeti.Manifold.IsGeodesicCurveOn`.  Its compatibility
on overlapping tangent-bundle charts is `TauCeti.Manifold.tangentCoordChange_geodesicSpray`; the
derivative term in the tangent lift cancels the inhomogeneous term in
`TauCeti.Manifold.christoffelMap_coordChange`.  That this formula solves the intended problem is
the content of
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
  preferred-chart formula, `TauCeti.Manifold.tangentCoordChange_geodesicSpray` its formula in every
  overlapping tangent-bundle chart, and
  `TauCeti.Manifold.isMIntegralCurveOn_curveVelocityLiftWithin_const` the constant-curve check.
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

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
set_option backward.isDefEq.respectTransparency false in
private theorem tangentCoordChange_tangent_apply {x x₀ : M}
    (hx₀ : x ∈ (extChartAt I x₀).source) (u w : TangentSpace I x) :
    tangentCoordChange I.tangent
        (TotalSpace.mk' E x u) (TotalSpace.mk' E x₀ 0) (TotalSpace.mk' E x u) (u, w) =
      (tangentCoordChange I x x₀ x u,
        mvfderiv I (fun y ↦ tangentCoordChange I x x₀ y u) x u +
          tangentCoordChange I x x₀ x w) := by
  change E at u w
  let z : TangentBundle I M := TotalSpace.mk' E x u
  let q : TangentBundle I M := TotalSpace.mk' E x₀ 0
  let p := extChartAt I.tangent z z
  let G := (extChartAt I.tangent q : TangentBundle I M → E × E) ∘
    (extChartAt I.tangent z).symm
  let T : E × E → E × E := fun a ↦
    let y := (extChartAt I x).symm a.1
    (extChartAt I x₀ y, tangentCoordChange I x x₀ y a.2)
  have hz : z ∈ (chartAt (ModelProd H E) z).source := mem_chart_source _ _
  have hzq : z ∈ (chartAt (ModelProd H E) q).source := by
    rw [TangentBundle.mem_chart_source_iff (I := I) (M := M)]
    rw [← extChartAt_source I x₀]
    exact hx₀
  have hN := (I.tangent.extendCoordChange_source_mem_nhdsWithin'
    (e := chartAt (ModelProd H E) z) (e' := chartAt (ModelProd H E) q) hz hzq)
  have hGT : G =ᶠ[𝓝[range I.tangent] p] T := by
    filter_upwards [hN] with a ha
    change a ∈ ((extChartAt I.tangent z).symm ≫ extChartAt I.tangent q).source at ha
    let b := (extChartAt I.tangent z).symm a
    have ha_target : a ∈ (extChartAt I.tangent z).target := ha.1
    have hbzT : b ∈ (extChartAt I.tangent z).source :=
      (extChartAt I.tangent z).map_target ha_target
    have hbqT : b ∈ (extChartAt I.tangent q).source := ha.2
    have hbz : b.proj ∈ (extChartAt I x).source := by
      rw [extChartAt_source] at hbzT ⊢
      exact (TangentBundle.mem_chart_source_iff b z).1 hbzT
    have hbq : b.proj ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source] at hbqT ⊢
      exact (TangentBundle.mem_chart_source_iff b q).1 hbqT
    have hright : extChartAt I.tangent z b = a :=
      (extChartAt I.tangent z).right_inv ha_target
    have hbase : extChartAt I x b.proj = a.1 := by
      have h := congrArg Prod.fst hright
      change extChartAt I x b.proj = a.1 at h
      exact h
    have hfiber : tangentCoordChange I b.proj x b.proj b.2 = a.2 := by
      have h := congrArg Prod.snd hright
      change tangentCoordChange I b.proj x b.proj b.2 = a.2 at h
      exact h
    have hy : (extChartAt I x).symm a.1 = b.proj := by
      rw [← hbase]
      exact (extChartAt I x).left_inv hbz
    have hsecond : (extChartAt I.tangent q b).2 =
        tangentCoordChange I x x₀ b.proj a.2 := by
      rw [← hfiber]
      have hcomp := tangentCoordChange_comp (I := I) (w := b.proj) (x := x)
        (y := x₀) (z := b.proj) (v := b.2)
        ⟨⟨mem_extChartAt_source b.proj, hbz⟩, hbq⟩
      change tangentCoordChange I b.proj x₀ b.proj b.2 = _
      exact hcomp.symm
    change extChartAt I.tangent q b = T a
    apply Prod.ext
    · change extChartAt I x₀ b.proj = extChartAt I x₀ ((extChartAt I x).symm a.1)
      rw [hy]
    · change (extChartAt I.tangent q b).2 =
        tangentCoordChange I x x₀ ((extChartAt I x).symm a.1) a.2
      simpa only [hy] using hsecond
  rw [tangentCoordChange_def]
  change fderivWithin ℝ G (range I.tangent) p (u, w) = _
  have hp_mem : p ∈ range I.tangent :=
    (extChartAt_target_subset_range z) ((extChartAt I.tangent z).map_source
      (mem_extChartAt_source z))
  have hp_eq : G p = T p := hGT.self_of_nhdsWithin hp_mem
  rw [hGT.fderivWithin_eq hp_eq]
  have hpcoord : p = (extChartAt I x x, u) := by
    apply Prod.ext
    · change extChartAt I x x = (extChartAt I x x, u).1
      rfl
    · change tangentCoordChange I x x x u = u
      exact tangentCoordChange_self (mem_extChartAt_source x)
  rw [hpcoord, ModelWithCorners.range_prod]
  rw [ModelWithCorners.range_eq_univ 𝓘(ℝ, E)]
  let a₀ := extChartAt I x x
  let F : E → E := fun a ↦ extChartAt I x₀ ((extChartAt I x).symm a)
  let C : E → E →L[ℝ] E := fun a ↦ tangentCoordChange I x x₀ ((extChartAt I x).symm a)
  have ha₀ : a₀ ∈ ((extChartAt I x).symm ≫ extChartAt I x₀).source := by
    rw [PartialEquiv.trans_source]
    exact ⟨(extChartAt I x).map_source (mem_extChartAt_source x), by
      change (extChartAt I x).symm a₀ ∈ (extChartAt I x₀).source
      simpa only [a₀, extChartAt_to_inv] using hx₀⟩
  have hF : DifferentiableWithinAt ℝ F (range I) a₀ :=
    (contDiffWithinAt_ext_coord_change x₀ x ha₀).differentiableWithinAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hI₂ : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
  have hCMD : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (tangentCoordChange I x x₀) x :=
    (contMDiffAt_tangentCoordChange (n := 1) hx₀).mdifferentiableAt one_ne_zero
  have hC : DifferentiableWithinAt ℝ C (range I) a₀ := by
    have h := (mdifferentiableAt_iff (tangentCoordChange I x x₀) x).1 hCMD |>.2
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe] at h
    change DifferentiableWithinAt ℝ C (range I) a₀ at h
    exact h
  have hmaps : MapsTo (Prod.fst : E × E → E) (range I ×ˢ univ) (range I) :=
    fun _ h ↦ h.1
  have huniqBase : UniqueDiffWithinAt ℝ (range I) a₀ := I.uniqueDiffWithinAt_image
  have huniq : UniqueDiffWithinAt ℝ (range I ×ˢ univ) (a₀, u) :=
    huniqBase.prod uniqueDiffWithinAt_univ
  have hFp : DifferentiableWithinAt ℝ (fun a : E × E ↦ F a.1)
      (range I ×ˢ univ) (a₀, u) := by
    change DifferentiableWithinAt ℝ (F ∘ Prod.fst) (range I ×ˢ univ) (a₀, u)
    exact hF.comp (a₀, u) differentiableWithinAt_fst hmaps
  have hCp : DifferentiableWithinAt ℝ (fun a : E × E ↦ C a.1)
      (range I ×ˢ univ) (a₀, u) := by
    change DifferentiableWithinAt ℝ (C ∘ Prod.fst) (range I ×ˢ univ) (a₀, u)
    exact hC.comp (a₀, u) differentiableWithinAt_fst hmaps
  have hAp : DifferentiableWithinAt ℝ (fun a : E × E ↦ C a.1 a.2)
      (range I ×ˢ univ) (a₀, u) :=
    hCp.clm_apply differentiableWithinAt_snd
  change (fderivWithin ℝ (fun a : E × E ↦ (F a.1, C a.1 a.2))
    (range I ×ˢ univ) (a₀, u)) (u, w) = _
  have hFp_eq := fderivWithin_comp (a₀, u) hF differentiableWithinAt_fst hmaps huniq
  change fderivWithin ℝ (fun a : E × E ↦ F a.1) (range I ×ˢ univ) (a₀, u) = _ at hFp_eq
  have hCp_eq := fderivWithin_comp (a₀, u) hC differentiableWithinAt_fst hmaps huniq
  change fderivWithin ℝ (fun a : E × E ↦ C a.1) (range I ×ˢ univ) (a₀, u) = _ at hCp_eq
  have hAp_eq := fderivWithin_clm_apply huniq hCp differentiableWithinAt_snd
  change fderivWithin ℝ (fun a : E × E ↦ C a.1 a.2) (range I ×ˢ univ) (a₀, u) = _ at hAp_eq
  have hfst_app : (fderivWithin ℝ (Prod.fst : E × E → E) (range I ×ˢ univ) (a₀, u))
      (u, w) = u := by
    rw [fderivWithin_fst huniq]
    rfl
  have hsnd_app : (fderivWithin ℝ (Prod.snd : E × E → E) (range I ×ˢ univ) (a₀, u))
      (u, w) = w := by
    rw [fderivWithin_snd huniq]
    rfl
  rw [hFp.fderivWithin_prodMk hAp huniq, ContinuousLinearMap.prod_apply, hFp_eq,
    hAp_eq, hCp_eq]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.flip_apply, C, F, a₀, extChartAt_to_inv]
  rw [hfst_app, hsnd_app, add_comm]
  have hFderiv : fderivWithin ℝ F (range I) a₀ = tangentCoordChange I x x₀ x := by
    rw [tangentCoordChange_def]
    rfl
  rw [hFderiv]
  have hMDu : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y ↦ tangentCoordChange I x x₀ y u) x :=
    hCMD.clm_apply mdifferentiableAt_const
  have hCuDeriv := fderivWithin_clm_apply huniqBase hC
    (differentiableWithinAt_const (c := u))
  have hCuDerivApp := congrArg (fun L : E →L[ℝ] E ↦ L u) hCuDeriv
  have hMv : mvfderiv I (fun y ↦ tangentCoordChange I x x₀ y u) x u =
      fderivWithin ℝ C (range I) a₀ u u := by
    rw [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv, ite_eq_left hMDu]
    change fderivWithin ℝ (fun a ↦ C a u) (range I) a₀ u = _
    simpa [fderivWithin_const_apply] using hCuDerivApp
  rw [hMv]

set_option backward.isDefEq.respectTransparency false in
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
  rw [geodesicSpray_apply, tangentCoordChange_tangent_apply hx₀]
  have hchange := geodesicSpray_coordChange (I := I) (M := M) hx₀ u
  simpa only [map_neg, ← sub_eq_add_neg] using hchange

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
