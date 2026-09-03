/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import TauCeti.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic

/-!
# Integral curves of invariant vector fields

Left-invariant vector fields on real Lie groups modeled on complete spaces are complete. Local
integral curves around the identity can be translated to give a uniform existence interval around
every point, after which Mathlib's uniform-time theorem produces global integral curves.

## Main results

* `IsMIntegralCurveOn.const_mul_mulInvariantVectorField`: left translation preserves invariant
  integral curves.
* `IsMIntegralCurve.const_mul_mulInvariantVectorField`: the global version of that translation law.
* `exists_isMIntegralCurve_mulInvariantVectorField`: every left-invariant vector field has a global
  integral curve through every point.
* `existsUnique_isMIntegralCurve_mulInvariantVectorField`: that global curve is unique.
* `mulInvariantIntegralCurve`: the resulting canonical global integral curve.
* `hasDerivAt_extChartAt_mulInvariantIntegralCurve_zero`: in identity-chart coordinates, the
  canonical curve has initial velocity equal to its generator.
* `contMDiff_mulInvariantIntegralCurve`: canonical invariant integral curves are smooth.
* `mulInvariantIntegralCurve_eq_const_mul`: curves through arbitrary points are left translates of
  the curve through the identity.
* `mulInvariantIntegralCurve_add`: the identity curve satisfies the one-parameter subgroup law.
* `mulInvariantIntegralCurve_smul`: scaling the vector field rescales time along its curves.
* `mulInvariantOneParameterSubgroup`: the identity curve bundled as a continuous homomorphism.
* `contMDiff_mulInvariantOneParameterSubgroup`: canonical one-parameter subgroups are smooth.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Function Manifold Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

namespace IsMIntegralCurveOn

/-- Left translation preserves integral curves of a left-invariant vector field. -/
theorem const_mul_mulInvariantVectorField [ContMDiffMul I 1 G]
    {v : GroupLieAlgebra I G} {γ : ℝ → G} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s) (g : G) :
    IsMIntegralCurveOn (fun t ↦ g * γ t) (mulInvariantVectorField v) s := by
  have hpush := hγ.map_of_mfderiv_eq (f := fun x : G ↦ g * x)
    (fun _ _ ↦ mdifferentiableAt_mul_left)
    (fun t _ ↦ mfderiv_mul_left_mulInvariantVectorField g (γ t) v)
  exact hpush

end IsMIntegralCurveOn

namespace IsMIntegralCurve

/-- Left translation preserves global integral curves of a left-invariant vector field. -/
theorem const_mul_mulInvariantVectorField [ContMDiffMul I 1 G]
    {v : GroupLieAlgebra I G} {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (g : G) :
    IsMIntegralCurve (fun t ↦ g * γ t) (mulInvariantVectorField v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn]
  exact (hγ.isMIntegralCurveOn univ).const_mul_mulInvariantVectorField g

end IsMIntegralCurve

/-- Every left-invariant vector field on a real Lie group modeled on a complete space has a global
integral curve through every point. -/
theorem exists_isMIntegralCurve_mulInvariantVectorField [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) :
    ∃ γ : ℝ → G, γ 0 = x ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  let V := mulInvariantVectorField v
  have hV : CMDiff 1 (fun g ↦ (⟨g, V g⟩ : TangentBundle I G)) :=
    (contMDiff_mulInvariantVectorField v).of_le (by simp)
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (x₀ := (1 : G)) 0 hV.contMDiffAt
  obtain ⟨ε, hε, hγ⟩ := isMIntegralCurveAt_iff'.mp hγ
  rw [Real.ball_eq_Ioo] at hγ
  have hγ : IsMIntegralCurveOn γ V (Ioo (-ε) ε) := by
    simpa only [zero_sub, zero_add] using hγ
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn hV hε
  intro y
  refine ⟨fun t ↦ y * γ t, by simp [hγ0], ?_⟩
  let _ : ContMDiffMul I 1 G :=
    ContMDiffMul.of_le (m := 1) (n := minSmoothness ℝ 3) (by norm_num)
  exact hγ.const_mul_mulInvariantVectorField y

/-- Every left-invariant vector field on a real Lie group modeled on a complete space has a unique
global integral curve through every point. -/
theorem existsUnique_isMIntegralCurve_mulInvariantVectorField [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) :
    ∃! γ : ℝ → G, γ 0 = x ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurve_mulInvariantVectorField v x
  refine ⟨γ, ⟨hγ0, hγ⟩, ?_⟩
  intro δ hδ
  apply isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    ((contMDiff_mulInvariantVectorField v).of_le (by simp)) hδ.2 hγ
  rw [hδ.1, hγ0]

/-- The unique global integral curve of a left-invariant vector field through a given point. -/
noncomputable def mulInvariantIntegralCurve [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) : ℝ → G :=
  (existsUnique_isMIntegralCurve_mulInvariantVectorField v x).choose

/-- The canonical invariant integral curve starts at its specified point. -/
@[simp]
theorem mulInvariantIntegralCurve_zero [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) :
    mulInvariantIntegralCurve v x 0 = x :=
  (existsUnique_isMIntegralCurve_mulInvariantVectorField v x).choose_spec.1.1

/-- The canonical invariant curve is a global integral curve of its left-invariant vector field. -/
theorem isMIntegralCurve_mulInvariantIntegralCurve [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) :
    IsMIntegralCurve (mulInvariantIntegralCurve v x) (mulInvariantVectorField v) :=
  (existsUnique_isMIntegralCurve_mulInvariantVectorField v x).choose_spec.1.2

/-- In the extended chart at the identity, the canonical invariant curve through the identity has
initial velocity equal to its generator. -/
theorem hasDerivAt_extChartAt_mulInvariantIntegralCurve_zero [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : E) :
    HasDerivAt
      ((extChartAt I (1 : G)) ∘
        mulInvariantIntegralCurve (I := I) (G := G) (v : GroupLieAlgebra I G) 1) v 0 := by
  have hcurve :=
    (isMIntegralCurve_mulInvariantIntegralCurve (I := I) (G := G)
      (v : GroupLieAlgebra I G) (1 : G)).isMIntegralCurveAt 0
  have hcurveDeriv := hcurve.eventually_hasDerivAt.self_of_nhds
  have hcurveZero : mulInvariantIntegralCurve (I := I) (G := G)
      (v : GroupLieAlgebra I G) 1 0 = 1 := mulInvariantIntegralCurve_zero _ _
  rw [hcurveZero] at hcurveDeriv
  have hfieldOne : mulInvariantVectorField (I := I) (G := G)
      (v : GroupLieAlgebra I G) (1 : G) = (v : GroupLieAlgebra I G) :=
    mulInvariantVectorField_one (I := I) (G := G) (v : GroupLieAlgebra I G)
  rw [hfieldOne] at hcurveDeriv
  have hone : (1 : G) ∈ (extChartAt I (1 : G)).source :=
    mem_of_mem_nhds (extChartAt_source_mem_nhds (I := I) (1 : G))
  rw [tangentCoordChange_self hone] at hcurveDeriv
  exact hcurveDeriv

attribute [local instance] LieGroup.minSmoothnessThree

section SmoothInvariantIntegralCurve

variable [CompleteSpace E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

/-- The canonical integral curve of an invariant vector field on a smooth Lie group is smooth. -/
theorem contMDiff_mulInvariantIntegralCurve (v : GroupLieAlgebra I G) (x : G) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (mulInvariantIntegralCurve v x) :=
  (isMIntegralCurve_mulInvariantIntegralCurve v x).contMDiff
    (contMDiff_mulInvariantVectorField_infty v)

end SmoothInvariantIntegralCurve

/-- Any global integral curve of a left-invariant vector field is the canonical one determined by
its value at zero. -/
theorem eq_mulInvariantIntegralCurve [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) {γ : ℝ → G}
    (hγ0 : γ 0 = x) (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) :
    γ = mulInvariantIntegralCurve v x :=
  (existsUnique_isMIntegralCurve_mulInvariantVectorField v x).unique ⟨hγ0, hγ⟩
    (existsUnique_isMIntegralCurve_mulInvariantVectorField v x).choose_spec.1

/-- The canonical invariant integral curve through `x` is the left translate by `x` of the
canonical curve through the identity. -/
theorem mulInvariantIntegralCurve_eq_const_mul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) :
    mulInvariantIntegralCurve v x = fun t ↦ x * mulInvariantIntegralCurve v 1 t := by
  symm
  apply eq_mulInvariantIntegralCurve v x
  · simp
  · let _ : ContMDiffMul I 1 G :=
      ContMDiffMul.of_le (m := 1) (n := minSmoothness ℝ 3) (by norm_num)
    exact (isMIntegralCurve_mulInvariantIntegralCurve v 1).const_mul_mulInvariantVectorField x

/-- The canonical invariant curve through the identity satisfies the one-parameter subgroup law. -/
@[simp]
theorem mulInvariantIntegralCurve_add [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (s t : ℝ) :
    mulInvariantIntegralCurve v 1 (s + t) =
      mulInvariantIntegralCurve v 1 s * mulInvariantIntegralCurve v 1 t := by
  let γ := mulInvariantIntegralCurve v 1
  have hshift : γ ∘ (· + s) = mulInvariantIntegralCurve v (γ s) := by
    apply eq_mulInvariantIntegralCurve v (γ s)
    · simp [γ]
    · exact (isMIntegralCurve_mulInvariantIntegralCurve v 1).comp_add s
  calc
    γ (s + t) = (γ ∘ (· + s)) t := by simp [add_comm]
    _ = mulInvariantIntegralCurve v (γ s) t := congrFun hshift t
    _ = γ s * γ t := congrFun (mulInvariantIntegralCurve_eq_const_mul v (γ s)) t

/-- Scaling an invariant vector field rescales time along its canonical integral curves. -/
theorem mulInvariantIntegralCurve_smul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (x : G) (t s : ℝ) :
    mulInvariantIntegralCurve (t • v) x s = mulInvariantIntegralCurve v x (s * t) := by
  let γ := mulInvariantIntegralCurve v x
  have hscaled : IsMIntegralCurve (γ ∘ (· * t)) (mulInvariantVectorField (t • v)) := by
    rw [mulInvariantVectorField_smul]
    exact (isMIntegralCurve_mulInvariantIntegralCurve v x).comp_mul t
  have heq : γ ∘ (· * t) = mulInvariantIntegralCurve (t • v) x := by
    apply eq_mulInvariantIntegralCurve (t • v) x
    · simp [γ]
    · exact hscaled
  exact (congrFun heq s).symm

/-- The canonical invariant curve through the identity, bundled as a continuous one-parameter
subgroup. -/
noncomputable def mulInvariantOneParameterSubgroup [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) :
    ContinuousMonoidHom (Multiplicative ℝ) G where
  toFun t := mulInvariantIntegralCurve v 1 (Multiplicative.toAdd t)
  map_one' := by simp
  map_mul' s t := by
    simp
  continuous_toFun :=
    (isMIntegralCurve_mulInvariantIntegralCurve v 1).continuous.comp continuous_toAdd

/-- Evaluating the invariant one-parameter subgroup at time `t` recovers the canonical integral
curve through the identity. -/
@[simp]
theorem mulInvariantOneParameterSubgroup_apply [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (t : ℝ) :
    mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd t) =
      mulInvariantIntegralCurve v 1 t :=
  (rfl)

section SmoothInvariantOneParameterSubgroup

variable [CompleteSpace E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

/-- The one-parameter subgroup generated by an invariant vector field is smooth in its additive
real parameter. -/
theorem contMDiff_mulInvariantOneParameterSubgroup (v : GroupLieAlgebra I G) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ ↦ mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd t)) := by
  simpa only [mulInvariantOneParameterSubgroup_apply] using
    contMDiff_mulInvariantIntegralCurve v (1 : G)

end SmoothInvariantOneParameterSubgroup
