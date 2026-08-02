/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Integral curves of invariant vector fields

Left-invariant vector fields on real Lie groups modeled on complete spaces are complete. Local
integral curves around the identity can be translated to give a uniform existence interval around
every point, after which Mathlib's uniform-time theorem produces global integral curves.

## Main results

* `IsMIntegralCurveOn.const_mul_mulInvariantVectorField`: left translation preserves invariant
  integral curves.
* `IsMIntegralCurve.const_mul_mulInvariantVectorField`: the global version of that translation law.
* `IsMIntegralCurve.contMDiff`: integral curves of smooth vector fields are smooth.
* `exists_isMIntegralCurve_mulInvariantVectorField`: every left-invariant vector field has a global
  integral curve through every point.
* `existsUnique_isMIntegralCurve_mulInvariantVectorField`: that global curve is unique.
* `mulInvariantIntegralCurve`: the resulting canonical global integral curve.
* `mulInvariantIntegralCurve_eq_const_mul`: curves through arbitrary points are left translates of
  the curve through the identity.
* `mulInvariantIntegralCurve_add`: the identity curve satisfies the one-parameter subgroup law.
* `mulInvariantIntegralCurve_smul`: scaling the vector field rescales time along its curves.
* `mulInvariantOneParameterSubgroup`: the identity curve bundled as a continuous homomorphism.

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

private theorem contDiffOn_succ_of_hasDerivAt_comp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} {f : ℝ → F} {v : F → F} {s : Set ℝ} {u : Set F}
    (hs : IsOpen s) (hv : ContDiffOn ℝ n v u) (hfu : MapsTo f s u)
    (hf : ∀ t ∈ s, HasDerivAt f (v (f t)) t) :
    ContDiffOn ℝ (n + 1 : ℕ) f s := by
  induction n generalizing f with
  | zero =>
      rw [show ((0 + 1 : ℕ) : ℕ∞ω) = 0 + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen hs]
      refine ⟨fun t ht => (hf t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      apply (hv.comp (contDiffOn_zero.mpr ?_) hfu).congr
      · exact fun t ht => (hf t ht).deriv
      · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
  | succ n ih =>
      have hfn : ContDiffOn ℝ (n + 1 : ℕ) f s :=
        ih (hv.of_le (by exact_mod_cast Nat.le_succ n)) hfu hf
      rw [show ((n + 1 + 1 : ℕ) : ℕ∞ω) = (n + 1 : ℕ∞ω) + 1 by norm_num,
        contDiffOn_succ_iff_deriv_of_isOpen hs]
      refine ⟨fun t ht => (hf t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (hv.comp hfn hfu).congr fun t ht => (hf t ht).deriv

namespace IsMIntegralCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- An integral curve of an infinitely smooth vector field on a boundaryless manifold is
infinitely smooth. -/
theorem contMDiff {γ : ℝ → M} {v : (x : M) → TangentSpace I x}
    (hγ : IsMIntegralCurve γ v)
    (hv : CMDiff ∞ (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
  rw [contMDiff_infty]
  intro n t₀
  rw [contMDiffAt_iff_target]
  refine ⟨hγ.continuous.continuousAt, ?_⟩
  apply ContDiffAt.contMDiffAt
  let c : ℝ → E := (extChartAt I (γ t₀)) ∘ γ
  change ContDiffAt ℝ n c t₀
  let v' : E → E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀)
      ((extChartAt I (γ t₀)).symm x) (v ((extChartAt I (γ t₀)).symm x))
  have hv' : ContDiffAt ℝ ∞ v' (extChartAt I (γ t₀) (γ t₀)) := by
    have hv₀ := hv.contMDiffAt (x := γ t₀)
    rw [contMDiffAt_iff] at hv₀
    exact (hv₀.2.contDiffAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)).snd
  obtain ⟨u, hxu, hvu⟩ := hv'.contDiffOn
    (mod_cast le_top : (n : ℕ∞ω) ≤ ∞) (by simp)
  have hcsrc : ∀ᶠ t in 𝓝 t₀, γ t ∈ (extChartAt I (γ t₀)).source :=
    hγ.continuous.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _)
  have hderiv : ∀ᶠ t in 𝓝 t₀, HasDerivAt c (v' (c t)) t :=
    (hγ.isMIntegralCurveAt t₀).eventually_hasDerivAt.and hcsrc |>.mono fun t ht => by
      apply ht.1.congr_deriv
      simp only [v', c, Function.comp_apply]
      rw [PartialEquiv.left_inv _ ht.2]
  have hcu : ∀ᶠ t in 𝓝 t₀, c t ∈ u :=
    ((continuousAt_extChartAt (γ t₀)).comp hγ.continuous.continuousAt).eventually hxu
  have hall : {t | HasDerivAt c (v' (c t)) t ∧ c t ∈ u} ∈ 𝓝 t₀ :=
    hderiv.and hcu
  obtain ⟨s, hsP, hsopen, hst₀⟩ := mem_nhds_iff.mp hall
  exact ((contDiffOn_succ_of_hasDerivAt_comp hsopen hvu (fun t ht => (hsP ht).2)
    (fun t ht => (hsP ht).1)).of_le (by exact_mod_cast Nat.le_succ n)).contDiffAt
      (hsopen.mem_nhds hst₀)

end IsMIntegralCurve

namespace IsMIntegralCurveOn

/-- Left translation preserves integral curves of a left-invariant vector field. -/
theorem const_mul_mulInvariantVectorField [LieGroup I (minSmoothness ℝ 3) G]
    {v : GroupLieAlgebra I G} {γ : ℝ → G} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s) (g : G) :
    IsMIntegralCurveOn (fun t ↦ g * γ t) (mulInvariantVectorField v) s := by
  intro t ht
  have hg : MDiffAt (fun x : G ↦ g * x) (γ t) :=
    (contMDiffAt_mul_left (n := minSmoothness ℝ 3)).mdifferentiableAt (by simp)
  have hder :
      (mfderiv% (fun x : G ↦ g * x) (γ t)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t)) := by
    have hvec : mfderiv% (fun x : G ↦ g * x) (γ t)
        (mulInvariantVectorField v (γ t)) = mulInvariantVectorField v (g * γ t) := by
      have hpull := congrFun (mpullback_mulInvariantVectorField g v) (γ t)
      have hcancel :
          mfderiv% (fun x : G ↦ g * x) (γ t)
              (mfderiv% (fun x : G ↦ g⁻¹ * x) (g * γ t)
                (mulInvariantVectorField v (g * γ t))) =
            mulInvariantVectorField v (g * γ t) := by
        rw [← mfderiv_comp_apply_of_eq (I' := I) (f := fun x : G ↦ g⁻¹ * x)
          (g := fun x : G ↦ g * x) (y := γ t) (g * γ t)
          ((contMDiffAt_mul_left (n := minSmoothness ℝ 3)).mdifferentiableAt (by simp))
          ((contMDiffAt_mul_left (n := minSmoothness ℝ 3)).mdifferentiableAt (by simp))
          (by simp)]
        have D : (fun x : G ↦ g * x) ∘ (fun x : G ↦ g⁻¹ * x) = id := by
          funext z
          simp
        rw [D, mfderiv_id, ContinuousLinearMap.id_apply]
      rw [← hpull, mpullback, inverse_mfderiv_mul_left]
      exact hcancel
    calc
      _ = (1 : ℝ →L[ℝ] ℝ).smulRight
          (mfderiv% (fun x : G ↦ g * x) (γ t) (mulInvariantVectorField v (γ t))) := by
        apply ContinuousLinearMap.ext
        intro c
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.smulRight_apply, map_smul]
      _ = _ := by rw [hvec]
  -- Write the translated curve as a composition so the manifold chain rule applies directly.
  change HasMFDerivAt[s] ((fun x : G ↦ g * x) ∘ γ) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (g * γ t)))
  rw [← hder]
  exact hg.hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)

end IsMIntegralCurveOn

namespace IsMIntegralCurve

/-- Left translation preserves global integral curves of a left-invariant vector field. -/
theorem const_mul_mulInvariantVectorField [LieGroup I (minSmoothness ℝ 3) G]
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
  · exact (isMIntegralCurve_mulInvariantIntegralCurve v 1).const_mul_mulInvariantVectorField x

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
