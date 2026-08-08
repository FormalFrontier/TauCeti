module

public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The boundary model of a Euclidean half-space

This file identifies the frontier of Mathlib's `(n + 1)`-dimensional manifold-with-boundary
model `𝓡∂ (n + 1)` with the boundaryless model `𝓡 n`.  Concretely, the frontier is the
coordinate hyperplane where the zeroth coordinate vanishes; deleting that coordinate gives a
continuous linear equivalence with `EuclideanSpace ℝ (Fin n)`.

The construction is the standard-model prerequisite for putting a manifold structure on the
boundary of a manifold modeled on a Euclidean half-space, as prescribed by Layer 1 of the
GeometricTopology roadmap.  The parametrization and projection API below is intended to let
boundary charts use this identification without unfolding its coordinate construction.
-/

public section

open Function Set

open scoped Manifold

namespace TauCeti

/-- The coordinate hyperplane which is the boundary of the `(n + 1)`-dimensional Euclidean
half-space. -/
def euclideanHalfSpaceBoundary (n : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) where
  carrier := {x | x 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    simp [hx, hy]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    simp [hx]

@[simp]
theorem mem_euclideanHalfSpaceBoundary {n : ℕ} {x : EuclideanSpace ℝ (Fin (n + 1))} :
    x ∈ euclideanHalfSpaceBoundary n ↔ x 0 = 0 :=
  Iff.rfl

private def euclideanHalfSpaceBoundaryLinearEquiv (n : ℕ) :
    euclideanHalfSpaceBoundary n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (Fin.tail x.1)
  invFun x := ⟨WithLp.toLp 2 (Fin.cons 0 x), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    simp only [WithLp.equiv_apply]
    exact (congrArg (fun z ↦ Fin.cons z (Fin.tail x.1.ofLp)) x.2.symm).trans
      (Fin.cons_self_tail x.1.ofLp)
  right_inv x := by
    apply (WithLp.equiv 2 _).injective
    exact @Fin.tail_cons n (fun _ ↦ ℝ) 0 x.ofLp
  map_add' x y := by
    apply (WithLp.equiv 2 _).injective
    exact funext fun _ ↦ rfl
  map_smul' c x := by
    apply (WithLp.equiv 2 _).injective
    exact funext fun _ ↦ rfl

private theorem euclideanHalfSpaceBoundaryLinearEquiv_apply {n : ℕ}
    (x : euclideanHalfSpaceBoundary n) (i : Fin n) :
    euclideanHalfSpaceBoundaryLinearEquiv n x i = x.1 i.succ :=
  rfl

private theorem euclideanHalfSpaceBoundaryLinearEquiv_symm_apply_zero {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ((euclideanHalfSpaceBoundaryLinearEquiv n).symm x).1 0 = 0 :=
  rfl

private theorem euclideanHalfSpaceBoundaryLinearEquiv_symm_apply_succ {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((euclideanHalfSpaceBoundaryLinearEquiv n).symm x).1 i.succ = x i :=
  rfl

/-- The continuous linear equivalence from the boundary hyperplane to its lower-dimensional
Euclidean model. -/
noncomputable def euclideanHalfSpaceBoundaryEquiv (n : ℕ) :
    euclideanHalfSpaceBoundary n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (euclideanHalfSpaceBoundaryLinearEquiv n).toContinuousLinearEquiv

@[simp]
theorem euclideanHalfSpaceBoundaryEquiv_apply {n : ℕ}
    (x : euclideanHalfSpaceBoundary n) (i : Fin n) :
    euclideanHalfSpaceBoundaryEquiv n x i = x.1 i.succ :=
  by
    simpa only [euclideanHalfSpaceBoundaryEquiv, LinearEquiv.coe_toContinuousLinearEquiv'] using
      euclideanHalfSpaceBoundaryLinearEquiv_apply x i

@[simp]
theorem euclideanHalfSpaceBoundaryEquiv_symm_apply_zero {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ((euclideanHalfSpaceBoundaryEquiv n).symm x).1 0 = 0 :=
  by
    simpa only [euclideanHalfSpaceBoundaryEquiv,
      LinearEquiv.coe_toContinuousLinearEquiv_symm'] using
      euclideanHalfSpaceBoundaryLinearEquiv_symm_apply_zero x

@[simp]
theorem euclideanHalfSpaceBoundaryEquiv_symm_apply_succ {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((euclideanHalfSpaceBoundaryEquiv n).symm x).1 i.succ = x i :=
  by
    simpa only [euclideanHalfSpaceBoundaryEquiv,
      LinearEquiv.coe_toContinuousLinearEquiv_symm'] using
      euclideanHalfSpaceBoundaryLinearEquiv_symm_apply_succ x i

/-- Insert a zero as the zeroth coordinate, parametrizing the boundary of a Euclidean
half-space by a Euclidean space of dimension one less. -/
noncomputable def euclideanHalfSpaceBoundaryParam (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (euclideanHalfSpaceBoundary n).subtypeL.comp
    (euclideanHalfSpaceBoundaryEquiv n).symm.toContinuousLinearMap

@[simp]
theorem euclideanHalfSpaceBoundaryParam_apply_zero {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryParam n x 0 = 0 :=
  by simpa only [euclideanHalfSpaceBoundaryParam, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe] using
      euclideanHalfSpaceBoundaryEquiv_symm_apply_zero x

@[simp]
theorem euclideanHalfSpaceBoundaryParam_apply_succ {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanHalfSpaceBoundaryParam n x i.succ = x i :=
  by simpa only [euclideanHalfSpaceBoundaryParam, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearEquiv.coe_coe] using
      euclideanHalfSpaceBoundaryEquiv_symm_apply_succ x i

private def euclideanHalfSpaceBoundaryProjLinearMap (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun x ↦ WithLp.toLp 2 (Fin.tail x)
      map_add' := by
        intro x y
        apply (WithLp.equiv 2 _).injective
        exact funext fun _ ↦ rfl
      map_smul' := by
        intro c x
        apply (WithLp.equiv 2 _).injective
        exact funext fun _ ↦ rfl }

private theorem euclideanHalfSpaceBoundaryProjLinearMap_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    euclideanHalfSpaceBoundaryProjLinearMap n x i = x i.succ :=
  rfl

/-- Delete the zeroth coordinate of a point in `(n + 1)`-dimensional Euclidean space. -/
noncomputable def euclideanHalfSpaceBoundaryProj (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (euclideanHalfSpaceBoundaryProjLinearMap n)

@[simp]
theorem euclideanHalfSpaceBoundaryProj_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    euclideanHalfSpaceBoundaryProj n x i = x i.succ :=
  by
    simpa only [euclideanHalfSpaceBoundaryProj, LinearMap.coe_toContinuousLinearMap'] using
      euclideanHalfSpaceBoundaryProjLinearMap_apply x i

@[simp]
theorem euclideanHalfSpaceBoundaryProj_param {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryProj n (euclideanHalfSpaceBoundaryParam n x) = x := by
  ext i
  simp

theorem euclideanHalfSpaceBoundaryParam_proj {n : ℕ}
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ euclideanHalfSpaceBoundary n) :
    euclideanHalfSpaceBoundaryParam n (euclideanHalfSpaceBoundaryProj n x) = x := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using hx.symm
  · simp

@[simp]
theorem euclideanHalfSpaceBoundaryParam_proj_eq_iff {n : ℕ}
    {x : EuclideanSpace ℝ (Fin (n + 1))} :
    euclideanHalfSpaceBoundaryParam n (euclideanHalfSpaceBoundaryProj n x) = x ↔
      x ∈ euclideanHalfSpaceBoundary n := by
  constructor
  · intro h
    rw [← h]
    simp
  · exact euclideanHalfSpaceBoundaryParam_proj

theorem euclideanHalfSpaceBoundaryParam_injective (n : ℕ) :
    Function.Injective (euclideanHalfSpaceBoundaryParam n) :=
  fun _ _ h ↦ by simpa using congrArg (euclideanHalfSpaceBoundaryProj n) h

@[simp]
theorem range_euclideanHalfSpaceBoundaryParam (n : ℕ) :
    range (euclideanHalfSpaceBoundaryParam n) = euclideanHalfSpaceBoundary n := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    exact ⟨euclideanHalfSpaceBoundaryProj n x,
      euclideanHalfSpaceBoundaryParam_proj hx⟩

/-- The coordinate hyperplane is the frontier of Mathlib's Euclidean half-space model. -/
theorem euclideanHalfSpaceBoundary_eq_frontier (n : ℕ) :
    (euclideanHalfSpaceBoundary n : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      frontier (range (modelWithCornersEuclideanHalfSpace (n + 1))) := by
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  ext x
  simp [eq_comm]

end TauCeti
