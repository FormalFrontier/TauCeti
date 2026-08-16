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
boundary charts use this identification without unfolding its coordinate construction.  The file
also splits the ambient Euclidean space into boundary and normal coordinates; the boundary
inclusion and the standard product collar both use this one coordinate equivalence.
-/

public section

open Function Set

open scoped Manifold

namespace TauCeti

/-- Identify `EuclideanSpace ℝ (Fin n) × ℝ` with `EuclideanSpace ℝ (Fin (n + 1))` by
placing the real factor in the zeroth coordinate.  The first factor parametrizes the boundary
hyperplane and the second is its normal coordinate. -/
noncomputable def euclideanHalfSpaceBoundaryNormalEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin n)) ℝ).trans <|
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin n) ℝ)).trans <|
      (Fin.consEquivL ℝ (fun _ : Fin (n + 1) ↦ ℝ)).trans
        (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm

/-- The boundary-normal equivalence places the normal coordinate in coordinate zero. -/
@[simp]
theorem euclideanHalfSpaceBoundaryNormalEquiv_apply_zero (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    euclideanHalfSpaceBoundaryNormalEquiv n (x, r) 0 = r := by
  simp [euclideanHalfSpaceBoundaryNormalEquiv]

/-- The boundary-normal equivalence places the boundary coordinates after coordinate zero. -/
@[simp]
theorem euclideanHalfSpaceBoundaryNormalEquiv_apply_succ (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (i : Fin n) :
    euclideanHalfSpaceBoundaryNormalEquiv n (x, r) i.succ = x i := by
  simp [euclideanHalfSpaceBoundaryNormalEquiv]

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

/-- Insert a zero as the zeroth coordinate, parametrizing the boundary of a Euclidean
half-space by a Euclidean space of dimension one less. -/
noncomputable def euclideanHalfSpaceBoundaryParam (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (euclideanHalfSpaceBoundaryNormalEquiv n).toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)

@[simp]
theorem euclideanHalfSpaceBoundaryParam_apply_zero {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryParam n x 0 = 0 :=
  by simp [euclideanHalfSpaceBoundaryParam]

@[simp]
theorem euclideanHalfSpaceBoundaryParam_apply_succ {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanHalfSpaceBoundaryParam n x i.succ = x i :=
  by simp [euclideanHalfSpaceBoundaryParam]

/-- The boundary-normal equivalence at normal coordinate zero is the boundary parametrization. -/
@[simp]
theorem euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryNormalEquiv n (x, 0) =
      euclideanHalfSpaceBoundaryParam n x := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- Delete the zeroth coordinate of a point in `(n + 1)`-dimensional Euclidean space. -/
noncomputable def euclideanHalfSpaceBoundaryProj (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp
    (euclideanHalfSpaceBoundaryNormalEquiv n).symm.toContinuousLinearMap

@[simp]
theorem euclideanHalfSpaceBoundaryProj_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    euclideanHalfSpaceBoundaryProj n x i = x i.succ :=
  by
    rw [euclideanHalfSpaceBoundaryProj, ContinuousLinearMap.comp_apply]
    -- `comp_apply` leaves the bundled first projection; expose its product application.
    change ((euclideanHalfSpaceBoundaryNormalEquiv n).symm x).1 i = x i.succ
    rw [← euclideanHalfSpaceBoundaryNormalEquiv_apply_succ n
      ((euclideanHalfSpaceBoundaryNormalEquiv n).symm x).1
      ((euclideanHalfSpaceBoundaryNormalEquiv n).symm x).2 i]
    exact congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i.succ)
      ((euclideanHalfSpaceBoundaryNormalEquiv n).apply_symm_apply x)

/-- The boundary component of the inverse boundary-normal equivalence deletes coordinate zero. -/
@[simp]
theorem euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_fst (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    ((euclideanHalfSpaceBoundaryNormalEquiv n).symm y).1 =
      euclideanHalfSpaceBoundaryProj n y := by
  ext i
  rw [euclideanHalfSpaceBoundaryProj_apply]
  symm
  calc
    y i.succ = euclideanHalfSpaceBoundaryNormalEquiv n
        ((euclideanHalfSpaceBoundaryNormalEquiv n).symm y) i.succ :=
      congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z i.succ)
        ((euclideanHalfSpaceBoundaryNormalEquiv n).apply_symm_apply y).symm
    _ = ((euclideanHalfSpaceBoundaryNormalEquiv n).symm y).1 i :=
      euclideanHalfSpaceBoundaryNormalEquiv_apply_succ ..

/-- The normal component of the inverse boundary-normal equivalence is coordinate zero. -/
@[simp]
theorem euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    ((euclideanHalfSpaceBoundaryNormalEquiv n).symm y).2 = y 0 := by
  symm
  calc
    y 0 = euclideanHalfSpaceBoundaryNormalEquiv n
        ((euclideanHalfSpaceBoundaryNormalEquiv n).symm y) 0 :=
      congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z 0)
        ((euclideanHalfSpaceBoundaryNormalEquiv n).apply_symm_apply y).symm
    _ = ((euclideanHalfSpaceBoundaryNormalEquiv n).symm y).2 :=
      euclideanHalfSpaceBoundaryNormalEquiv_apply_zero ..

@[simp]
theorem euclideanHalfSpaceBoundaryProj_param {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryProj n (euclideanHalfSpaceBoundaryParam n x) = x := by
  ext i
  simp

@[simp]
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

namespace EuclideanHalfSpace

variable {n : ℕ}

/-- Parametrize the boundary of the `(n + 1)`-dimensional Euclidean half-space by inserting a
zero as the zeroth coordinate. -/
noncomputable def boundaryParam (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanHalfSpace (n + 1) :=
  fun x ↦ ⟨euclideanHalfSpaceBoundaryParam n x, by simp⟩

/-- Delete the zeroth coordinate of a point of the `(n + 1)`-dimensional Euclidean half-space. -/
noncomputable def boundaryProj (n : ℕ) :
    EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin n) :=
  fun y ↦ euclideanHalfSpaceBoundaryProj n y.1

/-- The parametrized boundary point, read in the ambient Euclidean space. -/
@[simp]
theorem boundaryParam_coe (x : EuclideanSpace ℝ (Fin n)) :
    (boundaryParam n x).1 = euclideanHalfSpaceBoundaryParam n x := (rfl)

/-- The boundary projection agrees with the ambient linear projection. -/
@[simp]
theorem boundaryProj_coe (y : EuclideanHalfSpace (n + 1)) :
    boundaryProj n y = euclideanHalfSpaceBoundaryProj n y.1 := (rfl)

/-- The coordinates of the boundary projection are the positive-index coordinates. -/
theorem boundaryProj_apply (y : EuclideanHalfSpace (n + 1)) (i : Fin n) :
    boundaryProj n y i = y.1 i.succ := by
  rw [boundaryProj_coe, euclideanHalfSpaceBoundaryProj_apply]

/-- Deleting the zeroth coordinate undoes the boundary parametrization. -/
theorem boundaryProj_boundaryParam (x : EuclideanSpace ℝ (Fin n)) :
    boundaryProj n (boundaryParam n x) = x := by
  rw [boundaryProj_coe, boundaryParam_coe, euclideanHalfSpaceBoundaryProj_param]

/-- On the boundary of the half-space, deleting and reinserting the zeroth coordinate is the
identity. -/
@[simp]
theorem boundaryParam_boundaryProj {y : EuclideanHalfSpace (n + 1)} (hy : y.1 0 = 0) :
    boundaryParam n (euclideanHalfSpaceBoundaryProj n y.1) = y :=
  Subtype.ext (euclideanHalfSpaceBoundaryParam_proj (mem_euclideanHalfSpaceBoundary.2 hy))

/-- The boundary parametrization is continuous. -/
theorem continuous_boundaryParam : Continuous (boundaryParam n) :=
  (euclideanHalfSpaceBoundaryParam n).continuous.subtype_mk _

/-- The boundary projection is continuous. -/
theorem continuous_boundaryProj : Continuous (boundaryProj n) :=
  (euclideanHalfSpaceBoundaryProj n).continuous.comp continuous_subtype_val

/-- The inverse of the model map `𝓡∂ (n + 1)` sends the parametrized coordinate hyperplane to the
boundary parametrization. -/
@[simp]
theorem modelWithCornersEuclideanHalfSpace_symm_boundaryParam
    (x : EuclideanSpace ℝ (Fin n)) :
    (𝓡∂ (n + 1)).symm (euclideanHalfSpaceBoundaryParam n x) = boundaryParam n x := by
  refine Subtype.ext ?_
  rw [modelWithCornersEuclideanHalfSpace_symm_apply]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- The coordinate hyperplane lies in the range of the half-space model. -/
theorem boundaryParam_mem_range (x : EuclideanSpace ℝ (Fin n)) :
    euclideanHalfSpaceBoundaryParam n x ∈ range (𝓡∂ (n + 1)) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  simp

end EuclideanHalfSpace

/-- The boundary of the Euclidean half-space, viewed as a manifold over itself, is the coordinate
hyperplane where the zeroth coordinate vanishes. -/
@[simp]
theorem boundary_euclideanHalfSpace (n : ℕ) :
    (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1)) = {y | y.1 0 = 0} := by
  ext y
  rw [ModelWithCorners.boundary, mem_ofPred_eq, ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  simp [extChartAt, chartAt_self_eq, eq_comm]

end TauCeti
