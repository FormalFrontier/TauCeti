/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Boundary.Model

/-!
# The product collar of a Euclidean half-space

This file identifies the standard `(n + 1)`-dimensional Euclidean half-space with the product of
its `n`-dimensional boundary model and the one-dimensional Euclidean half-space.  It is the model
calculation behind collar charts: the last factor is the inward normal coordinate, and its zero
slice is exactly the boundary parametrization from `Boundary.Model`.

The equivalence is constructed first in the ambient Euclidean spaces by splitting off the zeroth
coordinate.  Restricting it to the half-spaces gives a homeomorphism and, with Mathlib's product
model-with-corners structure, a diffeomorphism.  The characteristic lemmas record both coordinate
projections and identify the zero slice, so later collar constructions do not need to unfold the
coordinate implementation.

This is the standard-model prerequisite for the collar-neighbourhood target in Layer 1 of the
GeometricTopology roadmap.  The global collar theorem requires patching these local product
coordinates on an arbitrary manifold and is not proved here.

## Main definitions

* `EuclideanHalfSpace.collarAmbientEquiv`: the continuous linear coordinate splitting on ambient
  Euclidean spaces.
* `EuclideanHalfSpace.collarHomeomorph`: the resulting homeomorphism from boundary times inward
  normal coordinate to the half-space.
* `EuclideanHalfSpace.collarDiffeomorph`: the same identification as a diffeomorphism of manifolds
  with corners.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Theorem 6.1.
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

/-- Split off the zeroth coordinate of `(n + 1)`-dimensional Euclidean space, with the
`n`-dimensional factor first and the one-dimensional normal factor second. -/
def collarAmbientEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
      ((EuclideanSpace.equiv (Fin 1) ℝ).trans
        (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)))).trans
    (euclideanHalfSpaceBoundaryNormalEquiv n)

/-- The ambient collar equivalence places the inward normal coordinate in coordinate zero. -/
@[simp]
theorem collarAmbientEquiv_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin 1)) : collarAmbientEquiv n (x, t) 0 = t 0 := by
  simp [collarAmbientEquiv]

/-- The ambient collar equivalence places the boundary coordinates after coordinate zero. -/
@[simp]
theorem collarAmbientEquiv_apply_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin 1)) (i : Fin n) :
    collarAmbientEquiv n (x, t) i.succ = x i := by
  simp [collarAmbientEquiv]

/-- The boundary component of the inverse ambient collar equivalence deletes coordinate zero. -/
@[simp]
theorem collarAmbientEquiv_symm_apply_fst (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) : ((collarAmbientEquiv n).symm y).1 =
      euclideanHalfSpaceBoundaryProj n y := by
  exact euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_fst n y

/-- The inverse ambient collar equivalence recovers the inward normal coordinate at zero. -/
@[simp]
theorem collarAmbientEquiv_symm_apply_snd_apply_zero (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) : ((collarAmbientEquiv n).symm y).2 0 = y 0 := by
  exact euclideanHalfSpaceBoundaryNormalEquiv_symm_apply_snd n y

/-- The product of the boundary Euclidean space and an inward half-line is homeomorphic to the
Euclidean half-space.  The second factor is the inward normal coordinate. -/
def collarHomeomorph (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace (n + 1) where
  toFun p := ⟨collarAmbientEquiv n (p.1, p.2.1), by simpa using p.2.2⟩
  invFun y :=
    ((collarAmbientEquiv n).symm y.1 |>.1,
      ⟨(collarAmbientEquiv n).symm y.1 |>.2, by
        simpa using y.2⟩)
  left_inv p := by
    -- Expose the two subtype-valued coordinate maps so the ambient inverse law can be applied.
    change
      (((collarAmbientEquiv n).symm (collarAmbientEquiv n (p.1, p.2.1))).1,
        ⟨((collarAmbientEquiv n).symm (collarAmbientEquiv n (p.1, p.2.1))).2, _⟩) = p
    have h := (collarAmbientEquiv n).symm_apply_apply (p.1, p.2.1)
    have hfst : ((collarAmbientEquiv n).symm
        (collarAmbientEquiv n (p.1, p.2.1))).1 = p.1 :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦ q.1) h
    have hsnd : ((collarAmbientEquiv n).symm
        (collarAmbientEquiv n (p.1, p.2.1))).2 = p.2.1 :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦ q.2) h
    exact Prod.ext hfst (Subtype.ext hsnd)
  right_inv y := by
    apply Subtype.ext
    exact (collarAmbientEquiv n).apply_symm_apply y.1
  continuous_toFun :=
    Continuous.subtype_mk
      ((collarAmbientEquiv n).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _
  continuous_invFun :=
    (((collarAmbientEquiv n).symm.continuous.comp continuous_subtype_val).fst.prodMk <|
      Continuous.subtype_mk
        (((collarAmbientEquiv n).symm.continuous.comp continuous_subtype_val).snd) _)

/-- The underlying map of the collar homeomorphism is the restricted ambient equivalence. -/
theorem collarHomeomorph_coe (n : ℕ) :
    ((collarHomeomorph n : _ → _) :
      EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1 → EuclideanHalfSpace (n + 1)) =
      fun p ↦ ⟨collarAmbientEquiv n (p.1, p.2.1), by simpa using p.2.2⟩ :=
  by rfl

/-- The collar homeomorphism agrees with the ambient equivalence after coercion. -/
theorem collarHomeomorph_apply_coe (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (collarHomeomorph n p).1 = collarAmbientEquiv n (p.1, p.2.1) :=
  by rfl

/-- The collar homeomorphism sends the inward normal coordinate to coordinate zero. -/
@[simp]
theorem collarHomeomorph_apply_zero (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (collarHomeomorph n p).1 0 = p.2.1 0 := by
  rw [collarHomeomorph_apply_coe, collarAmbientEquiv_apply_zero]

/-- The collar homeomorphism sends the boundary coordinates to the positive coordinates. -/
@[simp]
theorem collarHomeomorph_apply_succ (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) (i : Fin n) :
    (collarHomeomorph n p).1 i.succ = p.1 i := by
  rw [collarHomeomorph_apply_coe, collarAmbientEquiv_apply_succ]

/-- The boundary component of the inverse collar homeomorphism is the boundary projection. -/
@[simp]
theorem collarHomeomorph_symm_apply_fst (n : ℕ) (y : EuclideanHalfSpace (n + 1)) :
    ((collarHomeomorph n).symm y).1 = boundaryProj n y := by
  rw [boundaryProj_coe]
  exact collarAmbientEquiv_symm_apply_fst n y.1

/-- The inverse collar homeomorphism recovers the inward normal coordinate at zero. -/
@[simp]
theorem collarHomeomorph_symm_apply_snd_apply_zero (n : ℕ)
    (y : EuclideanHalfSpace (n + 1)) : (collarHomeomorph n).symm y |>.2.1 0 = y.1 0 := by
  exact collarAmbientEquiv_symm_apply_snd_apply_zero n y.1

/-- The zero-normal slice of the collar homeomorphism is the boundary parametrization. -/
@[simp]
theorem collarHomeomorph_apply_zero_normal (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    collarHomeomorph n (x, (0 : EuclideanHalfSpace 1)) = boundaryParam n x := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [collarHomeomorph_apply_zero]
    -- The zeroth coordinate of the zero point is hidden behind the `WithLp` coercion.
    change (0 : ℝ) = _
    simp
  · rw [collarHomeomorph_apply_succ]
    simp

/-- The product collar identification is smooth in both directions for Mathlib's standard
models with corners. -/
def collarDiffeomorph (n : ℕ) :
    Diffeomorph ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) (EuclideanHalfSpace (n + 1)) ∞ where
  toEquiv := (collarHomeomorph n).toEquiv
  contMDiff_toFun := by
    rw [chartedSpaceSelf_prod]
    let I := (𝓡 n).prod (𝓡∂ 1)
    let J := 𝓡∂ (n + 1)
    have hcoord : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
        (collarAmbientEquiv n ∘ I) :=
      (collarAmbientEquiv n).contDiff.contMDiff.comp I.contMDiff
    have hrange : ∀ p, collarAmbientEquiv n (I p) ∈ range J := by
      intro p
      rw [range_modelWithCornersEuclideanHalfSpace]
      -- Unfold the product model only enough to expose its normal coordinate.
      change 0 ≤ collarAmbientEquiv n (p.1, p.2.1) 0
      simpa using p.2.2
    refine (J.contMDiffOn_symm.comp_contMDiff hcoord hrange).congr ?_
    intro p
    apply Subtype.ext
    -- Both sides are points of the half-space; compare their ambient model coordinates.
    change collarAmbientEquiv n (I p) = J (J.symm (collarAmbientEquiv n (I p)))
    exact (J.right_inv (hrange p)).symm
  contMDiff_invFun := by
    rw [chartedSpaceSelf_prod]
    let I := (𝓡 n).prod (𝓡∂ 1)
    let J := 𝓡∂ (n + 1)
    have hcoord : ContMDiff J 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) ∞
        ((collarAmbientEquiv n).symm ∘ J) :=
      (collarAmbientEquiv n).symm.contDiff.contMDiff.comp J.contMDiff
    have hrange : ∀ y, (collarAmbientEquiv n).symm (J y) ∈ range I := by
      intro y
      rw [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace]
      refine ⟨mem_range_self _, ?_⟩
      -- The range condition is precisely nonnegativity of the split normal coordinate.
      change 0 ≤ ((collarAmbientEquiv n).symm y.1).2 0
      simpa using y.2
    refine (I.contMDiffOn_symm.comp_contMDiff hcoord hrange).congr ?_
    intro y
    let q := I.symm ((collarAmbientEquiv n).symm (J y))
    have hright : I q = (collarAmbientEquiv n).symm (J y) := I.right_inv (hrange y)
    have hfst : q.1 = ((collarAmbientEquiv n).symm y.1).1 := by
      simp [q, I, J]
    have hsnd : q.2.1 = ((collarAmbientEquiv n).symm y.1).2 := by
      simpa [q, I, J, ModelWithCorners.prod_apply] using congrArg Prod.snd hright
    -- The composite produced by `contMDiffOn_symm` is the inverse homeomorphism by construction.
    change (collarHomeomorph n).symm y = q
    refine Prod.ext ?_ ?_
    · exact hfst.symm
    · apply Subtype.ext
      exact hsnd.symm

/-- The underlying homeomorphism of the collar diffeomorphism is `collarHomeomorph`. -/
@[simp]
theorem collarDiffeomorph_toHomeomorph (n : ℕ) :
    (collarDiffeomorph n).toHomeomorph = collarHomeomorph n := by
  ext p
  rfl

/-- The collar diffeomorphism sends the inward normal coordinate to coordinate zero. -/
@[simp]
theorem collarDiffeomorph_apply_zero (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (collarDiffeomorph n p).1 0 = p.2.1 0 := by
  rw [← (collarDiffeomorph n).coe_toHomeomorph]
  rw [collarDiffeomorph_toHomeomorph, collarHomeomorph_apply_zero]

/-- The collar diffeomorphism sends the boundary coordinates to the positive coordinates. -/
@[simp]
theorem collarDiffeomorph_apply_succ (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) (i : Fin n) :
    (collarDiffeomorph n p).1 i.succ = p.1 i := by
  rw [← (collarDiffeomorph n).coe_toHomeomorph]
  rw [collarDiffeomorph_toHomeomorph, collarHomeomorph_apply_succ]

/-- The boundary component of the inverse collar diffeomorphism is the boundary projection. -/
@[simp]
theorem collarDiffeomorph_symm_apply_fst (n : ℕ) (y : EuclideanHalfSpace (n + 1)) :
    ((collarDiffeomorph n).symm y).1 = boundaryProj n y := by
  rw [← (collarDiffeomorph n).coe_toHomeomorph_symm, collarDiffeomorph_toHomeomorph]
  exact collarHomeomorph_symm_apply_fst n y

/-- The inverse collar diffeomorphism recovers the inward normal coordinate at zero. -/
@[simp]
theorem collarDiffeomorph_symm_apply_snd_apply_zero (n : ℕ)
    (y : EuclideanHalfSpace (n + 1)) : ((collarDiffeomorph n).symm y).2.1 0 = y.1 0 := by
  rw [← (collarDiffeomorph n).coe_toHomeomorph_symm, collarDiffeomorph_toHomeomorph]
  exact collarHomeomorph_symm_apply_snd_apply_zero n y

/-- The zero-normal slice of the collar diffeomorphism is the boundary parametrization. -/
@[simp]
theorem collarDiffeomorph_apply_zero_normal (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    collarDiffeomorph n (x, (0 : EuclideanHalfSpace 1)) = boundaryParam n x := by
  rw [← (collarDiffeomorph n).coe_toHomeomorph]
  rw [collarDiffeomorph_toHomeomorph, collarHomeomorph_apply_zero_normal]

end TauCeti.EuclideanHalfSpace
