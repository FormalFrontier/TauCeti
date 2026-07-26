/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.LinearAlgebra.OrthogonalGroup

/-!
# The orthogonal group acts on the sphere by diffeomorphisms

A linear isometry equivalence of a real inner product space `E` preserves norms, so it restricts
to a self-map of the unit sphere; this file shows that restriction is a diffeomorphism of the
sphere as an analytic manifold, and assembles the restrictions into a group homomorphism
`(E ≃ₗᵢ[ℝ] E) →* Diff (𝓡 n) (sphere (0 : E) 1) m` into the self-diffeomorphism group of
`TauCeti.Geometry.Diffeomorphism.Group`. Taking `E = EuclideanSpace ℝ (Fin (n + 1))`, whose
linear isometry group is the orthogonal group `O(n + 1)`, this is the reference inclusion
`O(n + 1) → Diff(Sⁿ)`.

That inclusion is the last item asked for by layer 3 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology"): "The reference inclusion `O(n+1) → Diff(Sⁿ)` (consume `Matrix.orthogonalGroup`,
layer 7's isometry action, and the sphere instance) as a continuous group homomorphism". The
roadmap wants it *continuous* for the `C^∞` topology on `Diff(Sⁿ)`, and that topology is a
separate layer-3 deliverable which does not exist yet, so this file builds the group
homomorphism and stops there; continuity is a statement to add once the topology lands. It is
also the map whose source and target the Smale conjecture `Diff(S³) ≃ O(4)`
(`[Kir97, Problem 4.34]`, Hatcher) compares, and the roadmap's acceptance criterion "the
inclusion `O(4) → Diff(S³)` is stateable" is `TauCeti.orthogonalToDiffSphere 3 ω`.

## Main definitions

* `TauCeti.LinearIsometryEquiv.unitSphereEquiv`: the self-equivalence of the unit sphere
  obtained by restricting a linear isometry equivalence.
* `TauCeti.LinearIsometryEquiv.unitSphereDiffeomorph`: that restriction as a `C^m`
  diffeomorphism of the unit sphere, viewed as a manifold modelled on `𝓡 n`.
* `TauCeti.LinearIsometryEquiv.unitSphereDiffHom`: the group homomorphism
  `(E ≃ₗᵢ[ℝ] E) →* Diff (𝓡 n) (sphere (0 : E) 1) m`.
* `TauCeti.orthogonalToDiffSphere`: the reference inclusion `O(n + 1) → Diff(Sⁿ)`, the case
  `E = EuclideanSpace ℝ (Fin (n + 1))` of `unitSphereDiffHom`.

## Main results

* `TauCeti.LinearIsometryEquiv.contMDiff_unitSphereEquiv`: the restriction to the unit sphere is
  `C^m` for every smoothness exponent.
* `TauCeti.LinearIsometryEquiv.isometry_unitSphereEquiv`: it is an isometry for the distance the
  sphere inherits from `E`, so the action is by isometries of the round sphere.
* `TauCeti.LinearIsometryEquiv.unitSphereDiffeomorph_neg_apply`: the diffeomorphism induced by
  `-1 ∈ O(n + 1)` is the antipodal map.
* `TauCeti.LinearMap.eq_of_eqOn_unitSphere`: a linear map is
  determined by its values on the unit sphere, whence
  `TauCeti.LinearIsometryEquiv.unitSphereDiffHom_injective` and
  `TauCeti.orthogonalToDiffSphere_injective`: the inclusion is injective, so `O(n + 1)` is
  realised as a subgroup of `Diff(Sⁿ)`.

## Implementation notes

The declarations below and the generic unit-sphere API in
`TauCeti.Geometry.Sphere.LinearIsometry` live in `TauCeti.LinearIsometryEquiv`, mirroring the
Mathlib namespace of the objects they are about, so they are applied in prefix form
(`unitSphereEquiv e`) rather than by dot notation.
-/

public section

namespace TauCeti

open Metric Module
open scoped Manifold ContDiff

namespace LinearIsometryEquiv

section InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {n k : ℕ} [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)] {m : ℕ∞ω}

/-- The restriction of a linear isometry equivalence to the unit sphere is `C^m`, for every
smoothness exponent `m`. -/
theorem contMDiff_unitSphereEquiv (e : E ≃ₗᵢ[ℝ] F) :
    ContMDiff (𝓡 n) (𝓡 k) m (unitSphereEquiv e) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, F) m fun x : sphere (0 : E) 1 => e (x : E) :=
    (e.toContinuousLinearEquiv : E →L[ℝ] F).contDiff.comp_contMDiff contMDiff_coe_sphere
  refine (h.codRestrict_sphere (n := k) fun x =>
    (map_mem_unitSphere_iff e _).2 x.2).congr fun x => ?_
  exact Subtype.ext (coe_unitSphereEquiv_apply e x)

/-- The diffeomorphism between unit spheres induced by a linear isometry equivalence. -/
def unitSphereDiffeomorph (e : E ≃ₗᵢ[ℝ] F) (m : ℕ∞ω) :
    sphere (0 : E) 1 ≃ₘ^m⟮𝓡 n, 𝓡 k⟯ sphere (0 : F) 1 where
  toEquiv := unitSphereEquiv e
  contMDiff_toFun := contMDiff_unitSphereEquiv e
  contMDiff_invFun := by
    simpa only [unitSphereEquiv_symm] using
      (contMDiff_unitSphereEquiv (n := k) (k := n) e.symm)

@[simp]
theorem coe_unitSphereDiffeomorph_apply (e : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1) :
    ((unitSphereDiffeomorph (n := n) (k := k) e m x : sphere (0 : F) 1) : F) = e x :=
  coe_unitSphereEquiv_apply e x

@[simp]
theorem unitSphereDiffeomorph_toEquiv (e : E ≃ₗᵢ[ℝ] F) :
    (unitSphereDiffeomorph (n := n) (k := k) e m).toEquiv = unitSphereEquiv e :=
  (rfl)

@[simp]
theorem unitSphereDiffeomorph_symm (e : E ≃ₗᵢ[ℝ] F) :
    (unitSphereDiffeomorph (n := n) (k := k) e m).symm =
      unitSphereDiffeomorph (n := k) (k := n) e.symm m :=
  _root_.Diffeomorph.ext fun x => Equiv.congr_fun (by
    rw [_root_.Diffeomorph.symm_toEquiv, unitSphereDiffeomorph_toEquiv,
      unitSphereDiffeomorph_toEquiv,
      unitSphereEquiv_symm]) x

/-- The antipodal map of the unit sphere is the diffeomorphism induced by `-1`, the element of
`O(n + 1)` given by `LinearIsometryEquiv.neg`. In particular Mathlib's `contMDiff_neg_sphere` is
the case `e = -1` of `contMDiff_unitSphereEquiv`. -/
theorem unitSphereDiffeomorph_neg_apply (x : sphere (0 : E) 1) :
    unitSphereDiffeomorph (n := n) (k := n) (_root_.LinearIsometryEquiv.neg ℝ) m x = -x := by
  ext
  simp

/-- The inclusion of the linear isometry group of `E` into the group of self-diffeomorphisms of
its unit sphere. For `E = EuclideanSpace ℝ (Fin (n + 1))` this is the reference inclusion
`O(n + 1) → Diff(Sⁿ)`; see `TauCeti.orthogonalToDiffSphere`. -/
def unitSphereDiffHom (m : ℕ∞ω) :
    (E ≃ₗᵢ[ℝ] E) →* Diff (𝓡 n) (sphere (0 : E) 1) m where
  toFun e := unitSphereDiffeomorph e m
  map_one' := _root_.Diffeomorph.ext fun x => by
    apply Subtype.ext
    simp
  map_mul' _ _ := _root_.Diffeomorph.ext fun x => by
    apply Subtype.ext
    simp

@[simp]
theorem unitSphereDiffHom_apply (e : E ≃ₗᵢ[ℝ] E) :
    unitSphereDiffHom (E := E) (n := n) m e = unitSphereDiffeomorph e m :=
  _root_.Diffeomorph.ext fun _ => rfl

/-- The inclusion of the linear isometry group into the diffeomorphism group of the unit sphere is
injective, so `O(n + 1)` is realised as a subgroup of `Diff(Sⁿ)`. -/
theorem unitSphereDiffHom_injective :
    Function.Injective (unitSphereDiffHom (E := E) (n := n) m) := by
  intro e e' h
  rw [unitSphereDiffHom_apply, unitSphereDiffHom_apply] at h
  apply _root_.LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.eq_of_eqOn_unitSphere fun x hx => ?_
  simpa using congrArg Subtype.val (DFunLike.congr_fun h ⟨x, hx⟩)

end InnerProduct

end LinearIsometryEquiv

open scoped EuclideanSpace

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)`: an orthogonal transformation of `ℝⁿ⁺¹`
restricts to a diffeomorphism of the unit sphere `Sⁿ`, and this restriction is a group
homomorphism. It is injective by `TauCeti.orthogonalToDiffSphere_injective`. -/
noncomputable def orthogonalToDiffSphere (n : ℕ) (m : ℕ∞ω) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ →*
      Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m :=
  (LinearIsometryEquiv.unitSphereDiffHom m).comp
    orthogonalGroupToLinearIsometryEquiv

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)` sends an orthogonal transformation to its
restriction to the unit sphere. -/
@[simp]
theorem orthogonalToDiffSphere_apply (n : ℕ) (m : ℕ∞ω)
    (A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    orthogonalToDiffSphere n m A =
      LinearIsometryEquiv.unitSphereDiffHom m (orthogonalGroupToLinearIsometryEquiv A) :=
  (rfl)

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)` is injective, so `O(n + 1)` is realised as a
subgroup of `Diff(Sⁿ)`. -/
theorem orthogonalToDiffSphere_injective (n : ℕ) (m : ℕ∞ω) :
    Function.Injective (orthogonalToDiffSphere n m) := by
  exact LinearIsometryEquiv.unitSphereDiffHom_injective.comp
    orthogonalGroupToLinearIsometryEquiv_injective

end TauCeti
