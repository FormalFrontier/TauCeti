/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Diffeomorphism.Group

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

The orthogonal group appears here in its coordinate-free form, the group `E ≃ₗᵢ[ℝ] E` of linear
isometry equivalences, rather than as Mathlib's matrix group `Matrix.orthogonalGroup`; the two
are related by `LinearIsometryEquiv.toMatrix_mem_unitaryGroup`, and packaging that comparison as
a group isomorphism is separate work that belongs upstream.

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
* `TauCeti.LinearIsometryEquiv.eq_of_eqOn_unitSphere`: a linear isometry equivalence is
  determined by its values on the unit sphere, whence
  `TauCeti.LinearIsometryEquiv.unitSphereDiffHom_injective`: the inclusion is injective, so
  `O(n + 1)` is realised as a subgroup of `Diff(Sⁿ)`.

## Implementation notes

The declarations below live in `TauCeti.LinearIsometryEquiv`, mirroring the Mathlib namespace of
the objects they are about, so they are applied in prefix form (`unitSphereEquiv e`) rather than
by dot notation.
-/

public section

namespace TauCeti

open Metric Module
open scoped Manifold ContDiff

namespace LinearIsometryEquiv

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear isometry equivalence preserves the unit sphere: it maps unit vectors to unit vectors,
and nothing else to unit vectors. -/
theorem map_mem_unitSphere_iff (e : E ≃ₗᵢ[ℝ] E) (x : E) :
    e x ∈ sphere (0 : E) 1 ↔ x ∈ sphere (0 : E) 1 := by
  simp

/-- A linear isometry equivalence of `E` restricts to a self-equivalence of the unit sphere. -/
@[expose]
def unitSphereEquiv (e : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ sphere (0 : E) 1 :=
  e.toEquiv.subtypeEquiv fun x => (map_mem_unitSphere_iff e x).symm

@[simp]
theorem coe_unitSphereEquiv_apply (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    (unitSphereEquiv e x : E) = e x :=
  rfl

@[simp]
theorem unitSphereEquiv_symm (e : E ≃ₗᵢ[ℝ] E) :
    (unitSphereEquiv e).symm = unitSphereEquiv e.symm :=
  rfl

@[simp]
theorem unitSphereEquiv_refl :
    unitSphereEquiv (_root_.LinearIsometryEquiv.refl ℝ E) = Equiv.refl (sphere (0 : E) 1) :=
  rfl

theorem unitSphereEquiv_trans (e e' : E ≃ₗᵢ[ℝ] E) :
    unitSphereEquiv (e.trans e') = (unitSphereEquiv e).trans (unitSphereEquiv e') :=
  rfl

/-- The restriction of a linear isometry equivalence to the unit sphere is an isometry for the
distance the sphere inherits from `E`: the action of `O(n + 1)` on `Sⁿ` is by isometries of the
round sphere. -/
theorem isometry_unitSphereEquiv (e : E ≃ₗᵢ[ℝ] E) : Isometry (unitSphereEquiv e) :=
  Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]

/-- A linear isometry equivalence is determined by its values on the unit sphere, since every
nonzero vector is a positive multiple of a unit vector. -/
theorem eq_of_eqOn_unitSphere {e e' : E ≃ₗᵢ[ℝ] E} (h : Set.EqOn e e' (sphere (0 : E) 1)) :
    e = e' := by
  ext v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hmem : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hnorm]
    have hsmul : ‖v‖⁻¹ • e v = ‖v‖⁻¹ • e' v := by simpa using h hmem
    exact smul_right_injective E (inv_ne_zero hnorm) hsmul

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] {m : ℕ∞ω}

/-- The restriction of a linear isometry equivalence to the unit sphere is `C^m`, for every
smoothness exponent `m`: it is the corestriction to the sphere of a continuous linear map
precomposed with the analytic inclusion of the sphere. -/
theorem contMDiff_unitSphereEquiv (e : E ≃ₗᵢ[ℝ] E) :
    ContMDiff (𝓡 n) (𝓡 n) m (unitSphereEquiv e) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, E) m fun x : sphere (0 : E) 1 => e (x : E) :=
    (e.toContinuousLinearEquiv : E →L[ℝ] E).contDiff.comp_contMDiff contMDiff_coe_sphere
  exact h.codRestrict_sphere fun x => (map_mem_unitSphere_iff e _).2 x.2

/-- The diffeomorphism of the unit sphere induced by a linear isometry equivalence of `E`. -/
@[expose]
def unitSphereDiffeomorph (e : E ≃ₗᵢ[ℝ] E) (m : ℕ∞ω) :
    sphere (0 : E) 1 ≃ₘ^m⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 where
  toEquiv := unitSphereEquiv e
  contMDiff_toFun := contMDiff_unitSphereEquiv e
  contMDiff_invFun := contMDiff_unitSphereEquiv e.symm

@[simp]
theorem coe_unitSphereDiffeomorph_apply (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    ((unitSphereDiffeomorph (n := n) e m x : sphere (0 : E) 1) : E) = e x :=
  rfl

@[simp]
theorem unitSphereDiffeomorph_toEquiv (e : E ≃ₗᵢ[ℝ] E) :
    (unitSphereDiffeomorph (n := n) e m).toEquiv = unitSphereEquiv e :=
  rfl

@[simp]
theorem unitSphereDiffeomorph_symm (e : E ≃ₗᵢ[ℝ] E) :
    (unitSphereDiffeomorph (n := n) e m).symm = unitSphereDiffeomorph e.symm m :=
  rfl

/-- The antipodal map of the unit sphere is the diffeomorphism induced by `-1`, the element of
`O(n + 1)` given by `LinearIsometryEquiv.neg`. In particular Mathlib's `contMDiff_neg_sphere` is
the case `e = -1` of `contMDiff_unitSphereEquiv`. -/
theorem unitSphereDiffeomorph_neg_apply (x : sphere (0 : E) 1) :
    unitSphereDiffeomorph (n := n) (_root_.LinearIsometryEquiv.neg ℝ) m x = -x := by
  ext
  simp

/-- The inclusion of the linear isometry group of `E` into the group of self-diffeomorphisms of
its unit sphere. For `E = EuclideanSpace ℝ (Fin (n + 1))` this is the reference inclusion
`O(n + 1) → Diff(Sⁿ)`; see `TauCeti.orthogonalToDiffSphere`. -/
@[expose]
def unitSphereDiffHom (m : ℕ∞ω) :
    (E ≃ₗᵢ[ℝ] E) →* Diff (𝓡 n) (sphere (0 : E) 1) m where
  toFun e := unitSphereDiffeomorph e m
  map_one' := _root_.Diffeomorph.ext fun _ => rfl
  map_mul' _ _ := _root_.Diffeomorph.ext fun _ => rfl

@[simp]
theorem unitSphereDiffHom_apply (e : E ≃ₗᵢ[ℝ] E) :
    unitSphereDiffHom (E := E) (n := n) m e = unitSphereDiffeomorph e m :=
  rfl

/-- The inclusion of the linear isometry group into the diffeomorphism group of the unit sphere is
injective, so `O(n + 1)` is realised as a subgroup of `Diff(Sⁿ)`. -/
theorem unitSphereDiffHom_injective :
    Function.Injective (unitSphereDiffHom (E := E) (n := n) m) := by
  intro e e' h
  rw [unitSphereDiffHom_apply, unitSphereDiffHom_apply] at h
  refine eq_of_eqOn_unitSphere fun x hx => ?_
  simpa using congrArg Subtype.val (DFunLike.congr_fun h ⟨x, hx⟩)

end InnerProduct

end LinearIsometryEquiv

open scoped EuclideanSpace

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)`: an orthogonal transformation of `ℝⁿ⁺¹`
restricts to a diffeomorphism of the unit sphere `Sⁿ`, and this restriction is a group
homomorphism. Here `O(n + 1)` appears in its coordinate-free form, as the group
`EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))` of linear isometry
equivalences of `(n + 1)`-dimensional Euclidean space. It is injective by
`TauCeti.LinearIsometryEquiv.unitSphereDiffHom_injective`. -/
@[expose]
noncomputable def orthogonalToDiffSphere (n : ℕ) (m : ℕ∞ω) :
    (EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) →*
      Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m :=
  LinearIsometryEquiv.unitSphereDiffHom m

/-- The reference inclusion `O(n + 1) → Diff(Sⁿ)` sends an orthogonal transformation to its
restriction to the unit sphere. -/
@[simp]
theorem orthogonalToDiffSphere_apply (n : ℕ) (m : ℕ∞ω)
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    orthogonalToDiffSphere n m e = LinearIsometryEquiv.unitSphereDiffHom m e :=
  rfl

end TauCeti
