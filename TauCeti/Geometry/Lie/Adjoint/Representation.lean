/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Adjoint.Smooth
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Smoothness of the group adjoint representation

The tangent adjoint action is jointly smooth. This file transports that result across the
canonical isometric identification between left-invariant derivations and the tangent space at the
identity, proving smoothness for the roadmap-facing group adjoint `Ad`.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `TauCeti.Lie.adjointRepresentation`: the group adjoint as a bundled representation.
* `TauCeti.Lie.continuousAdjointRepresentation`: the same representation valued in bounded
  operators.
* `TauCeti.Lie.contMDiff_Ad_apply`: the joint action `(g, X) ↦ Ad g X` is smooth.
* `TauCeti.Lie.contMDiff_continuousAdjointRepresentation`: the bounded-operator-valued
  representation is smooth.
* `TauCeti.Lie.contMDiff_adjointRepresentation_apply`: the bundled representation acts smoothly.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree

/-- Lie groups have no manifold boundary because every point is interior. -/
local instance lieGroupBoundarylessManifoldAdjointRepresentation : BoundarylessManifold I G where
  isInteriorPoint' g :=
    ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) g

/-- The normed additive structure transported from the finite-dimensional tangent Lie algebra. -/
local instance lieGroupNormedAddCommGroupAdjointRepresentation :
    NormedAddCommGroup (LeftInvariantDerivation I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  exact LeftInvariantDerivation.instNormedAddCommGroup

/-- The normed-space structure transported from the finite-dimensional tangent Lie algebra. -/
local instance lieGroupNormedSpaceAdjointRepresentation :
    NormedSpace ℝ (LeftInvariantDerivation I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  exact LeftInvariantDerivation.instNormedSpace

/-- Left-invariant derivations are finite-dimensional under the Lie-group hypotheses. -/
local instance lieGroupFiniteDimensionalAdjointRepresentation :
    FiniteDimensional ℝ (LeftInvariantDerivation I G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  exact finiteDimensional_leftInvariantDerivation
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))

/-- The adjoint representation valued in bounded operators. -/
def continuousAdjointRepresentation :
    ContRepresentation ℝ G (LeftInvariantDerivation I G) where
  toMonoidHom :=
    { toFun := fun g ↦ LinearMap.toContinuousLinearMap
        (Ad (I := I) g).toLinearEquiv.toLinearMap
      map_one' := by
        ext D
        simp
      map_mul' := by
        intro g h
        ext D
        rw [Ad_mul]
        rfl }

/-- The adjoint representation of a Lie group on its algebra of left-invariant derivations. -/
def adjointRepresentation :
    Representation ℝ G (LeftInvariantDerivation I G) :=
  (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation

@[simp]
theorem adjointRepresentation_apply (g : G) (D : LeftInvariantDerivation I G) :
    adjointRepresentation (I := I) g D = Ad (I := I) g D := by
  change LinearMap.toContinuousLinearMap
    (Ad (I := I) g).toLinearEquiv.toLinearMap D = Ad (I := I) g D
  rfl

@[simp]
theorem continuousAdjointRepresentation_apply (g : G) (D : LeftInvariantDerivation I G) :
    continuousAdjointRepresentation (I := I) g D = Ad (I := I) g D := by
  exact adjointRepresentation_apply g D

/-- The group adjoint action on left-invariant derivations is jointly smooth. -/
theorem contMDiff_Ad_apply :
    ContMDiff (I.prod 𝓘(ℝ, LeftInvariantDerivation I G))
      𝓘(ℝ, LeftInvariantDerivation I G) ∞
      (fun p : G × LeftInvariantDerivation I G ↦ Ad (I := I) p.1 p.2) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let e := leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G)
  have hin : ContMDiff
      (I.prod 𝓘(ℝ, LeftInvariantDerivation I G)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : G × LeftInvariantDerivation I G ↦ (p.1, e p.2)) :=
    contMDiff_fst.prodMk (e.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_snd)
  have hout : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, LeftInvariantDerivation I G) ∞ e.symm :=
    e.symm.toContinuousLinearEquiv.contDiff.contMDiff
  apply (hout.comp (contMDiff_tangentAd_apply (I := I) (G := G))).comp hin |>.congr
  intro p
  simp only [Function.comp_apply]
  rw [Ad_apply]
  rw [leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply]
  let v : E := show E from
    tangentAd (I := I) p.1 ((e p.2 : E) : GroupLieAlgebra I G)
  change tangentToLeftInvariantDerivation _ = e.symm v
  dsimp only [e]
  rw [leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_apply]
  congr 1
  dsimp only [v, e]
  rw [leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_apply]

/-- The bounded-operator-valued adjoint representation is smooth. -/
theorem contMDiff_continuousAdjointRepresentation :
    ContMDiff I
      𝓘(ℝ, LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G) ∞
      (continuousAdjointRepresentation (I := I) (G := G)) := by
  let b := Module.Free.chooseBasis ℝ (LeftInvariantDerivation I G)
  let eLin :
      (LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G) ≃ₗ[ℝ]
        (Module.Free.ChooseBasisIndex ℝ (LeftInvariantDerivation I G) →
          LeftInvariantDerivation I G) :=
    LinearMap.toContinuousLinearMap.symm.trans (b.constr ℝ).symm
  let e := eLin.toContinuousLinearEquiv
  have heval (T : LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G)
      (i : Module.Free.ChooseBasisIndex ℝ (LeftInvariantDerivation I G)) :
      e T i = T (b i) := by
    change ((b.constr ℝ).symm (LinearMap.toContinuousLinearMap.symm T)) i = T (b i)
    rw [Module.Basis.constr_symm_apply]
    rfl
  have he : ContMDiff I 𝓘(ℝ,
      Module.Free.ChooseBasisIndex ℝ (LeftInvariantDerivation I G) →
        LeftInvariantDerivation I G) ∞
      (e ∘ continuousAdjointRepresentation (I := I) (G := G)) := by
    rw [contMDiff_pi_space]
    intro i
    have hpair : ContMDiff I
        (I.prod 𝓘(ℝ, LeftInvariantDerivation I G)) ∞
        (fun g : G => (g, b i)) := contMDiff_id.prodMk contMDiff_const
    have h := (contMDiff_Ad_apply (I := I) (G := G)).comp hpair
    apply h.congr
    intro g
    rw [Function.comp_apply, heval, continuousAdjointRepresentation_apply]
    rfl
  have hback := e.symm.contDiff.contMDiff.comp he
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hback

/-- The action map of the bundled adjoint representation is jointly smooth. -/
theorem contMDiff_adjointRepresentation_apply :
    ContMDiff (I.prod 𝓘(ℝ, LeftInvariantDerivation I G))
      𝓘(ℝ, LeftInvariantDerivation I G) ∞
      (fun p : G × LeftInvariantDerivation I G ↦
        adjointRepresentation (I := I) p.1 p.2) := by
  simpa only [adjointRepresentation_apply] using
    contMDiff_Ad_apply (I := I) (G := G)

end TauCeti.Lie
