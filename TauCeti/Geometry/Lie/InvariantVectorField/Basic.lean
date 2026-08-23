/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import TauCeti.Geometry.Lie.Basic
public import TauCeti.Geometry.Manifold.VectorField.Regularity
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Invariant vector fields on Lie groups

This file records regularity properties of invariant vector fields expressed through Mathlib's
tangent Lie algebra. These results depend only on `GroupLieAlgebra`, not on the separate
left-invariant-derivation model of a Lie algebra. The regularity proofs reuse generic
tangent-bundle smoothness inputs from `TauCeti.Geometry.Manifold.VectorField.Regularity`.

## Main results

* `mulInvariantVectorField_one`: at the identity, an invariant vector field equals its generator.
* `contMDiff_tangentMap_mul_prod`: the tangent map of multiplication is smooth on a pair of
  tangent bundles.
* `tangentMap_mul_prod_apply`: the value of that tangent map is the sum of the two partial
  derivatives of multiplication.
* `mfderiv_mul_apply_one`: at the identity pair, the derivative of multiplication is addition.
* `mfderiv_mul_left_mulInvariantVectorField`: left translation intertwines a left-invariant vector
  field with itself.
* `contMDiff_tangentMap_mul_prod_comp`: regularity after feeding two smooth tangent-bundle inputs
  into the tangent map of multiplication.
* `contMDiff_mulInvariantVectorField_infty`: a left-invariant vector field on a smooth Lie group is
  smooth.
* `contMDiff_mulInvariantVectorField_modelSpace`: the invariant vector field is jointly `C^m` in
  its model-space generator and group argument when multiplication is `C^n` and `m + 1 ≤ n`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
* The proofs of `contMDiff_mulInvariantVectorField_modelSpace` and
  `contMDiff_mulInvariantVectorField_infty` adapt Sébastien Gouëzel's proof of Mathlib's
  `contMDiff_mulInvariantVectorField`.
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff LieGroup Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}

section Multiplication

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Mul G]

/-- The tangent map of multiplication, expressed on a pair of tangent bundles, is `C^m` when
multiplication is `C^n` and `m + 1 ≤ n`. -/
theorem contMDiff_tangentMap_mul_prod {m n : ℕ∞ω} [ContMDiffMul I n G]
    (hmn : m + 1 ≤ n) :
    let _ : IsManifold I 1 G := IsManifold.of_le (le_add_self.trans hmn)
    ContMDiff (I.tangent.prod I.tangent) I.tangent m
      ((tangentMap% (fun p : G × G => p.1 * p.2)) ∘
        (equivTangentBundleProd I G I G).symm) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (le_add_self.trans hmn)
  exact ((contMDiff_mul I n).contMDiff_tangentMap hmn).comp
    contMDiff_equivTangentBundleProd_symm

/-- The tangent map of multiplication is the sum of its two partial derivatives. -/
@[simp]
theorem tangentMap_mul_prod_apply [ContMDiffMul I 1 G] (p q : TangentBundle I G) :
    (tangentMap% (fun r : G × G => r.1 * r.2))
      ((equivTangentBundleProd I G I G).symm (p, q)) =
      ⟨p.proj * q.proj,
        mfderiv% (· * q.proj) p.proj p.2 + mfderiv% (p.proj * ·) q.proj q.2⟩ := by
  simp only [tangentMap]
  rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I 1).mdifferentiableAt (by simp))]
  simp +instances [equivTangentBundleProd]

end Multiplication

section MultiplicationAtOne

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- At the identity pair, the derivative of multiplication is addition on the tangent Lie
algebra. -/
theorem mfderiv_mul_apply_one [ContMDiffMul I 1 G] (v w : GroupLieAlgebra I G) :
    mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1, 1) : G × G) (v, w) =
      v + w := by
  have hmul_tangent := tangentMap_mul_prod_apply (I := I) (G := G)
    (⟨1, v⟩ : TangentBundle I G) (⟨1, w⟩ : TangentBundle I G)
  have hmul_apply := congrArg (fun z : TangentBundle I G => z.2) hmul_tangent
  -- Project the bundled tangent-map equation to its fiberwise `mfderiv` statement.
  change
    (mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1, 1) : G × G))
        (v, w) =
      (mfderiv I I (fun z : G => z * 1) 1) v +
        (mfderiv I I (fun z : G => 1 * z) 1) w at hmul_apply
  rw [show (fun z : G => z * 1) = id by funext z; simp,
    show (fun z : G => 1 * z) = id by funext z; simp, mfderiv_id] at hmul_apply
  exact hmul_apply

end MultiplicationAtOne

section TangentMapInputs

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Mul G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

/-- Composing the tangent map of multiplication with two smoothly varying tangent-bundle inputs
preserves the regularity allowed by multiplication. -/
theorem contMDiff_tangentMap_mul_prod_comp {m n : ℕ∞ω} [ContMDiffMul I n G]
    (hmn : m + 1 ≤ n) (f g : M → TangentBundle I G) :
    let _ : IsManifold I 1 G := IsManifold.of_le (le_add_self.trans hmn)
    ContMDiff J I.tangent m f →
      ContMDiff J I.tangent m g →
      ContMDiff J I.tangent m
        (fun p => (tangentMap% (fun q : G × G => q.1 * q.2))
          ((equivTangentBundleProd I G I G).symm (f p, g p))) := by
  dsimp only
  intro hf hg
  let _ : IsManifold I 1 G := IsManifold.of_le (le_add_self.trans hmn)
  simpa only [Function.comp_def] using
    (contMDiff_tangentMap_mul_prod (I := I) (G := G) hmn).comp (hf.prodMk hg)

end TangentMapInputs

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- At the identity, the invariant vector field generated by `v` equals `v`. -/
@[simp]
theorem mulInvariantVectorField_one (v : GroupLieAlgebra I G) :
    mulInvariantVectorField v (1 : G) = v := by
  -- Unfold the invariant field to expose the derivative of the identity map.
  change mfderiv I I (fun x : G ↦ 1 * x) 1 v = v
  rw [show (fun x : G ↦ 1 * x) = id by funext x; simp, mfderiv_id]
  rfl

/-- The derivative of left translation carries a left-invariant vector field to itself. -/
@[simp]
theorem mfderiv_mul_left_mulInvariantVectorField [ContMDiffMul I 1 G]
    (g x : G) (v : GroupLieAlgebra I G) :
    mfderiv I I (fun y : G ↦ g * y) x (mulInvariantVectorField v x) =
      mulInvariantVectorField v (g * x) := by
  simp only [mulInvariantVectorField]
  rw [← mfderiv_comp_apply_of_eq (I' := I) (f := fun y : G ↦ x * y)
    (g := fun y : G ↦ g * y) (y := x) (1 : G)
    (mdifferentiableAt_mul_left (a := g)) (mdifferentiableAt_mul_left (a := x)) (by simp)]
  rw [show (fun y : G ↦ g * y) ∘ (fun y : G ↦ x * y) =
      (fun y : G ↦ (g * x) * y) by
    funext y
    simp [mul_assoc]]

/-- In model coordinates, the invariant vector field is jointly `C^m` in its generating tangent
vector and the group point when multiplication is `C^n` and `m + 1 ≤ n`. -/
theorem contMDiff_mulInvariantVectorField_modelSpace {m n : ℕ∞ω}
    [ContMDiffMul I n G] (hmn : m + 1 ≤ n) :
    let _ : IsManifold I 1 G := IsManifold.of_le (le_add_self.trans hmn)
    ContMDiff (𝓘(𝕜, E).prod I) I.tangent m
      (fun p : E × G =>
        (mulInvariantVectorField (I := I) (G := G) p.1 p.2 : TangentBundle I G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (le_add_self.trans hmn)
  let fg : E × G → TangentBundle I G := fun p => TotalSpace.mk' E p.2 0
  have sfg : ContMDiff (𝓘(𝕜, E).prod I) I.tangent m fg := by
    simpa only [fg] using
      contMDiff_tangentBundle_mk_zero (I := I) (M := G) (n := m) contMDiff_snd
  let fv : E × G → TangentBundle I G := fun p => TotalSpace.mk' E 1 p.1
  have sfv : ContMDiff (𝓘(𝕜, E).prod I) I.tangent m fv := by
    simpa only [fv] using
      contMDiff_tangentBundle_mk_constBase (I := I) (M := G) (n := m) contMDiff_fst (1 : G)
  let S := contMDiff_tangentMap_mul_prod_comp (I := I) (G := G) hmn fg fv sfg sfv
  apply S.congr
  intro p
  let _ : ContMDiffMul I 1 G :=
    ContMDiffMul.of_le (m := 1) (n := n) (le_add_self.trans hmn)
  rw [tangentMap_mul_prod_apply]
  simp +instances only [mulInvariantVectorField, map_zero, zero_add, fg, fv]
  rw [mul_one]

/-- A left-invariant vector field on a smooth Lie group is smooth. -/
theorem contMDiff_mulInvariantVectorField_infty
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun g : G ↦ (mulInvariantVectorField v g : TangentBundle I G)) := by
  have h := contMDiff_mulInvariantVectorField_modelSpace
    (I := I) (G := G) (m := ∞) (n := ∞) (by simp)
  exact h.comp (contMDiff_const.prodMk contMDiff_id)
