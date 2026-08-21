/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Topology.Algebra.Homeomorph.Congr

/-!
# Transporting the self-diffeomorphism group along a diffeomorphism

A diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` conjugates self-diffeomorphisms of `M` into
self-diffeomorphisms of `N` by `φ ↦ e ∘ φ ∘ e⁻¹`. Because this preserves composition, it is a
group isomorphism `Diff I M n ≃* Diff J N n` between the self-diffeomorphism groups built in
`TauCeti.Geometry.Diffeomorphism.Group`. This file records that isomorphism,
`Diffeomorph.diffCongr`, its pointwise action, and its functoriality: it is the identity on
`Diffeomorph.refl`, respects `Diffeomorph.trans` and `Diffeomorph.symm`, and commutes with the
forgetful homomorphism to the permutation group (`Diffeomorph.toPerm`) through Mathlib's
`Equiv.permCongr`.

This expresses that the *algebraic* group object of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology") is a diffeomorphism invariant: diffeomorphic manifolds have isomorphic
self-diffeomorphism groups as abstract groups. The construction is purely algebraic and stops at the
bare group isomorphism; it does *not yet* carry the `C^∞` topology, so on its own it says nothing
about homotopy type. Transporting the homotopy-type statements the layer targets — the Smale
conjecture `Diff(S³) ≃ O(4)`, `[Kir97, Problem 4.34]`, and Watanabe's `π_k(Diff(D⁴, ∂))` classes,
`[Kir97, Problem 4.126]` — needs the refinement of this isomorphism to a topological-group (indeed
homeomorphism) isomorphism, which is a separate, later layer-3 deliverable. It works for every
smoothness exponent `n`.

The construction is the diffeomorphism analogue of `Equiv.permCongr`
(`Mathlib/Logic/Equiv/Defs.lean`), the conjugation isomorphism of permutation groups, and reuses it
for the naturality statement.

## Main definitions

* `TauCeti.Diffeomorph.diffCongr e`: the group isomorphism `Diff I M n ≃* Diff J N n` conjugating by
  a diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N`.

The analogous self-homeomorphism-group isomorphism `TauCeti.Homeomorph.homeoCongr`, the target of
the forgetful naturality below, lives in `TauCeti.Topology.Algebra.Homeomorph.Congr`.

## Main results

* `TauCeti.Diffeomorph.diffCongr_apply_apply`: the pointwise action
  `diffCongr e φ x = e (φ (e.symm x))`.
* `TauCeti.Diffeomorph.diffCongr_refl`: conjugating by the identity is the identity isomorphism.
* `TauCeti.Diffeomorph.diffCongr_trans`: `diffCongr` turns `Diffeomorph.trans` into
  `MulEquiv.trans`, so it is functorial on the groupoid of diffeomorphisms.
* `TauCeti.Diffeomorph.diffCongr_symm`: the inverse isomorphism conjugates by `e.symm`.
* `TauCeti.Diffeomorph.toHomeomorphHom_comp_diffCongr` and
  `TauCeti.Diffeomorph.toPerm_comp_diffCongr`: naturality of `diffCongr` against the forgetful
  homomorphisms `toHomeomorphHom` and `toPerm`, as commutative squares of group homomorphisms
  intertwining `diffCongr` with `Homeomorph.homeoCongr` and `Equiv.permCongrHom` respectively.
* `TauCeti.Diffeomorph.toHomeomorph_diffCongr` and `TauCeti.Diffeomorph.toPerm_diffCongr`: the
  elementwise shadows of those squares.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

namespace Diffeomorph

/-- Conjugation by a diffeomorphism `e : M ≃ₘ^n⟮I, J⟯ N` as a group isomorphism between the
self-diffeomorphism groups: `diffCongr e φ = e ∘ φ ∘ e⁻¹`. This is the diffeomorphism analogue of
`Equiv.permCongr` and expresses that diffeomorphic manifolds have isomorphic self-diffeomorphism
groups. -/
@[expose] def diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) : (M ≃ₘ^n⟮I, I⟯ M) ≃* (N ≃ₘ^n⟮J, J⟯ N) where
  toFun φ := (e.symm.trans φ).trans e
  invFun ψ := (e.trans ψ).trans e.symm
  left_inv φ := by
    ext x
    simp [_root_.Diffeomorph.coe_trans]
  right_inv ψ := by
    ext x
    simp [_root_.Diffeomorph.coe_trans]
  map_mul' φ ψ := by
    ext x
    simp [mul_def, _root_.Diffeomorph.coe_trans]

/-- The conjugating isomorphism acts pointwise by `diffCongr e φ x = e (φ (e.symm x))`. -/
@[simp, grind =]
theorem diffCongr_apply_apply (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) (x : N) :
    diffCongr e φ x = e (φ (e.symm x)) := rfl

/-- The underlying diffeomorphism of `diffCongr e φ` is `e ∘ φ ∘ e⁻¹`. -/
theorem diffCongr_apply (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    diffCongr e φ = (e.symm.trans φ).trans e := rfl

/-- The inverse of `diffCongr e φ` is `diffCongr e φ⁻¹`, since conjugation is a homomorphism. -/
theorem diffCongr_inv (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    (diffCongr e φ)⁻¹ = diffCongr e φ⁻¹ := (map_inv (diffCongr e) φ).symm

/-- Conjugating by the identity diffeomorphism is the identity isomorphism. -/
@[simp]
theorem diffCongr_refl :
    diffCongr (_root_.Diffeomorph.refl I M n) = MulEquiv.refl (M ≃ₘ^n⟮I, I⟯ M) := by
  ext φ x
  simp

/-- Conjugation is functorial: conjugating by a composite diffeomorphism is the composite of the
conjugating isomorphisms. -/
@[simp]
theorem diffCongr_trans (e : M ≃ₘ^n⟮I, J⟯ N) (e' : N ≃ₘ^n⟮J, K⟯ P) :
    diffCongr (e.trans e') = (diffCongr e).trans (diffCongr e') := by
  ext φ x
  simp [_root_.Diffeomorph.coe_trans, _root_.Diffeomorph.symm_trans']

/-- The isomorphism conjugating by `e.symm` is the inverse of the one conjugating by `e`. -/
@[simp, grind =]
theorem diffCongr_symm (e : M ≃ₘ^n⟮I, J⟯ N) : (diffCongr e).symm = diffCongr e.symm := by
  ext ψ x
  rfl

/-- Naturality of `diffCongr` against the forgetful homomorphism to self-homeomorphisms, as a
commutative square of group homomorphisms: conjugating diffeomorphisms by `e` and then forgetting
smoothness equals forgetting smoothness and then conjugating homeomorphisms by `e` through
`Homeomorph.homeoCongr`. This is the naturality of `diffCongr` against the stronger forgetful
homomorphism `Diffeomorph.toHomeomorphHom`, refining `toPerm_comp_diffCongr`. -/
theorem toHomeomorphHom_comp_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) :
    toHomeomorphHom.comp (diffCongr e).toMonoidHom =
      (Homeomorph.homeoCongr e.toHomeomorph).toMonoidHom.comp toHomeomorphHom := by
  ext φ x
  simp [toHomeomorphHom_apply]

/-- Naturality of `diffCongr` against the forgetful homomorphism to permutations, as a commutative
square of group homomorphisms intertwining `diffCongr` with `Equiv.permCongrHom`; this is the
`toPerm`-level shadow of `toHomeomorphHom_comp_diffCongr`. -/
theorem toPerm_comp_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) :
    toPerm.comp (diffCongr e).toMonoidHom = e.toEquiv.permCongrHom.toMonoidHom.comp toPerm := by
  ext φ x
  simp [Equiv.permCongr_apply]

/-- Forgetting only smoothness (keeping the topology) sends `diffCongr e φ` to the conjugate of
underlying self-homeomorphisms `e ∘ φ ∘ e⁻¹`; the elementwise shadow of
`toHomeomorphHom_comp_diffCongr`. -/
theorem toHomeomorph_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    (diffCongr e φ).toHomeomorph =
      (e.toHomeomorph.symm.trans φ.toHomeomorph).trans e.toHomeomorph := by
  have h := DFunLike.congr_fun (toHomeomorphHom_comp_diffCongr e) φ
  simpa using h

/-- Forgetting all topology intertwines `diffCongr` with `Equiv.permCongr` on the permutation
groups; the elementwise shadow of `toPerm_comp_diffCongr`. -/
theorem toPerm_diffCongr (e : M ≃ₘ^n⟮I, J⟯ N) (φ : M ≃ₘ^n⟮I, I⟯ M) :
    toPerm (diffCongr e φ) = e.toEquiv.permCongr (toPerm φ) := by
  have h := DFunLike.congr_fun (toPerm_comp_diffCongr e) φ
  simpa using h

end Diffeomorph

end TauCeti
