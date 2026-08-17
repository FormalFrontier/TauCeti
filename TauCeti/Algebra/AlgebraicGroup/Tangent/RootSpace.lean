/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Cotangent

/-!
# Weight spaces of the adjoint representation

Let `G = Spec H` be an affine group scheme over `R` whose augmentation cotangent space is finite
projective, so that its Lie algebra is the single `R`-module
`Module.Dual R (Bialgebra.CotangentSpace R H)` carrying the adjoint comodule of
`TauCeti.Algebra.AlgebraicGroup.Tangent.Representation`. Let `π : H →ₐc[R] R[M]` be a morphism of
coordinate bialgebras, that is, a homomorphism `D(M) → G` of affine group schemes out of the
diagonalizable group on a commutative group `M` written multiplicatively.

Restricting the adjoint representation along `π` decomposes the Lie algebra into weight
submodules, indexed by `M`. This file names them: `adjointWeightSpace π α` is the `α`-weight
submodule `𝔤_α`, `nontrivialAdjointWeights π` is the set of nontrivial characters whose weight
submodule is nonzero, and the Lie algebra is spanned by `𝔤_1` together with the `𝔤_α` for
`α ∈ nontrivialAdjointWeights π`. A point of `D(M)` acts on `𝔤_α` by the value of `α` at that
point, and the Lie bracket sends `𝔤_α × 𝔤_β` into `𝔤_{αβ}`.

Nothing here asserts that `π` is a closed immersion, that `D(M)` is a torus, let alone a maximal
one, or that `G` is reductive. When `π` does exhibit a split maximal torus `T` in a reductive `G`,
`nontrivialAdjointWeights π` is the set of roots of the split pair `(G, T)`.

## Main definitions

* `TauCeti.Derivation.adjointWeightSpace`: the `α`-weight submodule `𝔤_α` of the Lie algebra of
  `G` under a homomorphism from a diagonalizable group.
* `TauCeti.Derivation.nontrivialAdjointWeights`: the nontrivial characters whose adjoint weight
  submodule is nonzero.

## Main results

* `TauCeti.Derivation.isInternal_adjointWeightSpace`: **the Lie algebra of `G` is the internal
  direct sum of its weight submodules.**
* `TauCeti.Derivation.sup_iSup_adjointWeightSpace_eq_top`: the trivial weight submodule together
  with the submodules indexed by `nontrivialAdjointWeights π` exhaust the Lie algebra.
* `TauCeti.Derivation.finite_nontrivialAdjointWeights`: **the set of nontrivial adjoint weights is
  finite.**
* `TauCeti.Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace`: a point of `D(M)` acts on the
  `α`-weight submodule by the value of `α` at that point.
* `TauCeti.Derivation.lie_mem_adjointWeightSpace_mul`: the adjoint weight decomposition is a Lie
  grading: `[𝔤_α, 𝔤_β] ⊆ 𝔤_{αβ}`.

## Roadmap

Layer 7 of `TauCetiRoadmap/ReductiveGroups/README.md` asks for the root datum
`(X*(T), Φ, X_*(T), Φ^∨)` of a split pair `(G, T)`, taking the split case first. The character and
cocharacter lattices with their pairing are already in
`TauCeti.Algebra.AlgebraicGroup.Cocharacter`; this file supplies the weight decomposition that
`Φ` is read off, the remaining piece of the root datum that comes from the group rather than the
torus. Layer 9's split reductive group
schemes over `ℤ` take the split maximal torus as part of their data and are defined by conditions
on exactly this decomposition, and milestone `L0` of `TauCetiRoadmap/CFSGStatement/README.md`
consumes those pinned Chevalley--Demazure groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1 (the roots of a split reductive group).
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* B. Conrad, *Reductive Group Schemes* (SGA3 exposition), §3.2.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace Derivation

attribute [local instance] Classical.decEq
attribute [local instance] adjointComodule

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]
variable {M : Type w} [CommGroup M]

/-- The `α`-weight submodule `𝔤_α` of the Lie algebra of `G = Spec H` under a homomorphism
`D(M) → G` with coordinate morphism `π`: the part of the Lie algebra on which `D(M)` acts through
the character `α`. -/
noncomputable def adjointWeightSpace (π : H →ₐc[R] MonoidAlgebra R M) (α : M) :
    Submodule R (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M) α

/-- Membership in the `α`-weight submodule, in terms of the adjoint coaction: pushing the adjoint
coaction of `x` through `π` must give `x ⊗ α`. -/
@[simp]
theorem mem_adjointWeightSpace {π : H →ₐc[R] MonoidAlgebra R M} {α : M}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)} :
    x ∈ adjointWeightSpace π α ↔
      TensorProduct.map LinearMap.id (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap
          (Comodule.coact (R := R) (C := H)
            (M := Module.Dual R (Bialgebra.CotangentSpace R H)) x) =
        x ⊗ₜ[R] MonoidAlgebra.single α (1 : R) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.mem_weightSpace

/-- **The Lie algebra of `G` is the internal direct sum of its weight submodules under a
homomorphism from a diagonalizable group.** -/
theorem isInternal_adjointWeightSpace (π : H →ₐc[R] MonoidAlgebra R M) :
    DirectSum.IsInternal (adjointWeightSpace π) :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.isInternal_weightSpace (Module.Dual R (Bialgebra.CotangentSpace R H))
    (π : H →ₗc[R] MonoidAlgebra R M)

/-- The nontrivial characters of `D(M)` whose adjoint weight submodule in the Lie algebra of `G`
is nonzero. When `π` exhibits a split maximal torus `T` in a reductive `G`, these are the roots of
the split pair `(G, T)`. -/
def nontrivialAdjointWeights (π : H →ₐc[R] MonoidAlgebra R M) : Set M :=
  {α | α ≠ 1 ∧ adjointWeightSpace π α ≠ ⊥}

@[simp]
theorem mem_nontrivialAdjointWeights {π : H →ₐc[R] MonoidAlgebra R M} {α : M} :
    α ∈ nontrivialAdjointWeights π ↔ α ≠ 1 ∧ adjointWeightSpace π α ≠ ⊥ :=
  Iff.rfl

/-- Off the nontrivial adjoint weights and the trivial character the weight submodule vanishes. -/
theorem adjointWeightSpace_eq_bot_of_notMem_nontrivialAdjointWeights
    {π : H →ₐc[R] MonoidAlgebra R M} {α : M} (hα : α ≠ 1)
    (h : α ∉ nontrivialAdjointWeights π) : adjointWeightSpace π α = ⊥ := by
  by_contra hbot
  exact h ⟨hα, hbot⟩

/-- **The set of nontrivial adjoint weights is finite.** The Lie algebra is finitely generated, so
only finitely many weight submodules are nonzero. -/
theorem finite_nontrivialAdjointWeights (π : H →ₐc[R] MonoidAlgebra R M) :
    (nontrivialAdjointWeights π).Finite :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  Set.Finite.subset
    (DiagonalizableGroup.finite_setOf_weightSpace_ne_bot
      (Module.Dual R (Bialgebra.CotangentSpace R H)) (π : H →ₗc[R] MonoidAlgebra R M))
    fun _ hα => hα.2

/-- **The Lie algebra is spanned by the trivial weight submodule together with the submodules
indexed by the nontrivial adjoint weights.** -/
theorem sup_iSup_adjointWeightSpace_eq_top (π : H →ₐc[R] MonoidAlgebra R M) :
    (adjointWeightSpace π 1 ⊔
      ⨆ α ∈ nontrivialAdjointWeights π, adjointWeightSpace π α) = ⊤ := by
  refine top_unique ?_
  rw [← (isInternal_adjointWeightSpace π).submodule_iSup_eq_top]
  refine iSup_le fun α => ?_
  by_cases hα : α = 1
  · subst hα
    exact le_sup_left
  · by_cases hbot : adjointWeightSpace π α = ⊥
    · rw [hbot]
      exact bot_le
    · exact le_sup_of_le_right
        (le_iSup₂ (f := fun β (_ : β ∈ nontrivialAdjointWeights π) => adjointWeightSpace π β)
          α ⟨hα, hbot⟩)

/-- **A point of `D(M)` acts on the `α`-weight submodule `𝔤_α` by the value of the character
`α` at that point.** -/
theorem endOfPoint_tmul_of_mem_adjointWeightSpace {A : Type*} [CommSemiring A] [Algebra R A]
    (π : H →ₐc[R] MonoidAlgebra R M) (f : MonoidAlgebra R M →ₐ[R] A) (a : A) {α : M}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)} (hx : x ∈ adjointWeightSpace π α) :
    Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H))
        (f.comp (π : H →ₐ[R] MonoidAlgebra R M)) (a ⊗ₜ[R] x) =
      (a * f (MonoidAlgebra.single α (1 : R))) ⊗ₜ[R] x :=
  letI : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace
    (Module.Dual R (Bialgebra.CotangentSpace R H)) π f a hx

private theorem map_universalAdjointAction_eq_single_of_mem_adjointWeightSpace
    {π : H →ₐc[R] MonoidAlgebra R M} {α : M}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hx : x ∈ adjointWeightSpace π α) :
    TensorProduct.map
        ((π : H →ₗc[R] MonoidAlgebra R M).toLinearMap ∘ₗ
          (ULift.algEquiv (R := R) : ULift.{max u v} H ≃ₐ[R] H).toLinearMap)
        LinearMap.id
        ((adjointAction (CommAlgCat.of R (ULift.{max u v} H))
          (WithConv.toConv (ULift.algEquiv (R := R)).symm.toAlgHom)).val
            (1 ⊗ₜ[R] x)) =
      MonoidAlgebra.single α 1 ⊗ₜ[R] x := by
  let : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  have h := endOfPoint_tmul_of_mem_adjointWeightSpace π
    (AlgHom.id R (MonoidAlgebra R M)) 1 hx
  rw [Comodule.endOfPoint_tmul] at h
  simp only [one_smul] at h
  rw [adjointComodule_coact_apply, adjointPointRepresentation_action] at h
  rw [LinearMap.lTensor_def, ← TensorProduct.map_comm] at h
  simp only [AlgHom.id_comp, AlgHom.id_apply, one_mul, TensorProduct.comm_comm,
    TensorProduct.map_map, LinearMap.comp_id] at h
  have hπ : (π : H →ₐ[R] MonoidAlgebra R M).toLinearMap =
      (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_coe]
    exact BialgHom.toAlgHom_toLinearMap π
  rw [hπ] at h
  exact h

/-- **The bracket of an `α`-weight vector and a `β`-weight vector has weight `α * β`.**

For a split pair this is the root-space grading relation
`[𝔤_α, 𝔤_β] ⊆ 𝔤_{αβ}` (with characters written multiplicatively). -/
theorem lie_mem_adjointWeightSpace_mul {π : H →ₐc[R] MonoidAlgebra R M} {α β : M}
    {x y : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hx : x ∈ adjointWeightSpace π α) (hy : y ∈ adjointWeightSpace π β) :
    ⁅x, y⁆ ∈ adjointWeightSpace π (α * β) := by
  rw [mem_adjointWeightSpace]
  let U := ULift.{max u v} H
  let A := CommAlgCat.of R U
  let g : HopfAlgebra.points (H := H) A :=
    WithConv.toConv (ULift.algEquiv (R := R)).symm.toAlgHom
  let q : U →ₐ[R] MonoidAlgebra R M :=
    (π : H →ₐ[R] MonoidAlgebra R M).comp
      (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toAlgHom
  have hπ : (π : H →ₐ[R] MonoidAlgebra R M).toLinearMap =
      (π : H →ₗc[R] MonoidAlgebra R M).toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_coe]
    exact BialgHom.toAlgHom_toLinearMap π
  have hq : q.toLinearMap =
      ((π : H →ₗc[R] MonoidAlgebra R M).toLinearMap ∘ₗ
        (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toLinearMap) := by
    -- Unfold `q`: `AlgHom.comp` has no theorem exposing its underlying linear map.
    change
      ((π : H →ₐ[R] MonoidAlgebra R M).toLinearMap ∘ₗ
          (ULift.algEquiv (R := R) : U ≃ₐ[R] H).toLinearMap) = _
    rw [hπ]
  have hx' :
      TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] x)) =
        MonoidAlgebra.single α 1 ⊗ₜ[R] x := by
    rw [hq]
    exact map_universalAdjointAction_eq_single_of_mem_adjointWeightSpace hx
  have hy' :
      TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] y)) =
        MonoidAlgebra.single β 1 ⊗ₜ[R] y := by
    rw [hq]
    exact map_universalAdjointAction_eq_single_of_mem_adjointWeightSpace hy
  have hbracket := adjointAction_bracket A g (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)
  have hmapped := congrArg
    (LieAlgebra.ExtendScalars.map q
      (LieHom.id : Module.Dual R (Bialgebra.CotangentSpace R H) →ₗ⁅R⁆
        Module.Dual R (Bialgebra.CotangentSpace R H))) hbracket
  rw [LieHom.map_lie] at hmapped
  simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] at hmapped
  -- `ExtendScalars.map` exposes this tensor map only through its `LieHom` coercion.
  change
    TensorProduct.map q.toLinearMap LinearMap.id
        ((adjointAction A g).val (1 ⊗ₜ[R] ⁅x, y⁆)) =
      ⁅TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] x)),
        TensorProduct.map q.toLinearMap LinearMap.id
          ((adjointAction A g).val (1 ⊗ₜ[R] y))⁆ at hmapped
  rw [hx', hy'] at hmapped
  simp only [LieAlgebra.ExtendScalars.bracket_tmul,
    MonoidAlgebra.single_mul_single, one_mul] at hmapped
  rw [adjointComodule_coact_apply, adjointPointRepresentation_action]
  apply (TensorProduct.comm R (Module.Dual R (Bialgebra.CotangentSpace R H))
    (MonoidAlgebra R M)).injective
  rw [← TensorProduct.map_comm]
  simp only [TensorProduct.comm_comm, TensorProduct.map_map,
    LinearMap.comp_id, TensorProduct.comm_tmul]
  rw [hq] at hmapped
  exact hmapped

end Derivation

end TauCeti
