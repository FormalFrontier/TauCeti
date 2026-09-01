/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The differential is a Lie algebra morphism

Precomposition of counit-valued derivations along a bialgebra morphism
(`TauCeti.derivationComp`) preserves the convolution commutator: the differential of a
morphism of affine monoid schemes is a morphism of Lie algebras (ReductiveGroups
roadmap, Layer 2, "the differential of a homomorphism"). The bracket identity uses
only the coalgebra half of the morphism — it intertwines the convolution products
termwise; the algebra half already entered in `derivationComp`, which needs
`d (φ (x * y)) = d (φ x * φ y)` to produce a derivation at all.

## Main declarations

* `TauCeti.derivationComp_bracket`: the differential preserves the bracket.
* `TauCeti.derivationCompLieHom`: the differential as a morphism of Lie algebras.
* `TauCeti.derivationCompLieHom_injective_of_surjective`: the differential of a surjective
  bialgebra morphism is injective.
* `TauCeti.derivationCompLieHom_bijective_of_surjective_of_finrank_eq`: a surjective
  bialgebra morphism between equal-dimensional tangent Lie algebras induces a bijection.
-/

public section

namespace TauCeti

open _root_.Coalgebra TensorProduct WithConv

section Bracket

variable {R A A' B : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  [CommSemiring A'] [Bialgebra R A']

section Transport

-- The transport step needs no more of `B` than `derivationComp` itself does; only the bracket
-- below, being a commutator, asks for a ring.
variable [Semiring B] [Algebra R B]

/-- **Precomposing both slots by `φ` is multiplication of the transported derivations.** The two
sides differ only by which counit coefficient algebra they are read in, and those are the same
`B`. -/
private theorem mul'_comp_map_derivationComp (φ : A' →ₐc[R] A)
    (e₁ e₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    LinearMap.mul' R (Bialgebra.CounitAlgebra R A B) ∘ₗ
        TensorProduct.map
          ((↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ
            (φ : A' →ₐ[R] A).toLinearMap)
          ((↑e₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ
            (φ : A' →ₐ[R] A).toLinearMap) =
      LinearMap.mul' R (Bialgebra.CounitAlgebra R A' B) ∘ₗ
        TensorProduct.map
          (↑(derivationComp (B := B) φ e₁) : A' →ₗ[R] Bialgebra.CounitAlgebra R A' B)
          ↑(derivationComp (B := B) φ e₂) := by
  -- An equality of linear maps on `A' ⊗ A'`, checked on pure tensors; `TensorProduct.ext'`
  -- supplies the extensionality, so no induction is needed.
  refine TensorProduct.ext' fun x y => ?_
  -- Both composite applications unfold definitionally; restate them as values.
  change (e₁ ((φ : A' →ₐ[R] A) x) * e₂ ((φ : A' →ₐ[R] A) y) :
      Bialgebra.CounitAlgebra R A B) =
    derivationComp (B := B) φ e₁ x * derivationComp (B := B) φ e₂ y
  rw [derivationComp_apply, derivationComp_apply]
  -- The residual is print-identical across the two coefficient synonyms; both multiplications
  -- are definitionally `B`'s (the synonym is exposed), which is what this `rfl` uses.
  rfl

end Transport

variable [CommRing B] [Algebra R B]

/-- The differential preserves the convolution commutator: a bialgebra morphism
intertwines comultiplications, hence convolution products of derivations termwise. -/
@[simp]
theorem derivationComp_bracket (φ : A' →ₐc[R] A)
    (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationComp (B := B) φ ⁅d₁, d₂⁆ =
      ⁅derivationComp (B := B) φ d₁, derivationComp (B := B) φ d₂⁆ := by
  ext a
  rw [derivationComp_apply, Derivation.bracket_apply, Derivation.bracket_apply]
  -- Preservation of convolution under precomposition is
  -- `LinearMap.convMul_comp_coalgHom_distrib` at the coalgebra morphism underlying
  -- `φ`, evaluated at `a`.
  have hconv : ∀ e₁ e₂ : Derivation R A (Bialgebra.CounitAlgebra R A B),
      LinearMap.mul' R (Bialgebra.CounitAlgebra R A B)
          (TensorProduct.map (↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ↑e₂
            (comul ((φ : A' →ₐ[R] A).toLinearMap a))) =
        LinearMap.mul' R (Bialgebra.CounitAlgebra R A B)
          (TensorProduct.map
            ((↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ
              (φ : A' →ₐ[R] A).toLinearMap)
            ((↑e₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) ∘ₗ
              (φ : A' →ₐ[R] A).toLinearMap) (comul a)) := by
    intro e₁ e₂
    have h := DFunLike.congr_fun
      (LinearMap.convMul_comp_coalgHom_distrib
        (toConv (↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        (toConv (↑e₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B))
        ((φ : A' →ₐc[R] A) : A' →ₗc[R] A)) a
    simp only [LinearMap.convMul_apply, LinearMap.coe_comp, Function.comp_apply] at h
    exact h
  have h1 := DFunLike.congr_fun (mul'_comp_map_derivationComp φ d₁ d₂) (comul a)
  have h2 := DFunLike.congr_fun (mul'_comp_map_derivationComp φ d₂ d₁) (comul a)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h1 h2
  rw [← AlgHom.toLinearMap_apply (φ : A' →ₐ[R] A) a, hconv, hconv, h1, h2]
  -- The closing `rfl` identifies the two sides through the exposed coefficient
  -- synonyms: after the slotwise rewrites both are literally the same `B`-valued
  -- expression.
  rfl

end Bracket

section LieHom

variable {R A A' B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing A'] [Bialgebra R A'] [CommRing B] [Algebra R B]

/-- The differential on derivations, as a morphism of Lie algebras over the coefficient ring. -/
noncomputable def derivationCompLieHom (φ : A' →ₐc[R] A) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) →ₗ⁅B⁆
      Derivation R A' (Bialgebra.CounitAlgebra R A' B) where
  toFun := derivationComp (B := B) φ
  map_add' := map_add (derivationComp (B := B) φ)
  map_smul' b d := by
    ext a
    apply (Bialgebra.CounitAlgebra.algEquivSelf R A' B).injective
    rw [algEquivSelf_derivationComp_apply,
      algEquivSelf_derivation_smul_apply,
      algEquivSelf_derivation_smul_apply,
      algEquivSelf_derivationComp_apply]
    simp only [RingHom.id_apply]
  map_lie' := derivationComp_bracket φ _ _

@[simp]
lemma derivationCompLieHom_apply (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationCompLieHom (B := B) φ d = derivationComp φ d := by
  -- `derivationCompLieHom` has no equation lemma to rewrite with; `change` spells out
  -- its definitional unfolding once, explicitly.
  change derivationComp (B := B) φ d = _
  rfl

/-- The differential of a surjective bialgebra morphism is injective. -/
theorem derivationCompLieHom_injective_of_surjective (φ : A' →ₐc[R] A)
    (hφ : Function.Surjective φ) :
    Function.Injective (derivationCompLieHom (B := B) φ) := by
  intro d e hde
  apply derivationComp_injective_of_surjective φ hφ
  simpa only [derivationCompLieHom_apply] using hde

/-- The bundled differential along the identity is the identity Lie morphism. -/
@[simp]
theorem derivationCompLieHom_id :
    derivationCompLieHom (B := B) (BialgHom.id R A) =
      LieHom.id (R := B) (L₁ := Derivation R A (Bialgebra.CounitAlgebra R A B)) := by
  ext d
  simp [derivationCompLieHom_apply]

/-- The bundled differential along a composite is the composite of the bundled
differentials. -/
@[simp]
theorem derivationCompLieHom_comp {A'' : Type*} [CommRing A''] [Bialgebra R A'']
    (φ : A' →ₐc[R] A) (χ : A'' →ₐc[R] A') :
    derivationCompLieHom (B := B) (φ.comp χ) =
      (derivationCompLieHom (B := B) χ).comp (derivationCompLieHom (B := B) φ) := by
  ext d
  simp only [derivationCompLieHom_apply, LieHom.comp_apply, derivationComp_comp,
    LinearMap.coe_comp, Function.comp_apply]

end LieHom

section FiniteDimensional

variable {k A A' : Type*} [Field k] [CommRing A] [Bialgebra k A]
  [CommRing A'] [Bialgebra k A']
  [Module.Finite k (Derivation k A (Bialgebra.CounitAlgebra k A k))]
  [Module.Finite k (Derivation k A' (Bialgebra.CounitAlgebra k A' k))]

/-- A surjective bialgebra morphism between equal-dimensional tangent Lie algebras induces a
bijection on tangent Lie algebras. -/
theorem derivationCompLieHom_bijective_of_surjective_of_finrank_eq
    (φ : A' →ₐc[k] A) (hφ : Function.Surjective φ)
    (hfinrank :
      Module.finrank k (Derivation k A (Bialgebra.CounitAlgebra k A k)) =
        Module.finrank k (Derivation k A' (Bialgebra.CounitAlgebra k A' k))) :
    Function.Bijective (derivationCompLieHom (B := k) φ) := by
  have hinjective := derivationCompLieHom_injective_of_surjective (B := k) φ hφ
  refine ⟨hinjective, ?_⟩
  simpa only [LieHom.coe_toLinearMap] using
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (derivationCompLieHom (B := k) φ : _ →ₗ[k] _)) hfinrank).mp
      (by simpa only [LieHom.coe_toLinearMap] using hinjective)

end FiniteDimensional

end TauCeti
