/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Finiteness.Prod

/-!
# The tangent Lie algebra of a product

The tensor product of two commutative bialgebras is the coordinate algebra of the direct product
of the represented affine monoid schemes. Restricting a counit-valued derivation along the two
canonical inclusions gives its two tangent components. Conversely, the canonical projections,
obtained by applying the counit to the other tensor factor, extend a pair of tangent vectors back
to the product. These constructions are inverse and preserve the convolution Lie bracket.

Thus the tangent Lie algebra of a direct product is canonically the product of the tangent Lie
algebras of its factors. The equivalence is valid for coefficient-valued tangent vectors over an
arbitrary commutative coefficient algebra; it needs no antipode, finiteness, or field hypothesis.

## Main declarations

* `Derivation.tensorProductLieEquiv`: the canonical Lie equivalence
  `Lie(Spec (H₁ ⊗[R] H₂)) ≃ Lie(Spec H₁) × Lie(Spec H₂)`.
* `Derivation.tensorProductLieEquiv_apply`: its two components are restriction to the tensor
  factors.
* `Derivation.tensorProductLieEquiv_symm_apply_tmul`: the inverse evaluated on a
  pure tensor.
* `Derivation.finrank_tangent_tensorProduct`: for finite-dimensional tangent spaces over a field,
  tangent dimensions add over products.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 11.

This supplies the direct-product compatibility for `Lie(G)` in Layer 2, "Tangent space at the
identity / `Lie(G)`", of the ReductiveGroups roadmap. It also gives the additive tangent-dimension
formula needed by the same layer's dimension tools.
-/

public section

open TensorProduct

namespace Derivation

open TauCeti

universe u v w z

noncomputable section

variable {R : Type u} {H₁ : Type v} {H₂ : Type w} {B : Type z}
variable [CommRing R] [CommRing H₁] [CommRing H₂]
variable [Bialgebra R H₁] [Bialgebra R H₂]
variable [CommRing B] [Algebra R B]

/-- Restrict a tangent vector of a tensor product to its two tensor factors. -/
private noncomputable def tensorProductComponents :
    _root_.Derivation R (H₁ ⊗[R] H₂)
        (Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B) →ₗ⁅B⁆
      _root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B) ×
        _root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B) :=
  (derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H₁) (H₂ := H₂))).prod
    (derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H₁) (H₂ := H₂)))

/-- Extend two tangent vectors to the tensor product along the counit projections and add them. -/
private noncomputable def ofTensorProductComponents :
    (_root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B) ×
        _root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B)) →ₗ[B]
      _root_.Derivation R (H₁ ⊗[R] H₂) (Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B) :=
  ((derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.projectLeft
        (R := R) (H₁ := H₁) (H₂ := H₂))).toLinearMap.comp
      (LinearMap.fst B _ _)) +
    ((derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.projectRight
        (R := R) (H₁ := H₁) (H₂ := H₂))).toLinearMap.comp
      (LinearMap.snd B _ _))

private theorem tensorProductComponents_ofTensorProductComponents
    (d : _root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B) ×
      _root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B)) :
    tensorProductComponents (ofTensorProductComponents d) = d := by
  apply Prod.ext
  · simp only [tensorProductComponents, ofTensorProductComponents, LieHom.prod_apply,
      LieHom.coe_toLinearMap, derivationCompLieHom_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    -- The preceding simplification exposes the bundled maps' underlying derivations;
    -- `change` records that definitional identification before using the functorial API.
    change derivationComp (B := B)
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H₁) (H₂ := H₂))
        (derivationComp (B := B)
            (TauCeti.Bialgebra.TensorProduct.projectLeft
              (R := R) (H₁ := H₁) (H₂ := H₂)) d.1 +
          derivationComp (B := B)
            (TauCeti.Bialgebra.TensorProduct.projectRight
              (R := R) (H₁ := H₁) (H₂ := H₂)) d.2) = d.1
    rw [map_add]
    have hdiag : derivationComp (B := B)
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H₁) (H₂ := H₂))
        (derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := H₁) (H₂ := H₂))
            d.1) = d.1 := by
      rw [← LinearMap.comp_apply, ← derivationComp_comp,
        TauCeti.Bialgebra.TensorProduct.projectLeft_comp_includeLeft,
        derivationComp_id, LinearMap.id_apply]
    rw [hdiag]
    have hcross : derivationComp (B := B)
        (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H₁) (H₂ := H₂))
        (derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectRight (R := R) (H₁ := H₁) (H₂ := H₂))
            d.2) = 0 := by
      ext h
      simp only [derivationComp_apply, BialgHom.coe_toAlgHom,
        TauCeti.Bialgebra.TensorProduct.includeLeft_toAlgHom,
        Algebra.TensorProduct.includeLeft_apply,
        TauCeti.Bialgebra.TensorProduct.projectRight_tmul, Derivation.map_smul,
        Derivation.map_one_eq_zero, smul_zero]
      -- Both sides are zero in exposed counit-coefficient synonyms.
      rfl
    rw [hcross, add_zero]
  · simp only [tensorProductComponents, ofTensorProductComponents, LieHom.prod_apply,
      LieHom.coe_toLinearMap, derivationCompLieHom_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    -- As in the first component, the bundled maps reduce definitionally to this composite.
    change derivationComp (B := B)
        (TauCeti.Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H₁) (H₂ := H₂))
        (derivationComp (B := B)
            (TauCeti.Bialgebra.TensorProduct.projectLeft
              (R := R) (H₁ := H₁) (H₂ := H₂)) d.1 +
          derivationComp (B := B)
            (TauCeti.Bialgebra.TensorProduct.projectRight
              (R := R) (H₁ := H₁) (H₂ := H₂)) d.2) = d.2
    rw [map_add]
    have hdiag : derivationComp (B := B)
        (TauCeti.Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H₁) (H₂ := H₂))
        (derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectRight (R := R) (H₁ := H₁) (H₂ := H₂))
            d.2) = d.2 := by
      rw [← LinearMap.comp_apply, ← derivationComp_comp,
        TauCeti.Bialgebra.TensorProduct.projectRight_comp_includeRight,
        derivationComp_id, LinearMap.id_apply]
    rw [hdiag]
    have hcross : derivationComp (B := B)
        (TauCeti.Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H₁) (H₂ := H₂))
        (derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := H₁) (H₂ := H₂))
            d.1) = 0 := by
      ext h
      simp only [derivationComp_apply, BialgHom.coe_toAlgHom,
        TauCeti.Bialgebra.TensorProduct.includeRight_toAlgHom,
        Algebra.TensorProduct.includeRight_apply,
        TauCeti.Bialgebra.TensorProduct.projectLeft_tmul, Derivation.map_smul,
        Derivation.map_one_eq_zero, smul_zero]
      -- Both sides are zero in exposed counit-coefficient synonyms.
      rfl
    rw [hcross, zero_add]

private theorem tensorProduct_smul_eq_counit_smul
    (x : H₁ ⊗[R] H₂) (b : Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B) :
    x • b = Coalgebra.counit (R := R) x • b := by
  rw [Algebra.smul_def, Bialgebra.CounitAlgebra.algebraMap_apply, Algebra.smul_def,
    Bialgebra.CounitAlgebra.algebraMap_base]

private theorem ofTensorProductComponents_tensorProductComponents
    (d : _root_.Derivation R (H₁ ⊗[R] H₂)
      (Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B)) :
    ofTensorProductComponents (tensorProductComponents d) = d := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul h₁ h₂ =>
      simp only [ofTensorProductComponents, tensorProductComponents, LieHom.prod_apply,
        LieHom.coe_toLinearMap, derivationCompLieHom_apply, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
      -- The private linear-map wrappers are definitionally the displayed sum of composites;
      -- restate that representation before evaluating it on the pure tensor.
      change
        (derivationComp (B := B)
              (TauCeti.Bialgebra.TensorProduct.projectLeft
                (R := R) (H₁ := H₁) (H₂ := H₂))
              (derivationComp (B := B)
                (TauCeti.Bialgebra.TensorProduct.includeLeft
                  (R := R) (H₁ := H₁) (H₂ := H₂)) d) +
            derivationComp (B := B)
              (TauCeti.Bialgebra.TensorProduct.projectRight
                (R := R) (H₁ := H₁) (H₂ := H₂))
              (derivationComp (B := B)
                (TauCeti.Bialgebra.TensorProduct.includeRight
                  (R := R) (H₁ := H₁) (H₂ := H₂)) d)) (h₁ ⊗ₜ[R] h₂) =
          d (h₁ ⊗ₜ[R] h₂)
      rw [Derivation.add_apply, derivationComp_apply, derivationComp_apply,
        derivationComp_apply, derivationComp_apply]
      simp only [BialgHom.coe_toAlgHom, TauCeti.Bialgebra.TensorProduct.projectLeft_tmul,
        TauCeti.Bialgebra.TensorProduct.projectRight_tmul]
      rw [_root_.map_smul,
        TauCeti.Bialgebra.TensorProduct.includeLeft_apply,
        TauCeti.Bialgebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul]
      rw [Derivation.map_smul, Derivation.map_smul]
      -- The two projected terms are the two summands in the Leibniz rule for
      -- `(1 ⊗ h₂) * (h₁ ⊗ 1) = h₁ ⊗ h₂`.
      have hh₂ (b : Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B) :
          ((1 : H₁) ⊗ₜ[R] h₂) • b = Coalgebra.counit (R := R) h₂ • b := by
        rw [tensorProduct_smul_eq_counit_smul]
        simp
      have hh₁ (b : Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B) :
          (h₁ ⊗ₜ[R] (1 : H₂)) • b = Coalgebra.counit (R := R) h₁ • b := by
        rw [tensorProduct_smul_eq_counit_smul]
        simp
      rw [← hh₂, ← hh₁,
        ← Derivation.leibniz d ((1 : H₁) ⊗ₜ[R] h₂) (h₁ ⊗ₜ[R] (1 : H₂))]
      simp

/-- The tangent Lie algebra of a product is canonically the product of the tangent Lie algebras
of its factors. -/
noncomputable def tensorProductLieEquiv :
    LieEquiv B
      (_root_.Derivation R (H₁ ⊗[R] H₂) (Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B))
      (_root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B) ×
        _root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B)) where
  toFun := tensorProductComponents
  map_add' := map_add tensorProductComponents
  map_smul' := tensorProductComponents.map_smul
  invFun := ofTensorProductComponents
  left_inv := ofTensorProductComponents_tensorProductComponents
  right_inv := tensorProductComponents_ofTensorProductComponents
  map_lie' {d₁ d₂} :=
    (tensorProductComponents (R := R) (B := B) (H₁ := H₁) (H₂ := H₂)).map_lie d₁ d₂

/-- The product tangent equivalence restricts a derivation to the two tensor factors. -/
@[simp]
theorem tensorProductLieEquiv_apply
    (d : _root_.Derivation R (H₁ ⊗[R] H₂) (Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B)) :
    tensorProductLieEquiv d =
      (derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H₁) (H₂ := H₂)) d,
        derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.includeRight
            (R := R) (H₁ := H₁) (H₂ := H₂)) d) := by
  -- The forward function of the equivalence is definitionally `tensorProductComponents`.
  change tensorProductComponents d = _
  simp [tensorProductComponents]

/-- The inverse product tangent equivalence extends both components along the counit projections
and adds them. -/
@[simp]
theorem tensorProductLieEquiv_symm_apply
    (d : _root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B) ×
      _root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B)) :
    (tensorProductLieEquiv (R := R) (B := B) (H₁ := H₁) (H₂ := H₂)).symm d =
      derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := H₁) (H₂ := H₂)) d.1 +
        derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectRight
            (R := R) (H₁ := H₁) (H₂ := H₂)) d.2 := by
  -- The inverse function of the equivalence is definitionally `ofTensorProductComponents`.
  change ofTensorProductComponents d = _
  simp [ofTensorProductComponents]

/-- On a pure tensor, the tangent vector assembled from `d` is the Leibniz sum
`ε(h₂) • d.1 h₁ + ε(h₁) • d.2 h₂`. -/
theorem tensorProductLieEquiv_symm_apply_tmul
    (d : _root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B) ×
      _root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B))
    (h₁ : H₁) (h₂ : H₂) :
    Bialgebra.CounitAlgebra.algEquivSelf R (H₁ ⊗[R] H₂) B
        ((tensorProductLieEquiv (R := R) (B := B) (H₁ := H₁) (H₂ := H₂)).symm d
          (h₁ ⊗ₜ[R] h₂)) =
      Coalgebra.counit (R := R) h₂ •
          Bialgebra.CounitAlgebra.algEquivSelf R H₁ B (d.1 h₁) +
        Coalgebra.counit (R := R) h₁ •
          Bialgebra.CounitAlgebra.algEquivSelf R H₂ B (d.2 h₂) := by
  simp only [tensorProductLieEquiv_symm_apply, Derivation.add_apply, derivationComp_apply,
    BialgHom.coe_toAlgHom, TauCeti.Bialgebra.TensorProduct.projectLeft_tmul,
    TauCeti.Bialgebra.TensorProduct.projectRight_tmul, Derivation.map_smul, map_smul,
    Bialgebra.CounitAlgebra.algEquivSelf_apply]
  -- The remaining equality identifies the three exposed counit-coefficient synonyms with `B`.
  rfl

/-- Finiteness of the two factor tangent modules implies finiteness of the tensor-product tangent
module. -/
noncomputable instance
    [Module.Finite B (_root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B))]
    [Module.Finite B (_root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B))] :
    Module.Finite B
      (_root_.Derivation R (H₁ ⊗[R] H₂) (Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B)) :=
  Module.Finite.equiv
    (tensorProductLieEquiv (R := R) (B := B) (H₁ := H₁) (H₂ := H₂)).toLinearEquiv.symm

end

end Derivation

namespace Derivation

open TauCeti

section Dimension

variable {R H₁ H₂ B : Type*} [CommRing R] [CommRing H₁] [CommRing H₂]
variable [Bialgebra R H₁] [Bialgebra R H₂] [Field B] [Algebra R B]

/-- The dimension of the tangent Lie algebra of a product is the sum of the dimensions of the
tangent Lie algebras of its factors. -/
theorem finrank_tangent_tensorProduct
    [Module.Finite B
      (_root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B))]
    [Module.Finite B
      (_root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B))] :
    Module.finrank B
        (_root_.Derivation R (H₁ ⊗[R] H₂) (Bialgebra.CounitAlgebra R (H₁ ⊗[R] H₂) B)) =
      Module.finrank B
          (_root_.Derivation R H₁ (Bialgebra.CounitAlgebra R H₁ B)) +
        Module.finrank B
          (_root_.Derivation R H₂ (Bialgebra.CounitAlgebra R H₂ B)) := by
  rw [(tensorProductLieEquiv
    (R := R) (B := B) (H₁ := H₁) (H₂ := H₂)).toLinearEquiv.finrank_eq,
    Module.finrank_prod]

end Dimension

end Derivation
