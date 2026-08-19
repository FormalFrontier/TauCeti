/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The tangent Lie algebra of a product

The tensor product of two commutative bialgebras is the coordinate algebra of the direct product
of the represented affine monoid schemes. Restricting a counit-valued derivation along the two
canonical inclusions gives its two tangent components. Conversely, the canonical projections,
obtained by applying the counit to the other tensor factor, extend a pair of tangent vectors back
to the product. These constructions are inverse and preserve the convolution Lie bracket.

Thus the tangent Lie algebra of a direct product is canonically the product of the tangent Lie
algebras of its factors. The comparison is valid for coefficient-valued tangent vectors over an
arbitrary commutative coefficient algebra; no antipode, finiteness, or field hypothesis is needed.

## Main declarations

* `Derivation.productLieEquiv`: the canonical Lie equivalence
  `Lie(G × H) ≃ Lie(G) × Lie(H)`.
* `Derivation.productLieEquiv_apply`: its two components are restriction to the tensor
  factors.
* `Derivation.productLieEquiv_symm_apply_tmul`: the inverse evaluated on a pure tensor.
* `Derivation.finrank_tangent_tensorProduct`: tangent dimensions add over products.

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

variable {R : Type u} {H : Type v} {K : Type w} {B : Type z}
variable [CommRing R] [CommRing H] [CommRing K]
variable [Bialgebra R H] [Bialgebra R K]
variable [CommRing B] [Algebra R B]

/-- Restrict a tangent vector of a product to its two tensor factors. -/
noncomputable def productComponents :
    _root_.Derivation R (H ⊗[R] K) (Bialgebra.CounitAlgebra R (H ⊗[R] K) B) →ₗ[B]
      _root_.Derivation R H (Bialgebra.CounitAlgebra R H B) ×
        _root_.Derivation R K (Bialgebra.CounitAlgebra R K B) :=
  (derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K))).toLinearMap.prod
    (derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K))).toLinearMap

/-- Extend a pair of tangent vectors to the product by applying the counit in the other tensor
factor and adding the resulting derivations. -/
noncomputable def ofProductComponents :
    (_root_.Derivation R H (Bialgebra.CounitAlgebra R H B) ×
        _root_.Derivation R K (Bialgebra.CounitAlgebra R K B)) →ₗ[B]
      _root_.Derivation R (H ⊗[R] K) (Bialgebra.CounitAlgebra R (H ⊗[R] K) B) :=
  ((derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.projectLeft
        (R := R) (H₁ := H) (H₂ := K))).toLinearMap.comp
      (LinearMap.fst B _ _)) +
    ((derivationCompLieHom (B := B)
      (TauCeti.Bialgebra.TensorProduct.projectRight
        (R := R) (H₁ := H) (H₂ := K))).toLinearMap.comp
      (LinearMap.snd B _ _))

@[simp]
theorem productComponents_apply
    (d : _root_.Derivation R (H ⊗[R] K) (Bialgebra.CounitAlgebra R (H ⊗[R] K) B)) :
    productComponents d =
      (derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K)) d,
        derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K)) d) := by
  simp [productComponents]

@[simp]
theorem ofProductComponents_apply
    (d : _root_.Derivation R H (Bialgebra.CounitAlgebra R H B) ×
      _root_.Derivation R K (Bialgebra.CounitAlgebra R K B)) :
    ofProductComponents d =
      derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := H) (H₂ := K)) d.1 +
        derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectRight (R := R) (H₁ := H) (H₂ := K)) d.2 := by
  simp [ofProductComponents]

private theorem productComponents_ofProductComponents
    (d : _root_.Derivation R H (Bialgebra.CounitAlgebra R H B) ×
      _root_.Derivation R K (Bialgebra.CounitAlgebra R K B)) :
    productComponents (ofProductComponents d) = d := by
  apply Prod.ext
  · simp only [productComponents_apply, ofProductComponents_apply, Prod.fst_add,
      map_add]
    apply Derivation.ext
    intro h
    simp only [Derivation.coe_add, Pi.add_apply, derivationComp_apply,
      TauCeti.Bialgebra.TensorProduct.includeLeft_toAlgHom,
      Algebra.TensorProduct.includeLeft_apply, BialgHom.coe_toAlgHom,
      TauCeti.Bialgebra.TensorProduct.projectLeft_tmul, Bialgebra.counit_one, one_smul,
      TauCeti.Bialgebra.TensorProduct.projectRight_tmul, Derivation.map_smul,
      Derivation.map_one_eq_zero, smul_zero]
    exact add_zero _
  · simp only [productComponents_apply, ofProductComponents_apply, Prod.snd_add,
      map_add]
    apply Derivation.ext
    intro k
    simp only [Derivation.coe_add, Pi.add_apply, derivationComp_apply,
      TauCeti.Bialgebra.TensorProduct.includeRight_toAlgHom,
      Algebra.TensorProduct.includeRight_apply, BialgHom.coe_toAlgHom,
      TauCeti.Bialgebra.TensorProduct.projectLeft_tmul, Derivation.map_smul,
      Derivation.map_one_eq_zero, smul_zero, TauCeti.Bialgebra.TensorProduct.projectRight_tmul,
      Bialgebra.counit_one, one_smul]
    exact zero_add _

private theorem ofProductComponents_productComponents
    (d : _root_.Derivation R (H ⊗[R] K) (Bialgebra.CounitAlgebra R (H ⊗[R] K) B)) :
    ofProductComponents (productComponents d) = d := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul h k =>
      rw [ofProductComponents_apply, productComponents_apply, Derivation.add_apply,
        derivationComp_apply, derivationComp_apply, derivationComp_apply, derivationComp_apply]
      simp only [BialgHom.coe_toAlgHom, TauCeti.Bialgebra.TensorProduct.projectLeft_tmul,
        TauCeti.Bialgebra.TensorProduct.projectRight_tmul]
      rw [_root_.map_smul,
        TauCeti.Bialgebra.TensorProduct.includeLeft_apply,
        TauCeti.Bialgebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul]
      rw [Derivation.map_smul, Derivation.map_smul]
      have hk (b : Bialgebra.CounitAlgebra R (H ⊗[R] K) B) :
          ((1 : H) ⊗ₜ[R] k) • b = Coalgebra.counit (R := R) k • b := by
        simp [Algebra.smul_def, Bialgebra.CounitAlgebra.algebraMap_apply]
      have hh (b : Bialgebra.CounitAlgebra R (H ⊗[R] K) B) :
          (h ⊗ₜ[R] (1 : K)) • b = Coalgebra.counit (R := R) h • b := by
        simp [Algebra.smul_def, Bialgebra.CounitAlgebra.algebraMap_apply]
      rw [← hk, ← hh,
        ← Derivation.leibniz d ((1 : H) ⊗ₜ[R] k) (h ⊗ₜ[R] (1 : K))]
      simp

/-- The tangent Lie algebra of a product is canonically the product of the tangent Lie algebras
of its factors. -/
noncomputable def productLieEquiv :
    LieEquiv B
      (_root_.Derivation R (H ⊗[R] K) (Bialgebra.CounitAlgebra R (H ⊗[R] K) B))
      (_root_.Derivation R H (Bialgebra.CounitAlgebra R H B) ×
        _root_.Derivation R K (Bialgebra.CounitAlgebra R K B)) where
  toFun := productComponents
  map_add' := map_add productComponents
  map_smul' := productComponents.map_smul
  invFun := ofProductComponents
  left_inv := ofProductComponents_productComponents
  right_inv := productComponents_ofProductComponents
  map_lie' {d₁ d₂} := by
    ext <;> simp

/-- The product tangent equivalence restricts a derivation to the two tensor factors. -/
@[simp]
theorem productLieEquiv_apply
    (d : _root_.Derivation R (H ⊗[R] K) (Bialgebra.CounitAlgebra R (H ⊗[R] K) B)) :
    productLieEquiv d =
      (derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K)) d,
        derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K)) d) := by
  rw [← productComponents_apply]
  rfl

/-- The inverse product tangent equivalence extends both components along the counit projections
and adds them. -/
@[simp]
theorem productLieEquiv_symm_apply
    (d : _root_.Derivation R H (Bialgebra.CounitAlgebra R H B) ×
      _root_.Derivation R K (Bialgebra.CounitAlgebra R K B)) :
    (productLieEquiv (R := R) (B := B) (H := H) (K := K)).symm d =
      derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectLeft (R := R) (H₁ := H) (H₂ := K)) d.1 +
        derivationComp (B := B)
          (TauCeti.Bialgebra.TensorProduct.projectRight (R := R) (H₁ := H) (H₂ := K)) d.2 := by
  rw [← ofProductComponents_apply]
  rfl

/-- On a pure tensor, the tangent vector assembled from `(d₁, d₂)` is the Leibniz sum
`epsilon(k) * d₁(h) + epsilon(h) * d₂(k)`. -/
theorem productLieEquiv_symm_apply_tmul
    (d : _root_.Derivation R H (Bialgebra.CounitAlgebra R H B) ×
      _root_.Derivation R K (Bialgebra.CounitAlgebra R K B))
    (h : H) (k : K) :
    Bialgebra.CounitAlgebra.algEquivSelf R (H ⊗[R] K) B
        ((productLieEquiv (R := R) (B := B) (H := H) (K := K)).symm d (h ⊗ₜ[R] k)) =
      Coalgebra.counit (R := R) k •
          Bialgebra.CounitAlgebra.algEquivSelf R H B (d.1 h) +
        Coalgebra.counit (R := R) h •
          Bialgebra.CounitAlgebra.algEquivSelf R K B (d.2 k) := by
  simp [productLieEquiv_symm_apply, derivationComp_apply]
  rfl

end

end Derivation

namespace Derivation

open TauCeti

section Dimension

variable {R H K B : Type*} [CommRing R] [CommRing H] [CommRing K]
variable [Bialgebra R H] [Bialgebra R K] [Field B] [Algebra R B]

/-- The dimension of the tangent Lie algebra of a product is the sum of the dimensions of the
tangent Lie algebras of its factors. -/
@[simp]
theorem finrank_tangent_tensorProduct
    [Module.Finite B
      (_root_.Derivation R H (Bialgebra.CounitAlgebra R H B))]
    [Module.Finite B
      (_root_.Derivation R K (Bialgebra.CounitAlgebra R K B))] :
    Module.finrank B
        (_root_.Derivation R (H ⊗[R] K) (Bialgebra.CounitAlgebra R (H ⊗[R] K) B)) =
      Module.finrank B
          (_root_.Derivation R H (Bialgebra.CounitAlgebra R H B)) +
        Module.finrank B
          (_root_.Derivation R K (Bialgebra.CounitAlgebra R K B)) := by
  rw [(productLieEquiv (R := R) (B := B) (H := H) (K := K)).toLinearEquiv.finrank_eq,
    Module.finrank_prod]

end Dimension

end Derivation
