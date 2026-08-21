/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Product
public import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Conjugation in Hopf-algebra coordinates

For a commutative Hopf algebra `H` over a commutative semiring `R`, this file constructs the
algebra morphism `H →ₐ[R] H ⊗[R] H` representing the left conjugation action
`(g, x) ↦ g * x * g⁻¹`. The first tensor factor is the conjugating variable and the second is
the acted-on variable.

The construction uses the convolution group of points: if `i₁(h) = h ⊗ₜ 1` and
`i₂(h) = 1 ⊗ₜ h` are the two universal tensor-factor points, then the coordinate morphism
is the underlying algebra map of `i₁ * i₂ * i₁⁻¹`. Its characteristic theorem says that
post-composing with `Algebra.TensorProduct.productMap g x` gives the point `g * x * g⁻¹`.

The identity and associativity theorems record that this morphism is the coordinate form of a
left group action. No bialgebra-morphism structure is asserted: joint conjugation is not generally
a group homomorphism from the product.

## Main declarations

* `TauCeti.HopfAlgebra.conjugationAlgHom`: the coordinate algebra morphism of left conjugation.
* `TauCeti.HopfAlgebra.productMap_comp_conjugationAlgHom`: evaluation at arbitrary algebra-valued
  points.
* `TauCeti.HopfAlgebra.conjugationAlgHom_counit_left`: the identity element acts trivially.
* `TauCeti.HopfAlgebra.conjugationAlgHom_counit_right`: conjugation fixes the identity element.
* `TauCeti.HopfAlgebra.conjugationAlgHom_coassoc`: the coordinate action-associativity law.

## References

The orientation follows J. S. Milne, *Algebraic Groups* (2017), §3.5 and §10.20, where
`Ad(g)(x) = g x g⁻¹`. The adjoint-coaction action structure is also described in
I. Heckenberger and H.-J. Schneider, *Hopf Algebras and Root Systems*, §3.7. This is the
conjugation/adjoint-morphism prerequisite in Layer 3, “Normality and quotients”, of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} [CommSemiring R] [CommSemiring H]
variable [_root_.HopfAlgebra R H]

/-- The coordinate algebra morphism of the left conjugation action.

The first tensor factor is the conjugating variable and the second is the acted-on variable.
As a universal point, this is `i₁ * i₂ * i₁⁻¹`, so on algebra-valued points it represents
`(g, x) ↦ g * x * g⁻¹`. -/
noncomputable def conjugationAlgHom : H →ₐ[R] H ⊗[R] H :=
  (toConv (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
      toConv (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
      (toConv
          (Bialgebra.TensorProduct.includeLeft
            (R := R) (H₁ := H) (H₂ := H)).toAlgHom)⁻¹).ofConv

/-- The coordinate morphism of left conjugation is the convolution product of the two universal
tensor-factor points and the inverse of the first. -/
theorem toConv_conjugationAlgHom :
    toConv (conjugationAlgHom (R := R) (H := H)) =
      toConv (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
        toConv
          (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
        (toConv
          (Bialgebra.TensorProduct.includeLeft
            (R := R) (H₁ := H) (H₂ := H)).toAlgHom)⁻¹ := by
  rw [conjugationAlgHom, toConv_ofConv]

/-- Evaluating the coordinate morphism of left conjugation at two algebra-valued points gives
their group-theoretic conjugate.

Here `g` is the conjugating point and `x` is the acted-on point. The product map sends a pure
tensor `h ⊗ₜ k` to `g(h) * x(k)`. -/
@[simp]
theorem productMap_comp_conjugationAlgHom
    {A : Type w} [CommSemiring A] [Algebra R A]
    (g x : WithConv (H →ₐ[R] A)) :
    (Algebra.TensorProduct.productMap g.ofConv x.ofConv).comp
        (conjugationAlgHom (R := R) (H := H)) =
      (g * x * g⁻¹).ofConv := by
  have hmap :
      AlgHom.mapValue (H := H) (Algebra.TensorProduct.productMap g.ofConv x.ofConv)
          (toConv (conjugationAlgHom (R := R) (H := H))) =
        g * x * g⁻¹ := by
    rw [toConv_conjugationAlgHom, map_mul, map_mul, map_inv]
    simp only [AlgHom.mapValue_apply,
      Bialgebra.TensorProduct.includeLeft_toAlgHom,
      Bialgebra.TensorProduct.includeRight_toAlgHom,
      Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right]
  exact congrArg WithConv.ofConv hmap

/-- **Evaluation against an arbitrary algebra map out of the tensor square.** Every algebra map
`φ : H ⊗[R] H →ₐ[R] A` is the product map of its two restrictions, so composing it with the
conjugation morphism conjugates the second restriction by the first. This is the restriction form
of `productMap_comp_conjugationAlgHom`, which needs `φ` presented as a product map. -/
theorem comp_conjugationAlgHom {A : Type w} [CommSemiring A] [Algebra R A]
    (phi : H ⊗[R] H →ₐ[R] A) :
    phi.comp (conjugationAlgHom (R := R) (H := H)) =
      (toConv (phi.comp Algebra.TensorProduct.includeLeft) *
        toConv (phi.comp Algebra.TensorProduct.includeRight) *
        (toConv (phi.comp Algebra.TensorProduct.includeLeft))⁻¹).ofConv := by
  calc
    phi.comp (conjugationAlgHom (R := R) (H := H)) =
        (Algebra.TensorProduct.productMap
          (phi.comp Algebra.TensorProduct.includeLeft)
          (phi.comp Algebra.TensorProduct.includeRight)).comp
            (conjugationAlgHom (R := R) (H := H)) :=
      congrArg (fun psi : H ⊗[R] H →ₐ[R] A ↦ psi.comp (conjugationAlgHom (R := R) (H := H)))
        (AffineGroup.Product.productMap_restrict phi).symm
    _ = _ := by
      simpa only [ofConv_toConv] using
        productMap_comp_conjugationAlgHom (R := R) (H := H)
          (toConv (phi.comp Algebra.TensorProduct.includeLeft))
          (toConv (phi.comp Algebra.TensorProduct.includeRight))

/-- The identity point acts trivially by conjugation. This is the pointwise product-map form of
the left-unit law for the coordinate action. -/
@[simp]
theorem productMap_one_id_comp_conjugationAlgHom :
    (Algebra.TensorProduct.productMap
        (1 : WithConv (H →ₐ[R] H)).ofConv (AlgHom.id R H)).comp
      (conjugationAlgHom (R := R) (H := H)) =
        AlgHom.id R H := by
  simpa using
    (productMap_comp_conjugationAlgHom (R := R) (H := H)
      (1 : WithConv (H →ₐ[R] H)) (toConv (AlgHom.id R H)))

/-- Conjugation fixes the identity point. -/
@[simp]
theorem productMap_id_one_comp_conjugationAlgHom :
    (Algebra.TensorProduct.productMap
        (AlgHom.id R H) (1 : WithConv (H →ₐ[R] H)).ofConv).comp
      (conjugationAlgHom (R := R) (H := H)) =
        (1 : WithConv (H →ₐ[R] H)).ofConv := by
  simpa using
    (productMap_comp_conjugationAlgHom (R := R) (H := H)
      (toConv (AlgHom.id R H)) (1 : WithConv (H →ₐ[R] H)))

/-- Under the canonical left-unit identification, applying the counit to the conjugating
coordinate makes conjugation the identity. This is the coordinate identity-action law
`(ε ⊗ id) ∘ c♯ = id`. -/
@[simp]
theorem conjugationAlgHom_counit_left :
    (Algebra.TensorProduct.lid R H).toAlgHom.comp
        ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H)).comp
          (conjugationAlgHom (R := R) (H := H))) =
      AlgHom.id R H := by
  have hproduct :
      (Algebra.TensorProduct.lid R H).toAlgHom.comp
          (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H)) =
        Algebra.TensorProduct.productMap
          (1 : WithConv (H →ₐ[R] H)).ofConv (AlgHom.id R H) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [AlgHom.convOne_apply, Algebra.smul_def]
  rw [← AlgHom.comp_assoc, hproduct]
  exact productMap_one_id_comp_conjugationAlgHom (R := R) (H := H)

/-- Under the canonical right-unit identification, applying the counit to the acted-on
coordinate gives the identity point. This is the coordinate formula saying that conjugation
fixes the group identity. -/
@[simp]
theorem conjugationAlgHom_counit_right :
    (Algebra.TensorProduct.rid R R H).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H)).comp
          (conjugationAlgHom (R := R) (H := H))) =
      (1 : WithConv (H →ₐ[R] H)).ofConv := by
  have hproduct :
      (Algebra.TensorProduct.rid R R H).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H)) =
        Algebra.TensorProduct.productMap
          (AlgHom.id R H) (1 : WithConv (H →ₐ[R] H)).ofConv := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [AlgHom.convOne_apply, Algebra.smul_def, mul_comm]
  rw [← AlgHom.comp_assoc, hproduct]
  exact productMap_id_one_comp_conjugationAlgHom (R := R) (H := H)

/-- **Comultiplying the conjugating variable splits it into the first two universal points.**
Re-associating after comultiplying the first tensor factor sends the first universal point to the
convolution product of the first two points of the triple tensor algebra. This is
`TauCeti.Bialgebra.toConv_comp_comulAlgHom` at the tensor associator. -/
private theorem toConv_assoc_comp_map_comul_comp_includeLeft :
    toConv
        ((((Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
            (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))).comp
          Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] (H ⊗[R] H))) =
      toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] (H ⊗[R] H)) *
        toConv
          ((Algebra.TensorProduct.includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp
            (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)) := by
  let up : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
    (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
      Algebra.TensorProduct.includeLeft
  have hfactor :
      (((Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
          (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))).comp
        Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] (H ⊗[R] H)) =
        up.comp (Bialgebra.comulAlgHom R H) := by
    simp only [up, AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft]
  rw [hfactor, Bialgebra.toConv_comp_comulAlgHom]
  congr 1
  · apply congrArg WithConv.toConv
    ext h
    simp [up, Algebra.TensorProduct.one_def]
  · apply congrArg WithConv.toConv
    ext h
    simp [up]

/-- The coordinate morphism of left conjugation satisfies the action-associativity law.

The left side represents conjugation by the product of the first two universal points, while the
right side represents successive conjugation by the second and then the first. The tensor
associator identifies their common target. -/
theorem conjugationAlgHom_coassoc :
    (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
        ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H)).comp
          (conjugationAlgHom (R := R) (H := H))) =
      (Algebra.TensorProduct.map (AlgHom.id R H)
          (conjugationAlgHom (R := R) (H := H))).comp
        (conjugationAlgHom (R := R) (H := H)) := by
  let c := conjugationAlgHom (R := R) (H := H)
  let assoc : (H ⊗[R] H) ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
    (Algebra.TensorProduct.assoc R R R H H H).toAlgHom
  let mulFirst : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
    assoc.comp (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))
  let actSecond : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
    Algebra.TensorProduct.map (AlgHom.id R H) c
  -- The three tensor-factor inclusions are the universal points `g₁`, `g₂`, and `x`.
  let g₁ : WithConv (H →ₐ[R] H ⊗[R] (H ⊗[R] H)) :=
    toConv Algebra.TensorProduct.includeLeft
  let g₂ : WithConv (H →ₐ[R] H ⊗[R] (H ⊗[R] H)) :=
    toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft)
  let x : WithConv (H →ₐ[R] H ⊗[R] (H ⊗[R] H)) :=
    toConv (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight)
  -- The two restrictions of `mulFirst` are respectively `g₁ * g₂` and `x`.
  have hmulFirstLeft :
      toConv (mulFirst.comp Algebra.TensorProduct.includeLeft) = g₁ * g₂ :=
    toConv_assoc_comp_map_comul_comp_includeLeft
  have hmulFirstRight :
      toConv (mulFirst.comp Algebra.TensorProduct.includeRight) = x := by
    apply WithConv.ofConv_injective
    ext h
    simp [mulFirst, assoc, x, Algebra.TensorProduct.one_def]
  -- The two restrictions of `actSecond` are `g₁` and the inner conjugate of `x` by `g₂`.
  have hactSecondLeft :
      toConv (actSecond.comp Algebra.TensorProduct.includeLeft) = g₁ := by
    apply WithConv.ofConv_injective
    simp [actSecond, g₁]
  -- Restricting `id ⊗ c` to the second factor is `c` post-composed with the inclusion, and `g₂`
  -- and `x` are by definition that inclusion's own two restrictions.
  have hactSecondRight :
      toConv (actSecond.comp Algebra.TensorProduct.includeRight) =
        g₂ * x * g₂⁻¹ := by
    rw [Algebra.TensorProduct.map_comp_includeRight (AlgHom.id R H) c,
      comp_conjugationAlgHom _, toConv_ofConv]
  -- The two coordinate maps now evaluate to the corresponding conjugates; associativity and
  -- `(g₁ * g₂)⁻¹ = g₂⁻¹ * g₁⁻¹` finish the comparison.
  have hcoassoc : mulFirst.comp c = actSecond.comp c := by
    rw [comp_conjugationAlgHom mulFirst, comp_conjugationAlgHom actSecond,
      hmulFirstLeft, hmulFirstRight, hactSecondLeft, hactSecondRight]
    apply congrArg WithConv.ofConv
    exact
      mul_inv_eq_iff_eq_mul.2
        ((SemiconjBy.conj_mk g₁ (g₂ * x * g₂⁻¹)).mul_left
          (SemiconjBy.conj_mk g₂ x)).eq
  simpa only [mulFirst, actSecond, assoc, c, AlgHom.comp_assoc] using hcoassoc

end HopfAlgebra

end TauCeti
