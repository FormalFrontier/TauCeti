/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Multiplication of regular subcomodules

For a bialgebra `H`, multiplication is a morphism from the tensor square of the regular
right comodule to the regular right comodule. Consequently, if `N` and `P` are
subcomodules of the regular comodule and a third subcomodule `Q` contains all products
`n * p`, multiplication corestricts to a comodule morphism `N ⊗ P ⟶ Q`.

When `H` is free over the base semiring and `N` and `P` are finite, the products of their
elements lie in some finite regular subcomodule. This packages the multiplication map needed
to compare tensor-compatible natural transformations on finite regular subcomodules.

## Main declarations

* `TauCeti.Comodule.Hom.regularMul`: multiplication as a morphism from the tensor square
  of the regular comodule.
* `TauCeti.Subcomodule.mulHom`: multiplication corestricted to a containing regular
  subcomodule.
* `TauCeti.Subcomodule.exists_finite_mul_le`: two finite regular subcomodules have all
  their pairwise products in a third finite regular subcomodule.

## References

The regular-comodule multiplication is the coalgebra-homomorphism part of the bialgebra
axioms; see Sweedler, *Hopf Algebras*, Chapter 2. The finite containment argument uses the
finite-subcomodule theorem from the same chapter.

This advances the Layer 1 Tannakian reconstruction milestone of the reductive-groups
roadmap, `ReductiveGroups/README.md` in TauCetiRoadmap: tensor naturality applied to these
multiplication morphisms supplies the multiplicativity law for the reconstructed point.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

namespace Comodule.Hom

variable {R : Type u} {H : Type v}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]

attribute [local instance] Comodule.tensor

/-- Multiplication of a bialgebra, regarded as a morphism from the tensor square of its
regular right comodule to the regular right comodule. -/
@[expose]
noncomputable def regularMul : Hom R H (H ⊗[R] H) H where
  toLinearMap := LinearMap.mul' R H
  map_coact := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.mul'_apply]
    change TensorProduct.map (LinearMap.mul' R H) LinearMap.id
        (Comodule.tensorCoact (R := R) (C := H) (M := H) (N := H) (x ⊗ₜ[R] y)) =
      Coalgebra.comul (R := R) (A := H) (x * y)
    rw [Comodule.tensorCoact_tmul]
    have combine_mul (a b : H ⊗[R] H) :
        TensorProduct.map (LinearMap.mul' R H) LinearMap.id
            (Comodule.tensorCombine (R := R) (C := H) (M := H) (N := H) (a ⊗ₜ[R] b)) =
          TensorProduct.map (LinearMap.mul' R H) (LinearMap.mul' R H)
            (TensorProduct.tensorTensorTensorComm R H H H H (a ⊗ₜ[R] b)) := by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add a₁ a₂ ha₁ ha₂ =>
        simp only [TensorProduct.add_tmul, map_add, ha₁, ha₂]
      | tmul a₁ a₂ =>
        induction b using TensorProduct.induction_on with
        | zero => simp
        | add b₁ b₂ hb₁ hb₂ =>
          simp only [TensorProduct.tmul_add, map_add, hb₁, hb₂]
        | tmul b₁ b₂ => simp
    rw [combine_mul]
    have h := CoalgHomClass.map_comp_comul_apply (Bialgebra.mulCoalgHom R H) (x ⊗ₜ[R] y)
    change TensorProduct.map (LinearMap.mul' R H) (LinearMap.mul' R H)
        (TensorProduct.tensorTensorTensorComm R H H H H
          (Coalgebra.comul (R := R) (A := H) x ⊗ₜ[R]
            Coalgebra.comul (R := R) (A := H) y)) =
      Coalgebra.comul (R := R) (A := H) (x * y) at h
    exact h

/-- The underlying linear map of regular-comodule multiplication is bialgebra
multiplication. -/
@[simp]
theorem regularMul_toLinearMap :
    (regularMul (R := R) (H := H)).toLinearMap = LinearMap.mul' R H :=
  rfl

/-- Regular-comodule multiplication sends a pure tensor to the product of its factors. -/
@[simp]
theorem regularMul_tmul (x y : H) : regularMul (R := R) (H := H) (x ⊗ₜ[R] y) = x * y :=
  rfl

end Comodule.Hom

namespace Subcomodule

variable {R : Type u} {H : Type v}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]

attribute [local instance] Comodule.tensor

/-- Multiplication from `N ⊗ P`, corestricted to a regular subcomodule `Q` containing
every product `n * p`. -/
@[expose]
noncomputable def mulHom (N P Q : Subcomodule R H H)
    [Module.Flat R H]
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q) :
    Comodule.Hom R H (N ⊗[R] P) Q :=
  let ambient : Comodule.Hom R H (N ⊗[R] P) H :=
    (Comodule.Hom.regularMul (R := R) (H := H)).comp
      (Comodule.Hom.tensorMap (Subcomodule.subtype N) (Subcomodule.subtype P))
  ambient.codRestrict Q (by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact Q.toSubmodule.zero_mem
    | add x y hx hy =>
      change ambient.toLinearMap (x + y) ∈ Q
      rw [map_add]
      exact Q.toSubmodule.add_mem hx hy
    | tmul n p => simpa [ambient] using h n p)

/-- Corestricted regular multiplication sends a pure tensor to the product of its
factors. -/
@[simp]
theorem mulHom_tmul (N P Q : Subcomodule R H H)
    [Module.Flat R H]
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q) (n : N) (p : P) :
    ((mulHom N P Q h) (n ⊗ₜ[R] p) : H) = (n : H) * (p : H) := by
  simp [mulHom]

/-- The underlying linear map of corestricted regular multiplication is Mathlib's
`Submodule.mulMap`, with codomain restricted to `Q`. -/
@[simp]
theorem mulHom_toLinearMap (N P Q : Subcomodule R H H)
    [Module.Flat R H]
    (h : ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q) :
    (mulHom N P Q h).toLinearMap =
      (Submodule.mulMap N.toSubmodule P.toSubmodule).codRestrict Q.toSubmodule (by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => exact Q.toSubmodule.zero_mem
        | add x y hx hy =>
          rw [map_add]
          exact Q.toSubmodule.add_mem hx hy
        | tmul n p => exact h n p) := by
  apply TensorProduct.ext'
  intro n p
  exact Subtype.ext (mulHom_tmul N P Q h n p)

/-- Pairwise products from two finite regular subcomodules lie in a third finite regular
subcomodule.

The image of `Submodule.mulMap` is finitely generated because its tensor-product source is
finite. The finite-subcomodule theorem then supplies a regular subcomodule containing that
image. -/
theorem exists_finite_mul_le [Module.Free R H] (N P : Subcomodule R H H)
    [Module.Finite R N.toSubmodule] [Module.Finite R P.toSubmodule] :
    ∃ Q : Subcomodule R H H, Module.Finite R Q.toSubmodule ∧
      ∀ (n : N) (p : P), (n : H) * (p : H) ∈ Q := by
  let f := Submodule.mulMap N.toSubmodule P.toSubmodule
  obtain ⟨Q, hQfinite, hQ⟩ :=
    exists_finite_subcomodule_of_fg (R := R) (C := H) (M := H)
      f.range (Submodule.fg_range f)
  refine ⟨Q, hQfinite, fun n p ↦ hQ ?_⟩
  exact ⟨n ⊗ₜ[R] p, rfl⟩

end Subcomodule

end TauCeti
