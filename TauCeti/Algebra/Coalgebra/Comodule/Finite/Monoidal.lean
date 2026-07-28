/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.TensorProduct
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# The monoidal category of finitely generated comodules

This file equips finitely generated right comodules over a bialgebra with their standard
monoidal structure. The tensor product is the diagonal comodule constructed in
`TauCeti.Algebra.Coalgebra.Comodule.Finite.TensorProduct`, and the tensor unit is the base
semiring with its trivial coaction.

The associator and unitors are the usual tensor-product linear equivalences. Their
compatibility with the diagonal coaction reduces on pure coaction tensors to associativity
and the unit laws in the coefficient bialgebra. The coherence laws are then inherited from
`SemimoduleCat` along the faithful forgetful functor.

## Main declarations

* `TauCeti.FGComoduleCat.tensorUnit`: the finitely generated trivial comodule on the base.
* `MonoidalCategory (TauCeti.FGComoduleCat R C)`: the standard monoidal category structure.
* `TauCeti.FGComoduleCat.tensorHom_tmul`: tensor products of morphisms on pure tensors.
* `TauCeti.FGComoduleCat.leftUnitor_hom_apply`,
  `TauCeti.FGComoduleCat.rightUnitor_hom_apply`, and
  `TauCeti.FGComoduleCat.associator_hom_apply`: concrete formulas for the coherence maps.

## References

This is the monoidal-category part of Layer 1 of the Tau Ceti reductive-groups roadmap,
`ReductiveGroups/README.md` in TauCetiRoadmap, which asks for the rigid monoidal category of
finite-dimensional comodules. The construction is standard; see Sweedler, *Hopf Algebras*,
Chapter 2. The categorical packaging follows Mathlib's monoidal structure on `SemimoduleCat`
in `Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct
open TensorProduct

namespace TauCeti

universe u v

namespace FGComoduleCat

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [Semiring C] [Bialgebra R C]

attribute [local instance] Comodule.tensor

/-- The tensor unit in finitely generated right comodules: the base semiring with the trivial
coaction `r ↦ r ⊗ 1`. -/
noncomputable abbrev tensorUnit : FGComoduleCat.{u, v, u} R C :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  of (R := R) (C := C) R

/-- Reassociation of tensor products as an isomorphism of finite comodules. -/
noncomputable def associator
    (M N P : FGComoduleCat.{u, v, u} R C) :
    tensor R C (tensor R C M N) P ≅ tensor R C M (tensor R C N P) where
  hom :=
    ofHom
      { toLinearMap := (TensorProduct.assoc R M N P).toLinearMap
        map_coact := by
          apply TensorProduct.ext_threefold
          intro m n p
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            TensorProduct.assoc_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul]
          rw [Comodule.tensor_coact (R := R) (C := C) (M := M) (N := N),
            Comodule.tensorCoact_tmul,
            Comodule.tensor_coact (R := R) (C := C) (M := N) (N := P),
            Comodule.tensorCoact_tmul]
          exact Comodule.tensorCombine_assoc (R := R) (C := C)
            (Comodule.coact (R := R) (C := C) (M := M) m)
            (Comodule.coact (R := R) (C := C) (M := N) n)
            (Comodule.coact (R := R) (C := C) (M := P) p) }
  inv :=
    ofHom
      { toLinearMap := (TensorProduct.assoc R M N P).symm.toLinearMap
        map_coact := by
          apply TensorProduct.ext_threefold'
          intro m n p
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            TensorProduct.assoc_symm_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul]
          rw [Comodule.tensor_coact (R := R) (C := C) (M := N) (N := P),
            Comodule.tensorCoact_tmul,
            Comodule.tensor_coact (R := R) (C := C) (M := M) (N := N),
            Comodule.tensorCoact_tmul]
          exact Comodule.tensorCombine_assoc_symm (R := R) (C := C)
            (Comodule.coact (R := R) (C := C) (M := M) m)
            (Comodule.coact (R := R) (C := C) (M := N) n)
            (Comodule.coact (R := R) (C := C) (M := P) p) }
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact (TensorProduct.assoc R M N P).symm_apply_apply
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact (TensorProduct.assoc R M N P).apply_symm_apply

/-- The base semiring with its trivial coaction is a left tensor unit for finite comodules. -/
noncomputable def leftUnitor (M : FGComoduleCat.{u, v, u} R C) :
    tensor R C (tensorUnit R C) M ≅ M :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  {
  hom :=
    ofHom
      { toLinearMap := (TensorProduct.lid R M).toLinearMap
        map_coact := by
          apply TensorProduct.ext'
          intro r m
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            TensorProduct.lid_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul,
            Comodule.trivial_coact_apply]
          rw [map_smul]
          exact Comodule.tensorCombine_lid (R := R) (C := C) r
            (Comodule.coact (R := R) (C := C) (M := M) m) }
  inv :=
    ofHom
      { toLinearMap := (TensorProduct.lid R M).symm.toLinearMap
        map_coact := by
          ext m
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            TensorProduct.lid_symm_apply, Comodule.tensor_coact, Comodule.tensorCoact_tmul,
            Comodule.trivial_coact_apply]
          exact (Comodule.tensorCombine_lid_symm (R := R) (C := C)
            (Comodule.coact (R := R) (C := C) (M := M) m)).symm }
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact (TensorProduct.lid R M).symm_apply_apply
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact (TensorProduct.lid R M).apply_symm_apply
  }

/-- The base semiring with its trivial coaction is a right tensor unit for finite comodules. -/
noncomputable def rightUnitor (M : FGComoduleCat.{u, v, u} R C) :
    tensor R C M (tensorUnit R C) ≅ M :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  {
  hom :=
    ofHom
      { toLinearMap := (TensorProduct.rid R M).toLinearMap
        map_coact := by
          apply TensorProduct.ext'
          intro m r
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            TensorProduct.rid_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul,
            Comodule.trivial_coact_apply]
          rw [map_smul]
          exact Comodule.tensorCombine_rid (R := R) (C := C)
            (Comodule.coact (R := R) (C := C) (M := M) m) r }
  inv :=
    ofHom
      { toLinearMap := (TensorProduct.rid R M).symm.toLinearMap
        map_coact := by
          ext m
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
            TensorProduct.rid_symm_apply, Comodule.tensor_coact, Comodule.tensorCoact_tmul,
            Comodule.trivial_coact_apply]
          exact (Comodule.tensorCombine_rid_symm (R := R) (C := C)
            (Comodule.coact (R := R) (C := C) (M := M) m)).symm }
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact (TensorProduct.rid R M).symm_apply_apply
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ComoduleCat.hom_ext
    exact (TensorProduct.rid R M).apply_symm_apply
  }

/-- The tensor product, trivial unit, associator, and unitors on finitely generated right
comodules over a bialgebra. -/
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct (FGComoduleCat.{u, v, u} R C) where
  tensorObj := tensor R C
  whiskerLeft M _ _ f := tensorMap (𝟙 M) f
  whiskerRight f M := tensorMap f (𝟙 M)
  tensorHom := tensorMap
  tensorUnit := tensorUnit R C
  associator := associator R C
  leftUnitor := leftUnitor R C
  rightUnitor := rightUnitor R C

/-- The forgetful functor to semimodules strictly preserves the chosen monoidal data. -/
noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData
      (forget₂ (FGComoduleCat.{u, v, u} R C) (SemimoduleCat.{u} R)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  associator_eq _ _ _ := by
    ext1
    exact TensorProduct.ext (TensorProduct.ext rfl)
  leftUnitor_eq _ := by
    ext1
    exact TensorProduct.ext rfl
  rightUnitor_eq _ := by
    ext1
    exact TensorProduct.ext rfl

/-- Finitely generated right comodules over a bialgebra form a monoidal category under the
diagonal tensor product. Over a field, these are precisely finite-dimensional comodules. -/
noncomputable instance instMonoidalCategory :
    MonoidalCategory (FGComoduleCat.{u, v, u} R C) :=
  Monoidal.induced
    (forget₂ (FGComoduleCat.{u, v, u} R C) (SemimoduleCat.{u} R))
    (inducingFunctorData R C)

variable {R C}
variable {M M' N N' P : FGComoduleCat.{u, v, u} R C}

/-- The monoidal tensor product of two finite-comodule morphisms is their ordinary tensor
product on underlying linear maps. -/
@[simp]
theorem tensorHom_toLinearMap (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ₘ g).hom.toLinearMap =
      TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap :=
  rfl

/-- The monoidal tensor product of finite-comodule morphisms acts componentwise on pure
tensors. -/
@[simp]
theorem tensorHom_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    (f ⊗ₘ g) (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n :=
  rfl

/-- The left unitor acts by scalar multiplication. -/
@[simp]
theorem leftUnitor_hom_apply (r : R) (m : M) :
    (λ_ M).hom (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

/-- The inverse left unitor sends `m` to `1 ⊗ m`. -/
@[simp]
theorem leftUnitor_inv_apply (m : M) :
    (λ_ M).inv m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

/-- The right unitor acts by scalar multiplication. -/
@[simp]
theorem rightUnitor_hom_apply (m : M) (r : R) :
    (ρ_ M).hom (m ⊗ₜ[R] r) = r • m :=
  TensorProduct.rid_tmul m r

/-- The inverse right unitor sends `m` to `m ⊗ 1`. -/
@[simp]
theorem rightUnitor_inv_apply (m : M) :
    (ρ_ M).inv m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

/-- The associator sends `(m ⊗ n) ⊗ p` to `m ⊗ (n ⊗ p)`. -/
@[simp]
theorem associator_hom_apply (m : M) (n : N) (p : P) :
    (α_ M N P).hom (m ⊗ₜ[R] n ⊗ₜ[R] p) = m ⊗ₜ[R] (n ⊗ₜ[R] p) :=
  TensorProduct.assoc_tmul m n p

/-- The inverse associator sends `m ⊗ (n ⊗ p)` to `(m ⊗ n) ⊗ p`. -/
@[simp]
theorem associator_inv_apply (m : M) (n : N) (p : P) :
    (α_ M N P).inv (m ⊗ₜ[R] (n ⊗ₜ[R] p)) = m ⊗ₜ[R] n ⊗ₜ[R] p :=
  by
    rw [← associator_hom_apply]
    exact Iso.hom_inv_id_apply (α_ M N P) _

end FGComoduleCat

end TauCeti
