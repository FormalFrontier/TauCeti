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
and the unit laws in the coefficient bialgebra; compatibility of the *inverse* maps is then
automatic, and is supplied by `TauCeti.FGComoduleCat.isoOfLinearEquiv`. The coherence laws are
inherited from `SemimoduleCat` along the faithful forgetful functor.

## Main declarations

* `TauCeti.FGComoduleCat.tensorUnit`: the finitely generated trivial comodule on the base.
* `TauCeti.FGComoduleCat.tensorAssociator`, `TauCeti.FGComoduleCat.tensorLeftUnitor`, and
  `TauCeti.FGComoduleCat.tensorRightUnitor`: the coherence isomorphisms, together with the
  `tensorAssociator_eq` family identifying them with `α_`, `λ_`, and `ρ_`.
* `MonoidalCategory (TauCeti.FGComoduleCat R C)`: the standard monoidal category structure.
* `TauCeti.FGComoduleCat.tensorHom_tmul`: tensor products of morphisms on pure tensors.
* `TauCeti.FGComoduleCat.leftUnitor_hom_apply`,
  `TauCeti.FGComoduleCat.rightUnitor_hom_apply`, and
  `TauCeti.FGComoduleCat.associator_hom_apply`: concrete formulas for the coherence maps.
* `TauCeti.FGComoduleCat.leftUnitor_hom_toLinearMap`,
  `TauCeti.FGComoduleCat.rightUnitor_hom_toLinearMap`, and
  `TauCeti.FGComoduleCat.associator_hom_toLinearMap`: the same formulas at the level of
  underlying linear maps, together with their inverse variants.

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

/-- The associator on finitely generated comodules: the associativity
equivalence of tensor products, which intertwines the diagonal coactions because the coefficient
multiplication is associative. The user-facing form is `α_`, characterized by
`associator_hom_apply` below. -/
noncomputable def tensorAssociator (M N P : FGComoduleCat.{u, v, u} R C) :
    tensor R C (tensor R C M N) P ≅ tensor R C M (tensor R C N P) :=
  isoOfLinearEquiv (TensorProduct.assoc R M N P) <| by
    -- The goal names the coactions of the bundled objects `tensor R C _ _`; the coaction lemmas
    -- below are stated for the underlying modules. `FGComoduleCat.tensor_coact` and
    -- `FGComoduleCat.of_coact` say the two agree, and both are `rfl` — but rewriting with them
    -- is not enough, because what remains needs `Comodule.tensorCoact` and
    -- `Comodule.tensorCombine` unfolded, and the module system does not expose either body
    -- here. So the crossing is a single `exact` per coherence map, isolated at the end.
    have h : TensorProduct.map (TensorProduct.assoc R M N P).toLinearMap
          (LinearMap.id : C →ₗ[R] C) ∘ₗ
          Comodule.coact (R := R) (C := C) (M := (M ⊗[R] N) ⊗[R] P) =
        Comodule.coact (R := R) (C := C) (M := M ⊗[R] (N ⊗[R] P)) ∘ₗ
          (TensorProduct.assoc R M N P).toLinearMap := by
      apply TensorProduct.ext_threefold
      intro m n p
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.assoc_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul]
      exact Comodule.tensorCombine_assoc (R := R) (C := C)
        (Comodule.coact (R := R) (C := C) (M := M) m)
        (Comodule.coact (R := R) (C := C) (M := N) n)
        (Comodule.coact (R := R) (C := C) (M := P) p)
    exact h

/-- The left unitor on finitely generated comodules: the equivalence
`R ⊗ M ≃ M`, which intertwines the diagonal coactions because `1` is a left unit for the
coefficient multiplication. The user-facing form is `λ_`, characterized by
`leftUnitor_hom_apply` below. -/
noncomputable def tensorLeftUnitor (M : FGComoduleCat.{u, v, u} R C) :
    tensor R C (tensorUnit R C) M ≅ M :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  isoOfLinearEquiv (TensorProduct.lid R M) <| by
    -- Unbundled restatement, as in `tensorAssociator`.
    have h : TensorProduct.map (TensorProduct.lid R M).toLinearMap
          (LinearMap.id : C →ₗ[R] C) ∘ₗ Comodule.coact (R := R) (C := C) (M := R ⊗[R] M) =
        Comodule.coact (R := R) (C := C) (M := M) ∘ₗ (TensorProduct.lid R M).toLinearMap := by
      apply TensorProduct.ext'
      intro r m
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul,
        Comodule.trivial_coact_apply]
      rw [map_smul]
      exact Comodule.tensorCombine_lid (R := R) (C := C) r
        (Comodule.coact (R := R) (C := C) (M := M) m)
    exact h

/-- The right unitor on finitely generated comodules: the equivalence
`M ⊗ R ≃ M`, which intertwines the diagonal coactions because `1` is a right unit for the
coefficient multiplication. The user-facing form is `ρ_`, characterized by
`rightUnitor_hom_apply` below. -/
noncomputable def tensorRightUnitor (M : FGComoduleCat.{u, v, u} R C) :
    tensor R C M (tensorUnit R C) ≅ M :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  isoOfLinearEquiv (TensorProduct.rid R M) <| by
    -- Unbundled restatement, as in `tensorAssociator`.
    have h : TensorProduct.map (TensorProduct.rid R M).toLinearMap
          (LinearMap.id : C →ₗ[R] C) ∘ₗ Comodule.coact (R := R) (C := C) (M := M ⊗[R] R) =
        Comodule.coact (R := R) (C := C) (M := M) ∘ₗ (TensorProduct.rid R M).toLinearMap := by
      apply TensorProduct.ext'
      intro m r
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.rid_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul,
        Comodule.trivial_coact_apply]
      rw [map_smul]
      exact Comodule.tensorCombine_rid (R := R) (C := C)
        (Comodule.coact (R := R) (C := C) (M := M) m) r
    exact h

/-- The tensor product, trivial unit, associator, and unitors on finitely generated right
comodules over a bialgebra. -/
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct (FGComoduleCat.{u, v, u} R C) where
  tensorObj := tensor R C
  whiskerLeft M _ _ f := tensorMap (𝟙 M) f
  whiskerRight f M := tensorMap f (𝟙 M)
  tensorHom := tensorMap
  tensorUnit := tensorUnit R C
  associator := tensorAssociator R C
  leftUnitor := tensorLeftUnitor R C
  rightUnitor := tensorRightUnitor R C

/-- Finitely generated right comodules over a bialgebra form a monoidal category under the
diagonal tensor product. Over a field, these are precisely finite-dimensional comodules. -/
noncomputable instance instMonoidalCategory :
    MonoidalCategory (FGComoduleCat.{u, v, u} R C) :=
  Monoidal.induced
    (forget₂ (FGComoduleCat.{u, v, u} R C) (SemimoduleCat.{u} R))
    {
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
    }

variable {R C}
variable {M M' N N' P : FGComoduleCat.{u, v, u} R C}

/-- The monoidal associator is the named one. Rewriting in this direction sends the
implementation name to the notation, where `associator_hom_apply` and `associator_inv_apply`
take over. -/
@[simp]
theorem tensorAssociator_eq : tensorAssociator R C M N P = α_ M N P :=
  rfl

/-- The monoidal left unitor is the named one; see `tensorAssociator_eq`. -/
@[simp]
theorem tensorLeftUnitor_eq : tensorLeftUnitor R C M = λ_ M :=
  rfl

/-- The monoidal right unitor is the named one; see `tensorAssociator_eq`. -/
@[simp]
theorem tensorRightUnitor_eq : tensorRightUnitor R C M = ρ_ M :=
  rfl

/-- The monoidal tensor product of two finite-comodule morphisms is their ordinary tensor
product on underlying linear maps. -/
@[simp]
theorem tensorHom_toLinearMap (f : M ⟶ M') (g : N ⟶ N') : (f ⊗ₘ g).hom.toLinearMap =
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
theorem leftUnitor_hom_apply (r : R) (m : M) : (λ_ M).hom (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

/-- The inverse left unitor sends `m` to `1 ⊗ m`. -/
@[simp]
theorem leftUnitor_inv_apply (m : M) : (λ_ M).inv m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

/-- The right unitor acts by scalar multiplication. -/
@[simp]
theorem rightUnitor_hom_apply (m : M) (r : R) : (ρ_ M).hom (m ⊗ₜ[R] r) = r • m :=
  TensorProduct.rid_tmul m r

/-- The inverse right unitor sends `m` to `m ⊗ 1`. -/
@[simp]
theorem rightUnitor_inv_apply (m : M) : (ρ_ M).inv m = m ⊗ₜ[R] 1 :=
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

/-- The associator has the associativity equivalence of tensor products underneath. -/
@[simp]
theorem associator_hom_toLinearMap :
    ((α_ M N P).hom).hom.toLinearMap = (TensorProduct.assoc R M N P).toLinearMap := by
  apply TensorProduct.ext_threefold
  intro m n p
  exact associator_hom_apply m n p

/-- The inverse associator has the inverse associativity equivalence underneath. -/
@[simp]
theorem associator_inv_toLinearMap :
    ((α_ M N P).inv).hom.toLinearMap = (TensorProduct.assoc R M N P).symm.toLinearMap := by
  apply TensorProduct.ext_threefold'
  intro m n p
  exact associator_inv_apply m n p

/-- The left unitor has the left tensor identity underneath. -/
@[simp]
theorem leftUnitor_hom_toLinearMap :
    ((λ_ M).hom).hom.toLinearMap = (TensorProduct.lid R M).toLinearMap := by
  apply TensorProduct.ext'
  intro r m
  exact leftUnitor_hom_apply r m

/-- The inverse left unitor has the inverse left tensor identity underneath. -/
@[simp]
theorem leftUnitor_inv_toLinearMap :
    ((λ_ M).inv).hom.toLinearMap = (TensorProduct.lid R M).symm.toLinearMap := by
  apply LinearMap.ext
  intro m
  exact leftUnitor_inv_apply m

/-- The right unitor has the right tensor identity underneath. -/
@[simp]
theorem rightUnitor_hom_toLinearMap :
    ((ρ_ M).hom).hom.toLinearMap = (TensorProduct.rid R M).toLinearMap := by
  apply TensorProduct.ext'
  intro m r
  exact rightUnitor_hom_apply m r

/-- The inverse right unitor has the inverse right tensor identity underneath. -/
@[simp]
theorem rightUnitor_inv_toLinearMap :
    ((ρ_ M).inv).hom.toLinearMap = (TensorProduct.rid R M).symm.toLinearMap := by
  apply LinearMap.ext
  intro m
  exact rightUnitor_inv_apply m

end FGComoduleCat

end TauCeti
