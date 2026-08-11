/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal

/-!
# The symmetric monoidal category of finite comodules

This file equips finitely generated right comodules over a commutative bialgebra with their
standard symmetric monoidal structure. The braiding is the ordinary tensor-product swap

`m ⊗ n ↦ n ⊗ m`.

The swap respects the diagonal coaction because commutativity identifies the coefficient
products `m₁n₁` and `n₁m₁`. Its compatibility with the coaction is isolated in
`Comodule.tensorCombine_comm`. The remaining naturality, hexagon, and symmetry laws are
inherited from `SemimoduleCat` along the faithful monoidal forgetful functor.

## Main declarations

* `TauCeti.FGComoduleCat.tensorBraiding`: the tensor-product swap as a comodule isomorphism.
* `BraidedCategory (TauCeti.FGComoduleCat R C)`: the induced braided structure.
* `SymmetricCategory (TauCeti.FGComoduleCat R C)`: the standard symmetric structure.
* `TauCeti.FGComoduleCat.braiding_hom_apply` and `braiding_inv_apply`: the two concrete
  formulas for the braiding.

## References

This is the symmetric-category part of Layer 1 of the Tau Ceti reductive-groups roadmap,
`ReductiveGroups/README.md` in TauCetiRoadmap. It advances the requested rigid monoidal
category of finite-dimensional comodules and the later Tannakian reconstruction target.
The construction is standard; see Sweedler, *Hopf Algebras*, Chapter 2. The categorical
packaging follows Mathlib's symmetric structure on `SemimoduleCat` and uses
`BraidedCategory.ofFaithful` and `SymmetricCategory.ofFaithful`.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct
open TensorProduct

namespace TauCeti

universe u v

namespace FGComoduleCat

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [CommSemiring C] [Bialgebra R C]

attribute [local instance] Comodule.tensor

/-- The braiding on finite comodules: the ordinary tensor-product swap, which intertwines
the diagonal coactions because the coefficient bialgebra is commutative. -/
noncomputable def tensorBraiding (M N : FGComoduleCat.{u, v, u} R C) :
    tensor R C M N ≅ tensor R C N M :=
  isoOfLinearEquiv (TensorProduct.comm R M N) <| by
    -- As for the associator and unitors in `Finite.Monoidal`, cross the module boundary through
    -- the exposed elementwise coaction API and the carrier-generic compatibility lemma.
    have h : TensorProduct.map (TensorProduct.comm R M N).toLinearMap
          (LinearMap.id : C →ₗ[R] C) ∘ₗ
          Comodule.coact (R := R) (C := C) (M := M ⊗[R] N) =
        Comodule.coact (R := R) (C := C) (M := N ⊗[R] M) ∘ₗ
          (TensorProduct.comm R M N).toLinearMap := by
      apply TensorProduct.ext'
      intro m n
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.comm_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul]
      exact Comodule.tensorCombine_comm (R := R) (C := C)
        (Comodule.coact (R := R) (C := C) (M := M) m)
        (Comodule.coact (R := R) (C := C) (M := N) n)
    exact h

/-- The tensor-product swap makes finite comodules over a commutative bialgebra braided. -/
noncomputable instance instBraidedCategory :
    BraidedCategory (FGComoduleCat.{u, v, u} R C) :=
  BraidedCategory.ofFaithful
    (forget₂ (FGComoduleCat.{u, v, u} R C) (SemimoduleCat.{u} R))
    (tensorBraiding R C) <| by
      intro M N
      ext : 1
      apply TensorProduct.ext'
      intro m n
      rfl

/-- The forgetful functor from finite comodules to semimodules preserves the braiding. -/
noncomputable instance instForgetBraided :
    (forget₂ (FGComoduleCat.{u, v, u} R C) (SemimoduleCat.{u} R)).Braided where
  braided M N := by
    ext : 1
    apply TensorProduct.ext'
    intro m n
    rfl

/-- Finite comodules over a commutative bialgebra form a symmetric monoidal category. -/
noncomputable instance instSymmetricCategory :
    SymmetricCategory (FGComoduleCat.{u, v, u} R C) :=
  SymmetricCategory.ofFaithful
    (forget₂ (FGComoduleCat.{u, v, u} R C) (SemimoduleCat.{u} R))

variable {R C}
variable {M N : FGComoduleCat.{u, v, u} R C}

/-- The monoidal braiding is the named tensor-product swap. -/
@[simp]
theorem tensorBraiding_eq : tensorBraiding R C M N = β_ M N :=
  rfl

/-- The braiding sends `m ⊗ n` to `n ⊗ m`. -/
@[simp]
theorem braiding_hom_apply (m : M) (n : N) : (β_ M N).hom (m ⊗ₜ[R] n) = n ⊗ₜ[R] m :=
  TensorProduct.comm_tmul R M N m n

/-- The inverse braiding sends `n ⊗ m` back to `m ⊗ n`. -/
@[simp]
theorem braiding_inv_apply (n : N) (m : M) : (β_ M N).inv (n ⊗ₜ[R] m) = m ⊗ₜ[R] n :=
  TensorProduct.comm_symm_tmul R M N m n

end FGComoduleCat

end TauCeti
