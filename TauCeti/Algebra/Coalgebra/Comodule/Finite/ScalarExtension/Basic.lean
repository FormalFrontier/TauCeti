/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.ScalarExtension
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Scalar extension of comodules

Let `C` be a coalgebra over a commutative semiring `R`, and let `A` be an
`R`-algebra. This file restricts scalar extension of the underlying-module functor to finitely
generated comodules:

```text
FGComoduleCat R C ⥤ SemimoduleCat A,    M ↦ A ⊗[R] M.
```

No finiteness or bialgebra structure is needed for the construction.

An automorphism of this functor is the same data as a family of `A`-linear automorphisms of the
scalar extensions that is natural in the comodule, and `autOfComponents` assembles one from the
other. Nothing beyond the coalgebra structure enters, and the value algebra need not be
commutative.

## Main declarations

* `TauCeti.FGComoduleCat.scalarExtensionFunctor`: its restriction to finitely generated
  comodules.
* `TauCeti.FGComoduleCat.autOfComponents`: a natural family of linear automorphisms as an
  automorphism of that functor.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable (A : Type x) [Semiring A] [Algebra R A]

namespace FGComoduleCat

/-- Scalar extension of the underlying-module functor on finitely generated comodules. -/
noncomputable def scalarExtensionFunctor :
    FGComoduleCat.{u, v, w} R C ⥤ SemimoduleCat.{max x w} A :=
  incl ⋙ ComoduleCat.scalarExtensionFunctor R C A

/-- Finite-comodule scalar extension is obtained by precomposing scalar extension on all
comodules with the inclusion functor. -/
theorem scalarExtensionFunctor_def :
    scalarExtensionFunctor R C A =
      incl ⋙ ComoduleCat.scalarExtensionFunctor R C A :=
  (rfl)

/-- Finite-comodule scalar extension sends `M` to the semimodule `A ⊗[R] M`. -/
@[simp]
theorem scalarExtensionFunctor_obj (M : FGComoduleCat.{u, v, w} R C) :
    (scalarExtensionFunctor R C A).obj M = SemimoduleCat.of A (A ⊗[R] M) :=
  ComoduleCat.scalarExtensionFunctor_obj R C A M.obj

/-- Scalar extension maps a finite-comodule morphism to base change of its underlying linear
map. -/
@[simp]
theorem scalarExtensionFunctor_map {M N : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (scalarExtensionFunctor R C A).map f =
      eqToHom (scalarExtensionFunctor_obj R C A M) ≫
        SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A) ≫
          eqToHom (scalarExtensionFunctor_obj R C A N).symm :=
  ComoduleCat.scalarExtensionFunctor_map R C A f.hom

/-- A family of `A`-linear automorphisms of the scalar extensions of the finitely generated
comodules, natural in the comodule, as an automorphism of the scalar-extension functor. -/
noncomputable def autOfComponents
    (F : ∀ M : FGComoduleCat.{u, v, w} R C, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, w} R C} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A) :
    Aut (scalarExtensionFunctor R C A) :=
  NatIso.ofComponents
    (fun M ↦ (eqToIso (scalarExtensionFunctor_obj R C A M)).trans
      ((F M).toLinearEquiv.toModuleIsoₛ.trans
        (eqToIso (scalarExtensionFunctor_obj R C A M).symm)))
    (fun {M N} g ↦ by
      -- `NatIso.ofComponents` hides the component isomorphism; reduce it once so that its
      -- naturality can be proved through the public scalar-extension and linear-equivalence
      -- APIs, then cancel the object transports against those in the functor's action.
      change
        (scalarExtensionFunctor R C A).map g ≫
            eqToHom (scalarExtensionFunctor_obj R C A N) ≫
              (F N).toLinearEquiv.toModuleIsoₛ.hom ≫
                eqToHom (scalarExtensionFunctor_obj R C A N).symm =
          eqToHom (scalarExtensionFunctor_obj R C A M) ≫
              (F M).toLinearEquiv.toModuleIsoₛ.hom ≫
                eqToHom (scalarExtensionFunctor_obj R C A M).symm ≫
                  (scalarExtensionFunctor R C A).map g
      rw [scalarExtensionFunctor_map]
      simp only [Category.assoc]
      rw [cancel_epi]
      simp only [← Category.assoc]
      rw [cancel_mono]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
        LinearEquiv.toModuleIsoₛ_hom]
      apply SemimoduleCat.hom_ext
      exact (hnat g).symm)

/-- The component of the automorphism assembled from a natural family of linear automorphisms is
that family, transported to the object chosen by the scalar-extension functor. -/
@[simp]
theorem autOfComponents_hom_app
    (F : ∀ M : FGComoduleCat.{u, v, w} R C, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, w} R C} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A)
    (M : FGComoduleCat.{u, v, w} R C) :
    (autOfComponents R C A F hnat).hom.app M =
      eqToHom (scalarExtensionFunctor_obj R C A M) ≫
        (F M).toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (scalarExtensionFunctor_obj R C A M).symm := by
  simp [autOfComponents]

/-- The inverse component of the automorphism assembled from a natural family of linear
automorphisms is the inverse family, transported the same way. -/
@[simp]
theorem autOfComponents_inv_app
    (F : ∀ M : FGComoduleCat.{u, v, w} R C, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, w} R C} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A)
    (M : FGComoduleCat.{u, v, w} R C) :
    (autOfComponents R C A F hnat).inv.app M =
      eqToHom (scalarExtensionFunctor_obj R C A M) ≫
        (F M).toLinearEquiv.toModuleIsoₛ.inv ≫
          eqToHom (scalarExtensionFunctor_obj R C A M).symm := by
  simp [autOfComponents]

end FGComoduleCat

end TauCeti
