/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of comodules

Let `C` be a coalgebra over a commutative semiring `R`, and let `A` be a commutative
`R`-algebra. This file constructs scalar extension of the underlying-module functor on all
comodules, and its restriction to finitely generated comodules:

```text
ComoduleCat R C ⥤ SemimoduleCat A,      M ↦ A ⊗[R] M,
FGComoduleCat R C ⥤ SemimoduleCat A,    M ↦ A ⊗[R] M.
```

No finiteness or bialgebra structure is needed for the construction.

## Main declarations

* `TauCeti.ComoduleCat.scalarExtensionFunctor`: scalar extension on all comodules.
* `TauCeti.FGComoduleCat.scalarExtensionFunctor`: its restriction to finitely generated
  comodules.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable (A : Type u) [CommSemiring A] [Algebra R A]

namespace ComoduleCat

/-- Scalar extension of the underlying-module functor on comodules. -/
noncomputable def scalarExtensionFunctor :
    ComoduleCat.{u, v, u} R C ⥤ SemimoduleCat.{u} A where
  obj M := SemimoduleCat.of A (A ⊗[R] M)
  map f := SemimoduleCat.ofHom (f.toLinearMap.baseChange A)
  map_id M := by
    apply SemimoduleCat.hom_ext
    change (LinearMap.id : M →ₗ[R] M).baseChange A = LinearMap.id
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply SemimoduleCat.hom_ext
    change (g.toLinearMap ∘ₗ f.toLinearMap).baseChange A =
      g.toLinearMap.baseChange A ∘ₗ f.toLinearMap.baseChange A
    exact LinearMap.baseChange_comp f.toLinearMap g.toLinearMap

/-- Scalar extension sends `M` to the semimodule `A ⊗[R] M`. -/
@[simp]
theorem scalarExtensionFunctor_obj (M : ComoduleCat.{u, v, u} R C) :
    (scalarExtensionFunctor R C A).obj M = SemimoduleCat.of A (A ⊗[R] M) :=
  (rfl)

/-- Scalar extension maps a comodule morphism to base change of its underlying linear map. -/
@[simp]
theorem scalarExtensionFunctor_map {M N : ComoduleCat.{u, v, u} R C} (f : M ⟶ N) :
    (scalarExtensionFunctor R C A).map f =
      eqToHom (scalarExtensionFunctor_obj R C A M) ≫
        SemimoduleCat.ofHom (f.toLinearMap.baseChange A) ≫
          eqToHom (scalarExtensionFunctor_obj R C A N).symm :=
  (rfl)

end ComoduleCat

namespace FGComoduleCat

/-- Scalar extension of the underlying-module functor on finitely generated comodules. -/
noncomputable def scalarExtensionFunctor :
    FGComoduleCat.{u, v, u} R C ⥤ SemimoduleCat.{u} A :=
  incl ⋙ ComoduleCat.scalarExtensionFunctor R C A

/-- Finite-comodule scalar extension is obtained by precomposing scalar extension on all
comodules with the inclusion functor. -/
theorem scalarExtensionFunctor_eq :
    scalarExtensionFunctor R C A =
      incl ⋙ ComoduleCat.scalarExtensionFunctor R C A :=
  (rfl)

/-- Finite-comodule scalar extension sends `M` to the semimodule `A ⊗[R] M`. -/
@[simp]
theorem scalarExtensionFunctor_obj (M : FGComoduleCat.{u, v, u} R C) :
    (scalarExtensionFunctor R C A).obj M = SemimoduleCat.of A (A ⊗[R] M) :=
  (rfl)

/-- Scalar extension maps a finite-comodule morphism to base change of its underlying linear
map. -/
@[simp]
theorem scalarExtensionFunctor_map {M N : FGComoduleCat.{u, v, u} R C} (f : M ⟶ N) :
    (scalarExtensionFunctor R C A).map f =
      eqToHom (scalarExtensionFunctor_obj R C A M) ≫
        SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A) ≫
          eqToHom (scalarExtensionFunctor_obj R C A N).symm :=
  (rfl)

end FGComoduleCat

end TauCeti
