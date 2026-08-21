/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cat
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of comodules

Let `C` be a coalgebra over a commutative semiring `R`, and let `A` be an
`R`-algebra. This file constructs scalar extension of the underlying-module functor on all
comodules:

```text
ComoduleCat R C ⥤ SemimoduleCat A,      M ↦ A ⊗[R] M.
```

No finiteness or bialgebra structure is needed for the construction.

## Main declarations

* `TauCeti.ComoduleCat.scalarExtensionFunctor`: scalar extension on all comodules.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable (A : Type x) [Semiring A] [Algebra R A]

namespace ComoduleCat

/-- Scalar extension of the underlying-module functor on comodules. -/
noncomputable def scalarExtensionFunctor :
    ComoduleCat.{u, v, w} R C ⥤ SemimoduleCat.{max x w} A where
  obj M := SemimoduleCat.of A (A ⊗[R] M)
  map f := SemimoduleCat.ofHom (f.toLinearMap.baseChange A)
  map_id M := by
    apply SemimoduleCat.hom_ext
    -- `SemimoduleCat.hom_ext` leaves the bundled map of an identity comodule morphism;
    -- reducing that wrapper exposes precisely the linear-map base-change identity.
    change (LinearMap.id : M →ₗ[R] M).baseChange A = LinearMap.id
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply SemimoduleCat.hom_ext
    -- As above, reduction turns composition of bundled comodule morphisms into composition
    -- of their underlying linear maps, where the base-change API applies.
    change (g.toLinearMap ∘ₗ f.toLinearMap).baseChange A =
      g.toLinearMap.baseChange A ∘ₗ f.toLinearMap.baseChange A
    exact LinearMap.baseChange_comp f.toLinearMap g.toLinearMap

/-- Scalar extension sends `M` to the semimodule `A ⊗[R] M`. -/
@[simp]
theorem scalarExtensionFunctor_obj (M : ComoduleCat.{u, v, w} R C) :
    (scalarExtensionFunctor R C A).obj M = SemimoduleCat.of A (A ⊗[R] M) :=
  (rfl)

/-- Scalar extension maps a comodule morphism to base change of its underlying linear map. -/
@[simp]
theorem scalarExtensionFunctor_map {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (scalarExtensionFunctor R C A).map f =
      eqToHom (scalarExtensionFunctor_obj R C A M) ≫
        SemimoduleCat.ofHom (f.toLinearMap.baseChange A) ≫
          eqToHom (scalarExtensionFunctor_obj R C A N).symm :=
  (rfl)

end ComoduleCat

end TauCeti
