/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.RightRigid
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Symmetric

/-!
# Rigidity of finite-dimensional comodules

Let `H` be a commutative Hopf algebra over a field `k`. This file upgrades the existing
right-rigid monoidal structure on `FGComoduleCat.{u,v,u} k H` to a rigid monoidal structure.

The chosen right dual remains the antipode-twisted linear dual from
`TauCeti.Algebra.Coalgebra.Comodule.Finite.RightRigid`. Commutativity of `H` supplies the
braiding from `TauCeti.Algebra.Coalgebra.Comodule.Finite.Symmetric`, and the generic braided
rigidity construction reverses each exact pairing to obtain a left dual. In Mathlib's
terminology, the existing pairing has coevaluation `𝟙_ C ⟶ M ⊗ Mᘁ` and evaluation
`Mᘁ ⊗ M ⟶ 𝟙_ C`, and is called a right dual.

No cocommutativity or finite-dimensionality hypothesis is imposed on `H`. The carrier universe
of the finite comodules agrees with that of `k`, so that linear duals remain in the same category.

## Main declarations

* `TauCeti.FGComoduleCat.instRigidCategory`: finite-dimensional comodules over a commutative
  Hopf algebra form a rigid monoidal category.
-/

public section

open CategoryTheory

namespace TauCeti.FGComoduleCat

universe u v

variable (k : Type u) [Field k]
variable (H : Type v) [CommSemiring H] [HopfAlgebra k H]

/-- Finite-dimensional comodules over a commutative Hopf algebra form a rigid monoidal category.
The chosen right duals are the antipode-twisted linear duals. -/
noncomputable instance instRigidCategory :
    RigidCategory (FGComoduleCat.{u, v, u} k H) :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

end TauCeti.FGComoduleCat
