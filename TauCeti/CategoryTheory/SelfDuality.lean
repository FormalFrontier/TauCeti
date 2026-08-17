/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites

/-!
# Involutive contravariant endofunctors

A contravariant endofunctor `F : Cᵒᵖ ⥤ C` is *involutive* when double dualization is naturally
isomorphic to the identity. The linear dual on finite-dimensional vector spaces and finite
dualization of finite locally free Hopf algebras are the motivating examples.

Turning such an `F` into an equivalence `Cᵒᵖ ≌ C` by `CategoryTheory.Functor.asEquivalence`
loses the involutivity: the inverse produced there is an abstract quasi-inverse, so no theorem
identifies it with `F` again. `CategoryTheory.Functor.dualityEquivalence` instead takes the
double-dual isomorphism as input and returns an equivalence whose inverse is `F.rightOp`, so
both directions and both structural isomorphisms compute.

## Main declarations

* `CategoryTheory.Functor.dualityEquivalence`: the anti-equivalence attached to an involutive
  contravariant endofunctor, together with the computations of its functor, inverse, unit and
  counit.
-/

public section

namespace CategoryTheory

open Opposite

universe v u

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ C) (ev : 𝟭 C ≅ F.rightOp ⋙ F)

namespace Functor

/-- The triangle identity for a double-dual isomorphism `ev : 𝟭 C ≅ F.rightOp ⋙ F`: dualizing
`ev` at `X` and evaluating at the dual of `X` are inverse to one another. -/
abbrev IsInvolutiveDual : Prop :=
  ∀ X : C, F.map (ev.inv.app X).op ≫ ev.inv.app (F.obj (op X)) = 𝟙 (F.obj (op X))

variable (triangle : IsInvolutiveDual F ev)

/-- An involutive contravariant endofunctor is an anti-equivalence.

The double-dual isomorphism `ev` plays the role of the counit and the opposite of its inverse
plays the role of the unit, so unlike `CategoryTheory.Functor.asEquivalence` the inverse of the
resulting equivalence is `F.rightOp`: dualizing back is the same operation as dualizing. -/
@[expose, simps! functor inverse]
def dualityEquivalence : Cᵒᵖ ≌ C where
  functor := F
  inverse := F.rightOp
  unitIso := NatIso.ofComponents (fun X => (ev.app X.unop).symm.op)
    (fun f => Quiver.Hom.unop_inj (ev.inv.naturality f.unop).symm)
  counitIso := ev.symm
  functor_unitIso_comp X := triangle X.unop

/-- The unit of `dualityEquivalence` is the opposite of the inverse double-dual isomorphism. -/
@[simp]
theorem dualityEquivalence_unitIso_hom_app (X : Cᵒᵖ) :
    (dualityEquivalence F ev triangle).unitIso.hom.app X = (ev.inv.app X.unop).op :=
  rfl

/-- The counit of `dualityEquivalence` is the inverse double-dual isomorphism. -/
@[simp]
theorem dualityEquivalence_counitIso_hom_app (X : C) :
    (dualityEquivalence F ev triangle).counitIso.hom.app X = ev.inv.app X :=
  rfl

end Functor

end CategoryTheory
