/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Intertwiners of linear automorphisms

A linear map `f : V →ₗ[K] W` **intertwines** automorphisms `a` of `V` and `b` of `W` when
`f ∘ a = b ∘ f`. This is the heterogeneous form of `SemiconjBy`: source and target live in
different modules, so the relation is not a statement inside one monoid and Mathlib's
`SemiconjBy` API does not apply to it.

## Main declarations

* `TauCeti.GeneralLinearGroup.comp_inv_eq_of_comp_eq`: an intertwiner of two automorphisms also
  intertwines their inverses.
-/

public section

namespace TauCeti

open LinearMap

namespace GeneralLinearGroup

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- **Intertwining passes to inverses.** If `f` intertwines the automorphisms `a` and `b`, then it
intertwines `a⁻¹` and `b⁻¹`. -/
theorem comp_inv_eq_of_comp_eq (f : V →ₗ[K] W) (a : GeneralLinearGroup K V)
    (b : GeneralLinearGroup K W)
    (hab : f.comp (a : Module.End K V) = (b : Module.End K W).comp f) :
    f.comp (↑a⁻¹ : Module.End K V) = (↑b⁻¹ : Module.End K W).comp f := by
  have hb : (↑b⁻¹ : Module.End K W).comp (b : Module.End K W) = LinearMap.id := b.inv_val
  have ha : (a : Module.End K V).comp (↑a⁻¹ : Module.End K V) = LinearMap.id := a.val_inv
  calc f.comp (↑a⁻¹ : Module.End K V)
      = ((LinearMap.id : Module.End K W).comp f).comp (↑a⁻¹ : Module.End K V) := by
        rw [LinearMap.id_comp]
    _ = (↑b⁻¹ : Module.End K W).comp ((f.comp (a : Module.End K V)).comp
          (↑a⁻¹ : Module.End K V)) := by
        rw [← hb, hab]
        simp only [LinearMap.comp_assoc]
    _ = (↑b⁻¹ : Module.End K W).comp f := by
        rw [LinearMap.comp_assoc, ha, LinearMap.comp_id]

end GeneralLinearGroup

end TauCeti
