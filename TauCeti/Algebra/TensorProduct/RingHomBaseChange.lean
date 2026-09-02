/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of modules along ring homomorphisms

This file provides the scalar extension of a module along a ring homomorphism and its universal
property.  It is independent of any particular coefficient ring or source of the homomorphism.
-/

public section

open scoped TensorProduct

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module A N]

/-- Scalar extension of an `R`-module along `ev : R →+* A`. -/
abbrev RingHom.baseChangeModule (ev : R →+* A) (M : Type*) [AddCommMonoid M] [Module R M] :=
  letI := ev.toAlgebra
  A ⊗[R] M

namespace _root_.RingHom.baseChangeModule

/-- The canonical semilinear map from an `R`-module to its scalar extension along `ev`. -/
noncomputable def of (ev : R →+* A) (M : Type*) [AddCommMonoid M] [Module R M] :
    M →ₛₗ[ev] RingHom.baseChangeModule ev M := by
  letI := ev.toAlgebra
  exact
    { toAddHom := (TensorProduct.mk R A M 1).toAddMonoidHom
      map_smul' := by
        intro r x
        -- The scalar action on the first tensor factor is evaluation through `ev`.
        change (1 : A) ⊗ₜ[R] (r • x) = ev r • ((1 : A) ⊗ₜ[R] x)
        rw [TensorProduct.tmul_smul]
        rfl }

/-- The canonical map sends an element to the corresponding tensor with `1`. -/
@[simp]
theorem of_apply (ev : R →+* A) (M : Type*) [AddCommMonoid M] [Module R M] (x : M) :
    letI := ev.toAlgebra
    of ev M x = (1 : A) ⊗ₜ[R] x := by
  simp [of]

/-- A pure tensor is a scalar multiple of a canonical element. -/
theorem tmul_eq_smul_of (ev : R →+* A) (a : A) (x : M) :
    letI := ev.toAlgebra
    a ⊗ₜ[R] x = a • of ev M x := by
  let _ : Algebra R A := ev.toAlgebra
  rw [of_apply]
  exact TensorProduct.tmul_eq_smul_one_tmul a x

/-- An element of a scalar extension can be handled by zero, scalar multiples of canonical
elements, and addition. -/
@[elab_as_elim]
theorem induction_on (ev : R →+* A) (M : Type*) [AddCommMonoid M] [Module R M]
    {motive : RingHom.baseChangeModule ev M → Prop}
    (z : RingHom.baseChangeModule ev M) (h_zero : motive 0)
    (h_smul : ∀ (a : A) (x : M), motive (a • of ev M x))
    (h_add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  let _ : Algebra R A := ev.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => exact h_zero
  | add x y hx hy => exact h_add x y hx hy
  | tmul a x =>
      rw [tmul_eq_smul_of]
      exact h_smul a x

/-- The scalar-linear map induced by a semilinear map through scalar extension. -/
noncomputable def lift (ev : R →+* A) (f : M →ₛₗ[ev] N)
    : RingHom.baseChangeModule ev M →ₗ[A] N := by
  let _ : Algebra R A := ev.toAlgebra
  let _ : Module R N := Module.compHom N ev
  let _ : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  let f' : M →ₗ[R] N :=
    { f with
      map_smul' := by
        intro r x
        change f (r • x) = ev r • f x
        exact f.map_smulₛₗ r x }
  exact f'.liftBaseChange A

/-- The lift computes to the original semilinear map on canonical elements. -/
@[simp]
theorem lift_of (ev : R →+* A) (f : M →ₛₗ[ev] N) (x : M) :
    letI := ev.toAlgebra
    lift ev f ((1 : A) ⊗ₜ[R] x) = f x := by
  let _ : Algebra R A := ev.toAlgebra
  let _ : Module R N := Module.compHom N ev
  let _ : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  change (LinearMap.liftBaseChange A _) (1 ⊗ₜ[R] x) = f x
  apply LinearMap.liftBaseChange_one_tmul

/-- Two scalar-linear maps out of a scalar extension agree if they agree on canonical elements. -/
theorem hom_ext (ev : R →+* A) {g₁ g₂ : RingHom.baseChangeModule ev M →ₗ[A] N}
    (h : ∀ x, g₁ (of ev M x) = g₂ (of ev M x)) : g₁ = g₂ := by
  let _ : Algebra R A := ev.toAlgebra
  exact (TensorProduct.isBaseChange R M A).algHom_ext _ _ (by
    intro x
    simpa only [of_apply, TensorProduct.mk_apply] using h x)

/-- A scalar-linear map agreeing with `f` on canonical elements is `lift ev f`; `lift_of` gives
the existence half of this universal property. -/
theorem lift_unique (ev : R →+* A) (f : M →ₛₗ[ev] N)
    (g : RingHom.baseChangeModule ev M →ₗ[A] N)
    (hg : ∀ x, g (of ev M x) = f x) : g = lift ev f := by
  exact hom_ext ev fun x => (hg x).trans (by
    rw [of_apply]
    exact (lift_of ev f x).symm)

end _root_.RingHom.baseChangeModule
