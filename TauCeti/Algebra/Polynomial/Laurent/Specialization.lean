/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import TauCeti.Algebra.Polynomial.Laurent

/-!
# Specialization of Laurent modules

This file provides scalar extension of a Laurent module along evaluation maps.  For the
coefficient ring `ℤ[q,q⁻¹]`, the two distinguished evaluations are `laurentEvalOne` and
`laurentEvalNegOne`; the resulting shift formulas record the specializations at `q = 1` and
`q = -1`.  The construction is stated for an arbitrary ring homomorphism and uses Mathlib's
base-change universal property.

## Main definitions

* `TauCeti.LaurentSpecialization`: scalar extension along a ring homomorphism.
* `TauCeti.LaurentSpecialization.of`: the canonical map into the scalar extension.
* `TauCeti.LaurentSpecialization.lift`: the universal scalar-linear factor.
* `TauCeti.LaurentSpecializationAtOne` and `TauCeti.LaurentSpecializationAtNegOne`: the two
  specializations of a Laurent module at `q = 1` and `q = -1`.

## Main results

* `TauCeti.LaurentSpecialization.lift_of` and
  `TauCeti.LaurentSpecialization.lift_unique`: the universal property.
* `TauCeti.LaurentSpecialization.of_smul`: the defining scalar relation.
* `TauCeti.LaurentSpecialization.of_T_smul`: the shift/sign formula, with its `q = ±1`
  specializations.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Section 3.1, for the specialization convention and
  the warning that specialization may change nondegeneracy.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, "Algebraic specialization".
-/

public section

namespace TauCeti

open LaurentPolynomial
open scoped TensorProduct

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module A N]

/-- Scalar extension of an `R`-module along `ev : R →+* A`. -/
abbrev LaurentSpecialization (ev : R →+* A) (M : Type*) [AddCommMonoid M] [Module R M] :=
  letI := ev.toAlgebra
  A ⊗[R] M

namespace LaurentSpecialization

/-- The canonical semilinear map from an `R`-module to its scalar extension along `ev`. -/
noncomputable def of (ev : R →+* A) (M : Type*) [AddCommMonoid M] [Module R M] :
    M →ₛₗ[ev] LaurentSpecialization ev M := by
  letI := ev.toAlgebra
  exact
    { toAddHom := (TensorProduct.mk R A M 1).toAddMonoidHom
      map_smul' := by
        intro r x
        change (1 : A) ⊗ₜ[R] (r • x) = ev r • ((1 : A) ⊗ₜ[R] x)
        rw [TensorProduct.tmul_smul]
        rfl }

/-- The tensor representative of `LaurentSpecialization.of`. -/
theorem of_apply (ev : R →+* A) (x : M) :
    of ev M x =
      (let _ := ev.toAlgebra; (1 : A) ⊗ₜ[R] x) := by
  let _ := ev.toAlgebra
  rfl

/-- The scalar-linear map induced by a semilinear map through scalar extension. -/
noncomputable def lift (ev : R →+* A) (f : M →ₛₗ[ev] N)
    : LaurentSpecialization ev M →ₗ[A] N := by
  letI : Algebra R A := ev.toAlgebra
  letI : Module R N := Module.compHom N ev
  letI : IsScalarTower R A N :=
    { smul_assoc := by
        intro r a n
        -- The restricted scalar action on `N` is evaluation followed by multiplication.
        change (ev r * a) • n = ev r • (a • n)
        rw [mul_smul] }
  let f' : M →ₗ[R] N :=
    { f with
      map_smul' := by
        intro r x
        -- The target's restricted scalar action is the action through `ev`.
        change f (r • x) = ev r • f x
        exact f.map_smulₛₗ r x }
  exact f'.liftBaseChange A

@[simp]
theorem lift_of (ev : R →+* A) (f : M →ₛₗ[ev] N) (x : M) :
    lift ev f (of ev M x) = f x := by
  simp [lift, of]

private lemma tmul_eq_smul (a : A) (x : M) [Algebra R A] :
    (a : A) ⊗ₜ[R] x = a • ((1 : A) ⊗ₜ[R] x) := by
  rw [TensorProduct.smul_tmul']
  simp

/-- Two scalar-linear maps out of a scalar extension agree if they agree on canonical elements. -/
theorem hom_ext (ev : R →+* A) {g₁ g₂ : LaurentSpecialization ev M →ₗ[A] N}
    (h : ∀ x, g₁ (of ev M x) = g₂ (of ev M x)) : g₁ = g₂ := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      rw [tmul_eq_smul, map_smul, map_smul]
      simpa [of] using congrArg (fun z => a • z) (h x)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The universal property of scalar extension for a semilinear map. -/
theorem lift_unique (ev : R →+* A) (f : M →ₛₗ[ev] N)
    (g : LaurentSpecialization ev M →ₗ[A] N)
    (hg : ∀ x, g (of ev M x) = f x) : g = lift ev f := by
  let _ := ev.toAlgebra
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      rw [tmul_eq_smul, map_smul, map_smul]
      have hg' : g ((1 : A) ⊗ₜ[R] x) = f x := by simpa [of] using hg x
      have hlift : lift ev f ((1 : A) ⊗ₜ[R] x) = f x := by simp [lift]
      rw [hg', hlift]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

@[simp]
theorem of_smul (ev : R →+* A) (r : R) (x : M) :
    of ev M (r • x) = ev r • of ev M x :=
  (of ev M).map_smulₛₗ r x

end LaurentSpecialization

section LaurentIntegerSpecialization

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (LaurentPolynomial ℤ) M]

/-- Scalar extension of a Laurent module at a unit of `ℤ`. -/
abbrev LaurentSpecializationAt (u : ℤˣ) (M : Type*) [AddCommGroup M]
    [Module (LaurentPolynomial ℤ) M] :=
  LaurentSpecialization (laurentEvalUnit u) M

/-- The scalar extension of a Laurent module at `q = 1`. -/
abbrev LaurentSpecializationAtOne (M : Type*) [AddCommGroup M]
    [Module (LaurentPolynomial ℤ) M] := LaurentSpecialization laurentEvalOne M

/-- The scalar extension of a Laurent module at `q = -1`. -/
abbrev LaurentSpecializationAtNegOne (M : Type*) [AddCommGroup M]
    [Module (LaurentPolynomial ℤ) M] := LaurentSpecialization laurentEvalNegOne M

/-- At a unit `u`, a Laurent shift acts by the corresponding integer power on specialization. -/
@[simp]
theorem LaurentSpecialization.of_T_smul (u : ℤˣ) (n : ℤ) (x : M) :
    LaurentSpecialization.of (laurentEvalUnit u) M
        ((T n : LaurentPolynomial ℤ) • x) =
      ((u ^ n : ℤˣ) : ℤ) •
        LaurentSpecialization.of (laurentEvalUnit u) M x := by
  rw [LaurentSpecialization.of_smul, laurentEvalUnit_T]

@[simp]
theorem LaurentSpecialization.of_T_smul_atOne (n : ℤ) (x : M) :
    LaurentSpecialization.of laurentEvalOne M
        ((T n : LaurentPolynomial ℤ) • x) =
      LaurentSpecialization.of laurentEvalOne M x := by
  rw [LaurentSpecialization.of_smul, laurentEvalOne_T]
  simp

@[simp]
theorem LaurentSpecialization.of_T_smul_atNegOne (n : ℤ) (x : M) :
    LaurentSpecialization.of laurentEvalNegOne M
        ((T n : LaurentPolynomial ℤ) • x) =
      (n.negOnePow : ℤ) •
      LaurentSpecialization.of laurentEvalNegOne M x := by
  rw [LaurentSpecialization.of_smul, laurentEvalNegOne_T]

end LaurentIntegerSpecialization

end TauCeti
