/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Evaluating a Laurent polynomial at a unit of a not necessarily commutative algebra

Mathlib's `LaurentPolynomial.eval₂` substitutes a unit of a *commutative* semiring into a Laurent
polynomial.  The Laurent coefficient ring of graded `K`-theory has to act on abelian groups, so it
has to be substituted into endomorphism rings, which are not commutative.  This file supplies that
evaluation.

For a unit `u` of an `R`-algebra `A`, `TauCeti.laurentEval u : R[T;T⁻¹] →ₐ[R] A` is the algebra map
sending `T` to `u` and `T⁻¹` to `u⁻¹`.  It is the algebra map attached by
`AddMonoidAlgebra.lift` to the monoid homomorphism `n ↦ uⁿ` out of `Multiplicative ℤ`, so it exists
for an arbitrary semiring `A` and is the unique algebra map with the prescribed value at `T`.
Consequently `TauCeti.laurentEvalEquiv` identifies the units of `A` with the `R`-algebra maps out of
`R[T;T⁻¹]`: the Laurent polynomial ring is the free `R`-algebra on one invertible generator.

The module-theoretic use is `TauCeti.laurentTAut`: on any `R[T;T⁻¹]`-module, multiplication by `T`
-- written `q` in the graded `K`-theory literature -- is an automorphism of the underlying additive
monoid, and that automorphism is what a shift-compatible invariant is compared against.

## Main definitions

* `TauCeti.laurentEval`: evaluation of a Laurent polynomial at a unit of an `R`-algebra.
* `TauCeti.laurentEvalEquiv`: the units of `A` are the `R`-algebra maps `R[T;T⁻¹] →ₐ[R] A`.
* `TauCeti.laurentTAut`: multiplication by `T` on an `R[T;T⁻¹]`-module, as an additive
  automorphism.

## Main results

* `TauCeti.laurentEval_unique`: an algebra map out of `R[T;T⁻¹]` is determined by its value at `T`.
* `TauCeti.laurentEval_eq_eval₂`: over a commutative target, this evaluation is Mathlib's
  `LaurentPolynomial.eval₂`.
* `TauCeti.laurentPolynomialC_smul`: a constant Laurent polynomial acts by integer scalar
  multiplication.

## References

* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, which fixes `ℤ[q,q⁻¹]`,
  represented by `LaurentPolynomial ℤ`, as the coefficient ring of the graded theory.
-/

public section

namespace TauCeti

open LaurentPolynomial

section Eval

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- **Evaluation of a Laurent polynomial at a unit** `u` of an `R`-algebra `A`: the `R`-algebra
map `R[T;T⁻¹] →ₐ[R] A` sending `T` to `u`, hence `T⁻¹` to `u⁻¹`.

Unlike `LaurentPolynomial.eval₂` this does not ask `A` to be commutative, because the intended
targets are endomorphism rings.  The construction is the universal property of the group algebra
`R[ℤ]`: an integer power of a unit is a monoid homomorphism out of `Multiplicative ℤ`. -/
noncomputable def laurentEval (u : Aˣ) : R[T;T⁻¹] →ₐ[R] A :=
  AddMonoidAlgebra.lift R A ℤ ((Units.coeHom A).comp (zpowersHom Aˣ u))

@[simp]
lemma laurentEval_T (u : Aˣ) (n : ℤ) : laurentEval (R := R) u (T n) = ((u ^ n : Aˣ) : A) := by
  rw [laurentEval]
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp]
lemma laurentEval_C (u : Aˣ) (r : R) : laurentEval u (C r) = algebraMap R A r := by
  rw [C_eq_algebraMap]
  exact (laurentEval u).commutes r

/-- The generator `T` evaluates to the chosen unit. -/
lemma laurentEval_T_one (u : Aˣ) : laurentEval (R := R) u (T 1) = (u : A) := by
  simp

/-- **An `R`-algebra map out of `R[T;T⁻¹]` is determined by its value at `T`.** -/
theorem laurentEval_unique (u : Aˣ) (f : R[T;T⁻¹] →ₐ[R] A) (hf : f (T 1) = (u : A)) :
    f = laurentEval u :=
  (AddMonoidAlgebra.lift R A ℤ).symm.injective <|
    MonoidHom.ext_mint <| by
      rw [AddMonoidAlgebra.lift_symm_apply, AddMonoidAlgebra.lift_symm_apply]
      exact hf.trans (laurentEval_T_one u).symm

/-- **The Laurent polynomial ring is the free `R`-algebra on one invertible generator**: its
`R`-algebra maps to `A` are exactly the units of `A`, through evaluation at `T`. -/
noncomputable def laurentEvalEquiv : Aˣ ≃ (R[T;T⁻¹] →ₐ[R] A) where
  toFun := laurentEval
  invFun f :=
    { val := f (T 1)
      inv := f (T (-1))
      val_inv := by rw [← map_mul, ← T_add]; simp
      inv_val := by rw [← map_mul, ← T_add]; simp }
  left_inv u := Units.ext <| by simp
  right_inv f := (laurentEval_unique _ f rfl).symm

@[simp]
lemma laurentEvalEquiv_apply (u : Aˣ) : laurentEvalEquiv (R := R) u = laurentEval u :=
  (rfl)

@[simp]
lemma laurentEvalEquiv_symm_apply (f : R[T;T⁻¹] →ₐ[R] A) :
    ((laurentEvalEquiv.symm f : Aˣ) : A) = f (T 1) :=
  (rfl)

/-- Evaluation at a unit is natural in the target algebra. -/
@[simp]
theorem comp_laurentEval {B : Type*} [Semiring B] [Algebra R B] (g : A →ₐ[R] B) (u : Aˣ) :
    g.comp (laurentEval u) = laurentEval (Units.map (g : A →* B) u) :=
  laurentEval_unique _ _ <| by simp

/-- **Over a commutative target this is Mathlib's `LaurentPolynomial.eval₂`.**  The two
constructions are separate only because `LaurentPolynomial.eval₂` is built by localization and so
needs a commutative codomain. -/
theorem laurentEval_eq_eval₂ {S : Type*} [CommSemiring S] [Algebra R S] (u : Sˣ)
    (p : R[T;T⁻¹]) : laurentEval u p = eval₂ (algebraMap R S) u p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T n a => simp

end Eval

section TAut

variable (R : Type*) [Semiring R] (N : Type*) [AddCommMonoid N]
  [Module (LaurentPolynomial R) N]

/-- **Multiplication by the variable on an `R[T;T⁻¹]`-module**, as an automorphism of the
underlying additive monoid.  In the graded `K`-theory notation the variable is `q`, so this is the
operator `x ↦ q • x` against which a shift-compatible invariant is compared. -/
noncomputable def laurentTAut : AddAut N where
  toFun x := (T 1 : LaurentPolynomial R) • x
  invFun x := (T (-1) : LaurentPolynomial R) • x
  left_inv x := by
    simp only [smul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  right_inv x := by
    simp only [smul_smul, ← T_add, add_neg_cancel, T_zero, one_smul]
  map_add' _ _ := smul_add _ _ _

@[simp]
lemma laurentTAut_apply (x : N) : laurentTAut R N x = (T 1 : LaurentPolynomial R) • x :=
  (rfl)

@[simp]
lemma laurentTAut_symm_apply (x : N) :
    (laurentTAut R N).symm x = (T (-1) : LaurentPolynomial R) • x :=
  (rfl)

end TAut

section Constants

variable {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial ℤ) N]

/-- **A constant Laurent polynomial acts by the integer scalar multiplication** of the underlying
abelian group of a `ℤ[T;T⁻¹]`-module.

Not `@[simp]`: `LaurentPolynomial.C a` is not in simp-normal form, because `eq_intCast` rewrites
the ring homomorphism `C : ℤ →+* ℤ[T;T⁻¹]` to the integer cast; the normal form of the statement
is Mathlib's own `Int.cast_smul_eq_zsmul`. -/
lemma laurentPolynomialC_smul (a : ℤ) (x : N) :
    (C a : LaurentPolynomial ℤ) • x = a • x := by
  rw [C_eq_algebraMap, ← Int.cast_smul_eq_zsmul (LaurentPolynomial ℤ) a x]
  congr 1

end Constants

end TauCeti
