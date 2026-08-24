/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraTower

/-!
# Linear independence over a simple transcendental extension

A transcendental element `x` of an algebra makes the evaluation map `p ↦ p(x)` injective, so its
powers are linearly independent over the base ring.  Combined with the tower rule for linear
independence, a family that is linearly independent over the simple extension `k⟮x⟯` stays
linearly independent over `k` after multiplying by arbitrary powers of `x`.

The second statement is the source of dimension growth in the theory of algebraic function
fields: multiplying a basis of `F / k⟮x⟯` by the powers `1, x, …, xⁿ` exhibits `(n + 1) [F : k(x)]`
functions that are independent over `k` and whose poles are controlled by those of `x`.

## Main results

* `TauCeti.linearIndependent_pow_of_transcendental`: the powers of a transcendental element are
  linearly independent over the base ring.
* `TauCeti.linearIndependent_mul_pow_of_transcendental`: a `k⟮x⟯`-linearly independent family in
  `F`, multiplied by the powers of a transcendental `x`, is `k`-linearly independent.

Both statements were previously private, and specialised to a single call site, inside
`TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula`; they are stated here in the
generality their proofs support, and that file now consumes them.
-/

public section

open scoped IntermediateField

namespace TauCeti

/-- **The powers of a transcendental element are linearly independent** over the base ring: they
are the images of the monomial basis of `R[X]` under the injective evaluation map at `x`. -/
theorem linearIndependent_pow_of_transcendental {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {x : A} (hx : Transcendental R x) : LinearIndependent R fun n : ℕ ↦ x ^ n := by
  have h := (Polynomial.basisMonomials R).linearIndependent.map'
    (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hx))
  simpa [Function.comp_def] using h

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}

/-- The powers of a transcendental element of `F`, read inside the simple extension `k⟮x⟯` that it
generates, are linearly independent over `k`. -/
theorem linearIndependent_gen_pow_of_transcendental (hx : Transcendental k x) :
    LinearIndependent k fun n : ℕ ↦ IntermediateField.AdjoinSimple.gen k x ^ n :=
  LinearIndependent.of_comp k⟮x⟯.val.toLinearMap <| by
    simpa [Function.comp_def] using linearIndependent_pow_of_transcendental hx

/-- **The growth family**: multiplying a `k⟮x⟯`-linearly independent family by the powers of a
transcendental element `x` yields a `k`-linearly independent family.  This is Mathlib's tower rule
`linearIndependent_smul`, applied to the powers of `x` inside `k⟮x⟯`. -/
theorem linearIndependent_mul_pow_of_transcendental (hx : Transcendental k x) {ι : Type*}
    {c : ι → F} (hc : LinearIndependent k⟮x⟯ c) :
    LinearIndependent k fun p : ι × ℕ ↦ c p.1 * x ^ p.2 := by
  simpa only [Algebra.smul_def, map_pow, IntermediateField.AdjoinSimple.algebraMap_gen,
    mul_comm] using
    (linearIndependent_equiv' (Equiv.prodComm ι ℕ)
      (g := fun p : ι × ℕ ↦ IntermediateField.AdjoinSimple.gen k x ^ p.2 • c p.1) rfl).mpr
      (linearIndependent_smul (linearIndependent_gen_pow_of_transcendental hx) hc)

end TauCeti
