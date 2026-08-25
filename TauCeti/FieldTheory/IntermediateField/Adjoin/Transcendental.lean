/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraTower
public import TauCeti.RingTheory.Algebraic.LinearIndependent

/-!
# Linear independence over a simple transcendental extension

Combined with the tower rule for linear independence, a family that is linearly independent over
the simple extension `k⟮x⟯` stays linearly independent over `k` after multiplying by arbitrary
powers of a transcendental element `x`.

The second statement is the source of dimension growth in the theory of algebraic function
fields: multiplying a basis of `F / k⟮x⟯` by the powers `1, x, …, xⁿ` exhibits `(n + 1) [F : k(x)]`
functions that are independent over `k` and whose poles are controlled by those of `x`.

## Main results

* `Transcendental.linearIndependent_mul_pow`: a `k⟮x⟯`-linearly independent family in
  `F`, multiplied by the powers of a transcendental `x`, is `k`-linearly independent.
* `Transcendental.linearIndependent_mul_pow_fin`: the finite-power restriction used in
  dimension estimates.
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}

/-- **The growth family**: multiplying a `k⟮x⟯`-linearly independent family by the powers of a
transcendental element `x` yields a `k`-linearly independent family.  This is Mathlib's tower rule
`linearIndependent_smul`, applied to the powers of `x` inside `k⟮x⟯`. -/
theorem _root_.Transcendental.linearIndependent_mul_pow (hx : _root_.Transcendental k x) {ι : Type*}
    {c : ι → F} (hc : LinearIndependent k⟮x⟯ c) :
    LinearIndependent k fun p : ι × ℕ ↦ c p.1 * x ^ p.2 := by
  have hgen : _root_.Transcendental k (IntermediateField.AdjoinSimple.gen k x) :=
    (transcendental_algebraMap_iff (algebraMap k⟮x⟯ F).injective).mp (by
      rwa [IntermediateField.AdjoinSimple.algebraMap_gen])
  simpa only [Algebra.smul_def, map_pow, IntermediateField.AdjoinSimple.algebraMap_gen,
    mul_comm] using
    (linearIndependent_equiv' (Equiv.prodComm ι ℕ)
      (g := fun p : ι × ℕ ↦ IntermediateField.AdjoinSimple.gen k x ^ p.2 • c p.1) rfl).mpr
      (linearIndependent_smul (Transcendental.linearIndependent_pow hgen) hc)

/-- Restrict the growth family to the first `n` powers of `x`. -/
theorem _root_.Transcendental.linearIndependent_mul_pow_fin (hx : _root_.Transcendental k x)
    {ι : Type*} {c : ι → F}
    (hc : LinearIndependent k⟮x⟯ c) (n : ℕ) :
    LinearIndependent k fun p : ι × Fin n ↦ c p.1 * x ^ (p.2 : ℕ) := by
  have h := (Transcendental.linearIndependent_mul_pow hx hc).comp
    (fun p : ι × Fin n ↦ (p.1, (p.2 : ℕ)))
    (fun p q hpq ↦ by
      simp only [Prod.mk.injEq, Fin.val_inj] at hpq
      exact Prod.ext hpq.1 hpq.2)
  simpa [Function.comp_def] using h

end TauCeti
