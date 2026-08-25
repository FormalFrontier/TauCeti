/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Linear independence from transcendence

The powers of a transcendental element of an algebra are linearly independent over the base ring.

## Main results

* `Transcendental.linearIndependent_pow`: the powers of a transcendental element are
  linearly independent over the base ring.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The powers of a transcendental element are linearly independent** over the base ring: they
are the images of the monomial basis of `R[X]` under the injective evaluation map at `x`. -/
theorem _root_.Transcendental.linearIndependent_pow {x : A} (hx : Transcendental R x) :
    LinearIndependent R fun n : ℕ ↦ x ^ n := by
  have h := (Polynomial.basisMonomials R).linearIndependent.map'
    (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hx))
  simpa [Function.comp_def] using h

end TauCeti
