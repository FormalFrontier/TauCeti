/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Distinct Fourier monomials

Mathlib's `fourier n : C(AddCircle T, ℂ)` is developed as a family of `L²` monomials: the lemmas
about it record how it behaves in the *index* `n` (`fourier_add`, `fourier_neg`) and what it
contributes to the Fourier basis. Read the other way, as a family of characters of `AddCircle T`
indexed by `n`, the first thing a representation-theoretic consumer needs is that the family is
*faithful*: distinct indices give distinct characters, so the corresponding one-dimensional
representations are pairwise inequivalent.

That is the single fact recorded here. Multiplicativity in the circle argument needs no lemma of
its own: it is Mathlib's `AddCircle.toCircle_addChar`, the bundled additive character underlying
`fourier`.

## Main statements

* `TauCeti.fourier_injective`: `n ↦ fourier n` is injective, so distinct indices give distinct
  characters.

## Tags

Fourier, additive circle, character
-/

public section

namespace TauCeti

variable {T : ℝ}

/-- **Distinct indices give distinct Fourier monomials.** At the point `T / 2 / (m - n)` the two
monomials `fourier m` and `fourier n` differ by `Complex.exp (π * I) = -1`, so they are already
different there. Only `T ≠ 0` is needed: for `T = 0` the circle is trivial and every monomial is
the constant `1`. -/
theorem fourier_injective (hT : T ≠ 0) : Function.Injective (fourier (T := T)) := by
  intro m n hmn
  by_contra hne
  have hd : ((m : ℂ) - n) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  set y : ℝ := T / 2 / ((m : ℝ) - n) with hy
  have hx : fourier m (y : AddCircle T) = fourier n (y : AddCircle T) := by rw [hmn]
  rw [fourier_coe_apply, fourier_coe_apply] at hx
  have he : 2 * (Real.pi : ℂ) * Complex.I * m * y / T
      - 2 * (Real.pi : ℂ) * Complex.I * n * y / T = (Real.pi : ℂ) * Complex.I := by
    rw [hy]
    push_cast
    field_simp
  have hcontra : (-1 : ℂ) = 1 := by
    calc (-1 : ℂ) = Complex.exp ((Real.pi : ℂ) * Complex.I) := Complex.exp_pi_mul_I.symm
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * y / T)
            / Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * y / T) := by
          rw [← Complex.exp_sub, he]
      _ = 1 := by rw [hx, div_self (Complex.exp_ne_zero _)]
  norm_num at hcontra

end TauCeti
