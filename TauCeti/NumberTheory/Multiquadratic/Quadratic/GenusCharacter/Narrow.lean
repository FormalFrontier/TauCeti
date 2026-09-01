/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Basic
public import TauCeti.NumberTheory.NumberField.TotallyPositive
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Genus characters and narrow-equivalent ideals

This file proves the cancellation step needed to descend genus characters from norms of ideals to
the narrow class group of a quadratic field. Suppose two nonzero integral ideals `I` and `J` are
related by

`(x) I = (y) J`,

where `x * y` is totally positive. If `N(x)` and `N(y)` are coprime to the modulus of a genus
character, then that character takes the same value on `N(I)` and `N(J)`.

The proof uses two facts. Total positivity makes `N(x)` and `N(y)` have the same sign. The
genus-character relation for element norms says that the character of `N(xy)` is `1`, so the
character values of `N(x)` and `N(y)` agree. Taking ideal norms in `(x) I = (y) J` then cancels
that common value.

This is deliberately not yet packaged as a character of the narrow class group. That construction
also needs strong approximation in the form that every narrow class, and every comparison between
two representatives, can be chosen coprime to the discriminant. The theorem here isolates the
arithmetic cancellation that such a construction consumes.

The genus-character argument is classical; see D. A. Cox, *Primes of the Form x² + ny²*, §3.B,
and F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

## Main result

* `TauCeti.Multiquadratic.genusCharFun_absNorm_eq_of_span_mul_eq_span_mul`: genus characters agree
  on the norms of two ideals related by a coprime, totally positive principal ratio.
-/

public section

open Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- If two algebraic integers have coprime norms whose product has trivial genus character, and
their field norms have the same sign, then the character also agrees on their absolute norms. -/
private theorem genusCharFun_natAbs_norm_eq {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) {x y : 𝓞 K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hpos : NumberField.IsTotallyPositive ((x : K) * (y : K)))
    (hcopx : IsCoprime (Algebra.norm ℤ x) (∏ P ∈ t, P))
    (hcopy : IsCoprime (Algebra.norm ℤ y) (∏ P ∈ t, P)) :
    genusCharFun t (Algebra.norm ℤ x).natAbs =
      genusCharFun t (Algebra.norm ℤ y).natAbs := by
  have hcopxy : IsCoprime (Algebra.norm ℤ (x * y)) (∏ P ∈ t, P) := by
    rw [map_mul]
    exact hcopx.mul_left hcopy
  have hcharxy := genusCharFun_norm_eq_one hs heven hprod hmin hgen hsf hts (x * y) hcopxy
  rw [map_mul, genusCharFun_mul_right] at hcharxy
  have hchar : genusCharFun t (Algebra.norm ℤ x) = genusCharFun t (Algebra.norm ℤ y) :=
    Int.eq_of_mul_eq_one hcharxy
  have hnormpos : 0 < Algebra.norm ℤ x * Algebra.norm ℤ y := by
    have hxK : (x : K) ≠ 0 := by simpa using hx
    have hyK : (y : K) ≠ 0 := by simpa using hy
    have hq := NumberField.norm_pos_of_isTotallyPositive (mul_ne_zero hxK hyK) hpos
    rw [map_mul] at hq
    have hq' : (0 : ℚ) < (Algebra.norm ℤ x : ℚ) * (Algebra.norm ℤ y : ℚ) := by
      simpa only [Algebra.coe_norm_int] using hq
    exact_mod_cast hq'
  rcases (mul_pos_iff.mp hnormpos) with ⟨hxpos, hypos⟩ | ⟨hxneg, hyneg⟩
  · simpa [Int.natCast_natAbs, abs_of_pos hxpos, abs_of_pos hypos] using hchar
  · rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_neg hxneg, abs_of_neg hyneg]
    calc
      genusCharFun t (-Algebra.norm ℤ x) =
          genusCharFun t (-1) * genusCharFun t (Algebra.norm ℤ x) := by
            rw [← genusCharFun_mul_right]
            congr 1
            ring
      _ = genusCharFun t (-1) * genusCharFun t (Algebra.norm ℤ y) := by rw [hchar]
      _ = genusCharFun t (-Algebra.norm ℤ y) := by
            rw [← genusCharFun_mul_right]
            congr 1
            ring

/-- **Genus characters are invariant under a coprime narrow-principal comparison.**

Let `K = ℚ(√d)`, with a prime-discriminant factorization indexed by `s`, and let `t ⊆ s` index a
genus character. Suppose nonzero integral ideals `I` and `J` satisfy `(x) I = (y) J`, where `x * y`
is totally positive. If the element norms of `x` and `y` are coprime to the product of the factors
in `t`, then the genus character has the same value on `N(I)` and `N(J)`.

The nonvanishing hypotheses on `x` and `y` are separate because total positivity is vacuous over
totally complex fields, where it does not exclude zero.

By `NumberField.NarrowClassGroup.mk0_eq_mk0_iff`, the displayed ideal equality and positivity are
exactly the data witnessing equality of the narrow classes of `I` and `J`. The extra coprimality
conditions are the strong-approximation input still needed to package this result as a character
of the entire narrow class group. -/
theorem genusCharFun_absNorm_eq_of_span_mul_eq_span_mul {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) {I J : (Ideal (𝓞 K))⁰} {x y : 𝓞 K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hpos : NumberField.IsTotallyPositive ((x : K) * (y : K)))
    (hIJ : Ideal.span {x} * (I : Ideal (𝓞 K)) = Ideal.span {y} * (J : Ideal (𝓞 K)))
    (hcopx : IsCoprime (Algebra.norm ℤ x) (∏ P ∈ t, P))
    (hcopy : IsCoprime (Algebra.norm ℤ y) (∏ P ∈ t, P)) :
    genusCharFun t (Ideal.absNorm (I : Ideal (𝓞 K))) =
      genusCharFun t (Ideal.absNorm (J : Ideal (𝓞 K))) := by
  have hxychar := genusCharFun_natAbs_norm_eq hs heven hprod hmin hgen hsf hts hx hy hpos
    hcopx hcopy
  have hnorm := congrArg Ideal.absNorm hIJ
  rw [map_mul, map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hnorm
  have hnorm' :
      ((Algebra.norm ℤ x).natAbs : ℤ) * Ideal.absNorm (I : Ideal (𝓞 K)) =
        ((Algebra.norm ℤ y).natAbs : ℤ) * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    exact_mod_cast hnorm
  have hchar := congrArg (genusCharFun t) hnorm'
  rw [genusCharFun_mul_right, genusCharFun_mul_right, hxychar] at hchar
  have hcopAbsY : IsCoprime ((Algebra.norm ℤ y).natAbs : ℤ) (∏ P ∈ t, P) := by
    rw [Int.natCast_natAbs]
    exact hcopy.abs_left
  have hcharY_ne : genusCharFun t ((Algebra.norm ℤ y).natAbs : ℤ) ≠ 0 := by
    intro hzero
    exact ((genusCharFun_eq_zero_iff (fun P hP => hs P (hts hP))).mp hzero) hcopAbsY
  exact mul_left_cancel₀ hcharY_ne hchar

end TauCeti.Multiquadratic
