/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.CoprimeIdeal
public import TauCeti.NumberTheory.NumberField.TotallyPositive

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
* `TauCeti.Multiquadratic.genusCharFunCoprimeIdealHom_eq_one_of_eq_span_singleton`: the
  unit-valued character is trivial on a totally positive coprime principal ideal.
* `TauCeti.Multiquadratic.genusCharFunCoprimeIdealHom_eq_of_span_mul_eq_span_mul`: the same
  character is invariant under a coprime narrow comparison.
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

/-- **The unit-valued genus character is invariant under a coprime narrow-principal comparison.**
Let `I` and `J` be
nonzero integral ideals whose absolute norms are coprime to the modulus of a genus character. If
they are related by a narrow comparison `(x) I = (y) J`, and the principal factor `y` is coprime
to the modulus, then the corresponding values of
`genusCharFunCoprimeIdealHom` agree.

The explicit coprimality condition on one principal factor is the remaining strong-approximation
input needed to remove the coprimality restriction when constructing a character on the narrow
class group. -/
theorem genusCharFunCoprimeIdealHom_eq_of_span_mul_eq_span_mul
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s)
    {I J : genusCharFunCoprimeIdealSubmonoid (K := K) t}
    {x y : 𝓞 K} (hy : y ≠ 0)
    (hpos : NumberField.IsTotallyPositive ((x : K) * (y : K)))
    (hIJ : Ideal.span {x} * (I : Ideal (𝓞 K)) =
      Ideal.span {y} * (J : Ideal (𝓞 K)))
    (hcopy : IsCoprime (Algebra.norm ℤ y) (∏ P ∈ t, P)) :
    genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) I =
      genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) J := by
  have hx : x ≠ 0 := by
    have hJ0 : (J : Ideal (𝓞 K)) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp J.1.property
    have hspany : Ideal.span ({y} : Set (𝓞 K)) ≠ 0 := by
      rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hy
    have hprod : Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)) ≠ 0 :=
      mul_ne_zero hspany hJ0
    intro hx
    apply hprod
    rw [← hIJ, hx]
    simp
  have hnorm := congrArg Ideal.absNorm hIJ
  rw [map_mul, map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hnorm
  have hnorm' :
      ((Algebra.norm ℤ x).natAbs : ℤ) * Ideal.absNorm (I : Ideal (𝓞 K)) =
        ((Algebra.norm ℤ y).natAbs : ℤ) * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    exact_mod_cast hnorm
  have hcopAbsX : IsCoprime ((Algebra.norm ℤ x).natAbs : ℤ) (∏ P ∈ t, P) := by
    have hJcop : IsCoprime (Ideal.absNorm (J : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) :=
      (mem_genusCharFunCoprimeIdealSubmonoid_iff J.1).mp J.property
    have hcopAbsX' :
        IsCoprime (((Algebra.norm ℤ y).natAbs : ℤ) * Ideal.absNorm (J : Ideal (𝓞 K)))
          (∏ P ∈ t, P) := by
      simpa only [Int.natCast_natAbs] using hcopy.abs_left.mul_left hJcop
    rw [← hnorm'] at hcopAbsX'
    exact hcopAbsX'.of_mul_left_left
  have hcopx : IsCoprime (Algebra.norm ℤ x) (∏ P ∈ t, P) := by
    apply (IsCoprime.abs_left_iff _ _).mp
    simpa only [Int.natCast_natAbs] using hcopAbsX
  apply Units.ext
  rw [genusCharFunCoprimeIdealHom_apply, genusCharFunCoprimeIdealHom_apply]
  exact genusCharFun_absNorm_eq_of_span_mul_eq_span_mul hs heven hprod hmin hgen hsf hts hx hy
    hpos hIJ hcopx hcopy

/-- **A principal ideal with a totally positive generator, coprime to the modulus, has trivial
genus character.** Let `I` be a nonzero integral ideal whose absolute norm is coprime to the
modulus of a genus character. If `I = (x)` for a totally positive `x`, then the coprime-ideal genus
character of `I` is `1`; the corresponding properties of `x` follow from those of `I`.

This is the kernel calculation needed before the character can descend through the narrow class
group: a totally positive principal ideal is narrow-trivial, and this theorem handles the finite
coprimality restriction of the arithmetic character. -/
theorem genusCharFunCoprimeIdealHom_eq_one_of_eq_span_singleton
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s)
    {I : genusCharFunCoprimeIdealSubmonoid (K := K) t} {x : 𝓞 K}
    (hpos : NumberField.IsTotallyPositive ((x : K)))
    (hI : (I : Ideal (𝓞 K)) = Ideal.span {x}) :
    genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) I = 1 := by
  have hx : x ≠ 0 := by
    have hI0 : (I : Ideal (𝓞 K)) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp I.1.property
    intro hx
    apply hI0
    simp [hI, hx]
  have hcop : IsCoprime (Algebra.norm ℤ x) (∏ P ∈ t, P) := by
    have hIcop : IsCoprime (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) :=
      (mem_genusCharFunCoprimeIdealSubmonoid_iff I.1).mp I.property
    have hnorm := congrArg Ideal.absNorm hI
    rw [Ideal.absNorm_span_singleton] at hnorm
    have hnorm' : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) =
        ((Algebra.norm ℤ x).natAbs : ℤ) := by
      exact_mod_cast hnorm
    rw [hnorm', Int.natCast_natAbs] at hIcop
    exact (IsCoprime.abs_left_iff _ _).mp hIcop
  have hcomp := genusCharFunCoprimeIdealHom_eq_of_span_mul_eq_span_mul hs heven hprod hmin hgen
    hsf hts (I := I) (J := 1) (x := 1) (y := x) hx (by simpa using hpos)
    (by simp [hI]) hcop
  simpa only [map_one] using hcomp

end TauCeti.Multiquadratic
