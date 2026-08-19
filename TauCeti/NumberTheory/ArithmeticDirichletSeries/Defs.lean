/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Arithmetic functions on the nonzero ideals of a number field

An *ideal arithmetic function* on a number field `K` is a complex-valued function on the
nonzero integral ideals of `𝓞 K`, that is, on the submonoid `(Ideal (𝓞 K))⁰` of
non-zero-divisors of the ideal monoid. This is the primary carrier for the whole
`ArithmeticDirichletSeries` development: restricting to nonzero ideals from the start means
that a divisor sum over the factorizations `B * C = A` of an ideal `A` is always finite,
because the infinitely many formal factorizations `⊥ * J = ⊥` of the zero ideal are never
in the index type.

The counterpart to that choice is a canonical way back to functions on *all* ideals, and
that is `TauCeti.IdealArithmeticFunction.zeroExtend`, which extends by the value `0` at `⊥`.

## Main declarations

* `TauCeti.IdealArithmeticFunction`: the carrier, a function `(Ideal (𝓞 K))⁰ → ℂ`;
* `TauCeti.IdealArithmeticFunction.zeroExtend`: the canonical extension by zero at `⊥`;
* `TauCeti.IdealArithmeticFunction.zeroExtend_eq_zero_iff_eq_bot`: for a nowhere-vanishing
  ideal arithmetic function the extension vanishes exactly at `⊥`;
* `TauCeti.IdealArithmeticFunction.exists_zeroExtend_eq_iff`: a function on all ideals is a
  zero extension exactly when it vanishes at `⊥`, whence
  `TauCeti.IdealArithmeticFunction.one_ne_zeroExtend`: the everywhere-one function on all
  ideals is not a zero extension.

## Implementation notes

`IdealArithmeticFunction` is a reducible abbreviation for the function type, so the pointwise
`ℂ`-module and pointwise multiplication structures are the ones inherited from `Pi`. Ideal
convolution is a separate named operation, never the pointwise product.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace TauCeti

open NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- An **ideal arithmetic function** on a number field `K`: a complex-valued function on the
nonzero integral ideals of `𝓞 K`. The index type is the submonoid `(Ideal (𝓞 K))⁰` of
non-zero-divisors of the ideal monoid, which for a Dedekind domain is exactly the set of
ideals different from `⊥` (`TauCeti.Ideal.mem_nonZeroDivisors_iff_ne_bot`). -/
abbrev IdealArithmeticFunction (K : Type*) [Field K] [NumberField K] : Type _ :=
  (Ideal (𝓞 K))⁰ → ℂ

omit [NumberField K] in
/-- An ideal of the ring of integers of a number field is a non-zero-divisor of the ideal
monoid exactly when it is nonzero. -/
theorem Ideal.mem_nonZeroDivisors_iff_ne_bot {I : Ideal (𝓞 K)} :
    I ∈ (Ideal (𝓞 K))⁰ ↔ I ≠ ⊥ := by
  simp [mem_nonZeroDivisors_iff_ne_zero (M₀ := Ideal (𝓞 K)) (x := I)]

namespace IdealArithmeticFunction

open scoped Classical in
/-- The canonical extension of an ideal arithmetic function to *all* integral ideals of
`𝓞 K`, taking the value `0` at the zero ideal `⊥`. -/
noncomputable def zeroExtend (f : IdealArithmeticFunction K) (I : Ideal (𝓞 K)) : ℂ :=
  if h : I ∈ (Ideal (𝓞 K))⁰ then f ⟨I, h⟩ else 0

@[simp]
theorem zeroExtend_coe (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) :
    f.zeroExtend I = f I := by
  classical
  simp [zeroExtend, I.2]

theorem zeroExtend_of_ne_bot (f : IdealArithmeticFunction K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    f.zeroExtend I = f ⟨I, Ideal.mem_nonZeroDivisors_iff_ne_bot.mpr hI⟩ :=
  f.zeroExtend_coe ⟨I, Ideal.mem_nonZeroDivisors_iff_ne_bot.mpr hI⟩

@[simp]
theorem zeroExtend_bot (f : IdealArithmeticFunction K) : f.zeroExtend ⊥ = 0 := by
  classical
  simp [zeroExtend]

/-- **The zero extension detects the zero ideal.** If an ideal arithmetic function has no zero
values, then its zero extension vanishes at exactly one ideal, namely `⊥`. -/
theorem zeroExtend_eq_zero_iff_eq_bot {f : IdealArithmeticFunction K} (hf : ∀ I, f I ≠ 0)
    {I : Ideal (𝓞 K)} : f.zeroExtend I = 0 ↔ I = ⊥ := by
  refine ⟨fun h ↦ by_contra fun hI ↦ ?_, fun h ↦ h ▸ f.zeroExtend_bot⟩
  exact hf ⟨I, Ideal.mem_nonZeroDivisors_iff_ne_bot.mpr hI⟩
    (by rwa [f.zeroExtend_of_ne_bot hI] at h)

theorem zeroExtend_injective :
    Function.Injective (zeroExtend : IdealArithmeticFunction K → Ideal (𝓞 K) → ℂ) := by
  intro f g h
  ext I
  simpa using congrFun h I

@[simp]
theorem zeroExtend_inj {f g : IdealArithmeticFunction K} :
    f.zeroExtend = g.zeroExtend ↔ f = g :=
  zeroExtend_injective.eq_iff

/-- **The zero extensions are exactly the functions vanishing at `⊥`.** -/
theorem exists_zeroExtend_eq_iff {g : Ideal (𝓞 K) → ℂ} :
    (∃ f : IdealArithmeticFunction K, f.zeroExtend = g) ↔ g ⊥ = 0 := by
  refine ⟨fun ⟨f, hf⟩ ↦ hf ▸ f.zeroExtend_bot, fun hg ↦ ⟨fun I ↦ g I, funext fun I ↦ ?_⟩⟩
  rcases eq_or_ne I ⊥ with rfl | hI
  · simpa using hg.symm
  · simp [zeroExtend_of_ne_bot _ hI]

/-- **Rejection test.** The everywhere-one function on *all* integral ideals is not the zero
extension of any ideal arithmetic function: a zero extension vanishes at `⊥`. Compare
`TauCeti.IdealArithmeticFunction.zeroExtend_one_apply`, which computes the zero extension of
the constant function `1` on the *nonzero* ideals. -/
theorem one_ne_zeroExtend (f : IdealArithmeticFunction K) : f.zeroExtend ≠ 1 := by
  intro h
  simpa using congrFun h ⊥

theorem zeroExtend_one_apply (I : Ideal (𝓞 K)) :
    (1 : IdealArithmeticFunction K).zeroExtend I = if I = ⊥ then 0 else 1 := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [zeroExtend_of_ne_bot _ hI, hI]

@[simp]
theorem zeroExtend_zero : (0 : IdealArithmeticFunction K).zeroExtend = 0 := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [zeroExtend_of_ne_bot _ hI]

@[simp]
theorem zeroExtend_add (f g : IdealArithmeticFunction K) :
    (f + g).zeroExtend = f.zeroExtend + g.zeroExtend := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [zeroExtend_of_ne_bot _ hI]

@[simp]
theorem zeroExtend_smul (c : ℂ) (f : IdealArithmeticFunction K) :
    (c • f).zeroExtend = c • f.zeroExtend := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [zeroExtend_of_ne_bot _ hI]

end IdealArithmeticFunction

end TauCeti
