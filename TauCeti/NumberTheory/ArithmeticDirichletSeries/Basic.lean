/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Arithmetic functions on nonzero ideals

An ideal-indexed Dirichlet series should not assign an arithmetic coefficient to the zero ideal.
Indeed, the zero ideal has infinitely many formal factorizations `0 = 0 * I`, so including it in
the carrier makes ideal convolution ill behaved. This file introduces the carrier used throughout
the arithmetic-Dirichlet-series roadmap:

* `TauCeti.IdealArithmeticFunction K` is a complex-valued function on the nonzero integral ideals
  of a number field `K`;
* `TauCeti.IdealArithmeticFunction.zeroExtend` is its canonical extension to all integral ideals,
  with value zero at the zero ideal;
* `TauCeti.IdealArithmeticFunction.restrict` restricts a function on all ideals to the nonzero
  ideals.

The two operations are inverse precisely on functions vanishing at the zero ideal. The resulting
existence-and-uniqueness API is recorded without exposing the implementation of `zeroExtend`:
`TauCeti.IdealArithmeticFunction.existsUnique_zeroExtend_eq` characterizes its image, while
`TauCeti.IdealArithmeticFunction.zeroExtend_injective` says that no information is lost.

The extension respects the pointwise additive, scalar, and multiplicative operations. It does not
preserve the pointwise unit: the constant-one function on all ideals takes value one at the zero
ideal, and therefore cannot be a zero extension. The theorem
`TauCeti.IdealArithmeticFunction.not_exists_zeroExtend_eq_one` is the zero-ideal rejection test
required by Layer 0 of the roadmap.

## Roadmap role

This is Layer **0.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, and is the common
carrier on which its norm regrouping, ideal convolution, Euler products, and summatory functions
are built. Later Layer 0 files add completely multiplicative and unitary subtypes; those are
special coefficient systems on this general carrier, not replacements for it.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K]

/-- An **ideal arithmetic function** on a number field `K`: a complex-valued function on its
nonzero integral ideals.

The domain is `(Ideal (𝓞 K))⁰`, Mathlib's non-zero-divisor submonoid. Since the ring of integers is
a domain, its elements are exactly the ideals different from `⊥`. Keeping `⊥` out of the carrier
ensures that later divisor sums see only finite factorizations. -/
abbrev IdealArithmeticFunction := (Ideal (𝓞 K))⁰ → ℂ

namespace IdealArithmeticFunction

variable {K}

/-- Extend an ideal arithmetic function to all integral ideals by assigning zero to `⊥`.

Use `zeroExtend_bot` and `zeroExtend_coe` to simplify its two characteristic cases, rather than
unfolding this definition. -/
noncomputable def zeroExtend (f : IdealArithmeticFunction K) : Ideal (𝓞 K) → ℂ := fun I =>
  if hI : I = ⊥ then 0 else f ⟨I, by simpa using hI⟩

/-- Restrict a function on all integral ideals to the nonzero ideals. -/
def restrict (g : Ideal (𝓞 K) → ℂ) : IdealArithmeticFunction K := fun I => g I

@[simp]
theorem restrict_apply (g : Ideal (𝓞 K) → ℂ) (I : (Ideal (𝓞 K))⁰) : restrict g I = g I := by
  simp [restrict]

/-- The zero extension is zero at the zero ideal. -/
@[simp]
theorem zeroExtend_bot (f : IdealArithmeticFunction K) : f.zeroExtend ⊥ = 0 := by
  simp [zeroExtend]

/-- Away from `⊥`, the zero extension is the original ideal arithmetic function. -/
theorem zeroExtend_of_ne (f : IdealArithmeticFunction K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    f.zeroExtend I = f ⟨I, by simpa using hI⟩ := by
  simp [zeroExtend, hI]

/-- The zero extension agrees with the original function on every nonzero ideal. -/
@[simp]
theorem zeroExtend_coe (f : IdealArithmeticFunction K) (I : (Ideal (𝓞 K))⁰) :
    f.zeroExtend I = f I := by
  apply zeroExtend_of_ne
  simpa using nonZeroDivisors.coe_ne_zero I

/-- Restricting a zero extension recovers the original ideal arithmetic function. -/
@[simp]
theorem restrict_zeroExtend (f : IdealArithmeticFunction K) : restrict f.zeroExtend = f := by
  funext I
  simp

/-- Extending a restriction recovers a function on all ideals exactly when it vanishes at `⊥`. -/
theorem zeroExtend_restrict {g : Ideal (𝓞 K) → ℂ} (hg : g ⊥ = 0) :
    (restrict g).zeroExtend = g := by
  funext I
  by_cases hI : I = ⊥
  · simpa [hI] using hg.symm
  · simp [zeroExtend_of_ne, hI]

/-- A function on all ideals is a zero extension if and only if it vanishes at `⊥`. -/
theorem exists_zeroExtend_eq_iff {g : Ideal (𝓞 K) → ℂ} :
    (∃ f : IdealArithmeticFunction K, f.zeroExtend = g) ↔ g ⊥ = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact zeroExtend_bot f
  · intro hg
    exact ⟨restrict g, zeroExtend_restrict hg⟩

/-- Zero extension is injective: its values on nonzero ideals retain the entire function. -/
theorem zeroExtend_injective :
    Function.Injective (zeroExtend : IdealArithmeticFunction K → Ideal (𝓞 K) → ℂ) := by
  intro f g h
  simpa only [restrict_zeroExtend] using congrArg restrict h

/-- Two zero extensions agree exactly when the underlying ideal arithmetic functions agree. -/
@[simp]
theorem zeroExtend_eq_iff {f g : IdealArithmeticFunction K} :
    f.zeroExtend = g.zeroExtend ↔ f = g := zeroExtend_injective.eq_iff

/-- A function on all ideals that vanishes at `⊥` is the zero extension of a unique ideal
arithmetic function. -/
theorem existsUnique_zeroExtend_eq {g : Ideal (𝓞 K) → ℂ} (hg : g ⊥ = 0) :
    ∃! f : IdealArithmeticFunction K, f.zeroExtend = g := by
  refine ⟨restrict g, zeroExtend_restrict hg, fun f hf => ?_⟩
  exact zeroExtend_injective (hf.trans (zeroExtend_restrict hg).symm)

/-- The zero extension is zero exactly at `⊥` when the original function has no zero values. -/
theorem zeroExtend_eq_zero_iff (f : IdealArithmeticFunction K)
    (hf : ∀ I, f I ≠ 0) {I : Ideal (𝓞 K)} : f.zeroExtend I = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    by_contra hI
    exact hf ⟨I, by simpa using hI⟩ ((zeroExtend_of_ne f hI).symm.trans h)
  · rintro rfl
    exact zeroExtend_bot f

/-- If the original function does not vanish, its zero extension is nonzero at every nonzero
ideal. -/
theorem zeroExtend_ne_zero (f : IdealArithmeticFunction K) (hf : ∀ I, f I ≠ 0)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : f.zeroExtend I ≠ 0 := by
  intro hzero
  exact hI ((zeroExtend_eq_zero_iff f hf).mp hzero)

/-! ## Compatibility with pointwise operations -/

/-- Zero extension preserves the pointwise zero function. -/
@[simp]
theorem zeroExtend_zero : zeroExtend (0 : IdealArithmeticFunction K) = 0 := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI, zeroExtend_of_ne]

/-- Zero extension preserves pointwise addition. -/
@[simp]
theorem zeroExtend_add (f g : IdealArithmeticFunction K) :
    zeroExtend (f + g) = f.zeroExtend + g.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI, zeroExtend_of_ne]

/-- Zero extension preserves pointwise negation. -/
@[simp]
theorem zeroExtend_neg (f : IdealArithmeticFunction K) : zeroExtend (-f) = -f.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI, zeroExtend_of_ne]

/-- Zero extension preserves pointwise subtraction. -/
@[simp]
theorem zeroExtend_sub (f g : IdealArithmeticFunction K) :
    zeroExtend (f - g) = f.zeroExtend - g.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI, zeroExtend_of_ne]

/-- Zero extension preserves pointwise complex scalar multiplication. -/
@[simp]
theorem zeroExtend_smul (c : ℂ) (f : IdealArithmeticFunction K) :
    zeroExtend (c • f) = c • f.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI, zeroExtend_of_ne]

/-- Zero extension preserves pointwise multiplication. -/
@[simp]
theorem zeroExtend_mul (f g : IdealArithmeticFunction K) :
    zeroExtend (f * g) = f.zeroExtend * g.zeroExtend := by
  funext I
  by_cases hI : I = ⊥ <;> simp [hI, zeroExtend_of_ne]

/-- The everywhere-one function on all ideals is not the zero extension of an ideal arithmetic
function, since its value at `⊥` is one rather than zero. This is the roadmap's zero-ideal
rejection test. -/
theorem not_exists_zeroExtend_eq_one :
    ¬ ∃ f : IdealArithmeticFunction K, f.zeroExtend = (1 : Ideal (𝓞 K) → ℂ) := by
  rw [exists_zeroExtend_eq_iff]
  exact one_ne_zero

end IdealArithmeticFunction

end TauCeti
