/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Extending a valuation from a subring reached by the powers of an element

Let `R` be a subring of a commutative ring `A`, and let `s ∈ R` be an element some power of which
carries each element of `A` into `R`: for every `a` there is an `n` with `sⁿ * a ∈ R`. A
valuation `w` of `R` that does not vanish at `s` then has only one possible extension to `A`,

`v a = w (sⁿ * a) * (w s)⁻ⁿ`,

and this file shows that the formula is well defined, is a valuation, and is the only valuation
of `A` restricting to `w`.

No topology is involved. The hypothesis is met by a ring of definition of a Huber ring — it is
open, so a topologically nilpotent `s` satisfies it — and
`TauCeti.RingTheory.Huber.ExtendValuation` is that specialisation.

## Why this is not `Valuation.extendToLocalization`

Mathlib extends a valuation along a localisation that inverts a set on which the valuation is
nonzero. That does not apply here: the hypothesis does not make `s` invertible in `A`, so there
need be no ring map `R[1/s] → A` at all. Take `R = A = ℤ_[p]` and `s = p`, where `R[1/s] = ℚ_[p]`.
What is true, and is all the formula needs, is the one-sided statement that every element of `A`
is carried into `R` by a power of `s`.

## Well-definedness

Independence of `n` reduces to the case of comparing `n` with `n + j`, where
`s ^ (n + j) * a = s ^ j * (sⁿ * a)` splits off a factor whose `w`-value is `(w s) ^ j`, exactly
cancelling the extra `(w s)⁻ʲ`. Two arbitrary exponents are then compared through their sum.

The two valuation axioms reach a shared exponent differently. For a product, each argument keeps
its *own* workable exponent — `x` at `m` and `y` at `n` — and only the product is evaluated at
`m + n`, because `s ^ (m + n) * (x * y) = (sᵐ * x) * (sⁿ * y)` already splits that way. A sum has
no such splitting, so there both terms are raised to the common exponent `m + n`. In each case
the axiom is then inherited from `w` once the shared factor `(w s)⁻⁽ᵐ⁺ⁿ⁾` is divided out.

## Main definitions

* `Valuation.extendOfPowMulMem` : the extension of `w` to `A`.

## Main results

* `Valuation.extendOfPowMulMem_apply` : the defining formula, at **every** exponent that works,
  not just the chosen one. This is the interface; the definition goes through
  `Classical.choose` and is not meant to be unfolded.
* `Valuation.extendOfPowMulMem_coe` : the extension restricts to `w`.
* `Valuation.eq_extendOfPowMulMem` : **uniqueness** — any valuation of `A` restricting to `w`
  *is* this one, so the extension is canonical.
* `Valuation.extendOfPowMulMem_congr` : consequently the extension does not depend on which `s`
  is used to build it.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.44(3), which uses this
  extension for a ring of definition of a Huber ring.

## Provenance

Adapted from [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch
`dev/adic-spaces`, commit `37bbdaeb9`, `projects/AdicSpaces/Adic spaces/Lemma745.lean`,
declarations `vExtFun_step`, `vExtFun_well_defined`, `vExtFun_map_mul`,
`vExtFun_map_add_le_max` and `exists_valuation_extension`. **Adapted, not copied**: that
development states the result existentially, as `∃ v_ext, …`, for a pair of definition of a
Huber ring, and threads the value `w s` through five separate lemmas as an explicit parameter
with its own defining equation. Here the extension is a `def`, so it can be named and rewritten
at a call site, the arithmetic is one private lemma rather than four public ones, and the whole
construction is carried out for a subring reached by the powers of `s`. The uniqueness theorem
and the resulting independence of `s` have no counterpart there.
-/

public section

namespace Valuation

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {R : Subring A}

/-- Raising the exponent keeps the product in the subring: `s ^ (k + j) * a` splits as
`s ^ j * (s ^ k * a)`, and both factors lie in `R`. -/
private theorem pow_add_mul_mem {s : A} (hs : s ∈ R) {a : A} {k : ℕ} (hk : s ^ k * a ∈ R)
    (j : ℕ) : s ^ (k + j) * a ∈ R := by
  have hsplit : s ^ (k + j) * a = s ^ j * (s ^ k * a) := by rw [add_comm, pow_add, mul_assoc]
  rw [hsplit]
  exact R.mul_mem (R.pow_mem hs j) hk

/-- The quotient `w (sⁿ * a) * (w s)⁻ⁿ` does not depend on `n`. Both exponents are compared
with their sum, where the extra factor of `s` contributes `(w s) ^ j` and cancels. -/
private theorem extend_aux (w : Valuation R Γ₀) {s : A} (hs : s ∈ R) (hw : w ⟨s, hs⟩ ≠ 0)
    {a : A} {m n : ℕ} (hm : s ^ m * a ∈ R) (hn : s ^ n * a ∈ R) :
    w ⟨s ^ m * a, hm⟩ * (w ⟨s, hs⟩)⁻¹ ^ m = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n := by
  -- one step: comparing `k` with `k + j`
  have step : ∀ {k : ℕ} (hk : s ^ k * a ∈ R) (j : ℕ),
      w ⟨s ^ k * a, hk⟩ * (w ⟨s, hs⟩)⁻¹ ^ k =
        w ⟨s ^ (k + j) * a, pow_add_mul_mem hs hk j⟩ * (w ⟨s, hs⟩)⁻¹ ^ (k + j) := by
    intro k hk j
    have hsplit : (⟨s ^ (k + j) * a, pow_add_mul_mem hs hk j⟩ : R) =
        ⟨s, hs⟩ ^ j * ⟨s ^ k * a, hk⟩ :=
      Subtype.ext (by push_cast; ring)
    have hj : w ⟨s, hs⟩ ^ j * (w ⟨s, hs⟩)⁻¹ ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
    rw [hsplit, map_mul, map_pow, pow_add, mul_comm (w ⟨s, hs⟩ ^ j), mul_mul_mul_comm, hj,
      mul_one]
  -- compare both exponents with their sum
  rw [step hm n, step hn m]
  exact congrArg₂ (· * ·) (congrArg w (Subtype.ext (by push_cast; ring)))
    (by rw [Nat.add_comm])

/-- The underlying function of `extendOfPowMulMem`, `a ↦ w (sⁿ * a) * (w s)⁻ⁿ` at a chosen `n`.
Use `extendOfPowMulMem_apply`, which is valid at every workable `n`, rather than unfolding. -/
private noncomputable def extendFun (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (a : A) : Γ₀ :=
  w ⟨s ^ (hpow a).choose * a, (hpow a).choose_spec⟩ * (w ⟨s, hs⟩)⁻¹ ^ (hpow a).choose

private theorem extendFun_apply (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (a : A) {n : ℕ}
    (hn : s ^ n * a ∈ R) :
    extendFun w hs hpow a = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n :=
  extend_aux w hs hw _ hn

private theorem extendFun_coe (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (a : R) :
    extendFun w hs hpow (a : A) = w a := by
  rw [extendFun_apply w hs hpow hw (a : A) (n := 0) (by simp)]
  simp

/-- **The extension of `w` from `R` to `A`**, when every element of `A` is carried into `R` by
some power of `s`. For any `n` with `sⁿ * a ∈ R` the value is `w (sⁿ * a) * (w s)⁻ⁿ`, and
`extendOfPowMulMem_apply` says so at every such `n`. -/
noncomputable def extendOfPowMulMem (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) : Valuation A Γ₀ where
  toFun := extendFun w hs hpow
  map_zero' := by simpa using extendFun_coe w hs hpow hw 0
  map_one' := by simpa using extendFun_coe w hs hpow hw 1
  map_mul' x y := by
    obtain ⟨m, hm⟩ := hpow x
    obtain ⟨n, hn⟩ := hpow y
    have hprod : s ^ (m + n) * (x * y) = (s ^ m * x) * (s ^ n * y) := by ring
    have hxy : s ^ (m + n) * (x * y) ∈ R := by rw [hprod]; exact R.mul_mem hm hn
    have hsplit : (⟨s ^ (m + n) * (x * y), hxy⟩ : R) = ⟨s ^ m * x, hm⟩ * ⟨s ^ n * y, hn⟩ :=
      Subtype.ext (by push_cast; ring)
    rw [extendFun_apply w hs hpow hw _ hxy, extendFun_apply w hs hpow hw _ hm,
      extendFun_apply w hs hpow hw _ hn, hsplit, map_mul, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  map_add_le_max' x y := by
    -- a sum needs one exponent that works for both terms, so take the sum of the two
    obtain ⟨m, hm⟩ := hpow x
    obtain ⟨n, hn⟩ := hpow y
    have hx : s ^ (m + n) * x ∈ R := pow_add_mul_mem hs hm n
    have hy : s ^ (m + n) * y ∈ R := by
      rw [Nat.add_comm]; exact pow_add_mul_mem hs hn m
    have hxy : s ^ (m + n) * (x + y) ∈ R := by
      rw [mul_add]; exact R.add_mem hx hy
    have hsplit : (⟨s ^ (m + n) * (x + y), hxy⟩ : R) =
        ⟨s ^ (m + n) * x, hx⟩ + ⟨s ^ (m + n) * y, hy⟩ :=
      Subtype.ext (by push_cast; ring)
    rw [extendFun_apply w hs hpow hw _ hxy, extendFun_apply w hs hpow hw _ hx,
      extendFun_apply w hs hpow hw _ hy, hsplit]
    rcases le_max_iff.mp (w.map_add ⟨s ^ (m + n) * x, hx⟩ ⟨s ^ (m + n) * y, hy⟩) with h | h
    · exact le_max_of_le_left (mul_le_mul' h le_rfl)
    · exact le_max_of_le_right (mul_le_mul' h le_rfl)

/-- **The defining formula**, at every exponent that carries `a` into the subring. -/
theorem extendOfPowMulMem_apply (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (a : A) {n : ℕ}
    (hn : s ^ n * a ∈ R) :
    w.extendOfPowMulMem hs hpow hw a = w ⟨s ^ n * a, hn⟩ * (w ⟨s, hs⟩)⁻¹ ^ n :=
  extendFun_apply w hs hpow hw a hn

/-- **The extension restricts to `w`.** -/
@[simp]
theorem extendOfPowMulMem_coe (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (a : R) :
    w.extendOfPowMulMem hs hpow hw (a : A) = w a :=
  extendFun_coe w hs hpow hw a

/-- **The extension is the only one.** A valuation of `A` restricting to `w` on `R` is forced at
`a` by its value on `sⁿ * a`, which `w` already fixes, so it *is* `extendOfPowMulMem`. This is
what makes the extension canonical. -/
theorem eq_extendOfPowMulMem (w : Valuation R Γ₀) {s : A} (hs : s ∈ R)
    (hpow : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hw : w ⟨s, hs⟩ ≠ 0) (v : Valuation A Γ₀)
    (hv : ∀ a : R, v (a : A) = w a) : v = w.extendOfPowMulMem hs hpow hw := by
  ext a
  obtain ⟨n, hn⟩ := hpow a
  -- `v` is already pinned on `R`, and `sⁿ * a` lies there
  have hvs : v s = w ⟨s, hs⟩ := hv ⟨s, hs⟩
  have hval : w ⟨s ^ n * a, hn⟩ = v s ^ n * v a := by
    rw [← hv ⟨s ^ n * a, hn⟩, ← map_pow v s n, ← map_mul v]
  have hcancel : w ⟨s, hs⟩ ^ n * (w ⟨s, hs⟩)⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  rw [extendOfPowMulMem_apply w hs hpow hw a hn, hval, hvs, mul_right_comm, hcancel, one_mul]

/-- **The extension does not depend on `s`.** Two elements of `R` whose powers reach `A` and at
which `w` is nonzero give the same extension, because each restricts to `w` and the extension is
unique. -/
theorem extendOfPowMulMem_congr (w : Valuation R Γ₀) {s t : A} (hs : s ∈ R)
    (hpows : ∀ a : A, ∃ n : ℕ, s ^ n * a ∈ R) (hws : w ⟨s, hs⟩ ≠ 0) (ht : t ∈ R)
    (hpowt : ∀ a : A, ∃ n : ℕ, t ^ n * a ∈ R) (hwt : w ⟨t, ht⟩ ≠ 0) :
    w.extendOfPowMulMem hs hpows hws = w.extendOfPowMulMem ht hpowt hwt :=
  eq_extendOfPowMulMem w ht hpowt hwt _ (extendOfPowMulMem_coe w hs hpows hws)

end Valuation
