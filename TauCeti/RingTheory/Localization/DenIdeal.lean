/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The denominator ideal of an element of an algebra

For `x` in an `R`-algebra `K`, the denominator ideal `Algebra.denIdeal K x` is the colon ideal
`(R : x) = {r : R | r • x ∈ R}` — the `r` that clear the denominator of `x`. When `K` is the
localization of `R` at its non-zero-divisors it is nonzero (`Algebra.denIdeal_ne_bot`), because
any expression of `x` as a fraction exhibits a denominator in it.

This is general commutative algebra, used in
`TauCeti/RingTheory/DedekindDomain/SInteger/Basic.lean`
to show that every ideal of a ring of `S`-integers is extended from the base.

Split out of material adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

open scoped nonZeroDivisors

section Semiring

variable {R : Type*} [CommSemiring R] (K : Type*) [Semiring K] [Algebra R K]

/-- The denominator ideal of `x : K`: the colon ideal `(R : x) = {r : R | r • x ∈ R}`.

It is an opaque `def` rather than an `abbrev` so that `simp` cannot rewrite through it with
`Submodule.mem_colon_singleton` before `mem_denIdeal_iff` fires; membership is accessed
through that lemma throughout, and the colon-ideal description through `denIdeal_def`. -/
def Algebra.denIdeal (x : K) : Ideal R := (1 : Submodule R K).colon {x}

/-- The defining equality of `Algebra.denIdeal`, exported because the definition is opaque:
consumers reaching for colon-ideal operations rewrite with this, while `mem_denIdeal_iff`
remains the membership normal form. Not a `simp` lemma — rewriting with it would undo
`mem_denIdeal_iff`. -/
lemma Algebra.denIdeal_def (x : K) :
    Algebra.denIdeal K x = (1 : Submodule R K).colon {x} := by
  simp only [Algebra.denIdeal]

/-- Membership in the denominator ideal: `r` clears `x` into the image of `R`, in the sense that
`r * x` is the image of some `s : R`. -/
@[simp] lemma Algebra.mem_denIdeal_iff {x : K} {r : R} :
    r ∈ Algebra.denIdeal K x ↔ ∃ s : R, algebraMap R K r * x = algebraMap R K s := by
  rw [Algebra.denIdeal, Submodule.mem_colon_singleton, Algebra.smul_def, Submodule.mem_one]
  exact exists_congr fun s ↦ eq_comm

end Semiring

variable {R : Type*} [CommSemiring R] (K : Type*) [CommSemiring K] [Algebra R K]

/-- The denominator ideal of an element of a localization at the non-zero-divisors is nonzero:
a denominator witnessing the element as a fraction lies in it. -/
lemma Algebra.denIdeal_ne_bot [Nontrivial R] [IsLocalization R⁰ K] (x : K) :
    Algebra.denIdeal K x ≠ (⊥ : Ideal R) := by
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj R⁰ x
  refine fun h0 ↦ nonZeroDivisors.ne_zero hb ?_
  have : b ∈ Algebra.denIdeal K x := by
    rw [Algebra.mem_denIdeal_iff]; exact ⟨a, by rw [mul_comm]; exact hab⟩
  simpa [h0] using this

end
