/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.IrreducibleOfUnramified

/-!
# A cyclotomic extension meets an unramified extension trivially

Let `A` and `B` be intermediate fields of `Ω / K`, with `B` a `q`-th cyclotomic extension of `K`
for a prime `q`, and suppose every prime of `𝓞 A` above `q` is unramified over `ℤ`. Then
`A ⊓ B = ⊥`.

The ramification count itself is `IsCyclotomicExtension.inf_eq_bot_of_finrank_eq_totient`, which
takes `[B : K] = φ q` as a hypothesis. What this file adds is the observation that unramifiedness
of `A` already supplies that degree, through
`IsCyclotomicExtension.irreducible_cyclotomic_of_unramified`: the same hypothesis therefore
discharges both halves, and the caller is left with no degree obligation.

## Main results

* `IsCyclotomicExtension.inf_eq_bot_of_unramified`: `A ⊓ B = ⊥`.

## References

Milne, *Algebraic Number Theory*, proof of Proposition 6.2; Sharifi, *Algebraic Number Theory*,
proof of Lemma 3.1.13. Both run this argument with `K = ℚ`.
-/

public section

open scoped NumberField
open Polynomial TauCeti.RamificationInertia

namespace IsCyclotomicExtension

/-- **A cyclotomic extension meets an unramified extension trivially.** If `B` is a `q`-th
cyclotomic extension of `K` for a prime `q`, and every prime of `𝓞 A` above `q` is unramified
over `ℤ`, then `A ⊓ B = ⊥`.

This is `inf_eq_bot_of_finrank_eq_totient` with the degree hypothesis discharged. That theorem
asks for `[B : K] = φ q` and derives the intersection from the ramification count alone; here the
degree comes from `irreducible_cyclotomic_of_unramified`, so unramifiedness in `A` supplies both
halves and no separate degree hypothesis is left on the caller. -/
theorem inf_eq_bot_of_unramified {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (q : ℕ) (hq : q.Prime) (A B : IntermediateField K Ω) [NumberField A] [NumberField B]
    [IsCyclotomicExtension {q} K B]
    (hur : ∀ (P : Ideal (𝓞 A)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ P) :
    A ⊓ B = ⊥ := by
  -- `Fact q.Prime` is what supplies `NeZero q` to `IsCyclotomicExtension.finrank`.
  have : Fact q.Prime := ⟨hq⟩
  exact inf_eq_bot_of_finrank_eq_totient q hq A B hur <|
    IsCyclotomicExtension.finrank B
      (irreducible_cyclotomic_of_unramified K q hq fun 𝔮 ↦
        isUnramifiedAt_of_forall_isUnramifiedAt hur 𝔮)

end IsCyclotomicExtension
