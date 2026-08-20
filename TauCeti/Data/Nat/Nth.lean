/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Nth

/-!
# Recognizing `Nat.nth` from counts

`Nat.nth p k` is the `k`-th natural number satisfying `p`, and `0` when `p` holds at most `k`
times. Mathlib's `Nat.nth_count` identifies it whenever a witness is available: if `p n` holds and
`p` has exactly `k` predecessors below `n`, then `nth p k = n`. What is missing is the converse
bookkeeping — the *only if* half, including the degenerate branch — which is what a case analysis
on the value of `nth p k` needs.

`TauCeti.Nat.nth_eq_iff` supplies it: `nth p k = m` exactly when `m` is a counting witness, or else
`m = 0` and no counting witness exists at all. The two branches are mutually exclusive, and a
counting witness is unique when it exists, because `Nat.count p` strictly increases across a point
where `p` holds.

The degenerate branch is not a technicality that can be assumed away: `nth p k = 0` really does
happen when `p` has at most `k` witnesses, and a description of the fibres of `nth` has to name
that case. This makes the statement a usable membership criterion — for instance, it exhibits each
fibre of `x ↦ Nat.nth (fun i => x i = a) k` as a countable Boolean combination of conditions on
finitely many of the values of `x`.

## Main results

* `TauCeti.Nat.nth_eq_zero_of_forall_count_ne`: with no counting witness, `Nat.nth` takes its junk
  value.
* `TauCeti.Nat.nth_eq_iff`: the fibres of `Nat.nth p`.
-/

public section

namespace TauCeti

namespace Nat

/-- **Without a counting witness `Nat.nth` is junk.** If no `n` satisfying `p` has exactly `k`
predecessors satisfying `p`, then `p` holds at most `k` times, so `Nat.nth p k` is `0`. -/
theorem nth_eq_zero_of_forall_count_ne {p : ℕ → Prop} [DecidablePred p] {k : ℕ}
    (h : ∀ n, p n → Nat.count p n ≠ k) : Nat.nth p k = 0 := by
  by_contra h'
  exact h _ (Nat.nth_mem_of_ne_zero h')
    (Nat.count_nth fun hf => Nat.lt_card_toFinset_of_nth_ne_zero h' hf)

/-- **The fibres of `Nat.nth p`.** The value `Nat.nth p k` is `m` exactly when either `m` is the
counting witness for `k` — it satisfies `p` and has exactly `k` predecessors satisfying `p` — or
there is no counting witness at all and `m` is the junk value `0`. -/
theorem nth_eq_iff {p : ℕ → Prop} [DecidablePred p] {k m : ℕ} :
    Nat.nth p k = m ↔
      (p m ∧ Nat.count p m = k) ∨ (m = 0 ∧ ∀ n, ¬(p n ∧ Nat.count p n = k)) := by
  constructor
  · rintro rfl
    by_cases h : ∃ n, p n ∧ Nat.count p n = k
    · obtain ⟨n, hn, hcn⟩ := h
      subst hcn
      rw [Nat.nth_count hn]
      exact Or.inl ⟨hn, rfl⟩
    · exact Or.inr ⟨nth_eq_zero_of_forall_count_ne fun n hn hcn => h ⟨n, hn, hcn⟩,
        fun n hn => h ⟨n, hn.1, hn.2⟩⟩
  · rintro (⟨hm, hcm⟩ | ⟨rfl, h⟩)
    · rw [← hcm, Nat.nth_count hm]
    · exact nth_eq_zero_of_forall_count_ne fun n hn hcn => h n ⟨hn, hcn⟩

end Nat

end TauCeti
