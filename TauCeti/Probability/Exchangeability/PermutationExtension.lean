/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Permutation extensions for finite exchangeability

This file records the combinatorial extension lemmas used in the Layer 0
exchangeability API:

* strictly increasing finite subsequences extend to strictly increasing self-maps of `ℕ`.
* finite selections inside a larger finite prefix, or in `ℕ`, extend to permutations by Mathlib's
  `Equiv.Perm.exists_extending_pair`, which this module publicly re-exports.

The strict-monotone `ℕ` extension helper is adapted from the `cameronfreer/exchangeability`
Layer 0 sources pinned at `e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names
and hypotheses.
-/

public section

namespace TauCeti

namespace Probability

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing
self-map of `ℕ` that agrees with `k` on the first `m` inputs and is **eventually a translation**:
beyond the selection it adds a fixed constant.

The eventual-translation clause matters for invariant events. Composing with `φ` changes only the
first `m` coordinates and then acts as a fixed iterate of the shift, so any event that is unchanged
by dropping a finite prefix — a shift-invariant or tail event — is preserved by the reindexing. -/
theorem exists_strictMono_nat_extending_fin {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) :
    ∃ (φ : ℕ → ℕ) (C : ℕ), StrictMono φ ∧ (∀ i : Fin m, φ i.val = k i) ∧
      ∀ n, m ≤ n → φ n = n + C := by
  classical
  let C := Finset.univ.sup k + 1
  let φ : ℕ → ℕ := fun n => if h : n < m then k ⟨n, h⟩ else n + C
  refine ⟨φ, C, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only [φ]
    by_cases ha : a < m
    · by_cases hb : b < m
      · rw [dif_pos ha, dif_pos hb]
        exact hk (Fin.lt_def.mpr hab)
      · rw [dif_pos ha, dif_neg hb]
        have hle_sup : k ⟨a, ha⟩ ≤ Finset.univ.sup k :=
          Finset.le_sup (f := k) (Finset.mem_univ (⟨a, ha⟩ : Fin m))
        exact (Nat.lt_succ_of_le hle_sup).trans_le (Nat.le_add_left C b)
    · by_cases hb : b < m
      · exact (ha (hab.trans hb)).elim
      · rw [dif_neg ha, dif_neg hb]
        exact Nat.add_lt_add_right hab C
  · intro i
    simp [φ, i.isLt]
  · intro n hn
    simp [φ, Nat.not_lt.mpr hn]

end Probability

end TauCeti
