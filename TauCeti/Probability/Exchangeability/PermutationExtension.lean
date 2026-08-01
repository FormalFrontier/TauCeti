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

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing self-map
of `ℕ` that agrees with `k` on the first `m` inputs and is **eventually a translation**: beyond the
selection it adds a fixed constant `C`.

The eventual-translation clause matters for **shift-invariant** events. Beyond the first `m`
coordinates, reindexing by `φ` agrees with the fixed iterate `shift^[C]`, so for a set `S` with
`shift ⁻¹' S = S` membership is unchanged: exact shift invariance gives both
`x ∈ S ↔ shift^[C] x ∈ S` and insensitivity to the altered finite prefix.

**Tail measurability alone does not suffice.** A tail event is insensitive to finitely many
coordinates, but need not satisfy `shift ⁻¹' S = S`, and it is the shift invariance — not the
prefix insensitivity — that supplies the `shift^[C]` step. So this clause serves
`MeasurableSpace.invariants (shift α)`, not the path tail.

This concerns **exact** invariance, sets literally unchanged by the shift. It says nothing about the
a.e.-invariant formulation Mathlib's `ErgodicSMul` uses; relating the two is a separate matter. -/
theorem exists_strictMono_nat_extending_fin_eventually_add {m : ℕ} {k : Fin m → ℕ}
    (hk : StrictMono k) :
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

/-- A strictly monotone finite selection `k : Fin m → ℕ` extends to a strictly increasing
self-map of `ℕ` that agrees with `k` on the first `m` inputs.

The form most callers want. `exists_strictMono_nat_extending_fin_eventually_add` additionally
records that the extension is eventually a translation, which is what a reindexing needs in order
to preserve invariant events. -/
theorem exists_strictMono_nat_extending_fin {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i : Fin m, φ i.val = k i :=
  let ⟨φ, _, hφ, hφ_eq, _⟩ := exists_strictMono_nat_extending_fin_eventually_add hk
  ⟨φ, hφ, hφ_eq⟩

end Probability

end TauCeti
