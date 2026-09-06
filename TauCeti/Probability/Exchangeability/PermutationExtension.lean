/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* two disjoint finite index sets admit a permutation fixing the first pointwise and carrying the
  second past any cutoff (`exists_perm_fixOn_le_apply`).

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
  let C := Finset.univ.sup k + 1
  let φ : ℕ → ℕ := fun n => if h : n < m then k ⟨n, h⟩ else n + C
  refine ⟨φ, C, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only [φ]
    by_cases ha : a < m
    · by_cases hb : b < m
      · rw [dite_eq_left ha, dite_eq_left hb]
        exact hk (Fin.lt_def.mpr hab)
      · rw [dite_eq_left ha, dite_eq_right hb]
        have hle_sup : k ⟨a, ha⟩ ≤ Finset.univ.sup k :=
          Finset.le_sup (f := k) (Finset.mem_univ (⟨a, ha⟩ : Fin m))
        exact (Nat.lt_succ_of_le hle_sup).trans_le (Nat.le_add_left C b)
    · by_cases hb : b < m
      · exact (ha (hab.trans hb)).elim
      · rw [dite_eq_right ha, dite_eq_right hb]
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

/-- A permutation of `ℕ` that fixes a finite set `I` pointwise and carries a finite set `J`,
disjoint from `I`, past `n`. -/
theorem _root_.Finset.exists_perm_fixOn_le_apply (I J : Finset ℕ) (hIJ : Disjoint I J) (n : ℕ) :
    ∃ ρ : Equiv.Perm ℕ, (∀ i ∈ I, ρ i = i) ∧ ∀ j ∈ J, n ≤ ρ j := by
  classical
  -- shift `J` by `N`, large enough to clear both `n` and everything in `I`
  set N : ℕ := n + (I ∪ J).sup id + 1 with hN
  let g : ↥(I ∪ J) → ℕ := fun x => if (x : ℕ) ∈ I then x else x + N
  -- every element of `J` is sent past `N`, hence past everything in `I ∪ J`
  have hbig : ∀ x : ↥(I ∪ J), (x : ℕ) < N := fun x => by
    have := Finset.le_sup (f := id) x.property
    simp only [id] at this; omega
  have hg : Function.Injective g := by
    intro x y hxy
    simp only [g] at hxy
    apply Subtype.ext
    have hx := hbig x
    have hy := hbig y
    split_ifs at hxy <;> omega
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair (fun x : ↥(I ∪ J) => (x : ℕ)) g
    Subtype.val_injective hg
  refine ⟨ρ, fun i hi => ?_, fun j hj => ?_⟩
  · have := hρ ⟨i, Finset.mem_union_left _ hi⟩
    simpa [g, hi] using this
  · have hjI : j ∉ I := Finset.disjoint_right.mp hIJ hj
    have := hρ ⟨j, Finset.mem_union_right _ hj⟩
    simp only [g, hjI, ite_false] at this
    rw [this]; omega

end Probability

end TauCeti
