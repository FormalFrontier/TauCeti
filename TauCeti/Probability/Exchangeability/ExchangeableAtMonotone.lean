/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic
import TauCeti.Probability.Exchangeability.PermutationExtension

/-!
# Monotonicity of finite exchangeability

This file records the Layer 0 implication-lattice API for `ExchangeableAt`: if the first `n`
coordinates have permutation-invariant law, then so do the first `m` coordinates for every
`m ≤ n`. The proof is the finite-dimensional marginal argument: extend a permutation of
`Fin m` to one of `Fin n`, use exchangeability at `n`, and project the `n`-prefix law back to
the first `m` coordinates.

The permutation-extension step reuses Mathlib's `Equiv.Perm.exists_extending_pair`; the
measure-level projection step reuses Tau Ceti's `map_blockLaw_reindex` and `map_prefixLaw_castLE`.

This projection argument is adapted from Tau Ceti's credited
`Exchangeable.blockLaw_eq_prefixLaw_of_injective` proof in `Contractability.lean`, following the
`cameronfreer/exchangeability` Layer 0 sources.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

namespace ExchangeableAt

/-- An exchangeable `n`-prefix has the prefix law on every injective `m`-subselection inside
that prefix. -/
theorem blockLaw_eq_prefixLaw_of_injective {μ : Measure Ω} {X : ℕ → Ω → α} {m n : ℕ}
    (h : ExchangeableAt μ X n) (k : Fin m → Fin n) (hk : Function.Injective k)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    blockLaw μ X (fun i : Fin m => (k i).val) = prefixLaw μ X m := by
  have hmn : m ≤ n := by
    simpa using Fintype.card_le_of_injective k hk
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hmn) k
    (fun _ _ h => Fin.castLE_injective hmn h) hk
  have hperm : blockLaw μ X (fun j : Fin n => (σ j).val) = prefixLaw μ X n := h.permute σ
  have hLHS :
      (blockLaw μ X (fun j : Fin n => (σ j).val)).map
          (fun x : Fin n → α => fun i : Fin m => x (Fin.castLE hmn i)) =
        blockLaw μ X (fun i : Fin m => (k i).val) := by
    have hidx :
        (fun j : Fin n => (σ j).val) ∘ Fin.castLE hmn =
          fun i : Fin m => (k i).val := by
      funext i
      exact congrArg Fin.val (hσ i)
    rw [map_blockLaw_reindex μ _ (Fin.castLE hmn) (fun j => hX (σ j)), hidx]
  have hRHS :
      (prefixLaw μ X n).map (fun x : Fin n → α => fun i : Fin m => x (Fin.castLE hmn i)) =
        prefixLaw μ X m :=
    map_prefixLaw_castLE μ hmn hX
  have key := congrArg
    (Measure.map (fun x : Fin n → α => fun i : Fin m => x (Fin.castLE hmn i))) hperm
  rwa [hLHS, hRHS] at key

/-- Finite exchangeability at length `n` descends to every shorter prefix length `m ≤ n`. -/
theorem of_le {μ : Measure Ω} {X : ℕ → Ω → α} {m n : ℕ}
    (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    ExchangeableAt μ X m := by
  intro τ
  exact h.blockLaw_eq_prefixLaw_of_injective (fun i => Fin.castLE hmn (τ i))
    (by
      intro i j hij
      exact τ.injective (Fin.castLE_injective hmn hij))
    hX

/-- Finite exchangeability at length `n` descends to any strictly shorter prefix length. -/
theorem of_lt {μ : Measure Ω} {X : ℕ → Ω → α} {m n : ℕ}
    (h : ExchangeableAt μ X n) (hmn : m < n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    ExchangeableAt μ X m :=
  h.of_le hmn.le hX

/-- Exchangeability at `n + 1` descends to exchangeability at `n`. -/
theorem pred {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X (n + 1))
    (hX : ∀ i : Fin (n + 1), AEMeasurable (X i.val) μ) :
    ExchangeableAt μ X n :=
  h.of_le (Nat.le_succ n) hX

end ExchangeableAt

end Probability

end TauCeti
