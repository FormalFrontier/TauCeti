/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Exchangeability from adjacent transpositions

This file adds the finite adjacent-transposition characterization promised in
`TauCetiRoadmap/Exchangeability/README.md`, Layer 0. For a fixed block length, invariance under
the adjacent swaps of `Fin n` implies invariance under every permutation of `Fin n`; applying this
at every length gives the corresponding characterization of `Exchangeable`.

The proof uses Mathlib's `Equiv.Perm.mclosure_swap_castSucc_succ`, the theorem that adjacent
swaps generate the finite symmetric group.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

namespace ExchangeableAt

private theorem blockLaw_perm_mul {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ)
    (σ τ : Equiv.Perm (Fin n)) :
    blockLaw μ X (fun i : Fin n => ((σ * τ) i).val) =
      (blockLaw μ X fun i : Fin n => (σ i).val).map
        (fun x : Fin n → α => fun i => x (τ i)) := by
  have hXσ : ∀ i : Fin n, AEMeasurable (X (σ i).val) μ := fun i => hX (σ i)
  simpa [Function.comp_def] using
    (map_blockLaw_reindex μ (fun i : Fin n => (σ i).val) τ hXσ).symm

private theorem prefixLaw_map_perm {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (τ : Equiv.Perm (Fin n)) :
    (prefixLaw μ X n).map (fun x : Fin n → α => fun i => x (τ i)) =
      blockLaw μ X fun i : Fin n => (τ i).val := by
  simpa [Function.comp_def, prefixLaw_def] using
    map_blockLaw_reindex μ (fun i : Fin n => i.val) τ hX

/-- The submonoid of finite permutations preserving the `n`-dimensional law of a process. -/
private def invariantSubmonoid (μ : Measure Ω) (X : ℕ → Ω → α) {n : ℕ}
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) : Submonoid (Equiv.Perm (Fin n)) where
  carrier := {σ | blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n}
  one_mem' := by
    simp [prefixLaw_def]
  mul_mem' := by
    intro σ τ hσ hτ
    calc
      blockLaw μ X (fun i : Fin n => ((σ * τ) i).val) =
          (blockLaw μ X fun i : Fin n => (σ i).val).map
            (fun x : Fin n → α => fun i => x (τ i)) :=
        blockLaw_perm_mul hX σ τ
      _ = (prefixLaw μ X n).map (fun x : Fin n → α => fun i => x (τ i)) := by
        rw [hσ]
      _ = blockLaw μ X (fun i : Fin n => (τ i).val) :=
        prefixLaw_map_perm hX τ
      _ = prefixLaw μ X n := hτ

/-- Invariance under all adjacent swaps of `Fin (n + 1)` is equivalent to finite
exchangeability at length `n + 1`. -/
theorem succ_iff_forall_adjacent_swap {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (hX : ∀ i : Fin (n + 1), AEMeasurable (X i.val) μ) :
    ExchangeableAt μ X (n + 1) ↔
      ∀ i : Fin n,
        blockLaw μ X (fun j : Fin (n + 1) => (Equiv.swap i.castSucc i.succ j).val) =
          prefixLaw μ X (n + 1) := by
  constructor
  · intro h i
    exact h (Equiv.swap i.castSucc i.succ)
  · intro h σ
    let H := invariantSubmonoid μ X hX
    have hgen :
        Submonoid.closure (Set.range fun i : Fin n =>
          (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1)))) ≤ H :=
      Submonoid.closure_le.mpr <| by
        rintro τ ⟨i, rfl⟩
        exact h i
    have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin n =>
        (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1)))) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ n]
      trivial
    exact hgen hmem

/-- A restatement of `ExchangeableAt.succ_iff_forall_adjacent_swap` with the adjacent-swap
condition first. -/
theorem of_forall_adjacent_swap {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (hX : ∀ i : Fin (n + 1), AEMeasurable (X i.val) μ)
    (h :
      ∀ i : Fin n,
        blockLaw μ X (fun j : Fin (n + 1) => (Equiv.swap i.castSucc i.succ j).val) =
          prefixLaw μ X (n + 1)) :
    ExchangeableAt μ X (n + 1) :=
  (succ_iff_forall_adjacent_swap hX).2 h

end ExchangeableAt

namespace Exchangeable

private theorem exchangeableAt_zero {μ : Measure Ω} {X : ℕ → Ω → α} :
    ExchangeableAt μ X 0 := by
  intro σ
  have hσ : σ = 1 := Subsingleton.elim σ 1
  simp [hσ, prefixLaw_def]

/-- A process is exchangeable iff each finite block is invariant under adjacent swaps. -/
theorem iff_forall_adjacent_swap {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) :
    Exchangeable μ X ↔
      ∀ n (i : Fin n),
        blockLaw μ X (fun j : Fin (n + 1) => (Equiv.swap i.castSucc i.succ j).val) =
          prefixLaw μ X (n + 1) := by
  constructor
  · intro h n i
    exact h (n + 1) (Equiv.swap i.castSucc i.succ)
  · intro h n
    cases n with
    | zero => exact exchangeableAt_zero
    | succ n =>
        exact ExchangeableAt.of_forall_adjacent_swap (fun i => hX i.val) (h n)

/-- The introduction form of `Exchangeable.iff_forall_adjacent_swap`. -/
theorem of_forall_adjacent_swap {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ)
    (h :
      ∀ n (i : Fin n),
        blockLaw μ X (fun j : Fin (n + 1) => (Equiv.swap i.castSucc i.succ j).val) =
          prefixLaw μ X (n + 1)) :
    Exchangeable μ X :=
  (iff_forall_adjacent_swap hX).2 h

end Exchangeable

end Probability

end TauCeti
