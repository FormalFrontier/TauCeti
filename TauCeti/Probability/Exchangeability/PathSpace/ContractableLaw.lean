/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.FiniteMarginals
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic

/-!
# Contractable laws on path space

This file adds the path-law formulation of contractability, also called spreadability:
a measure on `ℕ → α` is invariant under every strictly increasing reindexing of time.
The process-level predicate `Contractable μ X` remains the main stochastic-process API;
`ContractableLaw` names the equivalent path-space viewpoint needed by the de Finetti
factorization and path-space dynamics.

This is the contractability analogue of `ExchangeableLaw`. It realizes the Exchangeability
roadmap's Layer 0 request for the characterization of contractability by strictly increasing
maps `ℕ → ℕ`, with finite-dimensional marginal consequences. The process-level ↔ path-law
bridges live in `TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge`, which imports this
file and `Contractability`; no Mathlib infrastructure is vendored.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A measure on one-sided path space is contractable, or spreadable, if it is invariant under
every strictly increasing reindexing of the time coordinate. -/
def ContractableLaw (ρ : Measure (ℕ → α)) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ

/-- Constructor for `ContractableLaw` from the defining map invariance. -/
theorem ContractableLaw.intro {ρ : Measure (ℕ → α)}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ) :
    ContractableLaw ρ :=
  h

/-- Simp normal form for `ContractableLaw`. -/
@[simp]
theorem contractableLaw_iff {ρ : Measure (ℕ → α)} :
    ContractableLaw ρ ↔
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ :=
  Iff.rfl

/-- The defining invariance of a contractable path law. -/
theorem ContractableLaw.map_reindex {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ :=
  hρ φ hφ

/-- A strictly increasing time reindexing preserves a contractable path law. -/
theorem ContractableLaw.measurePreserving_reindex {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ :=
  ⟨measurable_reindex φ, ContractableLaw.map_reindex hρ hφ⟩

/-- Path-law contractability is equivalently measure preservation by every strictly increasing
time reindexing. -/
theorem contractableLaw_iff_forall_measurePreserving_reindex {ρ : Measure (ℕ → α)} :
    ContractableLaw ρ ↔
      ∀ φ : ℕ → ℕ, StrictMono φ →
        MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ := by
  constructor
  · intro hρ φ hφ
    exact hρ.measurePreserving_reindex hφ
  · intro hρ φ hφ
    exact (hρ φ hφ).map_eq

/-- The finite marginal of a contractable path law along any strictly increasing selection
`k : Fin n → ℕ` equals its first-`n` prefix marginal. -/
theorem ContractableLaw.map_prefixProj_of_strictMono {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) {n : ℕ} {k : Fin n → ℕ} (hk : StrictMono k) :
    ρ.map (fun x : ℕ → α => fun i : Fin n => x (k i)) =
      ρ.map (prefixProj α n) := by
  obtain ⟨φ, -, hφ, hφ_eq, -⟩ := exists_strictMono_nat_extending_fin hk
  have hmap := congrArg (fun ν : Measure (ℕ → α) => ν.map (prefixProj α n))
    (hρ.map_reindex hφ)
  rw [map_reindex_prefixProj] at hmap
  have hidx :
      (fun x : ℕ → α => fun i : Fin n => x (φ i.val)) =
        fun x : ℕ → α => fun i : Fin n => x (k i) := by
    funext x i
    rw [hφ_eq i]
  simpa [hidx] using hmap

/-- For finite path laws, contractability is equivalently invariance of every finite-dimensional
marginal under strictly increasing finite selections. -/
theorem contractableLaw_iff_forall_map_prefixProj_of_strictMono {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] :
    ContractableLaw ρ ↔
      ∀ n (k : Fin n → ℕ), StrictMono k →
        ρ.map (fun x : ℕ → α => fun i : Fin n => x (k i)) =
          ρ.map (prefixProj α n) := by
  constructor
  · intro hρ n k hk
    exact hρ.map_prefixProj_of_strictMono hk
  · intro hρ
    refine ContractableLaw.intro ?_
    intro φ hφ
    haveI : IsFiniteMeasure (ρ.map (fun x : ℕ → α => fun k => x (φ k))) := by
      infer_instance
    refine measure_eq_of_prefixProj_map_eq ?_
    intro n
    rw [map_reindex_prefixProj]
    exact hρ n (fun i : Fin n => φ i.val) (hφ.comp Fin.val_strictMono)

/-- A contractable path law is preserved by the one-sided shift. -/
theorem ContractableLaw.measurePreserving_shift {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) :
    MeasurePreserving (shift α) ρ ρ :=
  hρ.measurePreserving_reindex (φ := fun k => k + 1) fun _ _ h => Nat.add_lt_add_right h 1

/-- Every iterate of the one-sided shift preserves a contractable path law. -/
theorem ContractableLaw.measurePreserving_shift_iterate {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) (n : ℕ) :
    MeasurePreserving ((shift α)^[n]) ρ ρ :=
  (hρ.measurePreserving_shift).iterate n

/-- The one-sided shift leaves a contractable path law unchanged. -/
theorem ContractableLaw.map_shift {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) :
    ρ.map (shift α) = ρ :=
  (ContractableLaw.measurePreserving_shift hρ).map_eq

/-- Iterating the one-sided shift leaves a contractable path law unchanged. -/
theorem ContractableLaw.map_shift_iterate {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) (n : ℕ) :
    ρ.map ((shift α)^[n]) = ρ :=
  (ContractableLaw.measurePreserving_shift_iterate hρ n).map_eq

end Probability

end TauCeti
