/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Basic
public import TauCeti.Probability.Exchangeability.PermutationExtension
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Exchangeable laws on path space

This file adds the path-law formulation of full exchangeability for measures on `ℕ → α`.
The process-level definitions in `TauCeti.Probability.Exchangeability.Basic` remain the main
user-facing API for stochastic processes; `ExchangeableLaw` names the equivalent path-space
viewpoint needed by π-system, invariant-σ-algebra, and shift arguments.

Everything here is pure path space: it depends only on the coordinate-reindexing and prefix
machinery of `Basic` and the finite permutation extension of `PermutationExtension`. The
process-level ↔ path-law bridges live in
`TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge`, which imports both this file and
`FullyExchangeable`. No measure-theoretic infrastructure is vendored.

The closure theorem `exchangeableLaw_map_prod_coding` records that applying one jointly measurable
coding function coordinatewise to independent parameter and exchangeable-noise laws preserves
exchangeability.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- A measure on one-sided path space is exchangeable if it is invariant under every
permutation of the time coordinate. -/
def ExchangeableLaw (ρ : Measure (ℕ → α)) : Prop :=
  ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ

/-- Constructor for `ExchangeableLaw` from the defining map invariance. -/
theorem ExchangeableLaw.intro {ρ : Measure (ℕ → α)}
    (h : ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ) :
    ExchangeableLaw ρ :=
  h

/-- Simp normal form for `ExchangeableLaw`. -/
@[simp]
theorem exchangeableLaw_iff {ρ : Measure (ℕ → α)} :
    ExchangeableLaw ρ ↔ ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ :=
  Iff.rfl

/-- The defining invariance of an exchangeable path law. -/
theorem ExchangeableLaw.map_permReindex {ρ : Measure (ℕ → α)} (hρ : ExchangeableLaw ρ)
    (π : Equiv.Perm ℕ) :
    ρ.map (permReindex (α := α) π) = ρ :=
  hρ π

/-- Reindexing by a time permutation preserves an exchangeable path law. -/
theorem ExchangeableLaw.measurePreserving_permReindex {ρ : Measure (ℕ → α)}
    (hρ : ExchangeableLaw ρ) (π : Equiv.Perm ℕ) :
    MeasurePreserving (permReindex (α := α) π) ρ ρ :=
  ⟨measurable_reindex π, hρ.map_permReindex π⟩

/-- Joint measurability of a coordinatewise map on a parameter and a path. -/
theorem measurable_pi_uncurry_prod {T β ι : Type*} [MeasurableSpace T] [MeasurableSpace β]
    {f : T → β → α} (hf : Measurable (Function.uncurry f)) :
    Measurable fun p : T × (ι → β) => fun i => f p.1 (p.2 i) :=
  measurable_pi_lambda _ fun i =>
    hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

/-- **An i.i.d. product law is exchangeable.** Reindexing a constant product law by a
permutation leaves every factor unchanged. -/
theorem exchangeableLaw_infinitePi_const (P : ProbabilityMeasure α) :
    ExchangeableLaw (Measure.infinitePi fun _ : ℕ => (P : Measure α)) := by
  intro π
  have hperm : permReindex (α := α) π = fun x i => x (π i) := by
    funext x i
    rw [permReindex_apply]
  rw [hperm]
  simpa only using
    Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => (P : Measure α)) π.injective

/-- **Coordinatewise coding preserves exchangeability.** Applying a jointly measurable `f`
coordinatewise to a parameter and an independent exchangeable noise sequence gives an
exchangeable law. -/
theorem exchangeableLaw_map_prod_coding {T β : Type*} [MeasurableSpace T] [MeasurableSpace β]
    (π : Measure T) [SFinite π] {ρ : Measure (ℕ → β)} [SFinite ρ]
    (hρ : ExchangeableLaw ρ) {f : T → β → α} (hf : Measurable (Function.uncurry f)) :
    ExchangeableLaw ((π.prod ρ).map fun p i => f p.1 (p.2 i)) := by
  refine ExchangeableLaw.intro fun τ => ?_
  have hG := measurable_pi_uncurry_prod (α := α) (ι := ℕ) hf
  have hcomp : permReindex (α := α) τ ∘ (fun p : T × (ℕ → β) => fun i => f p.1 (p.2 i))
      = (fun p : T × (ℕ → β) => fun i => f p.1 (p.2 i)) ∘
        Prod.map (id : T → T) (permReindex (α := β) τ) := by
    funext p i
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, permReindex_apply]
  have hpermα : Measurable (permReindex (α := α) τ) := measurable_reindex τ
  have hpermβ : Measurable (permReindex (α := β) τ) := measurable_reindex τ
  rw [Measure.map_map hpermα hG, hcomp, ← Measure.map_map hG (measurable_id.prodMap hpermβ),
    ← Measure.map_prod_map π ρ measurable_id hpermβ, Measure.map_id, hρ.map_permReindex τ]

/-- Path-law exchangeability is equivalently measure preservation by every time permutation. -/
theorem exchangeableLaw_iff_forall_measurePreserving_permReindex {ρ : Measure (ℕ → α)} :
    ExchangeableLaw ρ ↔
      ∀ π : Equiv.Perm ℕ, MeasurePreserving (permReindex (α := α) π) ρ ρ := by
  constructor
  · intro hρ π
    exact hρ.measurePreserving_permReindex π
  · intro hρ π
    exact (hρ π).map_eq

/-- The first-`n` prefix marginal of a path-space measure reindexed by `φ : ℕ → ℕ` is its
finite coordinate marginal along `i ↦ φ i`. This only uses coordinate reindexing, so it holds
for an arbitrary function `φ`, not just a permutation. -/
theorem map_reindex_prefixProj (ρ : Measure (ℕ → α)) (φ : ℕ → ℕ) (n : ℕ) :
    (ρ.map (fun x : ℕ → α => fun k => x (φ k))).map (prefixProj α n) =
      ρ.map (fun x : ℕ → α => fun i : Fin n => x (φ i.val)) := by
  rw [Measure.map_map (measurable_prefixProj n) (measurable_reindex φ)]
  rfl

/-- The finite marginal of an exchangeable path law along any injective selection
`k : Fin n → ℕ` equals its first-`n` prefix marginal: an exchangeable law has the same
finite-dimensional distribution along every injective finite selection of coordinates. -/
theorem ExchangeableLaw.map_prefixProj_of_injective {ρ : Measure (ℕ → α)}
    (hρ : ExchangeableLaw ρ) {n : ℕ} (k : Fin n → ℕ) (hk : Function.Injective k) :
    ρ.map (fun x : ℕ → α => fun i : Fin n => x (k i)) =
      ρ.map (prefixProj α n) := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin n => i.val) k
    Fin.val_injective hk
  have hidx :
      (fun x : ℕ → α => fun i : Fin n => x (π i.val)) =
        fun x : ℕ → α => fun i : Fin n => x (k i) := by
    funext x i
    rw [hπ i]
  have hperm : (permReindex (α := α) π) = (fun x : ℕ → α => fun k => x (π k)) := by
    funext x k
    rw [permReindex_apply]
  calc
    ρ.map (fun x : ℕ → α => fun i : Fin n => x (k i))
        = ρ.map (fun x : ℕ → α => fun i : Fin n => x (π i.val)) := by rw [← hidx]
    _ = (ρ.map (permReindex (α := α) π)).map (prefixProj α n) := by
          rw [hperm, map_reindex_prefixProj]
    _ = ρ.map (prefixProj α n) := by rw [hρ.map_permReindex π]

/-- The prefix marginal of an exchangeable path law is invariant under permutations of the
finite prefix, the special case of `ExchangeableLaw.map_prefixProj_of_injective` along the
injective selection `i ↦ (σ i).val`. -/
theorem ExchangeableLaw.map_prefixProj_perm {ρ : Measure (ℕ → α)} (hρ : ExchangeableLaw ρ)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ρ.map (fun x : ℕ → α => fun i : Fin n => x (σ i).val) =
      ρ.map (prefixProj α n) :=
  hρ.map_prefixProj_of_injective (fun i : Fin n => (σ i).val)
    (fun _ _ h => σ.injective (Fin.val_injective h))

end Probability

end TauCeti
