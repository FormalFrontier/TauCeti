/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Gluing a countable chain of transport plans

This file turns a sequence of probability measures on consecutive products
`X n × X (n + 1)`, with matching adjacent marginals, into a probability measure on the path
space `∀ n, X n`. Its projection to every consecutive pair is the prescribed measure.

The construction uses Mathlib's Ionescu--Tulcea trajectory measure. At step `n`, the conditional
kernel of the prescribed `(n, n + 1)`-plan is pulled back along evaluation at the last point of the
current finite trajectory. The main result is `TauCeti.Measure.map_adjacent_chainMeasure`.

The finite-prefix results project this path law to any initial segment of the supplied countable
chain; see `TauCeti.Measure.map_adjacent_prefixChainMeasure`. This is the iteration of the two-plan
gluing lemma needed by optimal transport, without rebuilding Mathlib's trajectory-measure
construction.
-/

public section

open Finset MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Measure

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

section Chain

variable [∀ n, StandardBorelSpace (X (n + 1))] [∀ n, Nonempty (X (n + 1))]

/-- The transition kernel associated to a chain of consecutive plans. It disintegrates the
`n`th plan over its first coordinate and depends on a finite trajectory only through its last
coordinate. -/
private noncomputable def chainKernel (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] (n : ℕ) :
    Kernel ((i : Iic n) → X i) (X (n + 1)) :=
  (pi n).condKernel.comap
    (fun x : (i : Iic n) → X i ↦ x ⟨n, mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply (X := fun i : Iic n ↦ X i) ⟨n, mem_Iic.mpr le_rfl⟩)

private instance chainKernel.instIsMarkovKernel (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsFiniteMeasure (pi n)] (n : ℕ) : IsMarkovKernel (chainKernel pi n) := by
  rw [chainKernel]
  infer_instance

/-- The path law obtained by disintegrating and iterating a countable chain of consecutive
probability plans. -/
noncomputable def chainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsProbabilityMeasure (pi n)] : Measure ((n : ℕ) → X n) :=
  Kernel.trajMeasure (pi 0).fst (chainKernel pi)

instance chainMeasure.instIsProbabilityMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsProbabilityMeasure (pi n)] :
    IsProbabilityMeasure (chainMeasure pi) := by
  rw [chainMeasure]
  infer_instance

private theorem map_zero_chainMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsProbabilityMeasure (pi n)] :
    (chainMeasure pi).map (fun x ↦ x 0) = (pi 0).fst := by
  let e : ((i : Iic 0) → X i) ≃ᵐ X 0 := MeasurableEquiv.piUnique _
  have heval : (fun x : (n : ℕ) → X n ↦ x 0) = e ∘ frestrictLe 0 := by
    funext x
    rfl
  have hprefix : (chainMeasure pi).map (frestrictLe 0) = (pi 0).fst.map e.symm := by
    rw [chainMeasure, Kernel.trajMeasure, MeasureTheory.Measure.map_comp,
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, MeasureTheory.Measure.id_comp]
    · rfl
    · exact measurable_frestrictLe 0
  calc
    (chainMeasure pi).map (fun x ↦ x 0)
        = ((chainMeasure pi).map (frestrictLe 0)).map e := by
            rw [heval]
            exact (MeasureTheory.Measure.map_map e.measurable (measurable_frestrictLe 0)).symm
    _ = ((pi 0).fst.map e.symm).map e := by rw [hprefix]
    _ = (pi 0).fst := MeasurableEquiv.map_map_symm e

private theorem map_adjacent_chainMeasure_of_map_eval
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsProbabilityMeasure (pi n)] (n : ℕ)
    (hn : (chainMeasure pi).map (fun x ↦ x n) = (pi n).fst) :
    (chainMeasure pi).map (fun x ↦ (x n, x (n + 1))) = pi n := by
  let last : ((i : Iic n) → X i) → X n := fun x ↦ x ⟨n, mem_Iic.mpr le_rfl⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hpair : (fun x : (k : ℕ) → X k ↦ (x n, x (n + 1))) =
      Prod.map last id ∘ (fun x ↦ (frestrictLe n x, x (n + 1))) := by
    funext x
    rfl
  rw [hpair, ← MeasureTheory.Measure.map_map (hlast.prodMap measurable_id) (by fun_prop),
    chainMeasure, ← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    chainKernel, map_prodMap_compProd_comap,
    MeasureTheory.Measure.map_map hlast (measurable_frestrictLe n)]
  have heval : last ∘ frestrictLe n = fun x : (k : ℕ) → X k ↦ x n := rfl
  rw [heval, ← chainMeasure, hn, MeasureTheory.Measure.disintegrate]

/-- Every time marginal of `chainMeasure pi` is the first marginal of the corresponding
consecutive plan, provided neighboring plans have matching marginals. -/
theorem map_eval_chainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsProbabilityMeasure (pi n)]
    (hpi : ∀ n, (pi n).snd = (pi (n + 1)).fst) (n : ℕ) :
    (chainMeasure pi).map (fun x ↦ x n) = (pi n).fst := by
  induction n with
  | zero => exact map_zero_chainMeasure pi
  | succ n hn =>
      have hp := map_adjacent_chainMeasure_of_map_eval pi n hn
      calc
        (chainMeasure pi).map (fun x ↦ x (n + 1))
            = ((chainMeasure pi).map (fun x ↦ (x n, x (n + 1)))).snd := by
                rw [MeasureTheory.Measure.snd, MeasureTheory.Measure.map_map]
                · rfl
                · exact measurable_snd
                · fun_prop
        _ = (pi n).snd := by rw [hp]
        _ = (pi (n + 1)).fst := hpi n

/-- **Countable chain gluing.** The consecutive-coordinate projection of `chainMeasure pi` is the
prescribed plan `pi n` at every time `n`. -/
theorem map_adjacent_chainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsProbabilityMeasure (pi n)]
    (hpi : ∀ n, (pi n).snd = (pi (n + 1)).fst) (n : ℕ) :
    (chainMeasure pi).map (fun x ↦ (x n, x (n + 1))) = pi n :=
  map_adjacent_chainMeasure_of_map_eval pi n (map_eval_chainMeasure pi hpi n)

/-- The finite trajectory law obtained by projecting `chainMeasure pi` to coordinates at most
`N`. -/
noncomputable def prefixChainMeasure (pi : ∀ n, Measure (X n × X (n + 1)))
    [∀ n, IsProbabilityMeasure (pi n)] (N : ℕ) : Measure ((i : Iic N) → X i) :=
  (chainMeasure pi).map (frestrictLe N)

instance prefixChainMeasure.instIsProbabilityMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsProbabilityMeasure (pi n)] (N : ℕ) :
    IsProbabilityMeasure (prefixChainMeasure pi N) := by
  rw [prefixChainMeasure]
  exact Measure.isProbabilityMeasure_map (measurable_frestrictLe N).aemeasurable

/-- Projecting a finite prefix further gives the corresponding shorter prefix. -/
theorem map_frestrictLe₂_prefixChainMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsProbabilityMeasure (pi n)]
    {M N : ℕ} (hMN : M ≤ N) :
    (prefixChainMeasure pi N).map (frestrictLe₂ hMN) = prefixChainMeasure pi M := by
  rw [prefixChainMeasure, MeasureTheory.Measure.map_map (measurable_frestrictLe₂ hMN)
    (measurable_frestrictLe N), frestrictLe₂_comp_frestrictLe]
  rfl

/-- Every adjacent projection of a finite prefix of the countable path law agrees with the
prescribed plan, as long as both coordinates occur in the prefix. -/
theorem map_adjacent_prefixChainMeasure
    (pi : ∀ n, Measure (X n × X (n + 1))) [∀ n, IsProbabilityMeasure (pi n)]
    (hpi : ∀ n, (pi n).snd = (pi (n + 1)).fst) {n N : ℕ} (hn : n < N) :
    (prefixChainMeasure pi N).map
        (fun x ↦ (x ⟨n, mem_Iic.mpr (Nat.le_of_lt hn)⟩, x ⟨n + 1, mem_Iic.mpr hn⟩)) = pi n := by
  let adjacent : ((i : Iic N) → X i) → X n × X (n + 1) :=
    fun x ↦ (x ⟨n, mem_Iic.mpr (Nat.le_of_lt hn)⟩, x ⟨n + 1, mem_Iic.mpr hn⟩)
  have hadjacent : Measurable adjacent := by fun_prop
  calc
    (prefixChainMeasure pi N).map adjacent
        = (chainMeasure pi).map (adjacent ∘ frestrictLe N) := by
            rw [prefixChainMeasure, MeasureTheory.Measure.map_map hadjacent
              (measurable_frestrictLe N)]
    _ = (chainMeasure pi).map (fun x ↦ (x n, x (n + 1))) := by
          congr 1
    _ = pi n := map_adjacent_chainMeasure pi hpi n

end Chain

end Measure

end TauCeti
