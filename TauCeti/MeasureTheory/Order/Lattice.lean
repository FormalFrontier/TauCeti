/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability of finite lattice extrema

Mathlib proves `Finset.measurable_sup'`; these are its three siblings — the finite infimum, and
the almost-everywhere-measurable versions of both — each by the corresponding `Finset` induction
with the binary closure lemma at the step.
-/

public section

namespace TauCeti

open MeasureTheory

variable {ι α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ] {μ : Measure δ}
  {s : Finset ι} {f : ι → δ → α}

/-- The infimum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem Finset.measurable_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.inf' hs f) :=
  Finset.inf'_induction hs _ (fun _f hf _g hg => hf.inf hg) fun n hn => hf n hn

/-- The supremum of a nonempty finite family of a.e.-measurable functions is a.e. measurable. -/
@[fun_prop]
theorem Finset.aemeasurable_sup' [SemilatticeSup α] [MeasurableSup₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.sup' hs f) μ :=
  Finset.sup'_induction (p := fun g : δ → α => AEMeasurable g μ) hs f (fun _ h₁ _ h₂ => h₁.sup h₂)
    fun n hn => hf n hn

/-- The infimum of a nonempty finite family of a.e.-measurable functions is a.e. measurable. -/
@[fun_prop]
theorem Finset.aemeasurable_inf' [SemilatticeInf α] [MeasurableInf₂ α] (hs : s.Nonempty)
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.inf' hs f) μ :=
  Finset.inf'_induction (p := fun g : δ → α => AEMeasurable g μ) hs f (fun _ h₁ _ h₂ => h₁.inf h₂)
    fun n hn => hf n hn

end TauCeti
