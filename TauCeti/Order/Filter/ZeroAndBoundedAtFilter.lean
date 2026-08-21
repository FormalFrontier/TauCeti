/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Gaps in Mathlib's `ZeroAtFilter` / `BoundedAtFilter` API

Mathlib's `Filter.ZeroAtFilter` and `Filter.BoundedAtFilter` are closed under binary sums
(`Filter.ZeroAtFilter.add`, `Filter.BoundedAtFilter.add`), and the bounded functions are closed
under a `Finset.prod` (`Filter.BoundedAtFilter.prod`, via `boundedFilterSubalgebra`). The additive
counterpart of that product lemma is not recorded upstream; this file adds it for both predicates.

The gap shows up wherever an operator is a finite sum of slashes: proving that such an operator
stays bounded, or stays vanishing, along `atImInfty` is an induction over the summands, and
without these each call site reruns it.

Mathlib also has no rule for pushing a vanishing function through a map. `ZeroAtFilter` is
convergence to `0`, so only the behaviour of that map **at `0`** matters — global continuity is
not needed, and asking for it would exclude the topological modules that carry `ContinuousAdd`
rather than `IsTopologicalAddGroup`.

## Main results

* `Filter.ZeroAtFilter.sum`: a finite sum of functions vanishing along `l` vanishes along `l`.
* `Filter.BoundedAtFilter.sum`: a finite sum of functions bounded along `l` is bounded along `l`.
* `Filter.ZeroAtFilter.comp`: a function vanishing along `l`, composed with a zero-preserving map
  continuous at `0`, still vanishes along `l`.

## Provenance

No code is transcribed. The gap was identified while porting the cusp chain of the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0),
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`: its `heckeT_p_ut_zero_at_cusps` (lines 62-70)
open-codes precisely this induction with `Finset.sum_induction`, which is also the proof plan
`BoundedAtFilter.sum` follows below. The statements here are about Mathlib's
`Filter.ZeroAtFilter` / `Filter.BoundedAtFilter` at an arbitrary filter and index type, not about
modular forms.
-/

public section

open Finset

namespace Filter

variable {α β ι : Type*} {l : Filter α} {s : Finset ι} {f : ι → α → β}

/-- **A finite sum of functions vanishing along `l` vanishes along `l`.** The additive companion
of `Filter.BoundedAtFilter.prod`. The `AddCommMonoid` hypothesis is what `Finset.sum` requires. -/
theorem ZeroAtFilter.sum [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    (h : ∀ i ∈ s, ZeroAtFilter l (f i)) : ZeroAtFilter l (∑ i ∈ s, f i) :=
  sum_mem (S := zeroAtFilterAddSubmonoid l) h

/-- **A finite sum of functions bounded along `l` is bounded along `l`** — the additive companion
of `Filter.BoundedAtFilter.prod`. -/
theorem BoundedAtFilter.sum [SeminormedAddCommGroup β]
    (h : ∀ i ∈ s, BoundedAtFilter l (f i)) : BoundedAtFilter l (∑ i ∈ s, f i) :=
  Finset.sum_induction f (BoundedAtFilter l) (fun _ _ ↦ BoundedAtFilter.add)
    (const_boundedAtFilter l 0) h

/-- **A vanishing function stays vanishing under a zero-preserving map continuous at `0`.**

Only continuity **at `0`** is asked for. `ZeroAtFilter` is convergence to `0`, so nothing about
`φ` away from `0` is involved; requiring `Continuous φ` would be strictly stronger, and for a
linear map the two coincide only when the topology is translation-invariant. -/
theorem ZeroAtFilter.comp {γ : Type*} [Zero β] [TopologicalSpace β] [Zero γ] [TopologicalSpace γ]
    {g : α → β} {φ : β → γ} (hg : ZeroAtFilter l g) (hφ : ContinuousAt φ 0) (h0 : φ 0 = 0) :
    ZeroAtFilter l (φ ∘ g) := by
  have h := Filter.Tendsto.comp hφ hg
  rwa [h0] at h

end Filter

end
