/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block
public import TauCeti.Probability.Exchangeability.Arrays.MixingLaw
public import TauCeti.Probability.DeFinetti.Theorem

/-!
# De Finetti's theorem for exchangeable arrays

The consequences of de Finetti's theorem for the array symmetries: over a nonempty standard Borel
state space, the rows and columns of a separately exchangeable array are conditionally i.i.d., as
are the rows of a block of a jointly exchangeable one, and the directing measures produced this way
inherit the symmetry of the array.

**This is the array subtree's only direct import of the de Finetti summit.** `Arrays.Coding`
reaches `DeFinetti.Theorem` too, transitively through this module, which is as it should be: the
coding representation is a de Finetti consequence. What changed is that the dependency now arrives
through the one file whose subject it is.

`Arrays.Basic` carries the symmetry predicates and their elementary theory, `Arrays.Block` the
combinatorics of blocks, and `Arrays.MixingLaw` the results that hold of *any* supplied mixing
representative. Each of those is now independent of `DeFinetti.Theorem`, so a file needing only
array symmetry — for instance `Arrays.AldousHoover.Basic`, which uses four declarations from
`Arrays.Basic` — no longer depends on the representation theory at all.

The layering is therefore

```text
array symmetry  →  consequences of a supplied mixture  →  de Finetti supplies one  →  coding
```

## Main results

* `SeparatelyExchangeable.conditionallyIID_arrayRow` and `…_arrayCol` — de Finetti for the rows and
  columns;
* `JointlyExchangeable.conditionallyIID_arrayRow_arrayBlock` and `…_arrayBlockPair` — de Finetti
  for the rows of a block;
* `SeparatelyExchangeable.exists_directing_arrayRow_mixingLaw_invariant` and `…_arrayCol…` — a
  directing measure whose law inherits the array's symmetry.
-/

public section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {μ : Measure Ω}
  {X : ℕ × ℕ → Ω → α} {e f : ℕ → ℕ}

/-- **De Finetti's theorem for the rows of a separately exchangeable array.** Over a nonempty
standard Borel state space `α`, the rows of a separately exchangeable array are conditionally
i.i.d. as random elements of path space `ℕ → α`.

This is the first step of the standard route to the Aldous–Hoover representation. Path space is
standard Borel because `α` is (`StandardBorelSpace.pi_countable`), so the hypotheses are exactly
de Finetti's. -/
theorem SeparatelyExchangeable.conditionallyIID_arrayRow [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ConditionallyIID μ (arrayRow X) :=
  deFinetti (aemeasurable_arrayRow hX) (h.exchangeable_arrayRow hX)

/-- **De Finetti's theorem for the columns of a separately exchangeable array.** -/
theorem SeparatelyExchangeable.conditionallyIID_arrayCol [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ConditionallyIID μ (arrayCol X) :=
  deFinetti (aemeasurable_arrayCol hX) (h.exchangeable_arrayCol hX)


/-- **De Finetti's theorem for the rows of a block of a jointly exchangeable array.** Over a
nonempty standard Borel state space, the rows of a block along injections with disjoint ranges are
conditionally i.i.d. as random elements of path space. -/
theorem JointlyExchangeable.conditionallyIID_arrayRow_arrayBlock [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    ConditionallyIID μ (arrayRow (arrayBlock X e f)) :=
  (h.separatelyExchangeable_arrayBlock hX he hf hd).conditionallyIID_arrayRow
    (aemeasurable_arrayBlock hX)

/-- **De Finetti's theorem for the rows of a block of pairs.** The conclusion simultaneously
describes both orientations of the selected rectangular cross-block. -/
theorem JointlyExchangeable.conditionallyIID_arrayRow_arrayBlockPair [StandardBorelSpace α]
    [Nonempty α] [IsFiniteMeasure μ] (h : JointlyExchangeable μ X)
    (hX : ∀ p, AEMeasurable (X p) μ) (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    ConditionallyIID μ (arrayRow (arrayBlockPair X e f)) :=
  (h.separatelyExchangeable_arrayBlockPair hX he hf hd).conditionallyIID_arrayRow
    (aemeasurable_arrayBlockPair hX)


/-- **De Finetti for the rows, with the inherited mixing-law symmetry.** A separately
exchangeable array has a directing measure for its row process whose law is invariant under every
permutation of the path coordinates. -/
theorem SeparatelyExchangeable.exists_directing_arrayRow_mixingLaw_invariant
    [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ ν : Ω → ProbabilityMeasure (ℕ → α), ConditionallyIIDWith μ (arrayRow X) ν ∧
      ∀ τ : Equiv.Perm ℕ,
        μ.map (fun ω ↦ (ν ω).map (fun x : ℕ → α => fun k => x (τ k))) = μ.map ν := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayRow hX).exists_directing
  exact ⟨ν, hν, fun τ ↦
    h.mixingLaw_map_permReindex_arrayRow_eq (mixedIIDWith_of_conditionallyIIDWith hν) τ⟩

/-- **De Finetti for the columns, with the inherited mixing-law symmetry.** -/
theorem SeparatelyExchangeable.exists_directing_arrayCol_mixingLaw_invariant
    [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ ν : Ω → ProbabilityMeasure (ℕ → α), ConditionallyIIDWith μ (arrayCol X) ν ∧
      ∀ σ : Equiv.Perm ℕ,
        μ.map (fun ω ↦ (ν ω).map (fun x : ℕ → α => fun k => x (σ k))) = μ.map ν := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayCol hX).exists_directing
  exact ⟨ν, hν, fun σ ↦
    h.mixingLaw_map_permReindex_arrayCol_eq (mixedIIDWith_of_conditionallyIIDWith hν) σ⟩


end Probability

end TauCeti
