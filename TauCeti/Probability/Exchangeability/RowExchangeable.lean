/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.Theorem
public import TauCeti.Probability.Exchangeability.FullyExchangeable
-- Non-public: evaluating a random probability measure at a fixed measurable set is measurable.
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Ext

/-!
# Row exchangeable arrays and the factorization of their directing measure

An array `Y : ι × ℕ → Ω → α` is **row exchangeable** when its law is unchanged by permuting the
entries of each row separately: for every family `π : ι → Equiv.Perm ℕ` of time permutations, one
for each row, the array `(a, k) ↦ Y (a, π a k)` has the law of `Y`. This is the symmetry of the
array of successors of a Markov exchangeable process, and it is stronger than asking that each row
be exchangeable on its own, because the permutations may be chosen independently.

Reading an array column by column gives the process `arrayColumn Y : ℕ → Ω → (ι → α)`, whose
`k`-th value is the vector of the `k`-th entries of all rows. Row exchangeability contains the
diagonal case `π = fun _ => σ`, so `arrayColumn Y` is a fully exchangeable process valued in
`ι → α`, which for countable `ι` and standard Borel `α` is again standard Borel. De Finetti's
theorem therefore hands the columns a directing measure `λ : Ω → ProbabilityMeasure (ι → α)`.

The theorem of this file is that the extra, off-diagonal part of the symmetry makes that directing
measure **factor over the rows**: almost surely, its mass on a finite box
`{x | ∀ a ∈ F, x a ∈ B a}` is the product over `a ∈ F` of its one-row masses. So conditionally on
the directing measure the rows are not merely identically distributed but independent, which is the
mixture-of-independent-i.i.d.-rows form that the Diaconis–Freedman representation of Markov
exchangeable processes consumes.

## Main definitions

* `TauCeti.Probability.RowExchangeable`: invariance of the array law under independent
  permutations of the individual rows;
* `TauCeti.Probability.arrayColumn`: the array read as a process of columns.

## Main results

* `TauCeti.Probability.RowExchangeable.fullyExchangeable_row` and
  `TauCeti.Probability.RowExchangeable.fullyExchangeable_arrayColumn`: each row, and the column
  process, is fully exchangeable;
* `TauCeti.Probability.RowExchangeable.map_values`: closure under coordinatewise pushforward;
* `TauCeti.Probability.RowExchangeable.measure_setOf_forall_pair_eq`: the combinatorial core —
  the probability that each row of a finite set lands in its own target set at two prescribed
  times does not depend on which two times are prescribed;
* `TauCeti.Probability.RowExchangeable.ae_apply_pi_union`: the directing measure of the column
  process is almost surely multiplicative across disjoint sets of rows;
* `TauCeti.Probability.RowExchangeable.ae_apply_pi_eq_prod` and
  `TauCeti.Probability.RowExchangeable.exists_directing_pi_eq_prod`: the resulting product formula
  over a finite set of rows, at a given witness and at the witness de Finetti supplies.

## Implementation

The multiplicativity is proved by a second-moment argument that never leaves the world of finite
blocks. Write `C` and `D` for the boxes cut out by two disjoint finite sets of rows. The mixture
identity turns each of

```text
∫ λ(C ∩ D)²,      ∫ λ(C ∩ D) · λ(C) · λ(D),      ∫ λ(C)² · λ(D)²
```

into the probability of an array event in which **every** row involved is tested at exactly two
times — times that differ from term to term. Row exchangeability moves those times back to `0` and
`1` one row at a time, so the three integrals coincide, and the integral of
`(λ(C ∩ D) - λ(C) · λ(D))²` vanishes.

Only the mixture identity `MixedIIDWith` is used, not the joint-law disintegration: the argument
tests the directing measure against nothing but block probabilities, so the factorization theorem
needs no standard Borel structure at all. That hypothesis enters exactly once, in the de Finetti
wrapper at the end, which is what produces a witness in the first place. Countability of the row
index is present throughout, since it is what makes an array with a.e. measurable entries an a.e.
measurable map into `ι × ℕ → α`.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable sequences
rather than arrays.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Countable ι]

/-- The array `Y` read as a process of columns: the `k`-th column is the vector of the `k`-th
entries of all rows. -/
def arrayColumn (Y : ι × ℕ → Ω → α) (k : ℕ) (ω : Ω) : ι → α :=
  fun a => Y (a, k) ω

-- The parentheses in `(rfl)` opt out of the exported-theorem exposure check, so that this, the
-- complete computational API of `arrayColumn`, can be stated without exposing its body.
omit [MeasurableSpace Ω] [MeasurableSpace α] [Countable ι] in
@[simp]
theorem arrayColumn_apply (Y : ι × ℕ → Ω → α) (k : ℕ) (ω : Ω) (a : ι) :
    arrayColumn Y k ω a = Y (a, k) ω :=
  (rfl)

/-- **Row exchangeability.** The law of the array is invariant under permuting the entries of each
row by a permutation of time chosen separately for that row.

Taking one and the same permutation in every row recovers the exchangeability of the columns; the
content beyond that is that the rows may be shuffled against one another. -/
def RowExchangeable (μ : Measure Ω) (Y : ι × ℕ → Ω → α) : Prop :=
  ∀ π : ι → Equiv.Perm ℕ,
    (μ.map fun ω (p : ι × ℕ) => Y (p.1, π p.1 p.2) ω) = μ.map fun ω (p : ι × ℕ) => Y p ω

variable {μ : Measure Ω} {Y : ι × ℕ → Ω → α}

omit [Countable ι] in
/-- Characterization of row exchangeability by invariance under every family of row-wise time
permutations. -/
theorem RowExchangeable_def :
    RowExchangeable μ Y ↔ ∀ π : ι → Equiv.Perm ℕ,
      (μ.map fun ω (p : ι × ℕ) => Y (p.1, π p.1 p.2) ω) =
        μ.map fun ω (p : ι × ℕ) => Y p ω :=
  Iff.rfl

/-- Every column of an array with a.e. measurable entries is a.e. measurable. -/
theorem aemeasurable_arrayColumn (hY : ∀ p, AEMeasurable (Y p) μ) (k : ℕ) :
    AEMeasurable (arrayColumn Y k) μ :=
  aemeasurable_pi_lambda _ fun a => hY (a, k)

/-- **Each row of a row exchangeable array is fully exchangeable.** -/
theorem RowExchangeable.fullyExchangeable_row (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) (a : ι) :
    FullyExchangeable μ fun k => Y (a, k) := by
  classical
  intro σ
  set π : ι → Equiv.Perm ℕ := fun b => if b = a then σ else 1 with hπ
  have hrow : Measurable fun y : ι × ℕ → α => fun k => y (a, k) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (a, k)
  have hmap := congrArg (fun ρ : Measure (ι × ℕ → α) => ρ.map fun y => fun k => y (a, k))
    (RowExchangeable_def.mp h π)
  rw [AEMeasurable.map_map_of_aemeasurable hrow.aemeasurable
      (aemeasurable_pi_lambda _ fun p => hY (p.1, π p.1 p.2)),
    AEMeasurable.map_map_of_aemeasurable hrow.aemeasurable
      (aemeasurable_pi_lambda _ fun p => hY p)] at hmap
  have hπa : π a = σ := by simp [hπ]
  simpa [Function.comp_def, pathLaw, hπa] using hmap

/-- **The column process of a row exchangeable array is fully exchangeable.** This is the diagonal
case `π = fun _ => σ` of the definition. -/
theorem RowExchangeable.fullyExchangeable_arrayColumn (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) :
    FullyExchangeable μ (arrayColumn Y) := by
  intro σ
  have hcol : Measurable fun y : ι × ℕ → α => fun (k : ℕ) (a : ι) => y (a, k) :=
    measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun a => measurable_pi_apply (a, k)
  have hmap := congrArg
    (fun ρ : Measure (ι × ℕ → α) =>
      ρ.map fun y => fun (k : ℕ) (a : ι) => y (a, k))
    (RowExchangeable_def.mp h fun _ => σ)
  rw [AEMeasurable.map_map_of_aemeasurable hcol.aemeasurable
      (aemeasurable_pi_lambda _ fun p => hY (p.1, σ p.2)),
    AEMeasurable.map_map_of_aemeasurable hcol.aemeasurable
      (aemeasurable_pi_lambda _ fun p => hY p)] at hmap
  have hleft : (fun ω (i : ℕ) => arrayColumn Y (σ i) ω) =
      fun (x : Ω) (k : ℕ) (a : ι) => Y (a, σ k) x := by
    funext ω k a
    rw [arrayColumn_apply]
  have hright : (fun ω (i : ℕ) => arrayColumn Y i ω) =
      fun (x : Ω) (k : ℕ) (a : ι) => Y (a, k) x := by
    funext ω k a
    rw [arrayColumn_apply]
  rw [pathLaw, hleft, hright]
  simpa [Function.comp_def] using hmap

/-- **Row exchangeability is closed under coordinatewise pushforward.** Applying one measurable map
to every entry of a row exchangeable array leaves it row exchangeable. -/
theorem RowExchangeable.map_values {β : Type*} [MeasurableSpace β] (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) {f : α → β} (hf : Measurable f) :
    RowExchangeable μ fun p ω => f (Y p ω) := by
  rw [RowExchangeable_def] at h ⊢
  intro π
  have hpush : Measurable fun y : ι × ℕ → α => fun p : ι × ℕ => f (y p) :=
    measurable_pi_lambda _ fun p => hf.comp (measurable_pi_apply p)
  have hmap := congrArg
    (fun ρ : Measure (ι × ℕ → α) => ρ.map fun y => fun p : ι × ℕ => f (y p)) (h π)
  rw [AEMeasurable.map_map_of_aemeasurable hpush.aemeasurable
      (aemeasurable_pi_lambda _ fun p => hY (p.1, π p.1 p.2)),
    AEMeasurable.map_map_of_aemeasurable hpush.aemeasurable
      (aemeasurable_pi_lambda _ fun p => hY p)] at hmap
  simpa [Function.comp_def] using hmap

/-- **The exchangeability of the columns.** -/
theorem RowExchangeable.exchangeable_arrayColumn (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) :
    Exchangeable μ (arrayColumn Y) :=
  FullyExchangeable.exchangeable (h.fullyExchangeable_arrayColumn hY)
    (aemeasurable_arrayColumn hY)

section TwoTimes

omit [Countable ι] in
private theorem measurableSet_pairEventPath (F : Finset ι) {B : ι → Set α}
    (hB : ∀ a ∈ F, MeasurableSet (B a)) (c d : ι → ℕ) :
    MeasurableSet {y : ι × ℕ → α | ∀ a ∈ F, y (a, c a) ∈ B a ∧ y (a, d a) ∈ B a} := by
  have : {y : ι × ℕ → α | ∀ a ∈ F, y (a, c a) ∈ B a ∧ y (a, d a) ∈ B a} =
      ⋂ a ∈ F, ((fun y : ι × ℕ → α => y (a, c a)) ⁻¹' B a ∩
        (fun y : ι × ℕ → α => y (a, d a)) ⁻¹' B a) := by
    ext y; simp [Set.mem_iInter]
  rw [this]
  exact MeasurableSet.biInter F.countable_toSet fun a _ =>
    ((measurable_pi_apply _) (hB a ‹a ∈ F›)).inter
      ((measurable_pi_apply _) (hB a ‹a ∈ F›))

/-- **The two-time pattern lemma.** Under row exchangeability the probability that every row of a
finite set lands in its own target set at two prescribed times is the same for all choices of the
two times, so long as the two times chosen in each row of that set are distinct.

This is the whole combinatorial input to the factorization theorem: each moment of the directing
measure computes such a probability, with a different time pattern. -/
theorem RowExchangeable.measure_setOf_forall_pair_eq (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) (F : Finset ι) {B : ι → Set α}
    (hB : ∀ a ∈ F, MeasurableSet (B a)) {c d : ι → ℕ} (hcd : ∀ a ∈ F, c a ≠ d a) :
    μ {ω | ∀ a ∈ F, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} =
      μ {ω | ∀ a ∈ F, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a} := by
  classical
  -- A permutation of time in row `a` carrying `0` to `c a` and `1` to `d a`. Only the rows of `F`
  -- are constrained, so rows outside `F` — where `c` and `d` may agree — take the identity.
  have hexists : ∀ a : ι, ∃ σ : Equiv.Perm ℕ, a ∈ F → σ 0 = c a ∧ σ 1 = d a := by
    intro a
    by_cases ha : a ∈ F
    · have h01 : Function.Injective (![0, 1] : Fin 2 → ℕ) := by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
      have hcd' : Function.Injective (![c a, d a] : Fin 2 → ℕ) := by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [hcd a ha, (hcd a ha).symm]
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ h01 hcd'
      exact ⟨σ, fun _ => ⟨by simpa using hσ 0, by simpa using hσ 1⟩⟩
    · exact ⟨1, fun ha' => absurd ha' ha⟩
  choose π hπ using hexists
  set A : Set (ι × ℕ → α) := {y : ι × ℕ → α | ∀ a ∈ F, y (a, 0) ∈ B a ∧ y (a, 1) ∈ B a} with hA
  have hAmeas : MeasurableSet A := measurableSet_pairEventPath F hB _ _
  have hLHS : (μ.map fun ω (p : ι × ℕ) => Y (p.1, π p.1 p.2) ω) A =
      μ {ω | ∀ a ∈ F, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} := by
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_pi_lambda _ fun p => hY (p.1, π p.1 p.2)) hAmeas]
    congr 1
    ext ω
    simp only [hA, Set.mem_preimage, Set.mem_ofPred_eq]
    refine forall_congr' fun a => forall_congr' fun ha => ?_
    rw [(hπ a ha).1, (hπ a ha).2]
  have hRHS : (μ.map fun ω (p : ι × ℕ) => Y p ω) A =
      μ {ω | ∀ a ∈ F, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a} := by
    rw [Measure.map_apply_of_aemeasurable (aemeasurable_pi_lambda _ fun p => hY p) hAmeas]
    rfl
  rw [← hLHS, ← hRHS, RowExchangeable_def.mp h π]

end TwoTimes

private theorem RowExchangeable.measure_setOf_two_blocks_eq (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) {F G : Finset ι} (hFG : Disjoint F G) {B : ι → Set α}
    (hB : ∀ a, a ∈ F ∨ a ∈ G → MeasurableSet (B a)) {m n m' n' : ℕ} (hmn : m ≠ n)
    (hmn' : m' ≠ n') :
    μ {ω | (∀ a ∈ F, Y (a, m) ω ∈ B a ∧ Y (a, n) ω ∈ B a) ∧
        ∀ a ∈ G, Y (a, m') ω ∈ B a ∧ Y (a, n') ω ∈ B a} =
      μ {ω | (∀ a ∈ F, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a) ∧
        ∀ a ∈ G, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a} := by
  classical
  -- Split a box over `F ∪ G` into its two halves; no disjointness is needed for that.
  have hsplit : ∀ c d : ι → ℕ,
      {ω | ∀ a ∈ F ∪ G, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} =
        {ω | (∀ a ∈ F, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a) ∧
          ∀ a ∈ G, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} := by
    intro c d
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.mem_union]
    exact ⟨fun hall => ⟨fun a ha => hall a (Or.inl ha), fun a ha => hall a (Or.inr ha)⟩,
      fun hall a ha => ha.elim (hall.1 a) (hall.2 a)⟩
  -- The two time patterns, glued from the two blocks.
  set c : ι → ℕ := fun a => if a ∈ F then m else m' with hc
  set d : ι → ℕ := fun a => if a ∈ F then n else n' with hd
  have hcd : ∀ a, c a ≠ d a := by
    intro a
    by_cases ha : a ∈ F <;> simp [hc, hd, ha, hmn, hmn']
  have hglue : {ω | (∀ a ∈ F, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a) ∧
      ∀ a ∈ G, Y (a, c a) ω ∈ B a ∧ Y (a, d a) ω ∈ B a} =
        {ω | (∀ a ∈ F, Y (a, m) ω ∈ B a ∧ Y (a, n) ω ∈ B a) ∧
          ∀ a ∈ G, Y (a, m') ω ∈ B a ∧ Y (a, n') ω ∈ B a} := by
    ext ω
    have hFval : ∀ a ∈ F, c a = m ∧ d a = n := fun a ha => by simp [hc, hd, ha]
    have hGval : ∀ a ∈ G, c a = m' ∧ d a = n' := fun a ha => by
      have : a ∉ F := Finset.disjoint_right.mp hFG ha
      simp [hc, hd, this]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · rw [← (hFval a ha).1, ← (hFval a ha).2]; exact h1 a ha
      · rw [← (hGval a ha).1, ← (hGval a ha).2]; exact h2 a ha
    · rintro ⟨h1, h2⟩
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · rw [(hFval a ha).1, (hFval a ha).2]; exact h1 a ha
      · rw [(hGval a ha).1, (hGval a ha).2]; exact h2 a ha
  rw [← hglue, ← hsplit c d, ← hsplit (fun _ => 0) (fun _ => 1),
    h.measure_setOf_forall_pair_eq hY (F ∪ G) (fun a ha => hB a (Finset.mem_union.mp ha))
      fun a _ => hcd a]

section Factorization

variable {lam : Ω → ProbabilityMeasure (ι → α)}

/-- **Multiplicativity of the directing measure across disjoint sets of rows.** If the columns of a
row exchangeable array are mixed i.i.d. with mixing representative `lam`, then almost surely `lam`
gives the box over `F ∪ G` the product of the masses of its two halves.

The proof is the second-moment computation described in the module docstring: the three integrals
that make up the mean square of the difference are, by the two-block pattern lemma, one and the
same array probability. -/
theorem RowExchangeable.ae_apply_pi_union [IsFiniteMeasure μ] (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) (hlam : MixedIIDWith μ (arrayColumn Y) lam)
    {F G : Finset ι} (hFG : Disjoint F G) {B : ι → Set α}
    (hB : ∀ a, a ∈ F ∨ a ∈ G → MeasurableSet (B a)) :
    ∀ᵐ ω ∂μ, (lam ω : Measure (ι → α)) (Set.pi (↑F ∪ ↑G) B) =
      (lam ω : Measure (ι → α)) (Set.pi (↑F) B) * (lam ω : Measure (ι → α)) (Set.pi (↑G) B) := by
  classical
  set C : Set (ι → α) := Set.pi (↑F) B with hC
  set D : Set (ι → α) := Set.pi (↑G) B with hD
  have hCm : MeasurableSet C := MeasurableSet.pi F.countable_toSet fun a ha =>
    hB a (Or.inl ha)
  have hDm : MeasurableSet D := MeasurableSet.pi G.countable_toSet fun a ha =>
    hB a (Or.inr ha)
  have hCDm : MeasurableSet (C ∩ D) := hCm.inter hDm
  have hunion : Set.pi (↑F ∪ ↑G) B = C ∩ D := Set.union_pi
  simp only [hunion]
  have hZ := aemeasurable_arrayColumn (μ := μ) hY
  have hmem : ∀ (H : Finset ι) (k : ℕ) (ω : Ω),
      arrayColumn Y k ω ∈ Set.pi (↑H : Set ι) B ↔ ∀ a ∈ H, Y (a, k) ω ∈ B a := by
    intro H k ω; simp [Set.mem_pi]
  -- Every mixed moment of `lam` on these boxes is the probability of an array event.
  have hblock : ∀ {r : ℕ} (k : Fin r → ℕ), Function.Injective k → ∀ E : Fin r → Set (ι → α),
      (∀ j, MeasurableSet (E j)) →
        ∫⁻ ω, ∏ j, (lam ω : Measure (ι → α)) (E j) ∂μ =
          μ {ω | ∀ j, arrayColumn Y (k j) ω ∈ E j} := by
    intro r k hk E hE
    rw [← hlam.blockLaw_univ_pi k hk E hE,
      blockLaw_apply_rectangle μ (arrayColumn Y) k (fun j => hZ (k j)) E hE]
  set T : ℝ≥0∞ := μ {ω | (∀ a ∈ F, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a) ∧
    ∀ a ∈ G, Y (a, 0) ω ∈ B a ∧ Y (a, 1) ω ∈ B a} with hT
  have hinj2 : Function.Injective (![0, 1] : Fin 2 → ℕ) := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hinj3 : Function.Injective (![0, 1, 2] : Fin 3 → ℕ) := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hinj4 : Function.Injective (![0, 1, 2, 3] : Fin 4 → ℕ) := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  -- First pattern: the whole box twice, read at times `0` and `1`.
  have hT1 : ∫⁻ ω, (lam ω : Measure (ι → α)) (C ∩ D) *
      (lam ω : Measure (ι → α)) (C ∩ D) ∂μ = T := by
    have key := hblock ![0, 1] hinj2 ![C ∩ D, C ∩ D] (fun j => by fin_cases j <;> exact hCDm)
    have hprod : ∀ ω : Ω, (lam ω : Measure (ι → α)) (C ∩ D) * (lam ω : Measure (ι → α)) (C ∩ D) =
          ∏ j : Fin 2, (lam ω : Measure (ι → α)) (![C ∩ D, C ∩ D] j) := by
      intro ω; simp [Fin.prod_univ_two]
    simp_rw [hprod]
    rw [key, hT]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_inter_iff, hC, hD, hmem]
    exact ⟨fun ⟨⟨hF0, hG0⟩, hF1, hG1⟩ =>
        ⟨fun a ha => ⟨hF0 a ha, hF1 a ha⟩, fun a ha => ⟨hG0 a ha, hG1 a ha⟩⟩,
      fun ⟨hF, hG⟩ => ⟨⟨fun a ha => (hF a ha).1, fun a ha => (hG a ha).1⟩,
        fun a ha => (hF a ha).2, fun a ha => (hG a ha).2⟩⟩
  -- Second pattern: the whole box and then each half, at times `0, 1` in `F` and `0, 2` in `G`.
  have hT2 : ∫⁻ ω, (lam ω : Measure (ι → α)) (C ∩ D) * (lam ω : Measure (ι → α)) C *
      (lam ω : Measure (ι → α)) D ∂μ = T := by
    have key := hblock ![0, 1, 2] hinj3 ![C ∩ D, C, D]
      (fun j => by fin_cases j <;> [exact hCDm; exact hCm; exact hDm])
    have hprod : ∀ ω : Ω, (lam ω : Measure (ι → α)) (C ∩ D) * (lam ω : Measure (ι → α)) C *
        (lam ω : Measure (ι → α)) D =
          ∏ j : Fin 3, (lam ω : Measure (ι → α)) (![C ∩ D, C, D] j) := by
      intro ω; simp [Fin.prod_univ_three]
    simp_rw [hprod]
    rw [key, hT, ← h.measure_setOf_two_blocks_eq hY hFG hB (m := 0) (n := 1) (m' := 0) (n' := 2)
      (by norm_num) (by norm_num)]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hall
      have e0 : arrayColumn Y 0 ω ∈ C ∩ D := hall 0
      have e1 : arrayColumn Y 1 ω ∈ C := hall 1
      have e2 : arrayColumn Y 2 ω ∈ D := hall 2
      exact ⟨fun a ha => ⟨e0.1 a ha, e1 a ha⟩, fun a ha => ⟨e0.2 a ha, e2 a ha⟩⟩
    · rintro ⟨hF, hG⟩ j
      -- `fin_cases` and simplification compute the finite-vector lookup; `hC` and `hD` expose
      -- the boxes, after which membership reduces definitionally to their coordinate conditions.
      fin_cases j
      · simp only [hC, hD]
        exact ⟨fun a ha => (hF a ha).1, fun a ha => (hG a ha).1⟩
      · simp only [hC]
        exact fun a ha => (hF a ha).2
      · simp only [hD]
        exact fun a ha => (hG a ha).2
  -- Third pattern: each half twice, at times `0, 1` in `F` and `2, 3` in `G`.
  have hT3 : ∫⁻ ω, (lam ω : Measure (ι → α)) C * (lam ω : Measure (ι → α)) C *
      (lam ω : Measure (ι → α)) D * (lam ω : Measure (ι → α)) D ∂μ = T := by
    have key := hblock ![0, 1, 2, 3] hinj4 ![C, C, D, D]
      (fun j => by fin_cases j <;> [exact hCm; exact hCm; exact hDm; exact hDm])
    have hprod : ∀ ω : Ω, (lam ω : Measure (ι → α)) C * (lam ω : Measure (ι → α)) C *
        (lam ω : Measure (ι → α)) D * (lam ω : Measure (ι → α)) D =
          ∏ j : Fin 4, (lam ω : Measure (ι → α)) (![C, C, D, D] j) := by
      intro ω; simp [Fin.prod_univ_four]
    simp_rw [hprod]
    rw [key, hT, ← h.measure_setOf_two_blocks_eq hY hFG hB (m := 0) (n := 1) (m' := 2) (n' := 3)
      (by norm_num) (by norm_num)]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hall
      have e0 : arrayColumn Y 0 ω ∈ C := hall 0
      have e1 : arrayColumn Y 1 ω ∈ C := hall 1
      have e2 : arrayColumn Y 2 ω ∈ D := hall 2
      have e3 : arrayColumn Y 3 ω ∈ D := hall 3
      exact ⟨fun a ha => ⟨e0 a ha, e1 a ha⟩, fun a ha => ⟨e2 a ha, e3 a ha⟩⟩
    · rintro ⟨hF, hG⟩ j
      -- As above, each branch computes the vector index and uses the named box equalities before
      -- reducing box membership to coordinate conditions.
      fin_cases j
      · simp only [hC]
        exact fun a ha => (hF a ha).1
      · simp only [hC]
        exact fun a ha => (hF a ha).2
      · simp only [hD]
        exact fun a ha => (hG a ha).1
      · simp only [hD]
        exact fun a ha => (hG a ha).2
  -- The mean square of the difference is `T - 2T + T = 0`.
  have hlam_meas := hlam.measurable_mixingRepresentative
  have hprob : ∀ (ω : Ω) (S : Set (ι → α)), (lam ω : Measure (ι → α)) S ≤ 1 := fun _ _ =>
    prob_le_one
  have hne : ∀ (ω : Ω) (S : Set (ι → α)), (lam ω : Measure (ι → α)) S ≠ ⊤ := fun ω S =>
    ((hprob ω S).trans_lt ENNReal.one_lt_top).ne
  have hle1 : ∀ (ω : Ω) (S : Set (ι → α)), ((lam ω : Measure (ι → α)) S).toReal ≤ 1 := by
    intro ω S
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hprob ω S)
  have hmC : Measurable fun ω => (lam ω : Measure (ι → α)) C :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hCm).comp hlam_meas
  have hmD : Measurable fun ω => (lam ω : Measure (ι → α)) D :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hDm).comp hlam_meas
  have hmCD : Measurable fun ω => (lam ω : Measure (ι → α)) (C ∩ D) :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_toMeasure_apply hCDm).comp hlam_meas
  set f : Ω → ℝ := fun ω => ((lam ω : Measure (ι → α)) (C ∩ D)).toReal with hf
  set g : Ω → ℝ := fun ω =>
    ((lam ω : Measure (ι → α)) C).toReal * ((lam ω : Measure (ι → α)) D).toReal with hg
  have hfm : Measurable f := ENNReal.measurable_toReal.comp hmCD
  have hgm : Measurable g :=
    (ENNReal.measurable_toReal.comp hmC).mul (ENNReal.measurable_toReal.comp hmD)
  have hmul1 : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |x * y| ≤ 1 := by
    intro x y hx hy
    rw [abs_mul]
    nlinarith [abs_nonneg x, abs_nonneg y]
  have hf1 : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [hf, abs_of_nonneg ENNReal.toReal_nonneg]; exact hle1 ω _
  have hg1 : ∀ ω, |g ω| ≤ 1 := fun ω => by
    rw [hg]
    exact hmul1 _ _ (by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact hle1 ω _)
      (by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact hle1 ω _)
  have hbdd : ∀ (c : ℝ) (φ : Ω → ℝ), Measurable φ → (∀ ω, |φ ω| ≤ c) → Integrable φ μ := by
    intro c φ hφ hb
    exact (integrable_const c).mono' hφ.aestronglyMeasurable
      (.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb ω)
  have htoReal : ∀ u : Ω → ℝ≥0∞, Measurable u → (∀ ω, u ω ≠ ⊤) →
      ∫ ω, (u ω).toReal ∂μ = (∫⁻ ω, u ω ∂μ).toReal := fun u hu hu' =>
    integral_toReal hu.aemeasurable (.of_forall fun ω => (hu' ω).lt_top)
  have hI1 : ∫ ω, f ω * f ω ∂μ = T.toReal := by
    have hrw : (fun ω => f ω * f ω) = fun ω =>
        ((lam ω : Measure (ι → α)) (C ∩ D) * (lam ω : Measure (ι → α)) (C ∩ D)).toReal := by
      funext ω; rw [ENNReal.toReal_mul]
    rw [hrw, htoReal (fun ω => (lam ω : Measure (ι → α)) (C ∩ D) *
      (lam ω : Measure (ι → α)) (C ∩ D)) (hmCD.mul hmCD)
      (fun ω => ENNReal.mul_ne_top (hne ω _) (hne ω _)), hT1]
  have hI2 : ∫ ω, f ω * g ω ∂μ = T.toReal := by
    have hrw : (fun ω => f ω * g ω) = fun ω =>
        ((lam ω : Measure (ι → α)) (C ∩ D) * (lam ω : Measure (ι → α)) C *
          (lam ω : Measure (ι → α)) D).toReal := by
      funext ω; rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hf, hg, mul_assoc]
    rw [hrw, htoReal (fun ω => (lam ω : Measure (ι → α)) (C ∩ D) * (lam ω : Measure (ι → α)) C *
      (lam ω : Measure (ι → α)) D) ((hmCD.mul hmC).mul hmD)
      (fun ω => ENNReal.mul_ne_top (ENNReal.mul_ne_top (hne ω _) (hne ω _)) (hne ω _)), hT2]
  have hI3 : ∫ ω, g ω * g ω ∂μ = T.toReal := by
    have hrw : (fun ω => g ω * g ω) = fun ω =>
        ((lam ω : Measure (ι → α)) C * (lam ω : Measure (ι → α)) C *
          (lam ω : Measure (ι → α)) D * (lam ω : Measure (ι → α)) D).toReal := by
      funext ω
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, hg]
      ring
    rw [hrw, htoReal (fun ω => (lam ω : Measure (ι → α)) C * (lam ω : Measure (ι → α)) C *
      (lam ω : Measure (ι → α)) D * (lam ω : Measure (ι → α)) D)
      (((hmC.mul hmC).mul hmD).mul hmD)
      (fun ω => ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (hne ω _) (hne ω _)) (hne ω _)) (hne ω _)), hT3]
  have e1 : Integrable (fun ω => f ω * f ω) μ :=
    hbdd 1 _ (hfm.mul hfm) fun ω => hmul1 _ _ (hf1 ω) (hf1 ω)
  have e2 : Integrable (fun ω => f ω * g ω) μ :=
    hbdd 1 _ (hfm.mul hgm) fun ω => hmul1 _ _ (hf1 ω) (hg1 ω)
  have e3 : Integrable (fun ω => g ω * g ω) μ :=
    hbdd 1 _ (hgm.mul hgm) fun ω => hmul1 _ _ (hg1 ω) (hg1 ω)
  have hexp : (fun ω => (f ω - g ω) ^ 2)
      = fun ω => f ω * f ω - 2 * (f ω * g ω) + g ω * g ω := by funext ω; ring
  have e2' : Integrable (fun ω => 2 * (f ω * g ω)) μ := e2.const_mul 2
  have e12 : Integrable (fun ω => f ω * f ω - 2 * (f ω * g ω)) μ := e1.sub e2'
  have hsq : Integrable (fun ω => (f ω - g ω) ^ 2) μ := by
    rw [hexp]; exact e12.add e3
  have hzero : ∫ ω, (f ω - g ω) ^ 2 ∂μ = 0 := by
    rw [hexp, integral_add e12 e3, integral_sub e1 e2', integral_const_mul, hI1, hI2, hI3]
    ring
  have hae : (fun ω => (f ω - g ω) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hsq).mp hzero
  filter_upwards [hae] with ω hω
  have hfg : f ω = g ω := by
    have h0 : f ω - g ω = 0 := by
      have : (f ω - g ω) ^ 2 = 0 := hω
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    linarith
  rw [← ENNReal.toReal_eq_toReal_iff' (hne ω _) (ENNReal.mul_ne_top (hne ω _) (hne ω _)),
    ENNReal.toReal_mul]
  simpa [hf, hg] using hfg

/-- **The directing measure of a row exchangeable array factors over the rows.** For a finite set
`F` of rows and measurable target sets `B`, the mass that the mixing representative of the columns
gives to the box `{x | ∀ a ∈ F, x a ∈ B a}` is almost surely the product of the masses it gives to
the individual rows. -/
theorem RowExchangeable.ae_apply_pi_eq_prod [IsFiniteMeasure μ] (h : RowExchangeable μ Y)
    (hY : ∀ p, AEMeasurable (Y p) μ) (hlam : MixedIIDWith μ (arrayColumn Y) lam)
    {B : ι → Set α} (F : Finset ι) (hB : ∀ a ∈ F, MeasurableSet (B a)) :
    ∀ᵐ ω ∂μ, (lam ω : Measure (ι → α)) (Set.pi (↑F) B) =
      ∏ a ∈ F, (lam ω : Measure (ι → α)) {x : ι → α | x a ∈ B a} := by
  classical
  induction F using Finset.induction_on with
  | empty => filter_upwards with ω; simp
  | insert a s ha ih =>
      have hdisj : Disjoint ({a} : Finset ι) s := by simpa using ha
      have hcoe : ((↑(insert a s) : Set ι)) = (↑({a} : Finset ι) : Set ι) ∪ (↑s : Set ι) := by
        simp
      filter_upwards [h.ae_apply_pi_union (B := B) hY hlam hdisj
        (fun b hb => hB b (by
          simpa only [Finset.mem_singleton, Finset.mem_insert] using hb)),
        ih (fun b hb => hB b (Finset.mem_insert_of_mem hb))] with ω h1 h2
      rw [hcoe, h1, h2, Finset.prod_insert ha, Finset.coe_singleton, Set.singleton_pi']

/-- **De Finetti for a row exchangeable array.** Over a countable row index and a nonempty standard
Borel state space, the columns of a row exchangeable array are conditionally i.i.d., and their
directing measure almost surely factors over the rows: conditionally on it, the rows are
independent as well as identically distributed within each row. -/
theorem RowExchangeable.exists_directing_pi_eq_prod [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (h : RowExchangeable μ Y) (hY : ∀ p, AEMeasurable (Y p) μ) :
    ∃ lam : Ω → ProbabilityMeasure (ι → α), ConditionallyIIDWith μ (arrayColumn Y) lam ∧
      ∀ (B : ι → Set α) (F : Finset ι), (∀ a ∈ F, MeasurableSet (B a)) →
        ∀ᵐ ω ∂μ, (lam ω : Measure (ι → α)) (Set.pi (↑F) B) =
          ∏ a ∈ F, (lam ω : Measure (ι → α)) {x : ι → α | x a ∈ B a} := by
  obtain ⟨lam, hlam⟩ := ConditionallyIID.exists_directing
    (deFinetti (X := arrayColumn Y) (aemeasurable_arrayColumn hY) (h.exchangeable_arrayColumn hY))
  exact ⟨lam, hlam, fun B F hB =>
    h.ae_apply_pi_eq_prod hY (mixedIIDWith_of_conditionallyIIDWith hlam) F hB⟩

end Factorization

end Probability

end TauCeti

end

end
