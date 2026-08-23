/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.Theorem
public import TauCeti.Probability.Exchangeability.Family
public import TauCeti.Probability.Exchangeability.FullyExchangeable
public import TauCeti.Probability.Exchangeability.IID
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Exchangeable arrays

A doubly indexed array `X : ℕ × ℕ → Ω → α` carries two symmetry notions, and they are genuinely
different:

* `SeparatelyExchangeable μ X` — the law of the array is unchanged when the two axes are permuted
  **independently**, by `(i, j) ↦ (σ i, τ j)`;
* `JointlyExchangeable μ X` — the law is unchanged when the **same** permutation is applied to both
  axes, by `(i, j) ↦ (σ i, σ j)`.

Separate exchangeability is the stronger notion (`SeparatelyExchangeable.jointlyExchangeable`).
Joint exchangeability is the one to ask of a *symmetric* array `X (i, j) = X (j, i)`, such as the
adjacency array of an exchangeable random graph. Symmetry is a pathwise condition and by itself
gives no invariance of the law; the point is rather that a joint reindexing `(i, j) ↦ (σ i, σ j)`
carries a symmetric array to a symmetric array, whereas permuting the rows alone does not, so joint
exchangeability is the invariance a symmetric array can consistently be asked to have.

The main theorem here is the first step of the standard route to the Aldous–Hoover representation:
the **rows of a separately exchangeable array form an exchangeable sequence of random paths**
(`SeparatelyExchangeable.fullyExchangeable_arrayRow`), so de Finetti's theorem applies to them and
makes them conditionally i.i.d. (`SeparatelyExchangeable.conditionallyIID_arrayRow`). The value
space of that sequence is path space `ℕ → α`, which is standard Borel whenever `α` is, so no new
hypothesis is needed beyond the ones de Finetti already asks of `α`.

## Main definitions

* `TauCeti.Probability.pairReindex` — the two-axis analogue of `permReindex`, reindexing an
  array-shaped path by a permutation of each axis.
* `TauCeti.Probability.SeparatelyExchangeable`, `TauCeti.Probability.JointlyExchangeable` — the two
  array symmetries.
* `TauCeti.Probability.arrayRow`, `TauCeti.Probability.arrayCol`,
  `TauCeti.Probability.arrayDiag` — the rows and columns of an array, as random elements of path
  space, and its diagonal, as a process.

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.jointlyExchangeable` — the implication between the
  two symmetries.
* `TauCeti.Probability.separatelyExchangeable_iff_axes` — separate exchangeability splits into
  invariance under row permutations and invariance under column permutations.
* `TauCeti.Probability.SeparatelyExchangeable.fullyExchangeable_arrayRow` and
  `TauCeti.Probability.SeparatelyExchangeable.fullyExchangeable_arrayCol` — the rows, and the
  columns, of a separately exchangeable array form fully exchangeable sequences of paths.
* `TauCeti.Probability.SeparatelyExchangeable.conditionallyIID_arrayRow` — **de Finetti for the
  rows**: over a nonempty standard Borel state space, the rows of a separately exchangeable array
  are conditionally i.i.d.
* `TauCeti.Probability.JointlyExchangeable.fullyExchangeable_arrayDiag` — the diagonal of a jointly
  exchangeable array is a fully exchangeable sequence.
* `TauCeti.Probability.ExchangeableFamily.separatelyExchangeable` and
  `TauCeti.Probability.separatelyExchangeable_of_iIndepFun_identDistrib` — the sources: an
  exchangeable family indexed by `ℕ × ℕ`, in particular an i.i.d. array, is separately
  exchangeable.
* `TauCeti.Probability.jointlyExchangeable_diagIndicatorArray` and
  `TauCeti.Probability.not_separatelyExchangeable_diagIndicatorArray` — the implication between the
  two symmetries is strict, witnessed by the deterministic diagonal-indicator array, whose rows are
  not exchangeable.

## Implementation notes

The two predicates are stated at the level of the whole array law, matching `FullyExchangeable`
rather than the finite-dimensional `Exchangeable`, and quantify over arbitrary permutations of `ℕ`.
This is the formulation that makes the row and column statements pushforwards of one array law
(`map_map_array`), and it is the one Kallenberg uses for infinite arrays. Every symmetry
consequence below is an instance of `SeparatelyExchangeable.map_comp` or
`JointlyExchangeable.map_comp` with a different measurable read-off `F` of the array's sample path.

The a.e.-measurability hypothesis `∀ p, AEMeasurable (X p) μ` is what turns a law identity for the
array into a law identity for a read-off; the definitions themselves are hypothesis-free.

This is the entry point of the Layer 8 target "exchangeable arrays and the Aldous–Hoover
representation" in `TauCetiRoadmap/Exchangeability/README.md`. The next law-level consequence of
the row and column decompositions is in `Arrays.MixingLaw`: the law of either directing measure is
invariant when every path coordinate is permuted. This is deliberately weaker than saying that the
directing measure is almost surely an exchangeable law, which is false in general.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* D. Aldous, *Representations for partially exchangeable arrays of random variables*, Journal of
  Multivariate Analysis 11 (1981), 581–598.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*}

/-! ## Reindexing the two axes -/

/-- Reindex an array-shaped path by a permutation of each axis: the `(i, j)`-entry of
`pairReindex σ τ x` is `x (σ i, τ j)`. This is the two-axis analogue of `permReindex`. -/
def pairReindex (σ τ : Equiv.Perm ℕ) (x : ℕ × ℕ → α) : ℕ × ℕ → α :=
  fun p => x (σ p.1, τ p.2)

@[simp]
theorem pairReindex_apply (σ τ : Equiv.Perm ℕ) (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    pairReindex σ τ x p = x (σ p.1, τ p.2) :=
  (rfl)

/-- Reindexing both axes twice composes the corresponding permutations on each axis. -/
@[simp]
theorem pairReindex_comp (σ₁ τ₁ σ₂ τ₂ : Equiv.Perm ℕ) :
    pairReindex (α := α) σ₁ τ₁ ∘ pairReindex σ₂ τ₂ =
      pairReindex (σ₂ * σ₁) (τ₂ * τ₁) :=
  (rfl)

/-- Reindexing both axes by the identity permutation leaves an array unchanged. -/
@[simp]
theorem pairReindex_one_one : pairReindex (α := α) 1 1 = id := by
  funext x p
  rfl

/-! ## Rows, columns and the diagonal -/

/-- The `i`-th row of an array, as a random element of path space. -/
def arrayRow (X : ℕ × ℕ → Ω → α) (i : ℕ) : Ω → (ℕ → α) :=
  fun ω j => X (i, j) ω

/-- The `j`-th column of an array, as a random element of path space. -/
def arrayCol (X : ℕ × ℕ → Ω → α) (j : ℕ) : Ω → (ℕ → α) :=
  fun ω i => X (i, j) ω

/-- The diagonal of an array, as a process. -/
def arrayDiag (X : ℕ × ℕ → Ω → α) (i : ℕ) : Ω → α :=
  X (i, i)

@[simp]
theorem arrayRow_apply (X : ℕ × ℕ → Ω → α) (i : ℕ) (ω : Ω) (j : ℕ) :
    arrayRow X i ω j = X (i, j) ω :=
  (rfl)

@[simp]
theorem arrayCol_apply (X : ℕ × ℕ → Ω → α) (j : ℕ) (ω : Ω) (i : ℕ) :
    arrayCol X j ω i = X (i, j) ω :=
  (rfl)

@[simp]
theorem arrayDiag_apply (X : ℕ × ℕ → Ω → α) (i : ℕ) : arrayDiag X i = X (i, i) :=
  (rfl)

variable [MeasurableSpace α] [MeasurableSpace Ω]

@[fun_prop]
theorem measurable_pairReindex (σ τ : Equiv.Perm ℕ) :
    Measurable (pairReindex (α := α) σ τ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem aemeasurable_arrayRow {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hX : ∀ p, AEMeasurable (X p) μ) (i : ℕ) : AEMeasurable (arrayRow X i) μ :=
  aemeasurable_pi_lambda _ fun j => hX (i, j)

theorem aemeasurable_arrayCol {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hX : ∀ p, AEMeasurable (X p) μ) (j : ℕ) : AEMeasurable (arrayCol X j) μ :=
  aemeasurable_pi_lambda _ fun i => hX (i, j)

/-! ## The two array symmetries -/

/-- **Separate exchangeability.** The law of the array `X` is unchanged when its two axes are
permuted independently. -/
def SeparatelyExchangeable (μ : Measure Ω) (X : ℕ × ℕ → Ω → α) : Prop :=
  ∀ σ τ : Equiv.Perm ℕ, (μ.map fun ω p => X (σ p.1, τ p.2) ω) = μ.map fun ω p => X p ω

/-- **Joint exchangeability.** The law of the array `X` is unchanged when one and the same
permutation is applied to both of its axes.

This, rather than separate exchangeability, is the hypothesis one puts on a *symmetric* array
`X (i, j) = X (j, i)`: reindexing both axes by the same permutation preserves pathwise symmetry,
while permuting the rows alone destroys it. Symmetry alone is not an exchangeability assumption —
it constrains the sample path, not the law. -/
def JointlyExchangeable (μ : Measure Ω) (X : ℕ × ℕ → Ω → α) : Prop :=
  ∀ σ : Equiv.Perm ℕ, (μ.map fun ω p => X (σ p.1, σ p.2) ω) = μ.map fun ω p => X p ω

/-- **The invariance law defining separate exchangeability**, as a restatement: the array law is
unchanged along every pair of axis permutations. This is the simp normal form of the predicate, and
serves as both its introduction and its elimination rule. -/
@[simp]
theorem separatelyExchangeable_iff {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} :
    SeparatelyExchangeable μ X ↔
      ∀ σ τ : Equiv.Perm ℕ, (μ.map fun ω p => X (σ p.1, τ p.2) ω) = μ.map fun ω p => X p ω :=
  (Iff.rfl)

/-- **The invariance law defining joint exchangeability**, as a restatement: the array law is
unchanged along every diagonal pair of axis permutations. This is the simp normal form of the
predicate, and serves as both its introduction and its elimination rule. -/
@[simp]
theorem jointlyExchangeable_iff {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} :
    JointlyExchangeable μ X ↔
      ∀ σ : Equiv.Perm ℕ, (μ.map fun ω p => X (σ p.1, σ p.2) ω) = μ.map fun ω p => X p ω :=
  (Iff.rfl)

/-- **Separate exchangeability implies joint exchangeability**: permuting both axes by the same
permutation is the special case `τ = σ`. -/
theorem SeparatelyExchangeable.jointlyExchangeable {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) : JointlyExchangeable μ X :=
  fun σ => h σ σ

/-! ## Reading off the array law -/

/-- Reading a measurable function `F` off the sample path of an array turns the law of the array
into a pushforward. Every symmetry consequence below is this lemma with a different `F`: currying
for the rows, currying after a swap for the columns, restriction to the diagonal, evaluation at a
single entry. -/
theorem map_map_array {β : Type*} [MeasurableSpace β] {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hX : ∀ p, AEMeasurable (X p) μ) {F : (ℕ × ℕ → α) → β} (hF : Measurable F) :
    (μ.map fun ω p => X p ω).map F = μ.map fun ω => F fun p => X p ω :=
  AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (aemeasurable_pi_lambda _ hX)

/-- Separate exchangeability, transported to any measurable read-off `F` of the array's sample
path. -/
theorem SeparatelyExchangeable.map_comp {β : Type*} [MeasurableSpace β] {μ : Measure Ω}
    {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) (σ τ : Equiv.Perm ℕ)
    {F : (ℕ × ℕ → α) → β} (hF : Measurable F) :
    (μ.map fun ω => F fun p => X (σ p.1, τ p.2) ω) = μ.map fun ω => F fun p => X p ω := by
  rw [← map_map_array (X := fun p => X (σ p.1, τ p.2)) (fun p => hX _) hF,
    ← map_map_array hX hF, h σ τ]

/-- Joint exchangeability, transported to any measurable read-off `F` of the array's sample
path. -/
theorem JointlyExchangeable.map_comp {β : Type*} [MeasurableSpace β] {μ : Measure Ω}
    {X : ℕ × ℕ → Ω → α}
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) (σ : Equiv.Perm ℕ)
    {F : (ℕ × ℕ → α) → β} (hF : Measurable F) :
    (μ.map fun ω => F fun p => X (σ p.1, σ p.2) ω) = μ.map fun ω => F fun p => X p ω := by
  rw [← map_map_array (X := fun p => X (σ p.1, σ p.2)) (fun p => hX _) hF,
    ← map_map_array hX hF, h σ]

/-! ## Splitting separate exchangeability into its two axes -/

/-- **Separate exchangeability splits into its two axes**: it is the conjunction of invariance
under a permutation of the rows and invariance under a permutation of the columns. The forward
direction is the two specializations `τ = 1` and `σ = 1`; the converse composes the two
pushforwards, which is where measurability of the coordinates is used. -/
theorem separatelyExchangeable_iff_axes {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hX : ∀ p, AEMeasurable (X p) μ) :
    SeparatelyExchangeable μ X ↔
      (∀ σ : Equiv.Perm ℕ, (μ.map fun ω p => X (σ p.1, p.2) ω) = μ.map fun ω p => X p ω) ∧
        ∀ τ : Equiv.Perm ℕ, (μ.map fun ω p => X (p.1, τ p.2) ω) = μ.map fun ω p => X p ω := by
  constructor
  · exact fun h => ⟨fun σ => h σ 1, fun τ => h 1 τ⟩
  · rintro ⟨hrow, hcol⟩ σ τ
    have hrow' : (μ.map fun ω p => X p ω).map (pairReindex σ 1) = μ.map fun ω p => X p ω :=
      (map_map_array hX (measurable_pairReindex (α := α) σ 1)).trans (hrow σ)
    have hcol' : (μ.map fun ω p => X p ω).map (pairReindex 1 τ) = μ.map fun ω p => X p ω :=
      (map_map_array hX (measurable_pairReindex (α := α) 1 τ)).trans (hcol τ)
    calc (μ.map fun ω p => X (σ p.1, τ p.2) ω)
        = (μ.map fun ω p => X p ω).map (pairReindex σ τ) :=
          (map_map_array hX (measurable_pairReindex σ τ)).symm
      _ = ((μ.map fun ω p => X p ω).map (pairReindex 1 τ)).map (pairReindex σ 1) := by
          rw [Measure.map_map (measurable_pairReindex σ 1) (measurable_pairReindex 1 τ),
            pairReindex_comp]
          simp only [one_mul, mul_one]
      _ = (μ.map fun ω p => X p ω).map (pairReindex σ 1) := by rw [hcol']
      _ = μ.map fun ω p => X p ω := hrow'

/-! ## Rows and columns of a separately exchangeable array -/

/-- **The rows of a separately exchangeable array form a fully exchangeable sequence** of random
paths: permuting the rows is the case `τ = 1` of separate exchangeability, read off by currying. -/
theorem SeparatelyExchangeable.fullyExchangeable_arrayRow {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    FullyExchangeable μ (arrayRow X) := fun σ =>
  h.map_comp hX σ 1 (MeasurableEquiv.curry ℕ ℕ α).measurable

/-- **The rows of a separately exchangeable array form an exchangeable sequence** of random
paths. -/
theorem SeparatelyExchangeable.exchangeable_arrayRow {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    Exchangeable μ (arrayRow X) :=
  FullyExchangeable.exchangeable (h.fullyExchangeable_arrayRow hX) (aemeasurable_arrayRow hX)

/-- **The columns of a separately exchangeable array form a fully exchangeable sequence** of random
paths. -/
theorem SeparatelyExchangeable.fullyExchangeable_arrayCol {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    FullyExchangeable μ (arrayCol X) := fun τ =>
  h.map_comp hX 1 τ (F := fun x j i => x (i, j))
    (measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _)

/-- **The columns of a separately exchangeable array form an exchangeable sequence** of random
paths. -/
theorem SeparatelyExchangeable.exchangeable_arrayCol {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    Exchangeable μ (arrayCol X) :=
  FullyExchangeable.exchangeable (h.fullyExchangeable_arrayCol hX) (aemeasurable_arrayCol hX)

/-- **Each single row of a separately exchangeable array is a fully exchangeable sequence.** This
is the column half of the symmetry, read off at one row index. -/
theorem SeparatelyExchangeable.fullyExchangeable_row {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) (i : ℕ) :
    FullyExchangeable μ fun j => X (i, j) := fun τ =>
  h.map_comp hX 1 τ (F := fun x j => x (i, j)) (measurable_pi_lambda _ fun _ =>
    measurable_pi_apply _)

/-- **Each single column of a separately exchangeable array is a fully exchangeable sequence.** -/
theorem SeparatelyExchangeable.fullyExchangeable_col {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) (j : ℕ) :
    FullyExchangeable μ fun i => X (i, j) := fun σ =>
  h.map_comp hX σ 1 (F := fun x i => x (i, j)) (measurable_pi_lambda _ fun _ =>
    measurable_pi_apply _)

/-- **The entries of a separately exchangeable array are identically distributed.** -/
theorem SeparatelyExchangeable.map_entry_eq {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) (p : ℕ × ℕ) :
    μ.map (X p) = μ.map (X (0, 0)) := by
  have := h.map_comp hX (Equiv.swap 0 p.1) (Equiv.swap 0 p.2)
    (F := fun x => x (0, 0)) (measurable_pi_apply _)
  simpa using this

/-! ## The diagonal of a jointly exchangeable array -/

/-- **The diagonal of a jointly exchangeable array is a fully exchangeable sequence.** Separate
exchangeability is not needed: joint exchangeability alone already constrains the diagonal, which
is what makes it a useful hypothesis on a jointly exchangeable symmetric array. -/
theorem JointlyExchangeable.fullyExchangeable_arrayDiag {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    FullyExchangeable μ (arrayDiag X) := fun σ =>
  h.map_comp hX σ (F := fun x i => x (i, i)) (measurable_pi_lambda _ fun _ =>
    measurable_pi_apply _)

/-- **The diagonal of a jointly exchangeable array is an exchangeable sequence.** -/
theorem JointlyExchangeable.exchangeable_arrayDiag {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : JointlyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    Exchangeable μ (arrayDiag X) :=
  FullyExchangeable.exchangeable (h.fullyExchangeable_arrayDiag hX) fun i => hX (i, i)

/-! ## De Finetti for the rows -/

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

/-! ## The two symmetries are distinct -/

/-- The deterministic diagonal-indicator array over a sample space `S`: its `(i, j)` entry is
`true` exactly when `i = j`. Under every measure it is jointly exchangeable, but under a
probability measure it is not separately exchangeable. -/
def diagIndicatorArray (S : Type*) : ℕ × ℕ → S → Bool :=
  fun p _ => decide (p.1 = p.2)

/-- The entries of the diagonal-indicator array: constant in the sample point, and `true` exactly
on the diagonal. -/
@[simp]
theorem diagIndicatorArray_apply (S : Type*) (p : ℕ × ℕ) (s : S) :
    diagIndicatorArray S p s = decide (p.1 = p.2) :=
  (rfl)

/-- The diagonal-indicator array is jointly exchangeable: permuting both axes by one injective map
leaves the array itself, not merely its law, unchanged. -/
theorem jointlyExchangeable_diagIndicatorArray (μ : Measure Ω) :
    JointlyExchangeable μ (diagIndicatorArray Ω) := fun σ =>
  congrArg μ.map (funext fun _ => funext fun _ => by simp [diagIndicatorArray])

/-- The rows of the diagonal-indicator array are **not** exchangeable: they are the distinct
deterministic paths `j ↦ decide (i = j)`, so permuting them moves the point mass. -/
theorem not_fullyExchangeable_arrayRow_diagIndicatorArray (μ : Measure Ω)
    [IsProbabilityMeasure μ] : ¬FullyExchangeable μ (arrayRow (diagIndicatorArray Ω)) := by
  intro h
  have key : (μ.map fun _ : Ω => (fun i j => decide (Equiv.swap 0 1 i = j) : ℕ → ℕ → Bool))
      = μ.map fun _ : Ω => (fun i j => decide (i = j) : ℕ → ℕ → Bool) := h (Equiv.swap 0 1)
  rw [Measure.map_const, Measure.map_const, measure_univ, one_smul, one_smul] at key
  refine dirac_ne_dirac (fun hEq => ?_) key
  simpa using congrFun (congrFun hEq 0) 0

/-- **Joint exchangeability is strictly weaker than separate exchangeability.** The
diagonal-indicator array is jointly exchangeable, but not separately so: separate exchangeability
would make its rows exchangeable, and they are not. -/
theorem not_separatelyExchangeable_diagIndicatorArray (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ¬SeparatelyExchangeable μ (diagIndicatorArray Ω) := fun h =>
  not_fullyExchangeable_arrayRow_diagIndicatorArray μ
    (h.fullyExchangeable_arrayRow fun _ => measurable_const.aemeasurable)

/-! ## Sources of separately exchangeable arrays -/

/-- **An exchangeable family indexed by `ℕ × ℕ` is a separately exchangeable array.** The converse
fails: `ExchangeableFamily` also constrains selections that no pair of axis permutations
realizes, such as the one sending `(0, 0), (0, 1)` to `(0, 0), (1, 1)`. -/
theorem ExchangeableFamily.separatelyExchangeable {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ × ℕ → Ω → α} (h : ExchangeableFamily μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    SeparatelyExchangeable μ X := fun σ τ =>
  h.map_eq_of_injective hX (e := fun p => (σ p.1, τ p.2)) (f := id)
    (fun _ _ hpq => Prod.ext (σ.injective (congrArg Prod.fst hpq))
      (τ.injective (congrArg Prod.snd hpq)))
    Function.injective_id

/-- **An i.i.d. array is separately exchangeable.** The non-vacuous base case of the definition:
independence gives a product block law, and identical distribution makes that product blind to any
reindexing of the two axes. -/
theorem separatelyExchangeable_of_iIndepFun_identDistrib {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hindep : iIndepFun X μ) (hident : ∀ p, IdentDistrib (X p) (X (0, 0)) μ μ) :
    SeparatelyExchangeable μ X := by
  have := hindep.isProbabilityMeasure
  exact (MixedIID.of_iIndepFun_identDistrib_at (0, 0) hindep hident).exchangeableFamily
    |>.separatelyExchangeable fun p => (hident p).aemeasurable_fst

/-- **An i.i.d. array is jointly exchangeable.** -/
theorem jointlyExchangeable_of_iIndepFun_identDistrib {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hindep : iIndepFun X μ) (hident : ∀ p, IdentDistrib (X p) (X (0, 0)) μ μ) :
    JointlyExchangeable μ X :=
  (separatelyExchangeable_of_iIndepFun_identDistrib hindep hident).jointlyExchangeable

end Probability

end TauCeti
