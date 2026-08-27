/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Block
public import TauCeti.Probability.Independence.DisjointBlocks
-- Non-public: the zero-one law for a self-independent event is used only inside a proof.
import Mathlib.Probability.Independence.ZeroOne

/-!
# Dissociated arrays

The Aldous--Hoover representation of an exchangeable array has an **ergodic form**, in which the
array is a fixed measurable function of one variable per row, one per column, and one per cell,
with no global variable; the general form is a mixture of these over the global variable. The class
of laws the ergodic form describes is singled out by *dissociation*: sub-arrays over disjoint sets
of rows **and** disjoint sets of columns are independent.

Two disjointness conditions are needed, one per axis, and this file therefore carries the two
notions the two array symmetries ask for:

* `SeparatelyDissociated μ X` — the blocks `X (i, j)`, `i ∈ A`, `j ∈ B`, and `X (i, j)`, `i ∈ A'`,
  `j ∈ B'`, are independent whenever `A ∩ A' = ∅` and `B ∩ B' = ∅`. This is the notion paired with
  `SeparatelyExchangeable`;
* `JointlyDissociated μ X` — the square blocks over `A × A` and `A' × A'` are independent whenever
  `A ∩ A' = ∅`. This is the notion paired with `JointlyExchangeable`, and it is genuinely weaker
  (`SeparatelyDissociated.jointlyDissociated`): a symmetric array is not separately dissociated
  unless its off-diagonal entries are trivial, since `X (i, j)` and `X (j, i)` are then equal while
  separate dissociation asks them to be independent; it may perfectly well be jointly dissociated.

Index sets are presented, as in `Arrays/Block.lean`, by index maps `e f : ℕ → ℕ`, so that the two
sub-arrays are the rectangular blocks `arrayBlock X e f` and `arrayBlock X e' f'` and the
disjointness conditions read `Disjoint (Set.range e) (Set.range e')` and
`Disjoint (Set.range f) (Set.range f')`. Ranges of maps `ℕ → ℕ` are exactly the nonempty sets of
indices, and a block over an empty set of indices carries no information, so nothing is lost.

Dissociation is a restriction on the array and not a consequence of any exchangeability: an array
all of whose entries are one common random variable is separately exchangeable, but dissociating it
forces that variable to be almost surely trivial
(`JointlyDissociated.measure_preimage_eq_zero_or_one_of_const`). Thus nontrivial randomness shared
unchanged by every entry is incompatible with dissociation; the ergodic Aldous--Hoover coding drops
the global noise coordinate entirely.

These results advance the exchangeable-arrays milestone of
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8. The dissociated codings themselves are in
`Arrays/AldousHoover.lean`.

## Main definitions

* `TauCeti.Probability.SeparatelyDissociated`;
* `TauCeti.Probability.JointlyDissociated`.

## Main results

* `TauCeti.Probability.SeparatelyDissociated.jointlyDissociated` — the implication between the two
  notions;
* `TauCeti.Probability.separatelyDissociated_of_iIndepFun` — an array of independent entries is
  separately dissociated;
* `TauCeti.Probability.SeparatelyDissociated.arrayBlock` and
  `TauCeti.Probability.JointlyDissociated.arrayBlock_diag` — dissociation passes to blocks along
  injective index maps;
* `TauCeti.Probability.SeparatelyDissociated.map_values` and
  `TauCeti.Probability.JointlyDissociated.map_values` — dissociation is preserved by a measurable
  coordinatewise pushforward;
* `TauCeti.Probability.SeparatelyDissociated.indepFun_apply` and
  `TauCeti.Probability.JointlyDissociated.indepFun_arrayDiag` — entries in different rows and
  different columns are independent, so in particular the diagonal entries of a jointly dissociated
  array are pairwise independent;
* `TauCeti.Probability.JointlyDissociated.measure_preimage_eq_zero_or_one_of_const` — a dissociated
  array with all entries equal has an almost surely trivial entry;
* `TauCeti.Probability.SeparatelyDissociated.measure_preimage_eq_zero_or_one_of_symm` — a symmetric
  array is separately dissociated only if it is trivial off the diagonal, which is the sharp form
  of the separation between the two notions.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable sequences
rather than exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}

/-- **Separate dissociation.** Two rectangular blocks of the array are independent whenever their
row index sets are disjoint and their column index sets are disjoint. The blocks are
`arrayBlock X e f` and `arrayBlock X e' f'`, read as random elements of array space. -/
def SeparatelyDissociated (μ : Measure Ω) (X : ℕ × ℕ → Ω → α) : Prop :=
  ∀ e f e' f' : ℕ → ℕ, Disjoint (Set.range e) (Set.range e') →
    Disjoint (Set.range f) (Set.range f') →
      IndepFun (fun ω (p : ℕ × ℕ) => X (e p.1, f p.2) ω)
        (fun ω (p : ℕ × ℕ) => X (e' p.1, f' p.2) ω) μ

/-- **Joint dissociation.** Two square blocks of the array, over disjoint sets of indices, are
independent. This is the notion a symmetric array can have: separate dissociation would ask
`X (i, j)` and `X (j, i)` to be independent, and a symmetric array has them equal, which forces
them to be trivial (`SeparatelyDissociated.measure_preimage_eq_zero_or_one_of_symm`). -/
def JointlyDissociated (μ : Measure Ω) (X : ℕ × ℕ → Ω → α) : Prop :=
  ∀ e e' : ℕ → ℕ, Disjoint (Set.range e) (Set.range e') →
    IndepFun (fun ω (p : ℕ × ℕ) => X (e p.1, e p.2) ω)
      (fun ω (p : ℕ × ℕ) => X (e' p.1, e' p.2) ω) μ

/-- **The independence law defining separate dissociation**, as a restatement: it is the simp
normal form of the predicate, and serves as both its introduction and its elimination rule. -/
@[simp]
theorem separatelyDissociated_iff :
    SeparatelyDissociated μ X ↔ ∀ e f e' f' : ℕ → ℕ, Disjoint (Set.range e) (Set.range e') →
      Disjoint (Set.range f) (Set.range f') →
        IndepFun (fun ω (p : ℕ × ℕ) => X (e p.1, f p.2) ω)
          (fun ω (p : ℕ × ℕ) => X (e' p.1, f' p.2) ω) μ :=
  (Iff.rfl)

/-- **The independence law defining joint dissociation**, as a restatement: it is the simp normal
form of the predicate, and serves as both its introduction and its elimination rule. -/
@[simp]
theorem jointlyDissociated_iff :
    JointlyDissociated μ X ↔ ∀ e e' : ℕ → ℕ, Disjoint (Set.range e) (Set.range e') →
      IndepFun (fun ω (p : ℕ × ℕ) => X (e p.1, e p.2) ω)
        (fun ω (p : ℕ × ℕ) => X (e' p.1, e' p.2) ω) μ :=
  (Iff.rfl)

/-- **Separate dissociation implies joint dissociation**: a square block is the rectangular block
with the two index maps equal. -/
theorem SeparatelyDissociated.jointlyDissociated (h : SeparatelyDissociated μ X) :
    JointlyDissociated μ X :=
  jointlyDissociated_iff.mpr fun e e' he => separatelyDissociated_iff.mp h e e e' e' he he

section Consequences

/-- Entries of a separately dissociated array in different rows **and** different columns are
independent. -/
theorem SeparatelyDissociated.indepFun_apply (h : SeparatelyDissociated μ X) {i j i' j' : ℕ}
    (hi : i ≠ i') (hj : j ≠ j') : IndepFun (X (i, j)) (X (i', j')) μ :=
  (separatelyDissociated_iff.mp h (fun _ => i) (fun _ => j) (fun _ => i') (fun _ => j')
    (by simpa using hi) (by simpa using hj)).comp
      (measurable_pi_apply (0, 0)) (measurable_pi_apply (0, 0))

/-- The diagonal entries of a jointly dissociated array are pairwise independent. -/
theorem JointlyDissociated.indepFun_arrayDiag (h : JointlyDissociated μ X) {i i' : ℕ}
    (hi : i ≠ i') : IndepFun (arrayDiag X i) (arrayDiag X i') μ := by
  rw [arrayDiag_apply, arrayDiag_apply]
  exact (jointlyDissociated_iff.mp h (fun _ => i) (fun _ => i') (by simpa using hi)).comp
    (measurable_pi_apply (0, 0)) (measurable_pi_apply (0, 0))

/-- A random variable independent of itself generates an almost surely trivial σ-algebra. -/
private theorem measure_preimage_eq_zero_or_one_of_indepFun_self [IsProbabilityMeasure μ]
    {Y : Ω → α} (hY : Measurable Y) (hindep : IndepFun Y Y μ) {s : Set α}
    (hs : MeasurableSet s) : μ (Y ⁻¹' s) = 0 ∨ μ (Y ⁻¹' s) = 1 :=
  ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self
    ((indepFun_iff_indepSet_preimage hY hY).mp hindep s s hs hs)

/-- **Dissociation makes a constant array trivial.** If every entry of a jointly dissociated array
is one and the same random variable `Y`, then `Y` generates an almost surely trivial σ-algebra.

In particular, the array `X (i, j) = U` built from global noise alone is separately exchangeable,
but dissociating it would make `U` degenerate. -/
theorem JointlyDissociated.measure_preimage_eq_zero_or_one_of_const [IsProbabilityMeasure μ]
    {Y : Ω → α} (hY : Measurable Y) (h : JointlyDissociated μ fun _ => Y) {s : Set α}
    (hs : MeasurableSet s) : μ (Y ⁻¹' s) = 0 ∨ μ (Y ⁻¹' s) = 1 :=
  measure_preimage_eq_zero_or_one_of_indepFun_self hY
    ((jointlyDissociated_iff.mp h (fun _ => 0) (fun _ => 1) (by simp)).comp
      (measurable_pi_apply (0, 0)) (measurable_pi_apply (0, 0))) hs

/-- **Equal transposed entries of a separately dissociated array are trivial off the diagonal.**
Separate dissociation asks `X (i, j)` and `X (j, i)` to be independent, so if those two entries
are equal, they are self-independent. This applies in particular to symmetric arrays. -/
theorem SeparatelyDissociated.measure_preimage_eq_zero_or_one_of_symm [IsProbabilityMeasure μ]
    (h : SeparatelyDissociated μ X) {i j : ℕ} (hij : i ≠ j)
    (hsymm : X (j, i) = X (i, j)) (hX : Measurable (X (i, j)))
    {s : Set α} (hs : MeasurableSet s) :
    μ (X (i, j) ⁻¹' s) = 0 ∨ μ (X (i, j) ⁻¹' s) = 1 := by
  have hindep := h.indepFun_apply hij hij.symm
  rw [hsymm] at hindep
  exact measure_preimage_eq_zero_or_one_of_indepFun_self hX hindep hs

end Consequences

section Stability

/-- Dissociation is preserved by a measurable coordinatewise pushforward of the entries. -/
theorem SeparatelyDissociated.map_values (h : SeparatelyDissociated μ X) {g : α → β}
    (hg : Measurable g) : SeparatelyDissociated μ fun p ω => g (X p ω) :=
  separatelyDissociated_iff.mpr fun e f e' f' he hf =>
    (separatelyDissociated_iff.mp h e f e' f' he hf).comp
      (measurable_pi_lambda _ fun p => hg.comp (measurable_pi_apply p))
      (measurable_pi_lambda _ fun p => hg.comp (measurable_pi_apply p))

/-- Joint dissociation is preserved by a measurable coordinatewise pushforward of the entries. -/
theorem JointlyDissociated.map_values (h : JointlyDissociated μ X) {g : α → β}
    (hg : Measurable g) : JointlyDissociated μ fun p ω => g (X p ω) :=
  jointlyDissociated_iff.mpr fun e e' he =>
    (jointlyDissociated_iff.mp h e e' he).comp
      (measurable_pi_lambda _ fun p => hg.comp (measurable_pi_apply p))
      (measurable_pi_lambda _ fun p => hg.comp (measurable_pi_apply p))

/-- **Dissociation passes to rectangular blocks** along injective index maps: a block of a block is
a block, and an injection carries disjoint index sets to disjoint index sets. -/
theorem SeparatelyDissociated.arrayBlock (h : SeparatelyDissociated μ X) {e f : ℕ → ℕ}
    (he : Function.Injective e) (hf : Function.Injective f) :
    SeparatelyDissociated μ (TauCeti.Probability.arrayBlock X e f) := by
  refine separatelyDissociated_iff.mpr fun e₁ f₁ e₂ f₂ h₁ h₂ => ?_
  simp only [arrayBlock_apply]
  refine separatelyDissociated_iff.mp h (e ∘ e₁) (f ∘ f₁) (e ∘ e₂) (f ∘ f₂) ?_ ?_
  · simpa only [Set.range_comp] using Set.disjoint_image_of_injective he h₁
  · simpa only [Set.range_comp] using Set.disjoint_image_of_injective hf h₂

/-- **Joint dissociation passes to the diagonal blocks** along an injective index map. -/
theorem JointlyDissociated.arrayBlock_diag (h : JointlyDissociated μ X) {e : ℕ → ℕ}
    (he : Function.Injective e) :
    JointlyDissociated μ (TauCeti.Probability.arrayBlock X e e) := by
  refine jointlyDissociated_iff.mpr fun e₁ e₂ h₁ => ?_
  simp only [arrayBlock_apply]
  exact jointlyDissociated_iff.mp h (e ∘ e₁) (e ∘ e₂)
    (by simpa only [Set.range_comp] using Set.disjoint_image_of_injective he h₁)

end Stability

section IID

/-- **An array of independent entries is separately dissociated.** The two blocks read disjoint
sets of entries, because their row index sets already are disjoint. -/
theorem separatelyDissociated_of_iIndepFun (hX : iIndepFun X μ) (hX_meas : ∀ p, Measurable (X p)) :
    SeparatelyDissociated μ X := by
  refine separatelyDissociated_iff.mpr fun e f e' f' he _ => ?_
  have key : ∀ a b : ℕ → ℕ, Measurable[blockSigma X (Set.range a ×ˢ Set.range b)]
      fun ω (p : ℕ × ℕ) => X (a p.1, b p.2) ω := fun a b =>
    @measurable_pi_lambda _ _ _ (blockSigma X (Set.range a ×ˢ Set.range b)) _ _ fun p =>
      measurable_blockSigma_of_mem (Z := X) (S := Set.range a ×ˢ Set.range b)
        ⟨⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩
  exact indepFun_of_measurable_blockSigma (hX.precomp Subtype.val_injective)
    (fun p _ => hX_meas p)
    (Set.disjoint_left.mpr fun p hp hp' => Set.disjoint_left.mp he hp.1 hp'.1)
    (key e f) (key e' f')

end IID

end Probability

end TauCeti
