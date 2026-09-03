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

The same disjoint-block device that turns joint exchangeability into separate exchangeability also
transfers dissociation. If `e` and `f` are injections with disjoint ranges, every rectangular block
of `arrayBlock X e f` reads a square block of `X` on the union of its selected row and column
indices. Thus joint dissociation of `X` makes this block separately dissociated
(`JointlyDissociated.separatelyDissociated_arrayBlock`), including the pair-valued version that
retains both orientations. This is the bridge from the ergodic jointly exchangeable branch to the
separate Aldous--Hoover branch.

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
* `TauCeti.Probability.JointlyDissociated.separatelyDissociated_arrayBlock` and
  `TauCeti.Probability.JointlyDissociated.separatelyDissociated_arrayBlockPair` — a block along two
  injections with disjoint ranges converts joint dissociation to separate dissociation;
* `TauCeti.Probability.SeparatelyDissociated.map_values` and
  `TauCeti.Probability.JointlyDissociated.map_values` — dissociation is preserved by a measurable
  coordinatewise pushforward;
* `TauCeti.Probability.JointlyDissociated.indep_blockSigma_prod_self` — square blocks over
  arbitrary disjoint index sets generate independent σ-algebras;
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

omit [MeasurableSpace Ω] in
/-- The entries indexed by `S` lie in the σ-algebra generated by reading the square block along
`e`, provided `S` is contained in the square of the range of `e`. -/
private theorem blockSigma_le_comap_arrayBlock_diag {e : ℕ → ℕ} {S : Set (ℕ × ℕ)}
    (hS : S ⊆ Set.range e ×ˢ Set.range e) :
    blockSigma X S ≤
      MeasurableSpace.comap (fun ω (q : ℕ × ℕ) => X (e q.1, e q.2) ω) inferInstance := by
  refine blockSigma_le_iff.mpr fun p hp => ?_
  obtain ⟨⟨i, hi⟩, j, hj⟩ := hS hp
  have hblock : Measurable[MeasurableSpace.comap
      (fun ω (r : ℕ × ℕ) => X (e r.1, e r.2) ω) inferInstance]
      fun ω (r : ℕ × ℕ) => X (e r.1, e r.2) ω :=
    Measurable.of_comap_le le_rfl
  have hmeas : Measurable[MeasurableSpace.comap
      (fun ω (r : ℕ × ℕ) => X (e r.1, e r.2) ω) inferInstance]
      (fun ω => X (e i, e j) ω) :=
    (measurable_pi_apply (i, j)).comp hblock
  simpa only [hi, hj, Prod.eta] using hmeas

/-- **Square blocks over disjoint nonempty index sets are independent.** This unnormalized form
uses nonemptiness to present both sets as ranges of maps from `ℕ`. It is the implementation of
`JointlyDissociated.indep_blockSigma_prod_self`, which is the exported form. -/
private theorem JointlyDissociated.indep_blockSigma_prod_self_of_nonempty
    (h : JointlyDissociated μ X)
    {S T : Set ℕ} (hS : S.Nonempty) (hT : T.Nonempty) (hd : Disjoint S T) :
    Indep (blockSigma X (S ×ˢ S)) (blockSigma X (T ×ˢ T)) μ := by
  classical
  obtain ⟨e, he⟩ := (Set.to_countable S).exists_eq_range hS
  obtain ⟨f, hf⟩ := (Set.to_countable T).exists_eq_range hT
  have hindep := jointlyDissociated_iff.mp h e f (by simpa only [← he, ← hf] using hd)
  rw [IndepFun_iff_Indep] at hindep
  exact indep_of_indep_of_le hindep
    (blockSigma_le_comap_arrayBlock_diag (X := X) (e := e) (by
      intro p hp
      simpa only [← he] using hp))
    (blockSigma_le_comap_arrayBlock_diag (X := X) (e := f) (by
      intro p hp
      simpa only [← hf] using hp))

/-- **Square blocks over arbitrary disjoint index sets are independent.** This is the σ-algebra
form of joint dissociation. Empty blocks generate the bottom σ-algebra; the normalization
assumption is needed for the bottom σ-algebra to be independent of every σ-algebra. -/
theorem JointlyDissociated.indep_blockSigma_prod_self [IsZeroOrProbabilityMeasure μ]
    (h : JointlyDissociated μ X) {S T : Set ℕ} (hd : Disjoint S T) :
    Indep (blockSigma X (S ×ˢ S)) (blockSigma X (T ×ˢ T)) μ := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [Set.empty_prod]
    rw [blockSigma_empty]
    exact indep_bot_left _
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp only [Set.empty_prod]
    rw [blockSigma_empty]
    exact indep_bot_right _
  exact h.indep_blockSigma_prod_self_of_nonempty hS hT hd

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
      (Measurable.of_eval fun p => hg.comp (measurable_pi_apply p))
      (Measurable.of_eval fun p => hg.comp (measurable_pi_apply p))

/-- Joint dissociation is preserved by a measurable coordinatewise pushforward of the entries. -/
theorem JointlyDissociated.map_values (h : JointlyDissociated μ X) {g : α → β}
    (hg : Measurable g) : JointlyDissociated μ fun p ω => g (X p ω) :=
  jointlyDissociated_iff.mpr fun e e' he =>
    (jointlyDissociated_iff.mp h e e' he).comp
      (Measurable.of_eval fun p => hg.comp (measurable_pi_apply p))
      (Measurable.of_eval fun p => hg.comp (measurable_pi_apply p))

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

private def mergeIndexMaps (a b : ℕ → ℕ) : ℕ → ℕ :=
  Sum.elim a b ∘ Equiv.natSumNatEquivNat.symm

private theorem range_mergeIndexMaps (a b : ℕ → ℕ) :
    Set.range (mergeIndexMaps a b) = Set.range a ∪ Set.range b := by
  rw [mergeIndexMaps, Equiv.natSumNatEquivNat.symm.surjective.range_comp,
    Set.Sum.elim_range]

/-- **A two-orientation block of a jointly dissociated array is separately dissociated.** The row
and column injections must have disjoint ranges. Each rectangular block of the pair-valued array
then reads a square block of the original array on the union of its row and column indices; the
two unions are disjoint when both pairs of rectangular index sets are disjoint. -/
theorem JointlyDissociated.separatelyDissociated_arrayBlockPair
    (h : JointlyDissociated μ X) {e f : ℕ → ℕ}
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    SeparatelyDissociated μ (TauCeti.Probability.arrayBlockPair X e f) := by
  refine separatelyDissociated_iff.mpr fun e₁ f₁ e₂ f₂ he₁₂ hf₁₂ => ?_
  let g₁ := mergeIndexMaps (e ∘ e₁) (f ∘ f₁)
  let g₂ := mergeIndexMaps (e ∘ e₂) (f ∘ f₂)
  have he_disjoint : Disjoint (Set.range (e ∘ e₁)) (Set.range (e ∘ e₂)) := by
    simpa only [Set.range_comp] using Set.disjoint_image_of_injective he he₁₂
  have hf_disjoint : Disjoint (Set.range (f ∘ f₁)) (Set.range (f ∘ f₂)) := by
    simpa only [Set.range_comp] using Set.disjoint_image_of_injective hf hf₁₂
  have hef_disjoint : Disjoint (Set.range (e ∘ e₁)) (Set.range (f ∘ f₂)) :=
    hd.mono (Set.range_comp_subset_range e₁ e) (Set.range_comp_subset_range f₂ f)
  have hfe_disjoint : Disjoint (Set.range (f ∘ f₁)) (Set.range (e ∘ e₂)) :=
    hd.symm.mono (Set.range_comp_subset_range f₁ f) (Set.range_comp_subset_range e₂ e)
  have hg_disjoint : Disjoint (Set.range g₁) (Set.range g₂) := by
    simp only [g₁, g₂, range_mergeIndexMaps]
    exact (he_disjoint.union_right hef_disjoint).union_left
      (hfe_disjoint.union_right hf_disjoint)
  have hindep := jointlyDissociated_iff.mp h g₁ g₂ hg_disjoint
  let read : (ℕ × ℕ → α) → (ℕ × ℕ → α × α) := fun x p =>
    (x (Equiv.natSumNatEquivNat (Sum.inl p.1),
        Equiv.natSumNatEquivNat (Sum.inr p.2)),
      x (Equiv.natSumNatEquivNat (Sum.inr p.2),
        Equiv.natSumNatEquivNat (Sum.inl p.1)))
  have hread : Measurable read :=
    Measurable.of_eval fun p => (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hleft :
      read ∘ (fun ω p => X (g₁ p.1, g₁ p.2) ω) =
        fun ω p => arrayBlockPair X e f (e₁ p.1, f₁ p.2) ω := by
    funext ω p
    simp only [read, g₁, mergeIndexMaps, Function.comp_apply, Equiv.symm_apply_apply,
      Sum.elim_inl, Sum.elim_inr, arrayBlockPair_apply]
  have hright :
      read ∘ (fun ω p => X (g₂ p.1, g₂ p.2) ω) =
        fun ω p => arrayBlockPair X e f (e₂ p.1, f₂ p.2) ω := by
    funext ω p
    simp only [read, g₂, mergeIndexMaps, Function.comp_apply, Equiv.symm_apply_apply,
      Sum.elim_inl, Sum.elim_inr, arrayBlockPair_apply]
  have hcomp := hindep.comp hread hread
  rw [hleft, hright] at hcomp
  exact hcomp

/-- **A rectangular block of a jointly dissociated array is separately dissociated** when its
row and column injections have disjoint ranges. This is the one-orientation consequence of
`JointlyDissociated.separatelyDissociated_arrayBlockPair`. -/
theorem JointlyDissociated.separatelyDissociated_arrayBlock
    (h : JointlyDissociated μ X) {e f : ℕ → ℕ}
    (he : Function.Injective e) (hf : Function.Injective f)
    (hd : Disjoint (Set.range e) (Set.range f)) :
    SeparatelyDissociated μ (TauCeti.Probability.arrayBlock X e f) := by
  have hfun :
      (fun p ω => Prod.fst (arrayBlockPair X e f p ω)) = arrayBlock X e f := by
    funext p ω
    simp only [arrayBlockPair_apply, arrayBlock_apply]
  rw [← hfun]
  exact (h.separatelyDissociated_arrayBlockPair he hf hd).map_values measurable_fst

/-! ## The canonical block, along the even and the odd indices -/

/-- **The canonical separately dissociated block of a jointly dissociated array**: read the rows
along the even indices and the columns along the odd ones. -/
theorem JointlyDissociated.separatelyDissociated_arrayBlock_evenOdd
    (h : JointlyDissociated μ X) :
    SeparatelyDissociated μ (arrayBlock X (fun i => 2 * i) fun j => 2 * j + 1) :=
  h.separatelyDissociated_arrayBlock (mul_right_injective₀ two_ne_zero)
    ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero)) (by
      simp [Set.disjoint_left])

/-- **The canonical separately dissociated block of pairs of a jointly dissociated array.** -/
theorem JointlyDissociated.separatelyDissociated_arrayBlockPair_evenOdd
    (h : JointlyDissociated μ X) :
    SeparatelyDissociated μ (arrayBlockPair X (fun i => 2 * i) fun j => 2 * j + 1) :=
  h.separatelyDissociated_arrayBlockPair (mul_right_injective₀ two_ne_zero)
    ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero)) (by
      simp [Set.disjoint_left])

end Stability

section IID

/-- **An array of independent entries is separately dissociated.** The two blocks read disjoint
sets of entries, because their row index sets already are disjoint. -/
theorem separatelyDissociated_of_iIndepFun (hX : iIndepFun X μ) (hX_meas : ∀ p, Measurable (X p)) :
    SeparatelyDissociated μ X := by
  refine separatelyDissociated_iff.mpr fun e f e' f' he _ => ?_
  have key : ∀ a b : ℕ → ℕ, Measurable[blockSigma X (Set.range a ×ˢ Set.range b)]
      fun ω (p : ℕ × ℕ) => X (a p.1, b p.2) ω := fun a b =>
    @Measurable.of_eval _ _ _ (blockSigma X (Set.range a ×ˢ Set.range b)) _ _ fun p =>
      measurable_blockSigma_of_mem (Z := X) (S := Set.range a ×ˢ Set.range b)
        ⟨⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩
  exact indepFun_of_measurable_blockSigma (hX.precomp Subtype.val_injective)
    (fun p _ => hX_meas p)
    (Set.disjoint_left.mpr fun p hp hp' => Set.disjoint_left.mp he hp.1 hp'.1)
    (key e f) (key e' f')

end IID

end Probability

end TauCeti
