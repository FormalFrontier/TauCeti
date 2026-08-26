/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

-- Public: dissociation is the hypothesis of every zero-one statement here.
public import TauCeti.Probability.Exchangeability.Arrays.Dissociated
-- Public: the zero-one criterion for i.i.d.-ness, of which the diagonal theorem is an instance.
public import TauCeti.Probability.DeFinetti.ZeroOne
-- Non-public: the zero-one law for a self-independent event is used only inside a proof.
import Mathlib.Probability.Independence.ZeroOne

/-!
# The zero-one law for a dissociated array

A dissociated array has no global randomness left to remember: the events readable from the entries
`X (i, j)` with both indices arbitrarily large are almost surely trivial.

The proof is Kolmogorov's. Split the index square at `n` into the corner `[0, n] × [0, n]` and the
tail block `[n + 1, ∞) × [n + 1, ∞)`. The two index sets are disjoint, so joint dissociation makes
the corner independent of the tail block; the tail blocks decrease to `arrayTail X`, which is
therefore independent of every corner, hence of the σ-algebra the corners generate, which is all of
the array. Being independent of itself, the array tail is trivial.

Two disjointness conditions per pair of blocks is what dissociation asks for, and `arrayTail` is
built to supply them: it is the **diagonal** tail, cutting *both* index axes at `n`. The row tail
`⨅ n, blockSigma X ([n, ∞) × ℕ)` is genuinely not trivial for a dissociated array — an array whose
rows are all one common i.i.d. random path is separately dissociated, and its row tail carries the
whole path.

The application is the diagonal. Dissociation separates any diagonal entry from the square block
over a finite set of other indices, and hence makes the whole diagonal independent
(`JointlyDissociated.iIndepFun_arrayDiag`). Joint exchangeability supplies the common law, so the
diagonal is i.i.d. (`JointlyDissociated.exists_mixedIIDWith_const_arrayDiag`). This is the array
analogue of a product law's being the extreme case of an exchangeable law, and it matches the
ergodic Aldous--Hoover coding
`X (i, j) = f (U_vert i) (U_vert j) (U_cell {i, j})` in `Arrays/AldousHoover.lean`, whose diagonal
reads a fresh vertex and cell variable at each index.

These results advance the exchangeable-arrays milestone of
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8: the ergodic form of the Aldous--Hoover
representation is the dissociated one, and this is the zero-one law separating it from the general
form.

## Main definitions

* `TauCeti.Probability.arrayTailFamily` — the σ-algebra of the entries with both indices at least
  `n`;
* `TauCeti.Probability.arrayTail` — the tail σ-algebra of an array, the infimum of the tail family.

## Main results

* `TauCeti.Probability.JointlyDissociated.measure_eq_zero_or_one_of_arrayTail` — **the zero-one
  law**: the tail σ-algebra of a jointly dissociated array is trivial;
* `TauCeti.Probability.SeparatelyDissociated.measure_eq_zero_or_one_of_arrayTail` — the same for the
  stronger symmetry;
* `TauCeti.Probability.JointlyDissociated.iIndepFun_arrayDiag` — the diagonal of a jointly
  dissociated array is independent.

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

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω}
  {X : ℕ × ℕ → Ω → α}

/-- The **tail family** of an array at time `n`: the events readable from the entries `X (i, j)`
with `n ≤ i` and `n ≤ j`. It is the array analogue of the future σ-algebra `tailFamily` of a
process, cutting both index axes at once. -/
@[implicit_reducible]
def arrayTailFamily (X : ℕ × ℕ → Ω → α) (n : ℕ) : MeasurableSpace Ω :=
  blockSigma X (Set.Ici n ×ˢ Set.Ici n)

/-- The **tail σ-algebra of an array**: the events readable from the entries with both indices
arbitrarily large. It is the array analogue of `tailProcess`. -/
@[implicit_reducible]
def arrayTail (X : ℕ × ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ n, arrayTailFamily X n

omit [MeasurableSpace Ω] in
/-- Normal form for the array tail family. -/
@[simp]
theorem arrayTailFamily_eq_blockSigma (X : ℕ × ℕ → Ω → α) (n : ℕ) :
    arrayTailFamily X n = blockSigma X (Set.Ici n ×ˢ Set.Ici n) :=
  (rfl)

omit [MeasurableSpace Ω] in
/-- Normal form for the tail σ-algebra of an array. -/
@[simp]
theorem arrayTail_eq_iInf_arrayTailFamily (X : ℕ × ℕ → Ω → α) :
    arrayTail X = ⨅ n, arrayTailFamily X n :=
  (rfl)

omit [MeasurableSpace Ω] in
/-- An entry with both indices at least `n` is measurable for the array tail family at `n`. -/
theorem measurable_arrayTailFamily_of_le {n i j : ℕ} (hi : n ≤ i) (hj : n ≤ j) :
    Measurable[arrayTailFamily X n] (X (i, j)) := by
  rw [arrayTailFamily_eq_blockSigma]
  exact measurable_blockSigma_of_mem ⟨hi, hj⟩

omit [MeasurableSpace Ω] in
/-- Universal property of the array tail family at `n`. -/
theorem arrayTailFamily_le_iff {n : ℕ} {m : MeasurableSpace Ω} :
    arrayTailFamily X n ≤ m ↔
      ∀ i j, n ≤ i → n ≤ j → Measurable[m] (X (i, j)) := by
  rw [arrayTailFamily_eq_blockSigma, blockSigma_le_iff]
  constructor
  · exact fun h i j hi hj => h (i, j) ⟨hi, hj⟩
  · exact fun h p hp => h p.1 p.2 hp.1 hp.2

omit [MeasurableSpace Ω] in
/-- The array tail family decreases. -/
theorem arrayTailFamily_antitone (X : ℕ × ℕ → Ω → α) : Antitone (arrayTailFamily X) := by
  intro n m hnm
  rw [arrayTailFamily_eq_blockSigma, arrayTailFamily_eq_blockSigma]
  exact blockSigma_mono
    (Set.prod_mono (Set.Ici_subset_Ici.mpr hnm) (Set.Ici_subset_Ici.mpr hnm))

omit [MeasurableSpace Ω] in
/-- The tail σ-algebra of an array sits inside every member of its tail family. -/
theorem arrayTail_le_arrayTailFamily (X : ℕ × ℕ → Ω → α) (n : ℕ) :
    arrayTail X ≤ arrayTailFamily X n := by
  rw [arrayTail_eq_iInf_arrayTailFamily]
  exact iInf_le _ n

/-- A member of the tail family is a sub-σ-algebra of the ambient one when the entries it sees are
measurable. -/
theorem arrayTailFamily_le_ambient (n : ℕ)
    (hX : ∀ p, n ≤ p.1 → n ≤ p.2 → Measurable (X p)) :
    arrayTailFamily X n ≤ (inferInstance : MeasurableSpace Ω) := by
  exact arrayTailFamily_le_iff.mpr fun i j hi hj => hX (i, j) hi hj

/-- The tail σ-algebra is a sub-σ-algebra of the ambient one when the entries beyond some cutoff
are measurable. -/
theorem arrayTail_le_ambient (n : ℕ)
    (hX : ∀ p, n ≤ p.1 → n ≤ p.2 → Measurable (X p)) :
    arrayTail X ≤ (inferInstance : MeasurableSpace Ω) :=
  (arrayTail_le_arrayTailFamily X n).trans (arrayTailFamily_le_ambient n hX)

omit [MeasurableSpace Ω] in
/-- **The tail of the diagonal is an array tail event.** The diagonal entries from time `n` on have
both indices at least `n`, so they generate a sub-σ-algebra of the tail family at `n`. -/
theorem tailProcess_arrayDiag_le_arrayTail (X : ℕ × ℕ → Ω → α) :
    tailProcess (arrayDiag X) ≤ arrayTail X := by
  rw [arrayTail_eq_iInf_arrayTailFamily]
  refine le_iInf fun n => (tailProcess_le_tailFamily _ n).trans (tailFamily_le_iff.mpr ?_)
  intro k hk
  simpa only [arrayDiag_apply] using
    (arrayTailFamily_le_iff (X := X) (m := arrayTailFamily X n)).mp le_rfl k k hk hk

/-- **A corner of a jointly dissociated array is independent of the complementary tail block.** The
corner `[0, n] × [0, n]` and the block `[n + 1, ∞) × [n + 1, ∞)` are square blocks over disjoint
sets of indices. -/
theorem JointlyDissociated.indep_blockSigma_Iic_arrayTailFamily (h : JointlyDissociated μ X)
    (n : ℕ) :
    Indep (blockSigma X (Set.Iic n ×ˢ Set.Iic n)) (arrayTailFamily X (n + 1)) μ := by
  rw [arrayTailFamily_eq_blockSigma]
  exact h.indep_blockSigma_prod ⟨0, by simp⟩ ⟨n + 1, by simp⟩
    (Set.disjoint_left.mpr fun i hi hi' =>
      (Nat.not_succ_le_self n) (hi'.trans hi))

/-- **The tail σ-algebra of a jointly dissociated array is independent of itself.** Every corner is
independent of the tail, the corners are increasing and generate the whole array σ-algebra, and the
tail sits inside it. -/
theorem JointlyDissociated.indep_arrayTail_self [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (hX : ∀ p, Measurable (X p)) :
    Indep (arrayTail X) (arrayTail X) μ := by
  have hle : ∀ n : ℕ,
      blockSigma X (Set.Iic n ×ˢ Set.Iic n) ≤ (inferInstance : MeasurableSpace Ω) :=
    fun _ => blockSigma_le _ fun p _ => hX p
  have hmono : Monotone fun n : ℕ => blockSigma X (Set.Iic n ×ˢ Set.Iic n) := fun a b hab =>
    blockSigma_mono (Set.prod_mono (Set.Iic_subset_Iic.mpr hab) (Set.Iic_subset_Iic.mpr hab))
  have hindep : ∀ n : ℕ, Indep (blockSigma X (Set.Iic n ×ˢ Set.Iic n)) (arrayTail X) μ := fun n =>
    indep_of_indep_of_le_right (h.indep_blockSigma_Iic_arrayTailFamily n)
      (arrayTail_le_arrayTailFamily X (n + 1))
  have hsup := indep_iSup_of_monotone hindep hle
    (arrayTail_le_ambient 0 fun p _ _ => hX p) hmono
  refine indep_of_indep_of_le_left hsup ((arrayTail_le_arrayTailFamily X 0).trans ?_)
  rw [arrayTailFamily_eq_blockSigma]
  refine blockSigma_le_iff.mpr fun p _ => ?_
  exact (measurable_blockSigma_of_mem (Z := X)
    (S := Set.Iic (max p.1 p.2) ×ˢ Set.Iic (max p.1 p.2))
    ⟨Set.mem_Iic.mpr (le_max_left p.1 p.2), Set.mem_Iic.mpr (le_max_right p.1 p.2)⟩).mono
      (le_iSup (fun n : ℕ => blockSigma X (Set.Iic n ×ˢ Set.Iic n)) (max p.1 p.2)) le_rfl

/-- **The zero-one law for a dissociated array.** Every event in the tail σ-algebra of a jointly
dissociated array has probability `0` or `1`.

The tail cuts both index axes, as dissociation requires: for the row tail alone the statement is
false, an array all of whose rows are one common i.i.d. random path being dissociated with a row
tail that carries the whole path. -/
theorem JointlyDissociated.measure_eq_zero_or_one_of_arrayTail [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (hX : ∀ p, Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[arrayTail X] s) : μ s = 0 ∨ μ s = 1 :=
  measure_eq_zero_or_one_of_indep_self (h.indep_arrayTail_self hX) hs

/-- **The zero-one law for a separately dissociated array**, the corollary of the jointly
dissociated form at the stronger symmetry. -/
theorem SeparatelyDissociated.measure_eq_zero_or_one_of_arrayTail [IsProbabilityMeasure μ]
    (h : SeparatelyDissociated μ X) (hX : ∀ p, Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[arrayTail X] s) : μ s = 0 ∨ μ s = 1 :=
  h.jointlyDissociated.measure_eq_zero_or_one_of_arrayTail hX hs

/-- **The diagonal of a jointly dissociated array has a trivial tail.** -/
theorem JointlyDissociated.measure_eq_zero_or_one_of_tailProcess_arrayDiag [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) (hX : ∀ p, Measurable (X p)) {s : Set Ω}
    (hs : MeasurableSet[tailProcess (arrayDiag X)] s) : μ s = 0 ∨ μ s = 1 :=
  h.measure_eq_zero_or_one_of_arrayTail hX (tailProcess_arrayDiag_le_arrayTail X s hs)

/-- **The diagonal of a jointly exchangeable, jointly dissociated array is i.i.d.**, with its common
law named: over a standard Borel state space there is a probability measure `P` with `fun _ => P` a
mixing representative of the diagonal, so the diagonal entries are independent with common law
`P`. Dissociation supplies independence, while joint exchangeability supplies the common law. -/
theorem JointlyDissociated.exists_mixedIIDWith_const_arrayDiag [StandardBorelSpace α]
    [IsProbabilityMeasure μ] (h : JointlyDissociated μ X) (hexch : JointlyExchangeable μ X)
    (hX : ∀ p, Measurable (X p)) :
    ∃ P : ProbabilityMeasure α, MixedIIDWith μ (arrayDiag X) fun _ => P :=
  exists_mixedIIDWith_const_of_exchangeable_of_tailProcess_trivial
    (fun n => by simpa only [arrayDiag_apply] using (hX (n, n)).aemeasurable)
    (hexch.exchangeable_arrayDiag fun p => (hX p).aemeasurable)
    fun _ hs => h.measure_eq_zero_or_one_of_tailProcess_arrayDiag hX hs

/-- **The diagonal entries of a jointly dissociated array are independent.** A diagonal entry is
independent of the square block over any finite set of other indices, which gives the finite-family
criterion for mutual independence. -/
theorem JointlyDissociated.iIndepFun_arrayDiag [IsProbabilityMeasure μ]
    (h : JointlyDissociated μ X) : iIndepFun (arrayDiag X) μ := by
  rw [iIndepFun_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      by_cases hs : s.Nonempty
      · have hdisj : Disjoint ({i} : Set ℕ) (s : Set ℕ) := by
          simpa [Set.disjoint_left] using hi
        have hindep := h.indep_blockSigma_prod (S := {i}) (T := (s : Set ℕ))
          (Set.singleton_nonempty i) hs hdisj
        have hfi' := hf i (Finset.mem_insert_self i s)
        rw [arrayDiag_apply] at hfi'
        have hfi : MeasurableSet[blockSigma X (({i} : Set ℕ) ×ˢ {i})] (f i) :=
          (measurable_blockSigma_of_mem (Z := X) (by simp)).comap_le _ hfi'
        have hrest : MeasurableSet[blockSigma X ((s : Set ℕ) ×ˢ (s : Set ℕ))]
            (⋂ j ∈ s, f j) := by
          refine s.measurableSet_biInter fun j hj => ?_
          have hfj := hf j (Finset.mem_insert_of_mem hj)
          rw [arrayDiag_apply] at hfj
          exact (measurable_blockSigma_of_mem (Z := X) (by simp [hj])).comap_le _ hfj
        rw [Finset.prod_insert hi, ← ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]
        simpa only [Finset.set_biInter_insert] using
          (Indep_iff _ _ _).mp hindep _ _ hfi hrest
      · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simp

end Probability

end TauCeti

end

end
