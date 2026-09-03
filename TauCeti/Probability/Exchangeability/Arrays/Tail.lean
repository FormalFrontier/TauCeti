/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
public import TauCeti.Probability.Independence.DisjointBlocks
public import TauCeti.Probability.Process.Tail.Basic

/-!
# Tail σ-algebras of arrays

This file defines the corner tail of an array: the events readable from entries `X (i, j)` with
both indices arbitrarily large. It is the two-dimensional analogue of the tail σ-algebra of a
process, cutting both index axes at the same time, and it is the σ-algebra the zero-one law for a
dissociated array in `Arrays.ZeroOne` is stated for. Cutting both axes is what dissociation asks
for: two square blocks are independent only when their index sets are disjoint, so a one-axis cut
would not do.

The corner tail need not be the tail of the diagonal process `arrayDiag X`; it contains it
(`tailProcess_arrayDiag_le_arrayTail`) and may additionally read off-diagonal entries above the
cutoff.

These definitions support the exchangeable-arrays milestone of
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8.

## Main definitions

* `TauCeti.Probability.arrayTailFamily` — the σ-algebra of the entries with both indices at least
  `n`;
* `TauCeti.Probability.arrayTail` — the tail σ-algebra of an array, the infimum of the tail family.

## Main results

* `TauCeti.Probability.arrayTailFamily_le_iff` and `TauCeti.Probability.le_arrayTail_iff` — the
  universal properties of the two σ-algebras;
* `TauCeti.Probability.arrayTailFamily_antitone` — the tail family decreases;
* `TauCeti.Probability.arrayTailFamily_eq_iSup_Icc` — finite corners exhaust a member of the tail
  family;
* `TauCeti.Probability.arrayTail_le_ambient` — the array tail is a sub-σ-algebra of the ambient one
  as soon as the entries beyond some cutoff are measurable;
* `TauCeti.Probability.blockSigma_arrayDiag_le_blockSigma_prod_self` — a block of diagonal entries
  is read by the square block over the same index set;
* `TauCeti.Probability.tailProcess_arrayDiag_le_arrayTail` — the tail of the diagonal process is an
  array tail event.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
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
/-- The finite corners above `n` exhaust the array tail family at `n`. -/
theorem arrayTailFamily_eq_iSup_Icc (X : ℕ × ℕ → Ω → α) (n : ℕ) :
    arrayTailFamily X n =
      ⨆ k, blockSigma X (Set.Icc n (n + k) ×ˢ Set.Icc n (n + k)) := by
  apply le_antisymm
  · rw [arrayTailFamily_le_iff]
    intro i j hi hj
    exact (measurable_blockSigma_of_mem (Z := X)
      (S := Set.Icc n (n + max i j) ×ˢ Set.Icc n (n + max i j))
      ⟨⟨hi, (le_max_left i j).trans (Nat.le_add_left _ _)⟩,
        ⟨hj, (le_max_right i j).trans (Nat.le_add_left _ _)⟩⟩).mono
      (le_iSup (fun k : ℕ =>
        blockSigma X (Set.Icc n (n + k) ×ˢ Set.Icc n (n + k))) (max i j)) le_rfl
  · refine iSup_le fun k => ?_
    rw [arrayTailFamily_eq_blockSigma]
    exact blockSigma_mono
      (Set.prod_mono Set.Icc_subset_Ici_self Set.Icc_subset_Ici_self)

omit [MeasurableSpace Ω] in
/-- The tail σ-algebra of an array sits inside every member of its tail family. -/
theorem arrayTail_le_arrayTailFamily (X : ℕ × ℕ → Ω → α) (n : ℕ) :
    arrayTail X ≤ arrayTailFamily X n := by
  rw [arrayTail_eq_iInf_arrayTailFamily]
  exact iInf_le _ n

omit [MeasurableSpace Ω] in
/-- Universal property of the array tail σ-algebra. -/
theorem le_arrayTail_iff {m : MeasurableSpace Ω} :
    m ≤ arrayTail X ↔ ∀ n, m ≤ arrayTailFamily X n := by
  rw [arrayTail_eq_iInf_arrayTailFamily, le_iInf_iff]

omit [MeasurableSpace Ω] in
/-- An event belongs to the array tail exactly when it belongs to every member of the tail
family. -/
@[simp]
theorem measurableSet_arrayTail_iff {s : Set Ω} :
    MeasurableSet[arrayTail X] s ↔ ∀ n, MeasurableSet[arrayTailFamily X n] s := by
  rw [arrayTail_eq_iInf_arrayTailFamily, MeasurableSpace.measurableSet_iInf]

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
/-- **The diagonal entries indexed by `S` are read by the square block over `S`.** The entry
`arrayDiag X i` is `X (i, i)`, and `(i, i)` lies in `S ×ˢ S` for every `i ∈ S`. -/
theorem blockSigma_arrayDiag_le_blockSigma_prod_self (X : ℕ × ℕ → Ω → α) (S : Set ℕ) :
    blockSigma (arrayDiag X) S ≤ blockSigma X (S ×ˢ S) :=
  blockSigma_le_iff.mpr fun i hi => by
    simpa only [arrayDiag_apply] using
      measurable_blockSigma_of_mem (Z := X) (S := S ×ˢ S) (i := (i, i)) ⟨hi, hi⟩

omit [MeasurableSpace Ω] in
/-- **The tail of the diagonal is an array tail event.** The diagonal entries from time `n` on have
both indices at least `n`, so they generate a sub-σ-algebra of the tail family at `n`. The
inclusion need not be an equality: the array tail may additionally read off-diagonal entries above
the cutoff. -/
theorem tailProcess_arrayDiag_le_arrayTail (X : ℕ × ℕ → Ω → α) :
    tailProcess (arrayDiag X) ≤ arrayTail X := by
  rw [le_arrayTail_iff]
  intro n
  refine (tailProcess_le_tailFamily _ n).trans (tailFamily_le_iff.mpr ?_)
  intro k hk
  simpa only [arrayDiag_apply] using measurable_arrayTailFamily_of_le (X := X) hk hk

end Probability

end TauCeti

end

end
