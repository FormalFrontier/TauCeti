/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Independent families and compactness

This file records lattice consequences of independence that involve compact elements and compact
generation.

## Main declarations

* `TauCeti.finite_ne_bot_of_iSupIndep_of_isCompactElement`: an independent family whose supremum
  is a compact element has only finitely many nonzero members. Compactness confines the whole
  family to a finite subfamily, and independence then forces every index outside it to be `⊥`.
  This is the compactness variant of Mathlib's
  `WellFoundedGT.finite_ne_bot_of_iSupIndep`, which instead assumes the ascending
  chain condition.
* `TauCeti.iSupIndep.iSup₂_inf_iSup_eq_iSup₂`: a partial supremum of an independent family
  meets the total supremum of a pointwise dominated family in its corresponding partial supremum.
-/

public section

namespace TauCeti

/-- An independent family whose supremum is a compact element has only finitely many nonzero
members. -/
theorem finite_ne_bot_of_iSupIndep_of_isCompactElement {α ι : Type*} [CompleteLattice α]
    {a : ι → α} (ha : iSupIndep a)
    (hc : IsCompactElement (⨆ i, a i)) : {i | a i ≠ ⊥}.Finite := by
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup α hc a le_rfl
  refine s.finite_toSet.subset fun i hi ↦ ?_
  by_contra his
  refine hi ((ha i).eq_bot_of_le ((le_iSup a i).trans (hs.trans (iSup₂_le fun j hj ↦ ?_))))
  exact le_iSup₂_of_le j (fun hji ↦ his (Finset.mem_coe.mpr (hji ▸ hj))) le_rfl

/-- **A subfamily of an independent family truncates a dominated supremum.** If `B i ≤ A i` for
every `i` and the `A i` are independent, then the total supremum of the `B` meets the partial
supremum of the `A` over the indices satisfying `P` in exactly the partial supremum of the `B` over
those indices. -/
theorem iSupIndep.iSup₂_inf_iSup_eq_iSup₂ {α ι : Type*} [CompleteLattice α]
    [IsModularLattice α] [IsCompactlyGenerated α] {A B : ι → α}
    (hA : iSupIndep A) (hB : ∀ i, B i ≤ A i) (P : ι → Prop) :
    (⨆ (i) (_ : P i), A i) ⊓ ⨆ i, B i = ⨆ (i) (_ : P i), B i := by
  have hle : (⨆ (i) (_ : P i), B i) ≤ ⨆ (i) (_ : P i), A i := iSup₂_mono fun i _ ↦ hB i
  have hdisj : Disjoint (⨆ (i) (_ : P i), A i) (⨆ (i) (_ : ¬ P i), B i) := by
    have h₀ : Disjoint (⨆ (i) (_ : P i), A i) (⨆ (i) (_ : ¬ P i), A i) := by
      simpa only [Set.mem_ofPred_eq] using
        hA.disjoint_biSup_biSup (s := {i | P i}) (t := {i | ¬ P i})
          (Set.disjoint_left.2 fun i hi hi' ↦ hi' hi)
    exact h₀.mono_right (iSup₂_mono fun i _ ↦ hB i)
  rw [iSup_split B P, inf_comm, sup_inf_assoc_of_le _ hle, inf_comm, hdisj.eq_bot, sup_bot_eq]

end TauCeti
