/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Independent families below a compact element

Mathlib's `CompleteLattice.WellFoundedGT.finite_ne_bot_of_iSupIndep` bounds an independent family
in a lattice satisfying the ascending chain condition. This file records the compactness variant:
an independent family whose supremum is a compact element has only finitely many nonzero members,
`TauCeti.finite_ne_bot_of_iSupIndep_of_isCompactElement`. Compactness confines the whole family to
a finite subfamily, and independence then forces every index outside it to be `⊥`.
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

end TauCeti
