/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.Geometry.Hodge.Structure

/-!
# The Hodge decomposition

This file proves that the Hodge components of a pure Hodge structure form an internal direct sum.
More precisely, it recovers every step of the decreasing Hodge filtration as the supremum of the
components in that step and proves that the full family of components is independent.

The key local calculation uses two adjacent opposedness decompositions. The component
`H^{p,n-p}` is complementary to the sum of the conjugate step below it and the filtration step
above it. Consequently every other component lies in this explicit complement. Boundedness then
turns the one-step identity `F p = H^{p,n-p} ⊔ F (p + 1)` into filtration recovery by descending
induction.

This is the opposed-filtration description of the Hodge decomposition in Deligne, *Théorie de
Hodge II*, §1.2.1, and Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §6.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.F_eq_iSup_piece`: a filtration step is the supremum of the
  Hodge components it contains.
* `TauCeti.Hodge.HodgeStructureOn.conjF_eq_iSup_piece`: a conjugate filtration step is the
  supremum of the Hodge components it contains.
* `TauCeti.Hodge.HodgeStructureOn.piece_iSupIndep`: the Hodge components are independent.
* `TauCeti.Hodge.HodgeStructureOn.isInternal_piece`: the Hodge components form an internal direct
  sum of the ambient complex vector space.
-/

public section

namespace TauCeti.Hodge

universe u

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]
variable {ω : Conjugation W} {n : ℤ}

/-- A filtration step is the sum of its Hodge component and the next filtration step. -/
theorem F_eq_piece_sup_succ (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.F p = hs.piece p ⊔ hs.F (p + 1) := by
  have hnext : IsCompl (hs.F (p + 1)) (hs.conjF (n - p)) := by
    have hindex : n + 1 - (p + 1) = n - p := by omega
    simpa only [hindex] using hs.isCompl_F_conjF (p + 1)
  have hle : hs.F (p + 1) ≤ hs.F p := hs.F_antitone (by omega)
  calc
    hs.F p = ⊤ ⊓ hs.F p := (top_inf_eq _).symm
    _ = (hs.F (p + 1) ⊔ hs.conjF (n - p)) ⊓ hs.F p := by rw [hnext.sup_eq_top]
    _ = hs.F (p + 1) ⊔ hs.conjF (n - p) ⊓ hs.F p :=
      sup_inf_assoc_of_le _ hle
    _ = hs.piece p ⊔ hs.F (p + 1) := by
      rw [hs.piece_def, inf_comm, sup_comm]

/-- The `p`-th Hodge component is complementary to the sum of the adjacent conjugate and ordinary
filtration steps. This complement contains every Hodge component of degree different from `p`. -/
theorem isCompl_piece_conjF_sup_F (hs : HodgeStructureOn W ω n) (p : ℤ) :
    IsCompl (hs.piece p) (hs.conjF (n + 1 - p) ⊔ hs.F (p + 1)) := by
  have hnext : IsCompl (hs.F (p + 1)) (hs.conjF (n - p)) := by
    have hindex : n + 1 - (p + 1) = n - p := by omega
    simpa only [hindex] using hs.isCompl_F_conjF (p + 1)
  have hdisjoint : Disjoint (hs.piece p) (hs.F (p + 1)) :=
    (hnext.disjoint.mono_right (hs.piece_le_conjF p)).symm
  have hcomp : IsCompl (hs.piece p ⊔ hs.F (p + 1)) (hs.conjF (n + 1 - p)) := by
    rw [← hs.F_eq_piece_sup_succ p]
    exact hs.isCompl_F_conjF p
  simpa only [sup_comm] using hdisjoint.isCompl_sup_right_of_isCompl_sup_left hcomp

/-- Every Hodge component whose degree is smaller than `p` lies in the conjugate filtration step
complementary to `F p`. -/
theorem piece_le_conjF_of_lt (hs : HodgeStructureOn W ω n) {p q : ℤ} (hqp : q < p) :
    hs.piece q ≤ hs.conjF (n + 1 - p) :=
  (hs.piece_le_conjF q).trans (hs.conjF_antitone (by omega))

/-- Every Hodge component whose degree is larger than `p` lies in the filtration step
complementary to `conjF (n - p)`. -/
theorem piece_le_F_succ_of_lt (hs : HodgeStructureOn W ω n) {p q : ℤ} (hpq : p < q) :
    hs.piece q ≤ hs.F (p + 1) :=
  (hs.piece_le_F q).trans (hs.F_antitone (by omega))

/-- The Hodge components of an opposed filtration are independent. -/
theorem piece_iSupIndep (hs : HodgeStructureOn W ω n) : iSupIndep hs.piece := by
  intro p
  refine (hs.isCompl_piece_conjF_sup_F p).disjoint.mono_right ?_
  refine iSup_le fun q ↦ iSup_le fun hqp ↦ ?_
  obtain hqp | hpq := lt_or_gt_of_ne hqp
  · exact (hs.piece_le_conjF_of_lt hqp).trans le_sup_left
  · exact (hs.piece_le_F_succ_of_lt hpq).trans le_sup_right

/-- Every Hodge filtration step is the supremum of the Hodge components in at least that degree:
`F p = ⨆ q ≥ p, H^{q,n-q}`. -/
theorem F_eq_iSup_piece (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.F p = ⨆ q, ⨆ (_ : p ≤ q), hs.piece q := by
  apply le_antisymm
  · obtain ⟨b, hb⟩ := hs.F_bot
    let c := max p b
    have hpc : p ≤ c := le_max_left _ _
    have hc : hs.F c = ⊥ := hs.F_eq_bot_of_le hb (le_max_right _ _)
    exact Int.leInductionDown (m := c)
      (motive := fun q _ ↦ hs.F q ≤ ⨆ r, ⨆ (_ : q ≤ r), hs.piece r)
      (by rw [hc]; exact bot_le)
      (fun q _ hq ↦ by
        rw [hs.F_eq_piece_sup_succ (q - 1)]
        refine sup_le (le_iSup₂_of_le (q - 1) le_rfl le_rfl) ?_
        have htail : (⨆ r, ⨆ (_ : q ≤ r), hs.piece r) ≤
            ⨆ r, ⨆ (_ : q - 1 ≤ r), hs.piece r := by
          exact iSup₂_le fun r hqr ↦ le_iSup₂_of_le r (by omega) le_rfl
        simpa only [sub_add_cancel] using hq.trans htail)
      p hpc
  · refine iSup_le fun q ↦ iSup_le fun hpq ↦ ?_
    exact (hs.piece_le_F q).trans (hs.F_antitone hpq)

/-- Every conjugate Hodge filtration step is the supremum of the Hodge components in at most the
complementary degree: `conjF p = ⨆ q ≤ n - p, H^{q,n-q}`. -/
theorem conjF_eq_iSup_piece (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.conjF p = ⨆ q, ⨆ (_ : q ≤ n - p), hs.piece q := by
  rw [hs.conjF_def, hs.F_eq_iSup_piece p]
  simp only [Submodule.map_iSup, hs.conj_piece]
  refine le_antisymm (iSup₂_le fun q _ ↦ le_iSup₂_of_le (n - q) (by omega) le_rfl)
    (iSup₂_le fun q _ ↦ le_iSup₂_of_le (n - q) (by omega) (le_of_eq (by rw [sub_sub_cancel])))

/-- The supremum of all Hodge components is the whole ambient complex vector space. -/
theorem iSup_piece_eq_top (hs : HodgeStructureOn W ω n) : ⨆ p, hs.piece p = ⊤ := by
  obtain ⟨p, hp⟩ := hs.F_top
  apply top_unique
  rw [← hp, hs.F_eq_iSup_piece p]
  exact iSup₂_le fun q _ ↦ le_iSup hs.piece q

/-- **The Hodge decomposition.** The Hodge components `H^{p,n-p}` form an internal direct sum of
the ambient complex vector space. -/
theorem isInternal_piece (hs : HodgeStructureOn W ω n) : DirectSum.IsInternal hs.piece := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    hs.piece_iSupIndep hs.iSup_piece_eq_top

end HodgeStructureOn

end TauCeti.Hodge
