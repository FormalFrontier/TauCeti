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
* `TauCeti.Hodge.HodgeStructureOn.decomposition`: that direct sum as a linear equivalence.
* `TauCeti.Hodge.HodgeStructureOn.piece_induction_on`: induction along the Hodge decomposition.
* `TauCeti.Hodge.HodgeStructureOn.proj`: the projection onto a Hodge component along that
  decomposition.
-/

public section

namespace TauCeti.Hodge

open scoped DirectSum

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

/-- The Hodge decomposition as a linear equivalence: the ambient complex vector space is the
direct sum of its Hodge components. -/
noncomputable def decomposition (hs : HodgeStructureOn W ω n) :
    W ≃ₗ[ℂ] ⨁ p, hs.piece p :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap hs.piece) hs.isInternal_piece).symm

/-- The inverse of the Hodge decomposition sums up the Hodge components. -/
@[simp]
theorem decomposition_symm_apply (hs : HodgeStructureOn W ω n) (x : ⨁ p, hs.piece p) :
    hs.decomposition.symm x = DirectSum.coeLinearMap hs.piece x := by
  rw [decomposition, LinearEquiv.symm_symm]
  rfl

/-- A vector lying in a single Hodge component decomposes as that one component. -/
theorem decomposition_apply_of_mem (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W}
    (hx : x ∈ hs.piece p) :
    hs.decomposition x = DirectSum.lof ℂ ℤ (fun q ↦ hs.piece q) p ⟨x, hx⟩ :=
  hs.decomposition.symm.injective (by simp)

/-- Induction along the Hodge decomposition: a property that holds at zero, is stable under
addition, and holds on every Hodge component holds everywhere. -/
theorem piece_induction_on (hs : HodgeStructureOn W ω n) {motive : W → Prop} (x : W)
    (mem : ∀ p, ∀ y ∈ hs.piece p, motive y) (zero : motive 0)
    (add : ∀ y z, motive y → motive z → motive (y + z)) : motive x := by
  have hx : x ∈ ⨆ p, hs.piece p := by
    rw [hs.iSup_piece_eq_top]
    exact Submodule.mem_top
  exact Submodule.iSup_induction (motive := motive) hs.piece hx mem zero add

/-- Two complex-linear maps out of the ambient space that agree on every Hodge component are
equal. -/
theorem linearMap_ext_of_piece {N : Type*} [AddCommGroup N] [Module ℂ N]
    (hs : HodgeStructureOn W ω n) {f g : W →ₗ[ℂ] N}
    (h : ∀ p, ∀ x ∈ hs.piece p, f x = g x) : f = g := by
  ext x
  refine hs.piece_induction_on x h (by simp) fun y z hy hz ↦ ?_
  rw [map_add, map_add, hy, hz]

/-! ### The Hodge projections -/

/-- The projection of the ambient complex vector space onto the Hodge component `H^{p, n-p}`
along the Hodge decomposition. -/
noncomputable def proj (hs : HodgeStructureOn W ω n) (p : ℤ) : W →ₗ[ℂ] W :=
  (hs.piece p).subtype ∘ₗ DirectSum.component ℂ ℤ (fun q ↦ hs.piece q) p ∘ₗ
    hs.decomposition.toLinearMap

theorem proj_apply (hs : HodgeStructureOn W ω n) (p : ℤ) (x : W) :
    hs.proj p x = (hs.decomposition x p : W) :=
  (rfl)

/-- A Hodge projection lands in the corresponding Hodge component. -/
theorem proj_mem (hs : HodgeStructureOn W ω n) (p : ℤ) (x : W) : hs.proj p x ∈ hs.piece p :=
  (hs.decomposition x p).2

/-- The Hodge projection of degree `p` fixes the Hodge component of degree `p`. -/
@[simp]
theorem proj_apply_of_mem (hs : HodgeStructureOn W ω n) {p : ℤ} {x : W} (hx : x ∈ hs.piece p) :
    hs.proj p x = x := by
  rw [proj_apply, hs.decomposition_apply_of_mem hx]
  simp

/-- The Hodge projection of degree `p` annihilates every other Hodge component. -/
theorem proj_apply_eq_zero_of_mem_of_ne (hs : HodgeStructureOn W ω n) {p q : ℤ} {x : W}
    (hx : x ∈ hs.piece q) (hqp : q ≠ p) : hs.proj p x = 0 := by
  rw [proj_apply, hs.decomposition_apply_of_mem hx, DirectSum.lof_eq_of,
    DirectSum.of_eq_of_ne _ _ _ hqp.symm]
  rfl

/-- A vector all of whose Hodge projections vanish is zero. -/
theorem eq_zero_of_proj_eq_zero (hs : HodgeStructureOn W ω n) {x : W}
    (h : ∀ p, hs.proj p x = 0) : x = 0 := by
  refine hs.decomposition.injective ?_
  rw [map_zero]
  ext p
  exact congrArg Subtype.val (Subtype.ext (h p) : hs.decomposition x p = 0)

/-- A vector lies in a supremum of submodules as soon as each of its Hodge projections does. -/
theorem mem_iSup_of_proj_mem (hs : HodgeStructureOn W ω n) {S : ℤ → Submodule ℂ W} {x : W}
    (h : ∀ p, hs.proj p x ∈ S p) : x ∈ ⨆ p, S p := by
  classical
  have hx : x = ∑ p ∈ (hs.decomposition x).support, hs.proj p x := by
    conv_lhs => rw [← hs.decomposition.symm_apply_apply x]
    rw [decomposition_symm_apply, DirectSum.coeLinearMap_eq_dfinsuppSum]
    rfl
  rw [hx]
  exact Submodule.sum_mem _ fun p _ ↦ Submodule.mem_iSup_of_mem p (h p)

/-- A submodule spanned by its intersections with the Hodge components contains the Hodge
projections of each of its vectors. -/
theorem proj_mem_of_le_iSup_inf (hs : HodgeStructureOn W ω n) {S : Submodule ℂ W}
    (hS : S ≤ ⨆ p, S ⊓ hs.piece p) {x : W} (hx : x ∈ S) (p : ℤ) : hs.proj p x ∈ S := by
  refine Submodule.iSup_induction (motive := fun y ↦ ∀ q, hs.proj q y ∈ S) _ (hS hx)
    (fun q y hy r ↦ ?_) (fun q ↦ by simp) (fun y z hy hz q ↦ ?_) p
  · rcases eq_or_ne q r with rfl | hqr
    · rw [hs.proj_apply_of_mem hy.2]
      exact hy.1
    · rw [hs.proj_apply_eq_zero_of_mem_of_ne hy.2 hqr]
      exact S.zero_mem
  · rw [map_add]
    exact S.add_mem (hy q) (hz q)

end HodgeStructureOn

end TauCeti.Hodge
