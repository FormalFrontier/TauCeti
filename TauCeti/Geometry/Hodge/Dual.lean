/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Hodge.Structure

/-!
# The dual of a pure Hodge structure

The dual `V^*` of a pure Hodge structure of weight `n` is a pure Hodge structure of weight `-n`
on the complex dual space: its filtration step at index `p` is the annihilator of the filtration
step of index `1 - p` of the original structure, and its conjugation is the twisted transpose of
the original conjugation, sending a functional `φ` to `v ↦ conj (φ (ω v))`.
The dual pairing then respects Hodge components of complementary indices: the `p`-th component
of the dual pairs nontrivially only against the component of index `-p`, and, when `W` is
finite-dimensional, has the same dimension as the `(-p)`-th component, so dualizing reflects
the table of Hodge numbers.

This is one of the companion constructions of Layer L0 of `TauCetiRoadmap/HodgeStructures/README.md`
(the `⊗`/`Hom`/dual companions), following Peters–Steenbrink, *Mixed Hodge Structures*, §2; it is
the base on which the internal hom of Hodge structures is to be built.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.dual`: the dual pure Hodge structure, of weight `-n`; its
  conjugation is the twisted transpose `TauCeti.Hodge.Conjugation.dual`, and the opposedness of
  its filtration holds since dual annihilators carry complements to complements.
* `TauCeti.Hodge.HodgeStructureOn.dual_F`, `…dual_conjF`: the step of the dual filtration at
  index `p` is the annihilator of the original step `1 - p`, and the conjugate step is the
  annihilator of the original conjugate step `1 - p`.
* `TauCeti.Hodge.HodgeStructureOn.dual_piece`: the components of the dual structure are
  annihilators of sums of complementary filtration steps.
* `TauCeti.Hodge.HodgeStructureOn.finrank_dual_piece`: when `W` is finite-dimensional, the
  dimension of the `p`-th component of the dual equals that of the `(-p)`-th component.
* `TauCeti.Hodge.HodgeStructureOn.apply_eq_zero_of_mem_piece_of_ne`: the dual pairing vanishes
  between components unless their indices are complementary.
-/

public section

namespace TauCeti.Hodge

universe u

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

namespace HodgeStructureOn

variable {ω : Conjugation W} {n : ℤ}

/-- Opposedness of the dual filtration: the annihilators of a complementary pair are
complementary. -/
private theorem isCompl_dual_annihilator (hs : HodgeStructureOn W ω n) (p : ℤ) :
    IsCompl (hs.F (1 - p)).dualAnnihilator
      ((hs.F (1 - (-n + 1 - p))).dualAnnihilator.map
        ω.dual.toEquiv.toLinearMap) := by
  have hidx : 1 - (-n + 1 - p) = n + p := by ring
  have hkey : n + 1 - (1 - p) = n + p := by ring
  have key := hs.isCompl_F_conjF (1 - p)
  rw [hkey] at key
  rw [hidx, Conjugation.map_dualAnnihilator, ← hs.conjF_def]
  exact Subspace.isCompl_dualAnnihilator key

variable (hs : HodgeStructureOn W ω n)

/-- **The dual pure Hodge structure**, of weight `-n`.

Its filtration step at index `p` is the annihilator of the original filtration step of index
`1 - p`; its conjugation is the twisted transpose `TauCeti.Hodge.Conjugation.dual`. Opposedness
of the dual filtration rests on the fact that dual annihilators carry complements to
complements (`Subspace.isCompl_dualAnnihilator`). -/
noncomputable def dual :
    HodgeStructureOn (Module.Dual ℂ W) ω.dual (-n) where
  F p := (hs.F (1 - p)).dualAnnihilator
  F_antitone := fun p q hpq =>
    Submodule.dualAnnihilator_anti (hs.F_antitone (by omega))
  F_top := by
    obtain ⟨q, hq⟩ := hs.F_bot
    refine ⟨1 - q, ?_⟩
    have hq' : 1 - (1 - q) = q := by ring
    rw [hq', hq, Submodule.dualAnnihilator_bot]
  opposed := hs.isCompl_dual_annihilator

/-- The filtration of the dual Hodge structure is made of dual annihilators of steps. -/
@[simp]
theorem dual_F (p : ℤ) :
    (hs.dual).F p = (hs.F (1 - p)).dualAnnihilator :=
  (rfl)

/-- The conjugate of a step of the dual filtration is the annihilator of a conjugate step. -/
@[simp]
theorem dual_conjF (p : ℤ) :
    (hs.dual).conjF p = (hs.conjF (1 - p)).dualAnnihilator := by
  rw [(hs.dual).conjF_def, hs.dual_F, Conjugation.map_dualAnnihilator, ← hs.conjF_def]

/-- A component of the dual Hodge structure is the annihilator of the sum of the two filtration
steps flanking the component of complementary index. -/
@[simp]
theorem dual_piece (p : ℤ) :
    (hs.dual).piece p =
      ((hs.F (1 - p)) ⊔ (hs.conjF (n + 1 + p))).dualAnnihilator := by
  rw [piece_def, hs.dual_F, dual_conjF, ← Submodule.dualAnnihilator_sup_eq]
  have hidx : 1 - (-n - p) = n + 1 + p := by omega
  rw [hidx]

section Dimension

/-- If `B` complements a submodule `C ≤ A`, the part of `A` complementary to `B` together with
`C` fills `A`. -/
private theorem finrank_inf_add_finrank_eq_finrank {A B C : Submodule ℂ W}
    (hcompl : IsCompl C B) (hCA : C ≤ A) [Module.Finite ℂ W] :
    Module.finrank ℂ ↥(A ⊓ B) + Module.finrank ℂ ↥C = Module.finrank ℂ ↥A := by
  have hsup : C ⊔ A ⊓ B = A := by
    refine le_antisymm (sup_le hCA inf_le_left) ?_
    intro x hxA
    have hx' : x ∈ (C ⊔ B : Submodule ℂ W) :=
      (le_of_eq hcompl.codisjoint.eq_top.symm) Submodule.mem_top
    obtain ⟨c, hc, b, hb, hx⟩ := Submodule.mem_sup.1 hx'
    have hm : x - c ∈ A := sub_mem hxA (hCA hc)
    have hxcb : x - c = b := by rw [← hx]; abel
    have hbx : x - c ∈ B := by rw [hxcb]; exact hb
    exact Submodule.mem_sup.mpr ⟨c, hc, x - c, ⟨hm, hbx⟩,
      by rw [hxcb]; exact hx⟩
  have hdisj : Disjoint C (A ⊓ B) :=
    hcompl.disjoint.mono_right inf_le_right
  have key := Submodule.finrank_sup_add_finrank_inf_eq C (A ⊓ B)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero, hsup] at key
  omega

/-- The dimension of the `p`-th component of the dual Hodge structure equals the dimension of
the `(-p)`-th component: dualizing reflects the table of Hodge numbers. -/
theorem finrank_dual_piece [Module.Finite ℂ W] (p : ℤ) :
    Module.finrank ℂ ((hs.dual).piece p) = Module.finrank ℂ (hs.piece (-p)) := by
  have hnpp : n - -p = n + p := by ring
  have hidx1 : n + 1 - (1 - p) = n + p := by ring
  have hidx2 : n + 1 - -p = n + 1 + p := by ring
  have hle : n + p ≤ n + 1 + p := by omega
  rw [dual_piece, piece_def, hnpp, inf_comm]
  have hcomp1 := hs.isCompl_F_conjF (1 - p)
  rw [hidx1] at hcomp1
  have hcomp2 := hs.isCompl_F_conjF (-p)
  rw [hidx2] at hcomp2
  have hd : Disjoint (hs.F (1 - p)) (hs.conjF (n + 1 + p)) :=
    hcomp1.disjoint.mono_right (hs.conjF_antitone hle)
  have hL1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    ((hs.F (1 - p)) ⊔ (hs.conjF (n + 1 + p)))
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (hs.F (1 - p)) (hs.conjF (n + 1 + p))
  rw [hd.eq_bot, finrank_bot, add_zero] at hsup
  have hsum := Submodule.finrank_add_eq_of_isCompl hcomp1
  have hrhs := finrank_inf_add_finrank_eq_finrank hcomp2.symm (hs.conjF_antitone hle)
  omega

end Dimension

/-- A functional in the `p`-th component of the dual vanishes on every component whose index is
not `-p`: the dual pairing pairs the `p`-th component of the dual only against the component of
complementary index. -/
theorem apply_eq_zero_of_mem_piece_of_ne {a p : ℤ}
    {u : W} {φ : Module.Dual ℂ W} (hu : u ∈ hs.piece a) (hφ : φ ∈ (hs.dual).piece p)
    (hne : a ≠ -p) :
    φ u = 0 := by
  simp only [dual_piece, Submodule.mem_dualAnnihilator] at hφ
  have hpair := (mem_piece_iff hs a u).mp hu
  rcases lt_trichotomy a (-p) with hlt | heq | hgt
  · have hlt' : n + 1 + p ≤ n - a := by omega
    exact hφ u (Submodule.mem_sup_right (hs.conjF_antitone hlt' hpair.2))
  · exact absurd heq hne
  · have hle : 1 - p ≤ a := by omega
    exact hφ u (Submodule.mem_sup_left (hs.F_antitone hle hpair.1))

end HodgeStructureOn

end TauCeti.Hodge
