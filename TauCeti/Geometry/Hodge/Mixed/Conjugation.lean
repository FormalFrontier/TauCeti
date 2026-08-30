/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Decomposition
public import Mathlib.LinearAlgebra.SModEq.Basic

/-!
# Conjugation of Deligne's bigrading

For a mixed Hodge structure, complex conjugation exchanges the Deligne bigrading pieces only up
to terms of lower weight. This file proves the first, weight-filtered form of that triangularity:

`conj I^{p,q} + W_{p+q-2} = I^{q,p} + W_{p+q-2}`.

The two-step weight bound follows directly from the current API. Deligne's closed formula puts a
vector of `conj I^{p,q}` in `F^q` modulo `W_{p+q-2}`, while it lies in `conj F^p` exactly. A
representative of the same class in `I^{q,p}` initially agrees only modulo `W_{p+q-1}`. On the
intervening graded piece, however, their difference lies in the opposed steps `F^q` and
`conj F^p` of a pure Hodge
structure of weight `p+q-1`, so it vanishes and the difference drops one step further.

The full Deligne relation refines the error term from `W_{p+q-2}` to the sum of the pieces
`I^{r,s}` with `r < q` and `s < p`.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting_le_sup_WC`: conjugating
  `I^{p,q}` lands in `I^{q,p} + W_{p+q-2}`.
* `TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting_sup_WC`: the symmetric
  equality modulo `W_{p+q-2}`.
* `TauCeti.Hodge.MixedHodgeStructure.exists_mem_deligneSplitting_smodEq_latticeConj`: the
  elementwise modular-congruence form.

## References

Deligne, *Théorie de Hodge II*, 1.2.10; Peters--Steenbrink, *Mixed Hodge Structures*,
Lemma-Definition 3.4. This is the first conjugation comparison in Layer L2 of the Hodge structures
roadmap.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}

namespace MixedHodgeStructure

variable (mhs : MixedHodgeStructure hℚ hℂ)

/-- An element of a weight step lying in opposed filtration steps modulo the preceding weight step
already lies in that preceding step. -/
private theorem mem_WC_sub_one_of_mem_F_sup_and_mem_conjF_sup (k p : ℤ) {x : Vℂ}
    (hxW : x ∈ mhs.WC k) (hxF : x ∈ mhs.F p ⊔ mhs.WC (k - 1))
    (hxConj : x ∈ mhs.conjF (k + 1 - p) ⊔ mhs.WC (k - 1)) :
    x ∈ mhs.WC (k - 1) := by
  obtain ⟨f, hf, wf, hwf, hfw⟩ := Submodule.mem_sup.1 hxF
  obtain ⟨c, hc, wc, hwc, hcw⟩ := Submodule.mem_sup.1 hxConj
  have hfW : f ∈ mhs.WC k := by
    have hfd : f = x - wf := by rw [← hfw]; abel
    rw [hfd]
    exact Submodule.sub_mem _ hxW (mhs.WC_monotone (by omega) hwf)
  have hcW : c ∈ mhs.WC k := by
    have hcd : c = x - wc := by rw [← hcw]; abel
    rw [hcd]
    exact Submodule.sub_mem _ hxW (mhs.WC_monotone (by omega) hwc)
  have hfc : f - c ∈ mhs.WC (k - 1) := by
    have hfc' : f - c = wc - wf := by
      calc
        f - c = (f + wf) - (c + wc) + (wc - wf) := by abel
        _ = wc - wf := by rw [hfw, hcw, sub_self, zero_add]
    rw [hfc']
    exact Submodule.sub_mem _ hwc hwf
  have hmk : (Submodule.Quotient.mk (⟨f, hfW⟩ : mhs.WC k) :
        weightGradedComplex mhs.WC k) = Submodule.Quotient.mk ⟨c, hcW⟩ :=
    (weightGradedComplex_mk_eq_mk_iff mhs.WC k _ _).2 hfc
  have hF := mhs.mk_mem_complexGradedHodgeStructure_F k p ⟨f, hfW⟩ hf
  have hConj := mhs.mk_mem_complexGradedHodgeStructure_conjF k (k + 1 - p) ⟨c, hcW⟩ hc
  rw [← hmk] at hConj
  have hzero := ((mhs.complexGradedHodgeStructure k).isCompl_F_conjF p).disjoint.le_bot
    ⟨hF, hConj⟩
  rw [Submodule.mem_bot] at hzero
  have hfLower : f ∈ mhs.WC (k - 1) :=
    (weightGradedComplex_mk_eq_zero_iff mhs.WC k ⟨f, hfW⟩).1 hzero
  rw [← hfw]
  exact Submodule.add_mem _ hfLower hwf

/-- Conjugating `I^{p,q}` lands in the swapped Deligne piece modulo `W_{p+q-2}`. -/
theorem map_latticeConj_deligneSplitting_le_sup_WC (p q : ℤ) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) ≤
      mhs.deligneSplitting q p ⊔ mhs.WC (p + q - 2) := by
  intro x hx
  rw [mhs.map_latticeConj_deligneSplitting p q] at hx
  obtain ⟨hxConj, hxW, hxSecond⟩ := by
    simpa only [Submodule.mem_inf, and_assoc] using hx
  obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.1 hxSecond
  have htW : t ∈ mhs.WC (p + q - 2) := by
    exact (iSup_le fun j ↦ inf_le_right.trans (mhs.WC_monotone (by omega))) ht
  have haW : a ∈ mhs.WC (p + q) := ha.2
  have hxW' : x ∈ mhs.WC (p + q) := hxW
  have hclassA : Submodule.Quotient.mk (⟨a, haW⟩ : mhs.WC (p + q)) ∈
      (mhs.complexGradedHodgeStructure (p + q)).piece q := by
    refine mhs.mk_mem_complexGradedHodgeStructure_piece (p + q) q ⟨a, haW⟩ ha.1 ?_
    have hax : a = x - t := by rw [← hat]; abel
    have haConj : a ∈ mhs.conjF p ⊔ mhs.WC (p + q - 1) := by
      rw [hax]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hxConj)
        (Submodule.mem_sup_right (mhs.WC_monotone (by omega) htW))
    have hindex : p + q - q = p := by ring
    simpa only [mhs.conjF_def, hindex] using haConj
  have hmap := mhs.map_deligneSplitting_eq_piece q p
  rw [add_comm q p] at hmap
  rw [← hmap] at hclassA
  obtain ⟨y, hyI, hyClass⟩ := hclassA
  have hyIAmbient : (y : Vℂ) ∈ mhs.deligneSplitting q p := hyI
  have hyW : (y : Vℂ) ∈ mhs.WC (p + q) := y.2
  have hyConj : (y : Vℂ) ∈ mhs.conjF p ⊔ mhs.WC (p + q - 2) := by
    have h := mhs.deligneSplitting_le_conjF_sup_WC q p hyIAmbient
    simpa only [add_comm q p] using h
  have hdiffW : x - (y : Vℂ) ∈ mhs.WC (p + q - 1) := by
    rw [Submodule.mkQ_apply] at hyClass
    have hxa : x - a = t := by rw [← hat]; abel
    have hxaW : x - a ∈ mhs.WC (p + q - 1) := by
      rw [hxa]
      exact mhs.WC_monotone (by omega) htW
    have hxy : (Submodule.Quotient.mk (⟨x, hxW'⟩ : mhs.WC (p + q)) :
          weightGradedComplex mhs.WC (p + q)) =
        Submodule.Quotient.mk ⟨(y : Vℂ), hyW⟩ := by
      have hxaClass : (Submodule.Quotient.mk (⟨x, hxW'⟩ : mhs.WC (p + q)) :
            weightGradedComplex mhs.WC (p + q)) = Submodule.Quotient.mk ⟨a, haW⟩ :=
        (weightGradedComplex_mk_eq_mk_iff mhs.WC (p + q) _ _).2 hxaW
      exact hxaClass.trans hyClass.symm
    exact (weightGradedComplex_mk_eq_mk_iff mhs.WC (p + q) ⟨x, hxW'⟩
      ⟨(y : Vℂ), hyW⟩).1 hxy
  have hdiffF : x - (y : Vℂ) ∈ mhs.F q ⊔ mhs.WC (p + q - 2) := by
    have hxmem : x ∈ mhs.F q ⊔ mhs.WC (p + q - 2) := by
      rw [← hat]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha.1) (Submodule.mem_sup_right htW)
    exact Submodule.sub_mem _ hxmem
      (Submodule.mem_sup_left (mhs.deligneSplitting_le_F q p hyIAmbient))
  have hdiffConj : x - (y : Vℂ) ∈ mhs.conjF p ⊔ mhs.WC (p + q - 2) :=
    Submodule.sub_mem _ (Submodule.mem_sup_left hxConj) hyConj
  have hdrop : x - (y : Vℂ) ∈ mhs.WC (p + q - 2) := by
    have hstep : p + q - 1 - 1 = p + q - 2 := by ring
    have hconjIndex : p + q - 1 + 1 - q = p := by ring
    simpa only [hstep] using mhs.mem_WC_sub_one_of_mem_F_sup_and_mem_conjF_sup
      (p + q - 1) q hdiffW (by simpa only [hstep] using hdiffF)
        (by simpa only [hstep, hconjIndex] using hdiffConj)
  convert Submodule.add_mem_sup hyIAmbient hdrop using 1
  all_goals abel

/-- The swapped Deligne piece lands in the conjugate of `I^{p,q}` modulo `W_{p+q-2}`.

This is the reverse containment to
`TauCeti.Hodge.MixedHodgeStructure.map_latticeConj_deligneSplitting_le_sup_WC`. It follows by
applying that containment with the indices exchanged and conjugating once more. -/
theorem deligneSplitting_le_map_latticeConj_sup_WC (p q : ℤ) :
    mhs.deligneSplitting q p ≤
      (mhs.deligneSplitting p q).map (latticeConj hℂ) ⊔ mhs.WC (p + q - 2) := by
  intro x hx
  have hxMap : latticeConj hℂ x ∈ (mhs.deligneSplitting q p).map (latticeConj hℂ) :=
    Submodule.mem_map_of_mem hx
  have hswap := mhs.map_latticeConj_deligneSplitting_le_sup_WC q p hxMap
  have h : latticeConj hℂ x ∈ mhs.deligneSplitting p q ⊔ mhs.WC (p + q - 2) := by
    simpa only [add_comm q p] using hswap
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
  have hconjA : latticeConj hℂ a ∈
      (mhs.deligneSplitting p q).map (latticeConj hℂ) :=
    Submodule.mem_map_of_mem ha
  have hconjB : latticeConj hℂ b ∈ mhs.WC (p + q - 2) := by
    rw [← mhs.WC_conj (p + q - 2)]
    exact Submodule.mem_map_of_mem hb
  have hsum : latticeConj hℂ a + latticeConj hℂ b = x := by
    rw [← map_add, hab, latticeConj_apply_apply]
  rw [← hsum]
  exact Submodule.add_mem_sup hconjA hconjB

/-- **Conjugation exchanges Deligne's bigrading modulo two lower weight steps:**

`conj I^{p,q} + W_{p+q-2} = I^{q,p} + W_{p+q-2}`.

The two containments are symmetric because lattice conjugation is an involution and preserves the
weight filtration. -/
theorem map_latticeConj_deligneSplitting_sup_WC (p q : ℤ) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) ⊔ mhs.WC (p + q - 2) =
      mhs.deligneSplitting q p ⊔ mhs.WC (p + q - 2) := by
  apply le_antisymm
  · exact sup_le (mhs.map_latticeConj_deligneSplitting_le_sup_WC p q) le_sup_right
  · exact sup_le (mhs.deligneSplitting_le_map_latticeConj_sup_WC p q) le_sup_right

/-- If the weight filtration already vanishes two steps below `p+q`, conjugation exchanges the
Deligne pieces `I^{p,q}` and `I^{q,p}` exactly. -/
theorem map_latticeConj_deligneSplitting_eq_of_WC_eq_bot {p q : ℤ}
    (hW : mhs.WC (p + q - 2) = ⊥) :
    (mhs.deligneSplitting p q).map (latticeConj hℂ) = mhs.deligneSplitting q p := by
  simpa only [hW, sup_bot_eq] using mhs.map_latticeConj_deligneSplitting_sup_WC p q

/-- The images of `conj I^{p,q}` and `I^{q,p}` in the quotient by `W_{p+q-2}` agree. -/
theorem map_mkQ_map_latticeConj_deligneSplitting_eq (p q : ℤ) :
    ((mhs.deligneSplitting p q).map (latticeConj hℂ)).map
        (mhs.WC (p + q - 2)).mkQ =
      (mhs.deligneSplitting q p).map (mhs.WC (p + q - 2)).mkQ := by
  apply Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective _)
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ]
  simpa only [sup_comm] using mhs.map_latticeConj_deligneSplitting_sup_WC p q

/-- Elementwise form of conjugation symmetry modulo `W_{p+q-2}`: every vector in `I^{p,q}` has
a conjugate congruent to a vector in `I^{q,p}`. -/
theorem exists_mem_deligneSplitting_smodEq_latticeConj (p q : ℤ) {x : Vℂ}
    (hx : x ∈ mhs.deligneSplitting p q) :
    ∃ y ∈ mhs.deligneSplitting q p,
      latticeConj hℂ x ≡ y [SMOD (mhs.WC (p + q - 2))] := by
  have hxMap : latticeConj hℂ x ∈
      (mhs.deligneSplitting p q).map (latticeConj hℂ) :=
    Submodule.mem_map_of_mem hx
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Submodule.mem_sup.1 (mhs.map_latticeConj_deligneSplitting_le_sup_WC p q hxMap)
  refine ⟨y, hy, SModEq.sub_mem.2 ?_⟩
  have hdiff : latticeConj hℂ x - y = z := by rw [← hyz]; abel
  rwa [hdiff]

end MixedHodgeStructure

end TauCeti.Hodge
