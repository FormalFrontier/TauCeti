/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import TauCeti.Combinatorics.Young.Corner
public import TauCeti.Combinatorics.Young.StandardTableau.Basic

/-!
# The corner recursion for standard Young tableaux

The largest label of a standard Young tableau of shape `μ` sits at a corner of `μ`
(`TauCeti.StandardYoungTableau.isCorner_maxCell`), and deleting that cell leaves a standard Young
tableau of the smaller shape.  This is a bijection, and summing it over the corners gives the
**corner recursion**

`standardCount μ = ∑ c ∈ corners μ, standardCount (erase μ c)`

for a nonempty diagram `μ` (`TauCeti.standardCount_eq_sum_corners`).  It is the recursion the
hook-length formula is proved by, and the one that makes `standardCount` computable from the shape
alone.

The bijection is stated fibrewise, as an equivalence between the tableaux whose largest label sits
at a *given* corner `c` and the tableaux of shape `erase μ c`, so that no type in this file depends
on a tableau and no transport along an equality of shapes is needed; that is why
`TauCeti.StandardYoungTableau.restrict` takes the corner and the equation naming it as parameters
rather than reading them off its argument.

## Main definitions

* `TauCeti.StandardYoungTableau.maxCell`: the cell carrying the largest label.
* `TauCeti.StandardYoungTableau.restrict`: delete the corner carrying the largest label.
* `TauCeti.StandardYoungTableau.extend`: the inverse, labelling a corner with the largest label.
* `TauCeti.StandardYoungTableau.cornerFiberEquiv`: the two as an equivalence.

## Main results

* `TauCeti.StandardYoungTableau.isCorner_maxCell`: the largest label of a standard Young tableau
  sits at a corner.
* `TauCeti.standardCount_eq_sum_corners`: the corner recursion.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10, where the corner recursion opens
  the proof of the hook-length formula.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose `hookLengthFormula` milestone is the induction this recursion drives.
-/

public section

namespace TauCeti

namespace StandardYoungTableau

variable {μ : YoungDiagram} {c : ℕ × ℕ}

/-! ### The cell carrying the largest label -/

/-- The cell of a standard Young tableau of a nonempty shape that carries the largest label,
`μ.card - 1`. -/
def maxCell (hμ : 0 < μ.card) (T : StandardYoungTableau μ) : ℕ × ℕ :=
  (T.toTableau.symm ⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩ : ↥μ.cells)

theorem maxCell_mem (hμ : 0 < μ.card) (T : StandardYoungTableau μ) : maxCell hμ T ∈ μ :=
  (T.toTableau.symm ⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩).2

/-- The label at `TauCeti.StandardYoungTableau.maxCell` is the largest one. -/
theorem apply_maxCell (hμ : 0 < μ.card) (T : StandardYoungTableau μ) :
    (T ⟨maxCell hμ T, maxCell_mem hμ T⟩).val + 1 = μ.card := by
  have h : T ⟨maxCell hμ T, maxCell_mem hμ T⟩ = ⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩ :=
    T.toTableau.apply_symm_apply _
  have hval : (⟨μ.card - 1, Nat.sub_lt hμ Nat.one_pos⟩ : Fin μ.card).val = μ.card - 1 := rfl
  rw [h]
  omega

/-- **The largest label of a standard Young tableau sits at a corner.**  Neither the cell to its
right nor the cell below it can be in the diagram, since either would carry a strictly larger
label. -/
theorem isCorner_maxCell (hμ : 0 < μ.card) (T : StandardYoungTableau μ) :
    YoungDiagram.IsCorner μ (maxCell hμ T) := by
  have hmax := apply_maxCell hμ T
  refine (YoungDiagram.isCorner_def μ _).mpr ⟨maxCell_mem hμ T, fun hmem => ?_, fun hmem => ?_⟩
  · have hlt : (T ⟨maxCell hμ T, maxCell_mem hμ T⟩).val
        < (T ⟨((maxCell hμ T).1, (maxCell hμ T).2 + 1), hmem⟩).val :=
      T.row_strict (Nat.lt_succ_self _) hmem
    have := (T ⟨((maxCell hμ T).1, (maxCell hμ T).2 + 1), hmem⟩).isLt
    omega
  · have hlt : (T ⟨maxCell hμ T, maxCell_mem hμ T⟩).val
        < (T ⟨((maxCell hμ T).1 + 1, (maxCell hμ T).2), hmem⟩).val :=
      T.col_strict (Nat.lt_succ_self _) hmem
    have := (T ⟨((maxCell hμ T).1 + 1, (maxCell hμ T).2), hmem⟩).isLt
    omega

/-- A cell carries the largest label exactly when it is the cell
`TauCeti.StandardYoungTableau.maxCell`. -/
theorem maxCell_eq_iff (hμ : 0 < μ.card) (T : StandardYoungTableau μ) (hc : c ∈ μ) :
    maxCell hμ T = c ↔ (T ⟨c, hc⟩).val + 1 = μ.card := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact apply_maxCell hμ T
  · have hval : T ⟨c, hc⟩ = T ⟨maxCell hμ T, maxCell_mem hμ T⟩ :=
      Fin.ext (by have := apply_maxCell hμ T; omega)
    have hcm : c = maxCell hμ T := congrArg Subtype.val (T.injective hval)
    exact hcm.symm

/-! ### Deleting the corner carrying the largest label -/

private theorem restrict_lt (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) (d : ↥(YoungDiagram.erase μ c).cells) :
    (T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val < (YoungDiagram.erase μ c).card := by
  have hd : d.1 ∈ μ := YoungDiagram.mem_of_mem_erase d.2
  have hcard := hc.card_erase
  have hlt := (T ⟨d.1, hd⟩).isLt
  rcases Nat.lt_or_ge (T ⟨d.1, hd⟩).val (YoungDiagram.erase μ c).card with h | h
  · exact h
  · have hval : T ⟨d.1, hd⟩ = T ⟨c, hc.mem⟩ := Fin.ext (by omega)
    have hdc : d.1 = c := congrArg Subtype.val (T.injective hval)
    exact absurd hdc (hc.mem_erase_iff.mp d.2).2

private def restrictFun (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) :
    ↥(YoungDiagram.erase μ c).cells → Fin (YoungDiagram.erase μ c).card :=
  fun d => ⟨(T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val, restrict_lt hc T hT d⟩

private theorem restrictFun_bijective (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau μ) (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) :
    Function.Bijective (restrictFun hc T hT) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun d e h => ?_, by simp⟩
  have hv : (T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val
      = (T ⟨e.1, YoungDiagram.mem_of_mem_erase e.2⟩).val := by
    have hval := congrArg Fin.val h
    exact hval
  refine Subtype.ext ?_
  simpa using T.injective (Fin.ext hv)

/-- **Deleting the corner carrying the largest label** from a standard Young tableau.  The corner
`c` and the fact that it carries the largest label are parameters rather than being read off `T`,
so that the shape of the result does not depend on `T`. -/
noncomputable def restrict (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) :
    StandardYoungTableau (YoungDiagram.erase μ c) where
  toTableau := Equiv.ofBijective _ (restrictFun_bijective hc T hT)
  row_strict' h hcell := T.row_strict h (YoungDiagram.mem_of_mem_erase hcell)
  col_strict' h hcell := T.col_strict h (YoungDiagram.mem_of_mem_erase hcell)

@[simp]
theorem restrict_apply_val (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) (d : ↥(YoungDiagram.erase μ c).cells) :
    (restrict hc T hT d).val = (T ⟨d.1, YoungDiagram.mem_of_mem_erase d.2⟩).val :=
  (rfl)

/-! ### Labelling a corner with the largest label -/

private theorem extend_lt (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥(YoungDiagram.erase μ c).cells) :
    (T d).val < μ.card := by
  have := (T d).isLt
  have := hc.card_erase
  omega

private def extendFun (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) : ↥μ.cells → Fin μ.card :=
  fun d =>
    if h : d.1 = c then ⟨μ.card - 1, Nat.sub_lt hc.card_pos Nat.one_pos⟩
    else ⟨(T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, h⟩⟩).val, extend_lt hc T _⟩

private theorem extendFun_apply_of_eq (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 = c) :
    (extendFun hc T d).val = μ.card - 1 := by
  simp only [extendFun, dite_eq_left h]

private theorem extendFun_apply_of_ne (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 ≠ c) :
    (extendFun hc T d).val = (T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, h⟩⟩).val := by
  simp only [extendFun, dite_eq_right h]

private theorem extendFun_bijective (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    Function.Bijective (extendFun hc T) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun d e h => ?_, by simp⟩
  have hval := congrArg Fin.val h
  have hcard := hc.card_erase
  by_cases hd : d.1 = c <;> by_cases he : e.1 = c
  · exact Subtype.ext (hd.trans he.symm)
  · rw [extendFun_apply_of_eq hc T d hd, extendFun_apply_of_ne hc T e he] at hval
    have := (T ⟨e.1, hc.mem_erase_iff.mpr ⟨e.2, he⟩⟩).isLt
    omega
  · rw [extendFun_apply_of_ne hc T d hd, extendFun_apply_of_eq hc T e he] at hval
    have := (T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, hd⟩⟩).isLt
    omega
  · rw [extendFun_apply_of_ne hc T d hd, extendFun_apply_of_ne hc T e he] at hval
    have h' : T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, hd⟩⟩
        = T ⟨e.1, hc.mem_erase_iff.mpr ⟨e.2, he⟩⟩ := Fin.ext hval
    refine Subtype.ext ?_
    simpa using T.injective h'

private theorem extendFun_row (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) {i j₁ j₂ : ℕ} (h : j₁ < j₂)
    (hcell : (i, j₂) ∈ μ) :
    (extendFun hc T ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩).val
      < (extendFun hc T ⟨(i, j₂), hcell⟩).val := by
  have hcard := hc.card_erase
  by_cases h2 : ((i, j₂) : ℕ × ℕ) = c
  · have h1 : ((i, j₁) : ℕ × ℕ) ≠ c := by
      rw [← h2]
      exact fun hh => absurd (congrArg Prod.snd hh) (by omega)
    rw [extendFun_apply_of_eq hc T ⟨(i, j₂), hcell⟩ h2,
      extendFun_apply_of_ne hc T ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ h1]
    have := (T ⟨(i, j₁), hc.mem_erase_iff.mpr ⟨μ.up_left_mem le_rfl h.le hcell, h1⟩⟩).isLt
    omega
  · have h1 : ((i, j₁) : ℕ × ℕ) ≠ c := fun hh => hc.right_notMem (by
      rw [← hh]
      exact μ.up_left_mem le_rfl h hcell)
    rw [extendFun_apply_of_ne hc T ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ h1,
      extendFun_apply_of_ne hc T ⟨(i, j₂), hcell⟩ h2]
    exact T.row_strict h (hc.mem_erase_iff.mpr ⟨hcell, h2⟩)

private theorem extendFun_col (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) {i₁ i₂ j : ℕ} (h : i₁ < i₂)
    (hcell : (i₂, j) ∈ μ) :
    (extendFun hc T ⟨(i₁, j), μ.up_left_mem h.le le_rfl hcell⟩).val
      < (extendFun hc T ⟨(i₂, j), hcell⟩).val := by
  have hcard := hc.card_erase
  by_cases h2 : ((i₂, j) : ℕ × ℕ) = c
  · have h1 : ((i₁, j) : ℕ × ℕ) ≠ c := by
      rw [← h2]
      exact fun hh => absurd (congrArg Prod.fst hh) (by omega)
    rw [extendFun_apply_of_eq hc T ⟨(i₂, j), hcell⟩ h2,
      extendFun_apply_of_ne hc T ⟨(i₁, j), μ.up_left_mem h.le le_rfl hcell⟩ h1]
    have := (T ⟨(i₁, j), hc.mem_erase_iff.mpr ⟨μ.up_left_mem h.le le_rfl hcell, h1⟩⟩).isLt
    omega
  · have h1 : ((i₁, j) : ℕ × ℕ) ≠ c := fun hh => hc.below_notMem (by
      rw [← hh]
      exact μ.up_left_mem h le_rfl hcell)
    rw [extendFun_apply_of_ne hc T ⟨(i₁, j), μ.up_left_mem h.le le_rfl hcell⟩ h1,
      extendFun_apply_of_ne hc T ⟨(i₂, j), hcell⟩ h2]
    exact T.col_strict h (hc.mem_erase_iff.mpr ⟨hcell, h2⟩)

/-- **Restoring a deleted corner**: extend a standard Young tableau of shape `erase μ c` to one of
shape `μ` by giving the corner `c` the largest label. -/
noncomputable def extend (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) : StandardYoungTableau μ where
  toTableau := Equiv.ofBijective _ (extendFun_bijective hc T)
  row_strict' h hcell := extendFun_row hc T h hcell
  col_strict' h hcell := extendFun_col hc T h hcell

@[simp]
theorem extend_apply_val_of_eq (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 = c) :
    (extend hc T d).val = μ.card - 1 :=
  extendFun_apply_of_eq hc T d h

@[simp]
theorem extend_apply_val_of_ne (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (d : ↥μ.cells) (h : d.1 ≠ c) :
    (extend hc T d).val = (T ⟨d.1, hc.mem_erase_iff.mpr ⟨d.2, h⟩⟩).val :=
  extendFun_apply_of_ne hc T d h

/-- The extended tableau does carry its largest label at the restored corner, so it lies in the
fibre that `TauCeti.StandardYoungTableau.restrict` is defined on.

This is deliberately not a `simp` lemma: `TauCeti.StandardYoungTableau.extend_apply_val_of_eq`
rewrites its left-hand side to `μ.card - 1 + 1`, so its statement is not in simp-normal form. -/
theorem extend_apply_self (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    ((extend hc T) ⟨c, hc.mem⟩).val + 1 = μ.card := by
  rw [extend_apply_val_of_eq hc T ⟨c, hc.mem⟩ rfl]
  have := hc.card_pos
  omega

@[simp]
theorem restrict_extend (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    restrict hc (extend hc T) (extend_apply_self hc T) = T := by
  refine DFunLike.ext _ _ fun d => Fin.ext ?_
  rw [restrict_apply_val, extend_apply_val_of_ne hc T _ (hc.mem_erase_iff.mp d.2).2]

@[simp]
theorem extend_restrict (hc : YoungDiagram.IsCorner μ c) (T : StandardYoungTableau μ)
    (hT : (T ⟨c, hc.mem⟩).val + 1 = μ.card) : extend hc (restrict hc T hT) = T := by
  refine DFunLike.ext _ _ fun d => Fin.ext ?_
  by_cases h : d.1 = c
  · have hd : d = ⟨c, hc.mem⟩ := Subtype.ext h
    rw [extend_apply_val_of_eq hc _ d h, hd]
    omega
  · rw [extend_apply_val_of_ne hc _ d h, restrict_apply_val]

/-- **The corner bijection**: the standard Young tableaux of shape `μ` whose largest label sits at
the corner `c` are the standard Young tableaux of shape `erase μ c`. -/
noncomputable def cornerFiberEquiv (hc : YoungDiagram.IsCorner μ c) :
    {T : StandardYoungTableau μ // (T ⟨c, hc.mem⟩).val + 1 = μ.card} ≃
      StandardYoungTableau (YoungDiagram.erase μ c) where
  toFun T := restrict hc T.1 T.2
  invFun T := ⟨extend hc T, extend_apply_self hc T⟩
  left_inv T := Subtype.ext (extend_restrict hc T.1 T.2)
  right_inv T := restrict_extend hc T

private noncomputable def maxCorner (hμ : 0 < μ.card) (T : StandardYoungTableau μ) :
    {c : ℕ × ℕ // c ∈ YoungDiagram.corners μ} :=
  ⟨maxCell hμ T, YoungDiagram.mem_corners.mpr (isCorner_maxCell hμ T)⟩

end StandardYoungTableau

/-- **The corner recursion for standard Young tableaux**: the standard Young tableaux of a nonempty
shape `μ` are counted by their corners, a tableau being recorded by the corner carrying its largest
label together with what is left after deleting that corner. -/
theorem standardCount_eq_sum_corners {μ : YoungDiagram} (hμ : 0 < μ.card) :
    standardCount μ = ∑ c ∈ YoungDiagram.corners μ, standardCount (YoungDiagram.erase μ c) := by
  classical
  have key : ∀ c : {c : ℕ × ℕ // c ∈ YoungDiagram.corners μ},
      Fintype.card {T : StandardYoungTableau μ // StandardYoungTableau.maxCorner hμ T = c}
        = standardCount (YoungDiagram.erase μ c.1) := by
    intro c
    have hc : YoungDiagram.IsCorner μ c.1 := YoungDiagram.mem_corners.mp c.2
    have e : {T : StandardYoungTableau μ // StandardYoungTableau.maxCorner hμ T = c} ≃
        StandardYoungTableau (YoungDiagram.erase μ c.1) :=
      (Equiv.subtypeEquivRight fun T => by
        rw [Subtype.ext_iff]
        exact StandardYoungTableau.maxCell_eq_iff hμ T hc.mem).trans
        (StandardYoungTableau.cornerFiberEquiv hc)
    rw [standardCount_def, Fintype.card_congr e]
  rw [standardCount_def, ← Fintype.card_congr
      (Equiv.sigmaFiberEquiv (StandardYoungTableau.maxCorner hμ)),
    Fintype.card_sigma, ← Finset.sum_coe_sort (YoungDiagram.corners μ)]
  exact Finset.sum_congr rfl fun c _ => key c

end TauCeti
