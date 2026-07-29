/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.FunLike.Fintype
public import TauCeti.Combinatorics.Young.YoungDiagram

/-!
# Standard Young tableaux

A standard Young tableau of shape `μ` is a bijective labeling of the cells of `μ` by
`Fin μ.card` that increases strictly from left to right and from top to bottom. This file
defines standard Young tableaux, their finite cardinality `standardCount`, and transposition.

The labels start at zero, following the `Fin μ.card` convention in the Schur--Weyl roadmap.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 1.1.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 0.
* Mathlib's `Mathlib.Combinatorics.Young.YoungDiagram`, for Young diagrams and their
  transposition.
-/

public section

namespace TauCeti

/-- A standard Young tableau of shape `μ` is a bijective labeling of its cells by
`Fin μ.card`, strictly increasing along rows and columns. -/
structure StandardYoungTableau (μ : YoungDiagram) where
  /-- The bijection from cells of the diagram to their labels. -/
  toEquiv : ↥μ.cells ≃ Fin μ.card
  /-- Labels increase strictly from left to right. -/
  row_strict' : ∀ {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ),
    toEquiv ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < toEquiv ⟨(i, j₂), hcell⟩
  /-- Labels increase strictly from top to bottom. -/
  col_strict' : ∀ {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ),
    toEquiv ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < toEquiv ⟨(i₂, j), hcell⟩

namespace StandardYoungTableau

instance instFunLike {μ : YoungDiagram} :
    FunLike (StandardYoungTableau μ) ↥μ.cells (Fin μ.card) where
  coe T := T.toEquiv
  coe_injective T U h := by
    cases T with
    | mk e _ _ =>
      cases U with
      | mk e' _ _ =>
        congr
        exact Equiv.ext fun c => congrFun h c

/-- The underlying function of a standard Young tableau is its labeling equivalence. -/
@[simp]
theorem coe_toEquiv {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    ⇑T.toEquiv = T :=
  rfl

/-- Evaluating the labeling equivalence agrees with evaluating the tableau. -/
@[simp]
theorem toEquiv_apply {μ : YoungDiagram} (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    T.toEquiv c = T c :=
  rfl

/-- Two standard Young tableaux are equal when all of their entries agree. -/
@[ext]
theorem ext {μ : YoungDiagram} {T U : StandardYoungTableau μ}
    (h : ∀ c, T c = U c) : T = U :=
  DFunLike.ext T U h

/-- The entries of a standard Young tableau form a bijection. -/
theorem bijective {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    Function.Bijective T :=
  T.toEquiv.bijective

/-- The entries of a standard Young tableau are injective. -/
theorem injective {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    Function.Injective T :=
  T.toEquiv.injective

/-- Every label occurs in a standard Young tableau. -/
theorem surjective {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    Function.Surjective T :=
  T.toEquiv.surjective

/-- Entries of a standard Young tableau increase strictly from left to right. -/
theorem row_strict {μ : YoungDiagram} (T : StandardYoungTableau μ)
    {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ) :
    T ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < T ⟨(i, j₂), hcell⟩ :=
  T.row_strict' h hcell

/-- Entries of a standard Young tableau increase strictly from top to bottom. -/
theorem col_strict {μ : YoungDiagram} (T : StandardYoungTableau μ)
    {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ) :
    T ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < T ⟨(i₂, j), hcell⟩ :=
  T.col_strict' h hcell

private def transposeCellEquiv (μ : YoungDiagram) : ↥μ.transpose.cells ≃ ↥μ.cells :=
  (Equiv.prodComm ℕ ℕ).subtypeEquiv fun _ => YoungDiagram.mem_transpose

/-- Transpose a standard Young tableau by swapping its rows and columns while preserving its
labels. -/
def transpose {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    StandardYoungTableau μ.transpose where
  toEquiv :=
    (transposeCellEquiv μ).trans
      (T.toEquiv.trans (finCongr (YoungDiagram.card_transpose μ).symm))
  row_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv, Equiv.subtypeEquiv_apply,
      Equiv.prodComm_apply, Prod.swap, finCongr, Equiv.coe_fn_mk, Fin.cast_lt_cast,
      toEquiv_apply] using
      T.col_strict h (YoungDiagram.mem_transpose.mp hcell)
  col_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv, Equiv.subtypeEquiv_apply,
      Equiv.prodComm_apply, Prod.swap, finCongr, Equiv.coe_fn_mk, Fin.cast_lt_cast,
      toEquiv_apply] using
      T.row_strict h (YoungDiagram.mem_transpose.mp hcell)

/-- Transposition preserves the numeric label of each cell. -/
@[simp]
theorem transpose_apply_val {μ : YoungDiagram} (T : StandardYoungTableau μ)
    (c : ↥μ.transpose.cells) :
    (T.transpose c).val =
      (T ⟨c.1.swap, YoungDiagram.mem_transpose.mp c.2⟩).val :=
  calc
    (T.transpose c).val = (T.transpose.toEquiv c).val :=
      congrArg Fin.val (toEquiv_apply T.transpose c).symm
    _ = (T ⟨c.1.swap, YoungDiagram.mem_transpose.mp c.2⟩).val := by
      simp only [transpose, Equiv.trans_apply, transposeCellEquiv,
        Equiv.subtypeEquiv_apply, Equiv.prodComm_apply, finCongr, Equiv.coe_fn_mk,
        Fin.val_cast, toEquiv_apply]

private def untranspose {μ : YoungDiagram} (T : StandardYoungTableau μ.transpose) :
    StandardYoungTableau μ where
  toEquiv :=
    (transposeCellEquiv μ).symm.trans
      (T.toEquiv.trans (finCongr (YoungDiagram.card_transpose μ)))
  row_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv, Equiv.subtypeEquiv_symm,
      Equiv.prodComm_symm, Equiv.subtypeEquiv_apply, Equiv.prodComm_apply, Prod.swap,
      finCongr, Equiv.coe_fn_mk, Fin.cast_lt_cast, toEquiv_apply] using
      T.col_strict h (YoungDiagram.mem_transpose.mpr hcell)
  col_strict' h hcell := by
    simpa only [Equiv.trans_apply, transposeCellEquiv, Equiv.subtypeEquiv_symm,
      Equiv.prodComm_symm, Equiv.subtypeEquiv_apply, Equiv.prodComm_apply, Prod.swap,
      finCongr, Equiv.coe_fn_mk, Fin.cast_lt_cast, toEquiv_apply] using
      T.row_strict h (YoungDiagram.mem_transpose.mpr hcell)

private theorem untranspose_apply_val {μ : YoungDiagram}
    (T : StandardYoungTableau μ.transpose) (c : ↥μ.cells) :
    (untranspose T c).val =
      (T ⟨c.1.swap, YoungDiagram.mem_transpose.mpr c.2⟩).val :=
  calc
    (untranspose T c).val = ((untranspose T).toEquiv c).val :=
      congrArg Fin.val (toEquiv_apply (untranspose T) c).symm
    _ = (T ⟨c.1.swap, YoungDiagram.mem_transpose.mpr c.2⟩).val := by
      simp only [untranspose, Equiv.trans_apply, transposeCellEquiv,
        Equiv.subtypeEquiv_symm, Equiv.prodComm_symm, Equiv.subtypeEquiv_apply,
        Equiv.prodComm_apply, finCongr, Equiv.coe_fn_mk, Fin.val_cast, toEquiv_apply]

/-- Transposition is an equivalence between standard Young tableaux of conjugate shapes. -/
def transposeEquiv (μ : YoungDiagram) :
    StandardYoungTableau μ ≃ StandardYoungTableau μ.transpose where
  toFun := transpose
  invFun := untranspose
  left_inv T := by
    apply DFunLike.ext
    intro c
    apply Fin.ext
    simp only [untranspose_apply_val, transpose_apply_val, Prod.swap_swap]
  right_inv T := by
    apply DFunLike.ext
    intro c
    apply Fin.ext
    simp only [transpose_apply_val, untranspose_apply_val, Prod.swap_swap]

/-- The forward map of `transposeEquiv` is tableau transposition. -/
@[simp]
theorem transposeEquiv_apply {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    transposeEquiv μ T = T.transpose :=
  by simp [transposeEquiv]

/-- The inverse transpose equivalence swaps cells while preserving their numeric labels. -/
@[simp]
theorem transposeEquiv_symm_apply_val {μ : YoungDiagram}
    (T : StandardYoungTableau μ.transpose) (c : ↥μ.cells) :
    (((transposeEquiv μ).symm T) c).val =
      (T ⟨c.1.swap, YoungDiagram.mem_transpose.mpr c.2⟩).val :=
  untranspose_apply_val T c

/-- Standard Young tableaux of a fixed shape form a finite type. -/
noncomputable instance instFintype (μ : YoungDiagram) :
    Fintype (StandardYoungTableau μ) :=
  FunLike.fintype (StandardYoungTableau μ)

end StandardYoungTableau

/-- The number of standard Young tableaux of shape `μ`. -/
noncomputable def standardCount (μ : YoungDiagram) : ℕ :=
  Fintype.card (StandardYoungTableau μ)

/-- The number of standard Young tableaux is the cardinality of their finite type. -/
theorem standardCount_def (μ : YoungDiagram) :
    standardCount μ = Fintype.card (StandardYoungTableau μ) :=
  by simp only [standardCount]

/-- Transposing a Young diagram does not change its number of standard Young tableaux. -/
@[simp]
theorem standardCount_transpose (μ : YoungDiagram) :
    standardCount μ.transpose = standardCount μ :=
  Fintype.card_congr (StandardYoungTableau.transposeEquiv μ).symm

end TauCeti
