/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Symmetric.SpechtIdeal.Basic

/-!
# The Specht ideals of the one-row and the one-column shape

The two extreme shapes of a partition of `n` are the single row `(n)` and the single column
`(1ⁿ)`, and their Specht modules are the two representations of `Sₙ` that are visible without any
representation theory: the trivial one and the sign one.  This file proves that for the left-ideal
presentation `ℚ[Sₙ] c_t` of the Specht module, and deduces that both are irreducible.

The shape hypotheses are stated on the row and column groups rather than on the diagram, because
that is the form the symmetrizer identities consume: `rowSubgroup t = ⊤` says that all the labels
share a row, and `colSubgroup t = ⊤` says that all of them share a column.  Each is supplied by a
diagram-level criterion, `YoungTableau.rowSubgroup_eq_top_iff` and
`YoungTableau.colSubgroup_eq_top_iff`, which say that the two hypotheses hold exactly for the
shapes intended: a diagram has at most one row exactly when its zeroth column has length at most
one, and dually.  The two hypotheses are compatible rather than exclusive -- the empty diagram
satisfies both, and there `Sₙ` is trivial and so are the sign and the trivial representation.

For a shape with at most one row the column antisymmetrizer is `1`, so `c_t` is the sum of the
whole group and every group element fixes it; for a shape with at most one column the row
symmetrizer is `1`, so `c_t` is the signed sum of the whole group and every group element scales
it by its sign.  Either way `c_t` spans a `ℚ`-line inside `ℚ[Sₙ]`, which is therefore the whole
left ideal it generates, and the action on that line is the character in question.

Only the ideal presentation `ℚ[Sₙ] c_t` of the Specht module is available here, so that is what
these results are about; the identification of `S^λ` with the span of the polytabloids inside the
Young permutation module is a separate milestone and is not used or claimed.  The corresponding
statements one level down, that the permutation module `M^{(n)}` is the trivial representation and
`M^{(1ⁿ)}` the regular one, are in
`TauCeti.RepresentationTheory.Symmetric.PermutationModule.Extremes`.

## Main results

* `YoungTableau.spechtIdealRep_ρ_eq_trivial`: the one-row Specht ideal is the trivial
  representation.
* `YoungTableau.spechtIdealRep_ρ_apply_of_colSubgroup_eq_top`: the one-column Specht ideal is the
  sign representation.
* `YoungTableau.isIrreducible_spechtIdealRep_of_rowSubgroup_eq_top` and
  `YoungTableau.isIrreducible_spechtIdealRep_of_colSubgroup_eq_top`: both are irreducible.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles".
-/

public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ### Recognising the two extreme shapes -/

/-- A diagram whose zeroth column has at most one cell has only one row, so every label of a
tableau on it lies in row `0`. -/
theorem rowIndex_eq_zero_of_colLen_le_one (t : YoungTableau μ) (h : μ.colLen 0 ≤ 1)
    (k : Fin μ.card) : rowIndex t k = 0 := by
  have hmem : (t.symm k : ℕ × ℕ) ∈ μ := (YoungDiagram.mem_cells _).mp (t.symm k).2
  have hlt : (t.symm k : ℕ × ℕ).1 < μ.colLen (t.symm k : ℕ × ℕ).2 :=
    YoungDiagram.mem_iff_lt_colLen.mp hmem
  have hle : μ.colLen (t.symm k : ℕ × ℕ).2 ≤ μ.colLen 0 := μ.colLen_anti 0 _ (Nat.zero_le _)
  rw [rowIndex_def]
  omega

/-- A diagram whose zeroth row has at most one cell has only one column, so every label of a
tableau on it lies in column `0`. -/
theorem colIndex_eq_zero_of_rowLen_le_one (t : YoungTableau μ) (h : μ.rowLen 0 ≤ 1)
    (k : Fin μ.card) : colIndex t k = 0 := by
  have hmem : (t.symm k : ℕ × ℕ) ∈ μ := (YoungDiagram.mem_cells _).mp (t.symm k).2
  have hlt : (t.symm k : ℕ × ℕ).2 < μ.rowLen (t.symm k : ℕ × ℕ).1 :=
    YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hle : μ.rowLen (t.symm k : ℕ × ℕ).1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 _ (Nat.zero_le _)
  rw [colIndex_def]
  omega

/-- The row group of a tableau is everything exactly when its shape has at most one row: one row
leaves the permutations nothing to do, and two rows are separated by a transposition. -/
theorem rowSubgroup_eq_top_iff (t : YoungTableau μ) : rowSubgroup t = ⊤ ↔ μ.colLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h => by ext σ; simp [rowIndex_eq_zero_of_colLen_le_one t h]⟩
  by_contra hc
  obtain ⟨k, hk⟩ : ∃ k : Fin μ.card, rowIndex t k = 0 :=
    ⟨t ⟨(0, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))⟩, rowIndex_apply t _⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin μ.card, rowIndex t l = 1 :=
    ⟨t ⟨(1, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))⟩, rowIndex_apply t _⟩
  have hswap := mem_rowSubgroup.mp (by rw [h]; exact Subgroup.mem_top (Equiv.swap k l)) k
  rw [Equiv.swap_apply_left, hk, hl] at hswap
  omega

/-- The column group of a tableau is everything exactly when its shape has at most one column: one
column leaves the permutations nothing to do, and two columns are separated by a transposition. -/
theorem colSubgroup_eq_top_iff (t : YoungTableau μ) : colSubgroup t = ⊤ ↔ μ.rowLen 0 ≤ 1 := by
  refine ⟨fun h => ?_, fun h => by ext σ; simp [colIndex_eq_zero_of_rowLen_le_one t h]⟩
  by_contra hc
  obtain ⟨k, hk⟩ : ∃ k : Fin μ.card, colIndex t k = 0 :=
    ⟨t ⟨(0, 0), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))⟩, colIndex_apply t _⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin μ.card, colIndex t l = 1 :=
    ⟨t ⟨(0, 1), (YoungDiagram.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))⟩, colIndex_apply t _⟩
  have hswap := mem_colSubgroup.mp (by rw [h]; exact Subgroup.mem_top (Equiv.swap k l)) k
  rw [Equiv.swap_apply_left, hk, hl] at hswap
  omega

/-- The row and column groups meet trivially, so a full row group forces a trivial column
group. -/
theorem colSubgroup_eq_bot_of_rowSubgroup_eq_top (t : YoungTableau μ) (h : rowSubgroup t = ⊤) :
    colSubgroup t = ⊥ := by
  have hinf := rowSubgroup_inf_colSubgroup_eq_bot t
  rwa [h, top_inf_eq] at hinf

/-- The row and column groups meet trivially, so a full column group forces a trivial row
group. -/
theorem rowSubgroup_eq_bot_of_colSubgroup_eq_top (t : YoungTableau μ) (h : colSubgroup t = ⊤) :
    rowSubgroup t = ⊥ := by
  have hinf := rowSubgroup_inf_colSubgroup_eq_bot t
  rwa [h, inf_top_eq] at hinf

/-! ### The symmetrizers of an extreme shape -/

/-- A trivial row group leaves the row symmetrizer as the empty symmetrization, `1`. -/
theorem rowSymmetrizer_eq_one (t : YoungTableau μ) (h : rowSubgroup t = ⊥) :
    rowSymmetrizer t = 1 := by
  ext σ
  by_cases hσ : σ = 1
  · simp [rowSymmetrizer_coeff, h, MonoidAlgebra.one_def, hσ]
  · simp [rowSymmetrizer_coeff, h, MonoidAlgebra.one_def, Subgroup.mem_bot, hσ]

/-- A trivial column group leaves the column antisymmetrizer as the empty antisymmetrization,
`1`. -/
theorem columnAntisymmetrizer_eq_one (t : YoungTableau μ) (h : colSubgroup t = ⊥) :
    columnAntisymmetrizer t = 1 := by
  ext σ
  by_cases hσ : σ = 1
  · simp [columnAntisymmetrizer_coeff, h, MonoidAlgebra.one_def, hσ]
  · simp [columnAntisymmetrizer_coeff, h, MonoidAlgebra.one_def, Subgroup.mem_bot, hσ]

/-- With a trivial column group the Young symmetrizer is the row symmetrizer. -/
theorem youngSymmetrizer_eq_rowSymmetrizer (t : YoungTableau μ) (h : colSubgroup t = ⊥) :
    youngSymmetrizer t = rowSymmetrizer t := by
  rw [youngSymmetrizer_def, columnAntisymmetrizer_eq_one t h, mul_one]

/-- With a trivial row group the Young symmetrizer is the column antisymmetrizer. -/
theorem youngSymmetrizer_eq_columnAntisymmetrizer (t : YoungTableau μ) (h : rowSubgroup t = ⊥) :
    youngSymmetrizer t = columnAntisymmetrizer t := by
  rw [youngSymmetrizer_def, rowSymmetrizer_eq_one t h, one_mul]

/-- On a shape with at most one row every group element fixes the Young symmetrizer. -/
theorem single_mul_youngSymmetrizer_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) :
    MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t = youngSymmetrizer t :=
  mul_youngSymmetrizer_left t ⟨g, by rw [h]; exact Subgroup.mem_top g⟩

/-- On a shape with at most one column every group element scales the Young symmetrizer by its
sign. -/
theorem single_mul_youngSymmetrizer_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) :
    MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t =
      ((Equiv.Perm.sign g : ℤ) : ℚ) • youngSymmetrizer t := by
  rw [youngSymmetrizer_eq_columnAntisymmetrizer t (rowSubgroup_eq_bot_of_colSubgroup_eq_top t h)]
  exact mul_columnAntisymmetrizer_left t ⟨g, by rw [h]; exact Subgroup.mem_top g⟩

/-! ### The left ideal generated by an eigenvector of the group -/

variable {χ : Equiv.Perm (Fin μ.card) → ℚ}

/-- If every group element multiplies the Young symmetrizer by a scalar, then the left ideal it
generates is already the `ℚ`-line through it: the whole group algebra acts through the scalars. -/
private theorem restrictScalars_spechtIdeal_eq_span (t : YoungTableau μ)
    (h : ∀ g, MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t = χ g • youngSymmetrizer t) :
    (spechtIdeal t).restrictScalars ℚ = ℚ ∙ youngSymmetrizer t := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨a, rfl⟩ := (mem_spechtIdeal_iff t x).mp hx
    clear hx
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add p q hp hq => rw [add_mul]; exact Submodule.add_mem _ hp hq
    | single g r =>
      have hr : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : ℚ) := by
        rw [MonoidAlgebra.smul_single', mul_one]
      rw [hr, smul_mul_assoc, h g, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact youngSymmetrizer_mem_spechtIdeal t

/-- A Young symmetrizer scaled by the group generates a one-dimensional left ideal. -/
private theorem finrank_spechtIdeal_eq_one (t : YoungTableau μ)
    (h : ∀ g, MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t = χ g • youngSymmetrizer t) :
    Module.finrank ℚ (spechtIdeal t) = 1 := by
  have hline : Module.finrank ℚ ((spechtIdeal t).restrictScalars ℚ) = 1 := by
    rw [restrictScalars_spechtIdeal_eq_span t h]
    exact finrank_span_singleton (youngSymmetrizer_ne_zero t)
  rwa [LinearEquiv.finrank_eq
    (LinearEquiv.restrictScalars ℚ (Submodule.restrictScalarsEquiv ℚ _ _ (spechtIdeal t)))] at hline

/-- A Young symmetrizer scaled by the group spans its left ideal, so the group acts on that ideal
through the same scalars. -/
private theorem spechtIdealRep_ρ_apply (t : YoungTableau μ)
    (h : ∀ g, MonoidAlgebra.single g (1 : ℚ) * youngSymmetrizer t = χ g • youngSymmetrizer t)
    (g : Equiv.Perm (Fin μ.card)) (x : spechtIdeal t) :
    (spechtIdealRep t).ρ g x = χ g • x := by
  have hx : (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) ∈ ℚ ∙ youngSymmetrizer t := by
    rw [← restrictScalars_spechtIdeal_eq_span t h, Submodule.restrictScalars_mem]
    exact x.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  refine Subtype.ext ?_
  rw [spechtIdealRep_ρ_apply_coe, Submodule.coe_smul_of_tower, ← hc, mul_smul_comm, h g,
    smul_smul, smul_smul, mul_comm]

/-! ### The one-row shape gives the trivial representation -/

/-- The Specht ideal of a shape with at most one row is a line. -/
theorem finrank_spechtIdeal_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) : Module.finrank ℚ (spechtIdeal t) = 1 :=
  finrank_spechtIdeal_eq_one (χ := fun _ => 1) t fun g => by
    rw [one_smul]
    exact single_mul_youngSymmetrizer_of_rowSubgroup_eq_top t h g

/-- The symmetric group fixes the Specht ideal of a shape with at most one row pointwise. -/
theorem spechtIdealRep_ρ_apply_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) (x : spechtIdeal t) :
    (spechtIdealRep t).ρ g x = x := by
  refine (spechtIdealRep_ρ_apply (χ := fun _ => 1) t (fun g => ?_) g x).trans (one_smul ℚ x)
  rw [one_smul]
  exact single_mul_youngSymmetrizer_of_rowSubgroup_eq_top t h g

/-- **`S^{(n)}` is the trivial representation**: on a shape with at most one row the Specht ideal
`ℚ[Sₙ] c_t` carries the trivial action of `Sₙ`.  Together with
`YoungTableau.finrank_spechtIdeal_of_rowSubgroup_eq_top` this identifies it as the one-dimensional
trivial representation. -/
theorem spechtIdealRep_ρ_eq_trivial (t : YoungTableau μ) (h : rowSubgroup t = ⊤) :
    (spechtIdealRep t).ρ =
      Representation.trivial ℚ (Equiv.Perm (Fin μ.card)) (spechtIdeal t) := by
  refine DFunLike.ext _ _ fun g => LinearMap.ext fun x => ?_
  rw [spechtIdealRep_ρ_apply_of_rowSubgroup_eq_top t h, Representation.trivial_apply]

/-- The Specht ideal of a shape with at most one row is irreducible, being a line. -/
theorem isIrreducible_spechtIdealRep_of_rowSubgroup_eq_top (t : YoungTableau μ)
    (h : rowSubgroup t = ⊤) : (spechtIdealRep t).ρ.IsIrreducible :=
  Representation.isIrreducible_of_finrank_eq_one _
    (finrank_spechtIdeal_of_rowSubgroup_eq_top t h)

/-! ### The one-column shape gives the sign representation -/

/-- The Specht ideal of a shape with at most one column is a line. -/
theorem finrank_spechtIdeal_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) : Module.finrank ℚ (spechtIdeal t) = 1 :=
  finrank_spechtIdeal_eq_one (χ := fun g => ((Equiv.Perm.sign g : ℤ) : ℚ)) t
    (single_mul_youngSymmetrizer_of_colSubgroup_eq_top t h)

/-- **`S^{(1ⁿ)}` is the sign representation**: on a shape with at most one column the symmetric
group acts on the Specht ideal `ℚ[Sₙ] c_t` through the sign character.  Together with
`YoungTableau.finrank_spechtIdeal_of_colSubgroup_eq_top` this identifies it as the
one-dimensional sign representation. -/
theorem spechtIdealRep_ρ_apply_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) (g : Equiv.Perm (Fin μ.card)) (x : spechtIdeal t) :
    (spechtIdealRep t).ρ g x = ((Equiv.Perm.sign g : ℤ) : ℚ) • x :=
  spechtIdealRep_ρ_apply (χ := fun g => ((Equiv.Perm.sign g : ℤ) : ℚ)) t
    (single_mul_youngSymmetrizer_of_colSubgroup_eq_top t h) g x

/-- The Specht ideal of a shape with at most one column is irreducible, being a line. -/
theorem isIrreducible_spechtIdealRep_of_colSubgroup_eq_top (t : YoungTableau μ)
    (h : colSubgroup t = ⊤) : (spechtIdealRep t).ρ.IsIrreducible :=
  Representation.isIrreducible_of_finrank_eq_one _
    (finrank_spechtIdeal_of_colSubgroup_eq_top t h)

end YoungTableau

end TauCeti
