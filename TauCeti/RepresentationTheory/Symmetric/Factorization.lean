/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import TauCeti.RepresentationTheory.Symmetric.Vanishing

/-!
# The row-column factorization of a permutation

For a `μ`-tableau `t` with row group `Row(t)` and column group `Col(t)`, the key vanishing lemma
of `TauCeti.RepresentationTheory.Symmetric.Vanishing` kills the sandwich `a_t σ b_t` whenever a
row of `t` meets a column of `relabel σ t` twice, and the converse direction there shows that the
criterion never fires on a permutation of the form `p q` with `p ∈ Row(t)` and `q ∈ Col(t)`.  What
was missing is that these two cases are exhaustive: this file proves the **row-column
factorization**, that a permutation on which the criterion does *not* fire already factors as
`p q` (`TauCeti.YoungTableau.mem_mul_of_not_rowMeetsColumnTwice`).

The combinatorial content is a counting argument, isolated as
`TauCeti.YoungTableau.colIndex_lt_rowLen_of_injective`.  Write `r` for `rowIndex t` and `c` for
`colIndex t`, and let `u` be a permutation of the labels for which `x ↦ (r x, c (u x))` is
injective -- that injectivity is exactly the failure of the criterion, for `u = σ⁻¹`.  Fix `k` and
count the labels `x` with `c (u x) < k`, row by row:

* summed over the rows, the count is `∑ᵢ min (μ.rowLen i) k`, because `u` is a bijection and the
  columns occupied by row `i` are exactly `0, …, μ.rowLen i - 1`;
* row `i` contributes at most `min (μ.rowLen i) k`, since it has `μ.rowLen i` labels and
  injectivity confines their `c ∘ u` values to the `k` values below `k`.

A family of upper bounds summing to the total is a family of equalities, so row `i` contributes
exactly `min (μ.rowLen i) k` for every `k`; taking `k = μ.rowLen i` says that every label of row
`i` has `c (u x) < μ.rowLen i`, that is, `(r x, c (u x))` is again a cell of `μ`.  Sending `x` to
the label of that cell is then an injective, hence bijective, self-map of the labels which
preserves rows, and it splits `u` into a column permutation times a row permutation.

The factorization completes the sandwich calculation.  Every sandwich `a_t x b_t` is a scalar
multiple of the Young symmetrizer `c_t = a_t b_t`
(`TauCeti.YoungTableau.exists_smul_youngSymmetrizer`): on a permutation the two cases above give
`0` or `sign q • c_t`, and the general case follows by linearity.  Consequently `c_t` is
**essentially idempotent**, `c_t x c_t ∈ ℚ ∙ c_t` for every `x`
(`TauCeti.YoungTableau.exists_smul_youngSymmetrizer_mul_mul`), and in particular
`c_t ^ 2 = n_t • c_t` (`TauCeti.YoungTableau.exists_smul_youngSymmetrizer_sq`).  Identifying the
scalar `n_t` as `μ.card ! / f^μ`, and with it the idempotent generating the Specht ideal, needs the
dimension count of the Specht module and is not done here.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.2, Lemma 3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lemma 4.24 and
  Lemma 4.26.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 3.
-/

public section

namespace TauCeti

namespace YoungTableau

open scoped Pointwise

variable {μ : YoungDiagram}

/-! ### Cells and labels -/

/-- The row and the column of a label are the coordinates of a cell of `μ`. -/
theorem rowIndex_colIndex_mem (t : YoungTableau μ) (x : Fin μ.card) :
    (rowIndex t x, colIndex t x) ∈ μ := by
  rw [rowIndex_def, colIndex_def]
  simp

/-- A label lies in a column strictly to the left of the end of its row. -/
theorem colIndex_lt_rowLen (t : YoungTableau μ) (x : Fin μ.card) :
    colIndex t x < μ.rowLen (rowIndex t x) :=
  YoungDiagram.mem_iff_lt_rowLen.mp (rowIndex_colIndex_mem t x)

/-- Every cell of `μ` carries a label. -/
theorem exists_rowIndex_colIndex (t : YoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    ∃ x, rowIndex t x = i ∧ colIndex t x = j :=
  ⟨t ⟨(i, j), (YoungDiagram.mem_cells _).mpr h⟩, by simp, by simp⟩

/-- Row `i` of a `μ`-tableau carries `μ.rowLen i` labels. -/
theorem card_filter_rowIndex_eq (t : YoungTableau μ) (i : ℕ) :
    (Finset.univ.filter fun y => rowIndex t y = i).card = μ.rowLen i := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rowFiberEquiv t i), Fintype.card_coe]
  exact (YoungDiagram.rowLen_eq_card μ).symm

/-! ### The counting lemma -/

/-- **The counting lemma behind the row-column factorization.**  If the row of a label together
with the column of its `u`-image determine the label, then that pair is again a cell of `μ`.

Both halves of the count are over the rows of `μ`: the labels whose `u`-image lies in one of the
first `k` columns number `∑ᵢ min (μ.rowLen i) k`, while row `i` can contribute at most
`min (μ.rowLen i) k` of them.  Upper bounds that add up to the total are equalities, and the case
`k = μ.rowLen i` of the resulting equality is the statement. -/
theorem colIndex_lt_rowLen_of_injective (t : YoungTableau μ) (u : Equiv.Perm (Fin μ.card))
    (hu : Function.Injective fun x => (rowIndex t x, colIndex t (u x))) (x : Fin μ.card) :
    colIndex t (u x) < μ.rowLen (rowIndex t x) := by
  -- the rows of `μ` that actually carry labels
  set S : Finset ℕ := Finset.image (rowIndex t) Finset.univ with hS
  have hmemS : ∀ y : Fin μ.card, rowIndex t y ∈ S := fun y =>
    Finset.mem_image_of_mem _ (Finset.mem_univ y)
  -- row `i` contributes exactly `min (μ.rowLen i) k` labels to the first `k` columns
  have hexact : ∀ i k : ℕ,
      (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card
        = min (μ.rowLen i) k := by
    intro i k
    have hinj : Set.InjOn (colIndex t)
        ↑(Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact rowIndex_colIndex_injective t (Prod.ext (ha.2.trans hb.2.symm) hab)
    have himg : (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).image
        (colIndex t) = (Finset.range (μ.rowLen i)).filter fun j => j < k := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨hy2 ▸ colIndex_lt_rowLen t y, hy1⟩
      · rintro ⟨hj1, hj2⟩
        obtain ⟨y, hy1, hy2⟩ :=
          exists_rowIndex_colIndex t (YoungDiagram.mem_iff_lt_rowLen.mpr hj1)
        exact ⟨y, ⟨hy2 ▸ hj2, hy1⟩, hy2⟩
    have hrange : ((Finset.range (μ.rowLen i)).filter fun j => j < k)
        = Finset.range (min (μ.rowLen i) k) := by
      ext j
      simp
    rw [← Finset.card_image_of_injOn hinj, himg, hrange, Finset.card_range]
  -- row `i` contributes at most `min (μ.rowLen i) k` labels along `u`
  have hle : ∀ i k : ℕ,
      (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
        ≤ min (μ.rowLen i) k := by
    intro i k
    refine le_min ?_ ?_
    · rw [← card_filter_rowIndex_eq t i]
      refine Finset.card_le_card fun y hy => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hy.2
    · have hinj : Set.InjOn (fun y => colIndex t (u y))
          ↑(Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        exact hu (Prod.ext (ha.2.trans hb.2.symm) hab)
      calc (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
          = ((Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).image
              fun y => colIndex t (u y)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range k).card := by
              refine Finset.card_le_card fun j hj => ?_
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
              obtain ⟨y, ⟨hy1, _⟩, rfl⟩ := hj
              exact Finset.mem_range.mpr hy1
        _ = k := Finset.card_range k
  -- the two counts agree, so the upper bounds are equalities
  have hsum : ∀ k : ℕ,
      ∑ i ∈ S, (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card
        = ∑ i ∈ S, min (μ.rowLen i) k := by
    intro k
    have h1 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
        = ∑ i ∈ S,
            (Finset.univ.filter fun y => colIndex t (u y) < k ∧ rowIndex t y = i).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t) (t := S) fun y _ => hmemS y]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
    have h2 : (Finset.univ.filter fun y => colIndex t y < k).card
        = ∑ i ∈ S, (Finset.univ.filter fun y => colIndex t y < k ∧ rowIndex t y = i).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := rowIndex t) (t := S) fun y _ => hmemS y]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.filter_filter]
    have h3 : (Finset.univ.filter fun y => colIndex t (u y) < k).card
        = (Finset.univ.filter fun y => colIndex t y < k).card :=
      Finset.card_equiv u fun i => by simp
    rw [← h1, h3, h2]
    exact Finset.sum_congr rfl fun i _ => hexact i k
  have hfull := fun k =>
    (Finset.sum_eq_sum_iff_of_le fun i _ => hle i k).mp (hsum k) (rowIndex t x) (hmemS x)
  have hi := hfull (μ.rowLen (rowIndex t x))
  rw [min_self] at hi
  -- a subset of the row with the same cardinality is the whole row
  have hsub : (Finset.univ.filter fun y =>
        colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x)
      ⊆ Finset.univ.filter fun y => rowIndex t y = rowIndex t x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.2
  have hEq := Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (by rw [card_filter_rowIndex_eq t (rowIndex t x), hi]))
  have hx : x ∈ Finset.univ.filter fun y =>
      colIndex t (u y) < μ.rowLen (rowIndex t x) ∧ rowIndex t y = rowIndex t x := by
    rw [hEq]
    simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact hx.1

/-! ### The factorization -/

/-- **The row-column factorization.**  A permutation on which the row/column criterion does not
fire lies in the product set `Row(t) · Col(t)`.

Together with `TauCeti.YoungTableau.notMem_mul_of_rowMeetsColumnTwice` this makes the criterion an
exact description of the complement of `Row(t) · Col(t)`, so the two cases of the sandwich
calculation are exhaustive. -/
theorem mem_mul_of_not_rowMeetsColumnTwice {t : YoungTableau μ} {σ : Equiv.Perm (Fin μ.card)}
    (h : ¬RowMeetsColumnTwice t (relabel σ t)) :
    σ ∈ (rowSubgroup t : Set (Equiv.Perm (Fin μ.card))) *
      (colSubgroup t : Set (Equiv.Perm (Fin μ.card))) := by
  rw [rowMeetsColumnTwice_relabel_iff] at h
  -- the failure of the criterion is injectivity of `x ↦ (row of x, column of σ⁻¹ x)`
  have hu : Function.Injective fun x => (rowIndex t x, colIndex t (σ⁻¹ x)) := by
    intro a b hab
    rw [Prod.mk.injEq] at hab
    by_contra hne
    exact h ⟨a, b, hne, hab.1, hab.2⟩
  -- the label of the cell `(row of x, column of σ⁻¹ x)`
  have hcell : ∀ x, (rowIndex t x, colIndex t (σ⁻¹ x)) ∈ μ := fun x =>
    YoungDiagram.mem_iff_lt_rowLen.mpr (colIndex_lt_rowLen_of_injective t σ⁻¹ hu x)
  set g : Fin μ.card → Fin μ.card := fun x =>
    t ⟨(rowIndex t x, colIndex t (σ⁻¹ x)), (YoungDiagram.mem_cells _).mpr (hcell x)⟩ with hg
  have hgrow : ∀ x, rowIndex t (g x) = rowIndex t x := fun x => by rw [hg]; simp
  have hgcol : ∀ x, colIndex t (g x) = colIndex t (σ⁻¹ x) := fun x => by rw [hg]; simp
  have hginj : Function.Injective g := by
    intro a b hab
    exact hu (Prod.ext ((hgrow a).symm.trans (by rw [hab, hgrow]))
      ((hgcol a).symm.trans (by rw [hab, hgcol])))
  -- as a permutation, `g` preserves rows and carries `σ⁻¹` into the column group
  set p : Equiv.Perm (Fin μ.card) :=
    Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj) with hp
  have hpapply : ∀ x, p x = g x := fun x => rfl
  have hprow : p ∈ rowSubgroup t := mem_rowSubgroup.mpr fun k => by rw [hpapply, hgrow]
  have hpinv : ∀ k, p (p⁻¹ k) = k := fun k => by
    rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hqcol : σ⁻¹ * p⁻¹ ∈ colSubgroup t := by
    refine mem_colSubgroup.mpr fun k => ?_
    rw [Equiv.Perm.mul_apply]
    have h1 := (hgcol (p⁻¹ k)).symm
    rwa [← hpapply, hpinv] at h1
  have hfac : σ⁻¹ = (σ⁻¹ * p⁻¹) * p := by
    rw [inv_mul_cancel_right]
  refine Set.mem_mul.mpr ⟨p⁻¹, inv_mem hprow, (σ⁻¹ * p⁻¹)⁻¹, inv_mem hqcol, ?_⟩
  rw [← mul_inv_rev, ← hfac, inv_inv]

/-- The row/column criterion fires on exactly the permutations outside `Row(t) · Col(t)`. -/
theorem rowMeetsColumnTwice_relabel_iff_notMem_mul (t : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) :
    RowMeetsColumnTwice t (relabel σ t) ↔
      σ ∉ (rowSubgroup t : Set (Equiv.Perm (Fin μ.card))) *
        (colSubgroup t : Set (Equiv.Perm (Fin μ.card))) :=
  ⟨notMem_mul_of_rowMeetsColumnTwice, fun hσ => by
    by_contra h
    exact hσ (mem_mul_of_not_rowMeetsColumnTwice h)⟩

/-! ### The symmetrizer sandwich -/

/-- The sandwich of a permutation between the row symmetrizer and the column antisymmetrizer is a
multiple of the Young symmetrizer: it vanishes off `Row(t) · Col(t)` by the key vanishing lemma,
and on `p q` it is `sign q • c_t`. -/
theorem exists_smul_youngSymmetrizer_single (t : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) :
    ∃ κ : ℚ, rowSymmetrizer t * MonoidAlgebra.single σ 1 * columnAntisymmetrizer t =
      κ • youngSymmetrizer t := by
  by_cases h : RowMeetsColumnTwice t (relabel σ t)
  · exact ⟨0, by
      rw [h.rowSymmetrizer_mul_single_mul_columnAntisymmetrizer_eq_zero, zero_smul]⟩
  · obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_mul.mp (mem_mul_of_not_rowMeetsColumnTwice h)
    exact ⟨((Equiv.Perm.sign q : ℤ) : ℚ),
      rowSymmetrizer_mul_single_mul_columnAntisymmetrizer_eq_sign_smul_youngSymmetrizer t
        (SetLike.mem_coe.mp hp) (SetLike.mem_coe.mp hq)⟩

/-- **Every symmetrizer sandwich is a multiple of the Young symmetrizer**: for every element `x`
of the group algebra, `a_t x b_t ∈ ℚ ∙ c_t`.  This is the linear extension of
`TauCeti.YoungTableau.exists_smul_youngSymmetrizer_single`. -/
theorem exists_smul_youngSymmetrizer (t : YoungTableau μ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :
    ∃ κ : ℚ, rowSymmetrizer t * x * columnAntisymmetrizer t = κ • youngSymmetrizer t := by
  have hspan : rowSymmetrizer t * x * columnAntisymmetrizer t ∈
      Submodule.span ℚ {youngSymmetrizer t} := by
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      obtain ⟨κ, hκ⟩ := exists_smul_youngSymmetrizer_single t g
      rw [MonoidAlgebra.of_apply, hκ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | add f g hf hg =>
      rw [mul_add, add_mul]
      exact Submodule.add_mem _ hf hg
    | smul r f hf =>
      rw [mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ _ hf
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp hspan
  exact ⟨κ, hκ.symm⟩

/-- **The Young symmetrizer is essentially idempotent**: `c_t x c_t` is a multiple of `c_t` for
every element `x` of the group algebra.  Writing `c_t = a_t b_t` turns the sandwich `c_t x c_t`
into the sandwich `a_t (b_t x a_t) b_t`. -/
theorem exists_smul_youngSymmetrizer_mul_mul (t : YoungTableau μ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :
    ∃ κ : ℚ, youngSymmetrizer t * x * youngSymmetrizer t = κ • youngSymmetrizer t := by
  obtain ⟨κ, hκ⟩ :=
    exists_smul_youngSymmetrizer t (columnAntisymmetrizer t * x * rowSymmetrizer t)
  refine ⟨κ, ?_⟩
  rw [← hκ]
  simp only [youngSymmetrizer_def, mul_assoc]

/-- The square of a Young symmetrizer is a multiple of it.  The scalar is `μ.card ! / f^μ`, with
`f^μ` the number of standard tableaux of shape `μ`; identifying it needs the dimension of the
Specht module and is not proved here. -/
theorem exists_smul_youngSymmetrizer_sq (t : YoungTableau μ) :
    ∃ κ : ℚ, youngSymmetrizer t * youngSymmetrizer t = κ • youngSymmetrizer t := by
  obtain ⟨κ, hκ⟩ := exists_smul_youngSymmetrizer_mul_mul t 1
  exact ⟨κ, by rwa [mul_one] at hκ⟩

end YoungTableau

end TauCeti
