/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

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

The combinatorial content is the counting lemma
`TauCeti.YoungTableau.colIndex_lt_rowLen_of_injective` of
`TauCeti.Combinatorics.Young.Tableau`.  Write `r` for `rowIndex t` and `c` for `colIndex t`: the
failure of the criterion says exactly that `x ↦ (r x, c (u x))` is injective, for `u = σ⁻¹`, and
the counting lemma then puts `(r x, c (u x))` back inside `μ`.  Sending `x` to the label of that
cell is an injective, hence bijective, self-map of the labels which preserves rows, and it splits
`u` into a column permutation times a row permutation.

The factorization completes the sandwich calculation.  Every sandwich `a_t x b_t` is a scalar
multiple of the Young symmetrizer `c_t = a_t b_t`
(`TauCeti.YoungTableau.exists_eq_smul_youngSymmetrizer`): on a permutation the two cases above give
`0` or `sign q • c_t`, and the general case follows by linearity.  Consequently `c_t` is
**essentially idempotent**, `c_t x c_t ∈ ℚ ∙ c_t` for every `x`
(`TauCeti.YoungTableau.exists_eq_smul_youngSymmetrizer_mul_mul`), and in particular
`c_t ^ 2 = n_t • c_t` (`TauCeti.YoungTableau.exists_eq_smul_youngSymmetrizer_sq`).  Identifying the
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
  have hpapply : ∀ x, p x = g x := fun x => by
    rw [hp, Equiv.coe_ofBijective]
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
theorem exists_eq_smul_youngSymmetrizer_single (t : YoungTableau μ)
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
`TauCeti.YoungTableau.exists_eq_smul_youngSymmetrizer_single`. -/
theorem exists_eq_smul_youngSymmetrizer (t : YoungTableau μ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :
    ∃ κ : ℚ, rowSymmetrizer t * x * columnAntisymmetrizer t = κ • youngSymmetrizer t := by
  have hspan : rowSymmetrizer t * x * columnAntisymmetrizer t ∈
      Submodule.span ℚ {youngSymmetrizer t} := by
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      obtain ⟨κ, hκ⟩ := exists_eq_smul_youngSymmetrizer_single t g
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
theorem exists_eq_smul_youngSymmetrizer_mul_mul (t : YoungTableau μ)
    (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card))) :
    ∃ κ : ℚ, youngSymmetrizer t * x * youngSymmetrizer t = κ • youngSymmetrizer t := by
  obtain ⟨κ, hκ⟩ :=
    exists_eq_smul_youngSymmetrizer t (columnAntisymmetrizer t * x * rowSymmetrizer t)
  refine ⟨κ, ?_⟩
  rw [← hκ]
  simp only [youngSymmetrizer_def, mul_assoc]

/-- The square of a Young symmetrizer is a multiple of it.  Identifying the scalar needs the
dimension of the left ideal `ℚ[Sₙ] c_t`, so it is done downstream, in
`TauCeti.YoungTableau.youngSymmetrizer_sq`, which proves the scalar is
`μ.card ! / finrank ℚ (ℚ[Sₙ] c_t)`.  The roadmap writes it as `μ.card ! / f^μ`, with `f^μ` the
number of standard tableaux of shape `μ`; that form needs the standard basis theorem
`dim S^μ = f^μ`, which is not available yet. -/
theorem exists_eq_smul_youngSymmetrizer_sq (t : YoungTableau μ) :
    ∃ κ : ℚ, youngSymmetrizer t * youngSymmetrizer t = κ • youngSymmetrizer t := by
  obtain ⟨κ, hκ⟩ := exists_eq_smul_youngSymmetrizer_mul_mul t 1
  exact ⟨κ, by rwa [mul_one] at hκ⟩

end YoungTableau

end TauCeti
