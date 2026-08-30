/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.FixingSubgroup
public import TauCeti.RepresentationTheory.AsAlgebraHom
public import TauCeti.RepresentationTheory.Symmetric.Specht.Module

/-!
# The Garnir relations

The polytabloids `e_t` of the `μ`-tableaux span the Specht module `S^μ`, and the standard basis
theorem says that the polytabloids of the *standard* tableaux already do.  The relations that
rewrite an arbitrary polytabloid in terms of ones closer to standard are the **Garnir relations**,
and this file proves them.

Write `A_X` for the signed sum `∑ sgn(σ) σ` over the permutations `σ` fixing every label outside a
finite set `X` (`TauCeti.antisymmetrizerOn`).  The Garnir relation is

`A_X · e_t = 0`

whenever `X` is too large to be spread over the rows available to it: all the labels of `X` lie in
columns of `μ` of length at most `r`, and `X` has more than `r` elements
(`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`).  Since the identity
contributes the term `e_t`, this expresses `e_t` as a combination of the polytabloids of the
relabelings `σt`, `σ ≠ 1`
(`TauCeti.YoungTableau.polytabloid_eq_neg_sum_signChar_smul_polytabloid_relabel`).

Two facts drive the proof.

* **A signed sum kills whatever an odd permutation in it fixes.**  If `σ ↦ sgn(σ) σ` is summed over
  a subgroup containing a transposition `τ`, then reindexing by `τ` on the right turns the sum into
  its own negative, so it annihilates every vector fixed by `τ`
  (`TauCeti.asAlgebraHom_antisymmetrizerOn_apply_eq_zero`).
* **Pigeonhole in the columns.**  A column permutation `q` of `t` moves a label only within its own
  column, so in the tabloid `q · {t}` the labels of `X` still lie in columns of length at most `r`,
  that is, in `r` rows.  As `X` has more than `r` elements, two of them share a row of `q · {t}`,
  and the transposition swapping those two fixes that tabloid.  Every tabloid occurring in `e_t` is
  of this form, so `A_X` kills them all.

The sets `X` the relation is applied to are the **Garnir sets** `TauCeti.YoungTableau.garnirSet t i
j`: the labels of `t` in column `j` from row `i` downwards together with those in column `j + 1`
from row `i` upwards.  As soon as `(i, j + 1)` is a cell of `μ` there are `μ.colLen j + 1` of them
(`TauCeti.YoungTableau.card_garnirSet`) while they occupy only the `μ.colLen j` rows of column `j`,
so the relation applies (`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_garnirSet_eq_zero`).
Those are the sets that straighten a tableau whose rows fail to increase across the cell `(i, j)`.

The classical Garnir *element* of a Garnir set is a shorter signed sum, over a transversal of the
permutations internal to the two halves of the set; multiplying it by the signed sum over those
internal permutations recovers `A_X`.  That repackaging is not carried out here: the relation is
proved, and stated, for the whole of `A_X`.

## Main definitions

* `TauCeti.antisymmetrizerOn`: the signed sum `∑ sgn(σ) σ` over the permutations supported in a
  finite set.
* `TauCeti.YoungTableau.garnirSet`: the Garnir set of a tableau at a row and a column.

## Main results

* `TauCeti.asAlgebraHom_antisymmetrizerOn_apply_eq_zero`: the signed sum annihilates a vector fixed
  by a transposition of two of its points.
* `TauCeti.YoungTableau.exists_ne_rowIndex_relabel_eq`: the pigeonhole step, two labels of an
  oversized set share a row after any column permutation.
* `TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`: **the Garnir
  relation**.
* `TauCeti.YoungTableau.polytabloid_eq_neg_sum_signChar_smul_polytabloid_relabel`: the relation with
  the identity term isolated, which is the form that straightens a polytabloid.
* `TauCeti.YoungTableau.card_garnirSet`: a Garnir set has one more element than the column it
  straddles has cells.
* `TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_garnirSet_eq_zero`: the Garnir relation at a
  Garnir set.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Section 7.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 2.6.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, whose standard basis of the Specht module these relations straighten towards.
-/

public section

namespace TauCeti

open scoped BigOperators

/-- Classical decidability of membership in the subgroup of permutations fixing everything outside
a finite set, used to form its finite sum. -/
noncomputable local instance {α : Type*} (X : Finset α) :
    DecidablePred (· ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ)) :=
  Classical.decPred _

/-! ## The signed sum over the permutations supported in a set -/

section Antisymmetrizer

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The **antisymmetrizer** of a finite set `X` of points: the signed sum `∑ sgn(σ) σ`, in the
rational group algebra of `Equiv.Perm α`, over the permutations `σ` fixing every point outside `X`.

For `X` the labels lying in one column of a Young tableau this is the factor of that tableau's
column antisymmetrizer belonging to that column; the relations it satisfies on the polytabloids of
a tableau are the Garnir relations. -/
noncomputable def antisymmetrizerOn (X : Finset α) : MonoidAlgebra ℚ (Equiv.Perm α) :=
  subgroupCharSum YoungTableau.signChar
    (fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ))

theorem antisymmetrizerOn_def (X : Finset α) :
    antisymmetrizerOn X =
      subgroupCharSum YoungTableau.signChar
        (fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ)) :=
  (rfl)

/-- The coefficient of a permutation in `TauCeti.antisymmetrizerOn X` is its sign if it is
supported in `X`, and zero otherwise. -/
@[simp]
theorem antisymmetrizerOn_coeff (X : Finset α) (σ : Equiv.Perm α) :
    (antisymmetrizerOn X).coeff σ =
      if ∀ k ∉ X, σ k = k then ((Equiv.Perm.sign σ : ℤ) : ℚ) else 0 := by
  classical
  rw [antisymmetrizerOn_def, subgroupCharSum_coeff]
  simp [mem_fixingSubgroup_compl_coe_iff]

/-- The permutations summed over by `TauCeti.antisymmetrizerOn X`, as a `Finset`. -/
private theorem mem_filter_forall_notMem_iff (X : Finset α)
    [DecidablePred fun σ : Equiv.Perm α => ∀ k ∉ X, σ k = k] (σ : Equiv.Perm α) :
    σ ∈ ({σ : Equiv.Perm α | ∀ k ∉ X, σ k = k} : Finset (Equiv.Perm α)) ↔
      σ ∈ fixingSubgroup (Equiv.Perm α) ((X : Set α)ᶜ) := by
  simp [mem_fixingSubgroup_compl_coe_iff]

/-- The antisymmetrizer of a set, acting on a representation of the symmetric group, is the signed
sum of the actions of the permutations fixing everything outside that set.

The decidability of the summation range is an instance argument rather than a synthesized one, so
that the equation rewrites a sum however its own filter was built. -/
theorem asAlgebraHom_antisymmetrizerOn_apply {M : Type*} [AddCommGroup M] [Module ℚ M]
    (V : Representation ℚ (Equiv.Perm α) M) (X : Finset α)
    [DecidablePred fun σ : Equiv.Perm α => ∀ k ∉ X, σ k = k] (v : M) :
    V.asAlgebraHom (antisymmetrizerOn X) v =
      ∑ σ ∈ {σ : Equiv.Perm α | ∀ k ∉ X, σ k = k}, YoungTableau.signChar σ • V σ v := by
  rw [Finset.sum_subtype _ (mem_filter_forall_notMem_iff X)
      (fun σ => YoungTableau.signChar σ • V σ v),
    antisymmetrizerOn_def, subgroupCharSum_def, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun σ _ => by
    rw [map_smul, LinearMap.smul_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single_one]

/-- Right multiplication by the transposition of two points of `X` negates the antisymmetrizer of
`X`, since the antisymmetrizer absorbs it up to its sign. -/
theorem antisymmetrizerOn_mul_single_swap {X : Finset α} {x y : α} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x ≠ y) :
    antisymmetrizerOn X * MonoidAlgebra.single (Equiv.swap x y) (1 : ℚ) = -antisymmetrizerOn X := by
  rw [antisymmetrizerOn_def,
    subgroupCharSum_mul_single _ _ ⟨Equiv.swap x y, swap_mem_fixingSubgroup_compl_coe hx hy⟩,
    Equiv.swap_inv, YoungTableau.signChar_apply, Equiv.Perm.sign_swap hxy]
  simp

/-- **A signed sum annihilates whatever an odd permutation in it fixes.**  If two distinct points
of `X` are swapped by a transposition fixing `v`, then the antisymmetrizer of `X` kills `v`:
absorbing that transposition negates the sum while leaving `v` alone. -/
theorem asAlgebraHom_antisymmetrizerOn_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℚ M]
    (V : Representation ℚ (Equiv.Perm α) M) {X : Finset α} {x y : α} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x ≠ y) {v : M} (hv : V (Equiv.swap x y) v = v) :
    V.asAlgebraHom (antisymmetrizerOn X) v = 0 :=
  have : IsAddTorsionFree M := .of_module_rat _
  Representation.asAlgebraHom_eq_zero_of_mul_single_eq_neg
    (nsmul_right_injective two_ne_zero) _ hv (antisymmetrizerOn_mul_single_swap hx hy hxy)

end Antisymmetrizer

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ## The Garnir relation -/

/-- **Pigeonhole in the columns.**  Suppose every label of `X` lies in a column of `μ` with at most
`r` cells, and `X` has more than `r` elements.  Then a column permutation `q` of `t` leaves two
distinct labels of `X` in a common row of `qt`: it moves each of them only inside its own column,
so all of them still lie in the top `r` rows. -/
theorem exists_ne_rowIndex_relabel_eq (t : YoungTableau μ) {X : Finset (Fin μ.card)} {r : ℕ}
    (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r) (hcard : r < X.card)
    {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup t) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ rowIndex (relabel q t) x = rowIndex (relabel q t) y := by
  have hmaps : ∀ k ∈ X, rowIndex (relabel q t) k ∈ Finset.range r := by
    intro k hk
    have hcol : colIndex t (q⁻¹ k) = colIndex t k := mem_colSubgroup.mp (inv_mem hq) k
    have hmem : (rowIndex t (q⁻¹ k), colIndex t (q⁻¹ k)) ∈ μ := rowIndex_colIndex_mem t (q⁻¹ k)
    have hlt : rowIndex t (q⁻¹ k) < μ.colLen (colIndex t (q⁻¹ k)) :=
      YoungDiagram.mem_iff_lt_colLen.mp hmem
    rw [Finset.mem_range, rowIndex_relabel]
    calc rowIndex t (q⁻¹ k) < μ.colLen (colIndex t (q⁻¹ k)) := hlt
      _ = μ.colLen (colIndex t k) := by rw [hcol]
      _ ≤ r := hX k hk
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simpa using hcard) hmaps

/-- The antisymmetrizer of `X` annihilates every tabloid reachable from `{t}` by a column
permutation of `t`, because two labels of `X` share a row of that tabloid. -/
private theorem asAlgebraHom_antisymmetrizerOn_single_smul_tabloid_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) {q : Equiv.Perm (Fin μ.card)} (hq : q ∈ colSubgroup t) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn X)
        (MonoidAlgebra.single (q • tabloid t) (1 : ℚ)) = 0 := by
  obtain ⟨x, hx, y, hy, hxy, hrow⟩ := exists_ne_rowIndex_relabel_eq t hX hcard hq
  refine asAlgebraHom_antisymmetrizerOn_apply_eq_zero _ hx hy hxy ?_
  rw [Representation.ofMulAction_single, ← tabloid_relabel]
  exact congrArg (MonoidAlgebra.single · (1 : ℚ))
    (smul_tabloid_eq_self_iff.mpr (swap_mem_rowSubgroup hrow))

/-- **The Garnir relation.**  If every label of the finite set `X` lies in a column of `μ` with at
most `r` cells and `X` has more than `r` elements, then the antisymmetrizer of `X` annihilates the
polytabloid of `t`.

The labels of `X` cannot be spread over the rows of those columns, so every tabloid occurring in
`e_t` has two of them in a common row and is killed by the signed sum. -/
theorem asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn X)
        (polytabloid t) = 0 := by
  rw [polytabloid_eq_sum, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, asAlgebraHom_antisymmetrizerOn_single_smul_tabloid_eq_zero t hX hcard q.2,
    smul_zero]

/-- **The Garnir relation, as a signed sum of polytabloids.**  Under the hypotheses of
`TauCeti.YoungTableau.asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero`, the signed sum of the
polytabloids of the relabelings `σt`, over the permutations `σ` supported in `X`, vanishes. -/
theorem sum_signChar_smul_polytabloid_relabel_eq_zero (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) :
    ∑ σ ∈ {σ : Equiv.Perm (Fin μ.card) | ∀ k ∉ X, σ k = k},
        signChar σ • polytabloid (relabel σ t) = 0 := by
  rw [← asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero t hX hcard,
    asAlgebraHom_antisymmetrizerOn_apply]
  simp only [polytabloid_relabel]

/-- **The Garnir relation, straightening a polytabloid.**  Isolating the identity term of
`TauCeti.YoungTableau.sum_signChar_smul_polytabloid_relabel_eq_zero` writes `e_t` as a rational
combination of the polytabloids of the relabelings `σt` by the nontrivial permutations `σ`
supported in `X`. -/
theorem polytabloid_eq_neg_sum_signChar_smul_polytabloid_relabel (t : YoungTableau μ)
    {X : Finset (Fin μ.card)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (colIndex t k) ≤ r)
    (hcard : r < X.card) :
    polytabloid t =
      -∑ σ ∈ ({σ : Equiv.Perm (Fin μ.card) | ∀ k ∉ X, σ k = k} :
          Finset (Equiv.Perm (Fin μ.card))).erase 1,
        signChar σ • polytabloid (relabel σ t) := by
  have hone : (1 : Equiv.Perm (Fin μ.card)) ∈
      ({σ : Equiv.Perm (Fin μ.card) | ∀ k ∉ X, σ k = k} : Finset (Equiv.Perm (Fin μ.card))) := by
    simp
  have hsum := sum_signChar_smul_polytabloid_relabel_eq_zero t hX hcard
  rw [← Finset.add_sum_erase _ _ hone] at hsum
  rw [eq_neg_iff_add_eq_zero, ← hsum]
  simp

/-! ## Garnir sets -/

/-- The **Garnir set** of a tableau `t` at row `i` and column `j`: the labels of `t` lying in
column `j` from row `i` downwards, together with those lying in column `j + 1` from row `i`
upwards.

When `(i, j + 1)` is a cell of `μ` this set has one element more than column `j` has cells, while
its labels stay in column `j` or `j + 1` under a column permutation of `t`; that is what makes the
Garnir relation apply to it. -/
def garnirSet (t : YoungTableau μ) (i j : ℕ) : Finset (Fin μ.card) :=
  {k | (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i)}

@[simp]
theorem mem_garnirSet {t : YoungTableau μ} {i j : ℕ} {k : Fin μ.card} :
    k ∈ garnirSet t i j ↔
      (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i) := by
  simp [garnirSet]

/-- Every label of a Garnir set at column `j` lies in a column with at most as many cells as column
`j` has, since columns of a Young diagram shorten to the right. -/
theorem colLen_colIndex_le_of_mem_garnirSet {t : YoungTableau μ} {i j : ℕ} {k : Fin μ.card}
    (hk : k ∈ garnirSet t i j) : μ.colLen (colIndex t k) ≤ μ.colLen j := by
  rcases mem_garnirSet.mp hk with ⟨hcol, -⟩ | ⟨hcol, -⟩
  · rw [hcol]
  · rw [hcol]
    exact μ.colLen_anti j (j + 1) (Nat.le_succ j)

/-- The cells occupied by a Garnir set: those of column `j` from row `i` down, and those of column
`j + 1` from row `i` up. -/
private theorem image_rowIndex_colIndex_garnirSet (t : YoungTableau μ) (i j : ℕ) :
    (garnirSet t i j).image (fun k => (rowIndex t k, colIndex t k)) =
      {c ∈ μ.cells | (c.2 = j ∧ i ≤ c.1) ∨ (c.2 = j + 1 ∧ c.1 ≤ i)} := by
  ext c
  simp only [Finset.mem_image, mem_garnirSet, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨rowIndex_colIndex_mem t k, hk⟩
  · rintro ⟨hmem, hc⟩
    refine ⟨t ⟨c, hmem⟩, ?_, ?_⟩ <;> simp [hc]

/-- The cells of column `j` from row `i` down. -/
private theorem filter_cells_col (i j : ℕ) :
    {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} = (Finset.Ico i (μ.colLen j)).image (fun a => (a, j)) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq,
    YoungDiagram.mem_cells]
  constructor
  · rintro ⟨hmem, rfl, hi⟩
    exact ⟨a, ⟨hi, YoungDiagram.mem_iff_lt_colLen.mp hmem⟩, rfl, rfl⟩
  · rintro ⟨a', ⟨hi, ha⟩, rfl, rfl⟩
    exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr ha, rfl, hi⟩

/-- The cells of column `j + 1` from row `i` up, when `(i, j + 1)` is a cell. -/
private theorem filter_cells_col_succ {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} =
      (Finset.range (i + 1)).image (fun a => (a, j + 1)) := by
  have hlt : i < μ.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp h
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, Prod.mk.injEq,
    YoungDiagram.mem_cells]
  constructor
  · rintro ⟨-, rfl, hi⟩
    exact ⟨a, by omega, rfl, rfl⟩
  · rintro ⟨a', ha, rfl, rfl⟩
    exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by omega), rfl, by omega⟩

/-- **A Garnir set is one bigger than the column it straddles.**  Column `j` contributes its cells
from row `i` down and column `j + 1` its cells from row `i` up, and `(i, j + 1) ∈ μ` makes both
counts available. -/
theorem card_garnirSet (t : YoungTableau μ) {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    (garnirSet t i j).card = μ.colLen j + 1 := by
  classical
  have hij : (i, j) ∈ μ := μ.up_left_mem (le_refl i) (Nat.le_succ j) h
  have hi : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hij
  have hinj : Function.Injective fun k : Fin μ.card => (rowIndex t k, colIndex t k) :=
    rowIndex_colIndex_injective t
  have hcard := Finset.card_image_of_injective (garnirSet t i j) hinj
  rw [image_rowIndex_colIndex_garnirSet] at hcard
  have hdisj :
      Disjoint {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} := by
    rw [Finset.disjoint_left]
    rintro c h₁ h₂
    simp only [Finset.mem_filter] at h₁ h₂
    omega
  rw [← hcard, Finset.filter_or, Finset.card_union_of_disjoint hdisj, filter_cells_col,
    filter_cells_col_succ h, Finset.card_image_of_injective _ (Prod.mk_left_injective j),
    Finset.card_image_of_injective _ (Prod.mk_left_injective (j + 1)), Nat.card_Ico,
    Finset.card_range]
  omega

/-- **The Garnir relation at a Garnir set.**  If `(i, j + 1)` is a cell of `μ`, the antisymmetrizer
of the Garnir set of `t` at `(i, j)` annihilates the polytabloid of `t`. -/
theorem asAlgebraHom_antisymmetrizerOn_garnirSet_eq_zero (t : YoungTableau μ) {i j : ℕ}
    (h : (i, j + 1) ∈ μ) :
    (permutationModule (shapePartition μ)).ρ.asAlgebraHom (antisymmetrizerOn (garnirSet t i j))
        (polytabloid t) = 0 :=
  asAlgebraHom_antisymmetrizerOn_polytabloid_eq_zero t
    (fun _ hk => colLen_colIndex_le_of_mem_garnirSet hk)
    (by rw [card_garnirSet t h]; exact Nat.lt_succ_self _)

end YoungTableau

end TauCeti
