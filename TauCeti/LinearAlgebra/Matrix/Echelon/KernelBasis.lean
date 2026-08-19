/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Echelon.RowReduce
-- `Matrix.mulVecLin` and `Matrix.dotProductBilin`, the two linear maps the statements are about.
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A computable basis of the kernel of a matrix

`TauCeti.rowReduce` puts a list of rows into reduced row echelon form. This file reads a basis of
the kernel off that form, as a genuine `def` on `[Field F] [DecidableEq F]` data.

The recipe is the classical one. Elimination splits the columns in two: the **pivot** columns, one
for each reduced row, and the **free** columns (`TauCeti.IsFreeColumn`), which are the rest. A
vector in the kernel may take arbitrary values in the free columns, and those values then force its
values in the pivot columns; so the kernel has one basis vector per free column, namely
`TauCeti.kernelVector`, which is `1` in its own free column, `0` in every other free column, and
the negated entry of the reduced row of a pivot column there.

## Main definitions

* `TauCeti.pivotColumn`: the pivot column of a reduced row, the untopped
  `TauCeti.rowReducePivot`.
* `TauCeti.IsFreeColumn`: a column at which elimination records no pivot.
* `TauCeti.kernelVector`: the kernel vector attached to a column.
* `TauCeti.kernelBasis`: the kernel basis of a matrix, as a computable list of vectors.
* `TauCeti.freeColumnBasis`: the same basis, bundled as a `Module.Basis` of the kernel indexed by
  the free columns.

## Main results

* `TauCeti.mulVec_kernelVector`: **the kernel vectors lie in the kernel**.
* `TauCeti.linearIndependent_kernelVector`: **they are linearly independent**.
* `TauCeti.span_kernelVector`: **they span the kernel**; with the previous two this makes
  `TauCeti.freeColumnBasis` a basis of it.
* `TauCeti.card_isFreeColumn` and `TauCeti.finrank_ker_mulVecLin`: there are `n - A.rank` free
  columns, so the kernel has that dimension.
* `TauCeti.mulVec_eq_zero_of_mem_kernelBasis`, `TauCeti.linearIndepOn_kernelBasis`,
  `TauCeti.span_kernelBasis`, `TauCeti.nodup_kernelBasis` and `TauCeti.length_kernelBasis`: the
  same four statements and the count, read off the list the algorithm returns.

## Implementation notes

`TauCeti.kernelVector` is defined at every column, not only at the free ones, and is the zero
vector at a pivot column. That is what lets `TauCeti.mulVec_kernelVector` be stated without a
freeness hypothesis, and it is why the sum defining it runs over all reduced rows with a test on
the pivot column rather than over a subtype: no dependent index has to be manufactured.

The list `TauCeti.kernelBasis` is the algorithm's output and `TauCeti.freeColumnBasis` is the
mathematical object; they are kept apart because a `Module.Basis` is not computable data, its
`repr` field being built from the axiom of choice. Each statement about the list has a counterpart
about the family indexed by the free columns, which is the indexing the proofs are done in, and
`TauCeti.range_kernelVector_freeColumn_eq_kernelBasis` is the passage between the two.

## References

Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
asks, as its computable finite-field linear algebra, for a `kernelBasis` produced by verified
Gaussian elimination; `TauCeti.rowReduce` is that elimination and this file reads the basis off it.
-/

public section

namespace TauCeti

open scoped Matrix

universe u

variable {F : Type u} [Field F] [DecidableEq F] {m n : ℕ}

/-! ## Pivot and free columns -/

/-- The pivot column of the `i`-th row of `TauCeti.rowReduceMatrix`. -/
@[expose] def pivotColumn (L : List (Fin n → F)) (i : Fin (rowReduce L).length) : Fin n :=
  ((rowReduce L).get i).1

/-- A column of a list of rows is **free** when Gauss-Jordan elimination records no pivot there.
The free columns index the kernel basis. -/
def IsFreeColumn (L : List (Fin n → F)) (j : Fin n) : Prop :=
  ∀ q ∈ rowReduce L, q.1 ≠ j

instance (L : List (Fin n → F)) : DecidablePred (IsFreeColumn L) := fun j =>
  inferInstanceAs (Decidable (∀ q ∈ rowReduce L, q.1 ≠ j))

variable (L : List (Fin n → F))

/-- The pivot column of a reduced row is the column `TauCeti.rowReducePivot` records. Not `simp`:
`TauCeti.rowReducePivot_apply` already rewrites this left-hand side, to the unbundled
`((rowReduce L).get i).1`. -/
theorem rowReducePivot_eq_pivotColumn (i : Fin (rowReduce L).length) :
    rowReducePivot L i = (pivotColumn L i : WithTop (Fin n)) :=
  rowReducePivot_apply L i

/-- The pivot column of a reduced row, as the column recorded alongside it. -/
theorem pivotColumn_apply (i : Fin (rowReduce L).length) :
    pivotColumn L i = ((rowReduce L).get i).1 :=
  rfl

/-- Distinct reduced rows have distinct pivot columns. -/
theorem pivotColumn_injective : Function.Injective (pivotColumn L) :=
  (strictMono_fst_get_rowReduce L).injective

/-- A column is not free exactly when it is the pivot column of a reduced row. -/
theorem not_isFreeColumn_iff {c : Fin n} :
    ¬IsFreeColumn L c ↔ ∃ i, pivotColumn L i = c := by
  simp only [IsFreeColumn, not_forall, ne_eq, not_not, exists_prop]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hq
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(rowReduce L).get i, List.get_mem _ _, (pivotColumn_apply L i).symm⟩

/-- The pivot column of a reduced row is not free. -/
@[simp]
theorem not_isFreeColumn_pivotColumn (i : Fin (rowReduce L).length) :
    ¬IsFreeColumn L (pivotColumn L i) :=
  (not_isFreeColumn_iff L).mpr ⟨i, rfl⟩

/-- **The reduced rows are the identity on the pivot columns**: the `i`-th reduced row is `1` in
its own pivot column and `0` in every other. -/
@[simp]
theorem rowReduceMatrix_pivotColumn (i i' : Fin (rowReduce L).length) :
    rowReduceMatrix L i (pivotColumn L i') = if i' = i then 1 else 0 := by
  rw [rowReduceMatrix_apply, pivotColumn_apply]
  rcases eq_or_ne i' i with rfl | hne
  · simpa using rowReduce_self L (List.get_mem _ _)
  · rw [ite_eq_right hne]
    exact rowReduce_eq_zero_of_ne L (List.get_mem _ _) (List.get_mem _ _)
      (by simpa only [← pivotColumn_apply] using (pivotColumn_injective L).ne hne)

/-! ## The kernel vectors -/

/-- The kernel vector attached to a column `j` of a list of rows: it is `1` at `j`, `0` at every
other column that is not a pivot, and the negated entry in column `j` of the reduced row of a
pivot column there.

At a pivot column `j` this is the zero vector; the free columns are the ones it is used at. -/
@[expose] def kernelVector (L : List (Fin n → F)) (j : Fin n) : Fin n → F := fun c =>
  (if c = j then 1 else 0) -
    ∑ i : Fin (rowReduce L).length, if pivotColumn L i = c then rowReduceMatrix L i j else 0

/-- The defining formula of `TauCeti.kernelVector`, entry by entry. -/
theorem kernelVector_apply (j c : Fin n) :
    kernelVector L j c =
      (if c = j then 1 else 0) -
        ∑ i : Fin (rowReduce L).length, if pivotColumn L i = c then rowReduceMatrix L i j else 0 :=
  rfl

variable {L}

/-- A kernel vector is `1` in its own column and `0` in every other free column. -/
@[simp]
theorem kernelVector_apply_of_isFreeColumn {c : Fin n} (hc : IsFreeColumn L c) (j : Fin n) :
    kernelVector L j c = if c = j then 1 else 0 := by
  rw [kernelVector_apply, sub_eq_self]
  refine Finset.sum_eq_zero fun i _ => ite_eq_right fun h => ?_
  exact not_isFreeColumn_pivotColumn L i (h ▸ hc)

/-- In a pivot column a kernel vector of a free column is the negated entry of the corresponding
reduced row. -/
@[simp]
theorem kernelVector_pivotColumn {j : Fin n} (hj : IsFreeColumn L j)
    (i : Fin (rowReduce L).length) :
    kernelVector L j (pivotColumn L i) = -rowReduceMatrix L i j := by
  have hne : pivotColumn L i ≠ j := fun h => not_isFreeColumn_pivotColumn L i (h ▸ hj)
  rw [kernelVector_apply, ite_eq_right hne, zero_sub, Finset.sum_eq_single i
    (fun i' _ hne' => ite_eq_right ((pivotColumn_injective L).ne hne'))
    (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl]

/-- **Each reduced row annihilates each kernel vector.** -/
theorem dotProduct_rowReduceMatrix_kernelVector (i : Fin (rowReduce L).length) (j : Fin n) :
    rowReduceMatrix L i ⬝ᵥ kernelVector L j = 0 := by
  have h₁ : ∑ c : Fin n, rowReduceMatrix L i c * (if c = j then (1 : F) else 0) =
      rowReduceMatrix L i j := by simp
  have h₂ : ∑ c : Fin n, rowReduceMatrix L i c *
      ∑ i' : Fin (rowReduce L).length,
        (if pivotColumn L i' = c then rowReduceMatrix L i' j else 0) =
      rowReduceMatrix L i j := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, rowReduceMatrix_pivotColumn]
    simp
  simp only [dotProduct, kernelVector_apply, mul_sub, Finset.sum_sub_distrib, h₁, h₂, sub_self]

/-! ## The kernel of a matrix -/

omit [DecidableEq F] in
/-- A vector annihilated by every element of a set of rows is annihilated by their whole span. -/
private theorem dotProduct_eq_zero_of_mem_span {v : Fin n → F} {s : Set (Fin n → F)}
    (h : ∀ r ∈ s, r ⬝ᵥ v = 0) {r : Fin n → F} (hr : r ∈ Submodule.span F s) : r ⬝ᵥ v = 0 :=
  LinearMap.mem_ker.mp <|
    Submodule.span_le (p := LinearMap.ker ((dotProductBilin F F).flip v)).mpr
      (fun w hw => LinearMap.mem_ker.mpr (h w hw)) hr

variable (L)

/-- **Elimination does not change what is annihilated**: a vector is annihilated by every reduced
row exactly when it is annihilated by every original row. -/
theorem forall_dotProduct_rowReduceMatrix_iff (v : Fin n → F) :
    (∀ i, rowReduceMatrix L i ⬝ᵥ v = 0) ↔ ∀ r ∈ L, r ⬝ᵥ v = 0 := by
  constructor
  · refine fun h r hr => dotProduct_eq_zero_of_mem_span
      (s := {w : Fin n → F | w ∈ (rowReduce L).map Prod.snd}) ?_
      (by rw [span_rowReduce]; exact Submodule.subset_span hr)
    intro w hw
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hq
    simpa only [rowReduceMatrix_apply] using h i
  · refine fun h i => dotProduct_eq_zero_of_mem_span (s := {w : Fin n → F | w ∈ L}) h ?_
    rw [← span_rowReduce]
    exact Submodule.subset_span
      (List.mem_map.mpr ⟨(rowReduce L).get i, List.get_mem _ _, (rowReduceMatrix_apply L i).symm⟩)

variable {L}

variable (A : Matrix (Fin m) (Fin n) F)

/-- The kernel of a matrix, read through elimination: a vector lies in it exactly when every
reduced row of the matrix annihilates it. -/
theorem mulVec_eq_zero_iff_rowReduceMatrix (v : Fin n → F) :
    A *ᵥ v = 0 ↔ ∀ i, rowReduceMatrix (List.ofFn A) i ⬝ᵥ v = 0 := by
  rw [forall_dotProduct_rowReduceMatrix_iff]
  constructor
  · rintro h r hr
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' A r).mp hr
    simpa only [Matrix.mulVec, Pi.zero_apply] using congrFun h i
  · intro h
    funext i
    simpa only [Matrix.mulVec, Pi.zero_apply] using
      h (A i) ((List.mem_ofFn' A (A i)).mpr ⟨i, rfl⟩)

/-- **The kernel vectors lie in the kernel of the matrix.** -/
@[simp]
theorem mulVec_kernelVector (j : Fin n) : A *ᵥ kernelVector (List.ofFn A) j = 0 :=
  (mulVec_eq_zero_iff_rowReduceMatrix A _).mpr fun i => dotProduct_rowReduceMatrix_kernelVector i j

/-! ## The kernel vectors of the free columns are a basis -/

/-- **The kernel vectors of the free columns are linearly independent**, because in the free
columns they are the standard basis. -/
theorem linearIndependent_kernelVector :
    LinearIndependent F fun j : {j : Fin n // IsFreeColumn (List.ofFn A) j} =>
      kernelVector (List.ofFn A) j.1 := by
  refine LinearIndependent.of_comp
    (LinearMap.funLeft F F (Subtype.val : {j : Fin n // IsFreeColumn (List.ofFn A) j} → Fin n)) ?_
  have hcomp : (LinearMap.funLeft F F
      (Subtype.val : {j : Fin n // IsFreeColumn (List.ofFn A) j} → Fin n)) ∘
      (fun j : {j : Fin n // IsFreeColumn (List.ofFn A) j} => kernelVector (List.ofFn A) j.1) =
      fun j => Pi.single j (1 : F) := by
    funext j c
    simp only [Function.comp_apply, LinearMap.funLeft_apply,
      kernelVector_apply_of_isFreeColumn c.2, Pi.single_apply, Subtype.ext_iff]
  rw [hcomp]
  refine linearIndependent_iff'.mpr fun s g hg j hj => ?_
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, ite_eq_left hj, Pi.zero_apply] using congrFun hg j

/-- **Every vector in the kernel is the sum of the kernel vectors of the free columns**, with its
own values in the free columns as coefficients. -/
theorem eq_sum_smul_kernelVector_of_mulVec_eq_zero {v : Fin n → F} (hv : A *ᵥ v = 0) :
    v = ∑ j : {j : Fin n // IsFreeColumn (List.ofFn A) j},
      v j.1 • kernelVector (List.ofFn A) j.1 := by
  set L := List.ofFn A
  have hrow : ∀ i, rowReduceMatrix L i ⬝ᵥ v = 0 := (mulVec_eq_zero_iff_rowReduceMatrix A v).mp hv
  funext c
  rw [Finset.sum_apply]
  by_cases hc : IsFreeColumn L c
  · rw [Finset.sum_eq_single (⟨c, hc⟩ : {j : Fin n // IsFreeColumn L j})
      (fun j _ hne => by
        rw [Pi.smul_apply, kernelVector_apply_of_isFreeColumn hc,
          ite_eq_right fun h => hne (Subtype.ext h.symm), smul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [Pi.smul_apply, kernelVector_apply_of_isFreeColumn hc, ite_eq_left rfl, smul_eq_mul, mul_one]
  obtain ⟨i, rfl⟩ := (not_isFreeColumn_iff L).mp hc
  have hfree : ∑ c ∈ Finset.univ.filter (IsFreeColumn L), rowReduceMatrix L i c * v c =
      ∑ j : {j : Fin n // IsFreeColumn L j}, rowReduceMatrix L i j.1 * v j.1 :=
    Finset.sum_subtype _ (fun x => by simp) _
  have himg : Finset.univ.filter (fun c => ¬IsFreeColumn L c) =
      Finset.image (pivotColumn L) Finset.univ := by
    ext c
    simp [not_isFreeColumn_iff]
  have hpivot : ∑ c ∈ Finset.univ.filter (fun c => ¬IsFreeColumn L c),
      rowReduceMatrix L i c * v c = v (pivotColumn L i) := by
    rw [himg, Finset.sum_image fun x _ y _ h => pivotColumn_injective L h]
    simp
  have hzero : ∑ j : {j : Fin n // IsFreeColumn L j}, rowReduceMatrix L i j.1 * v j.1 +
      v (pivotColumn L i) = 0 := by
    rw [← hfree, ← hpivot, Finset.sum_filter_add_sum_filter_not]
    simpa only [dotProduct] using hrow i
  have hrhs : ∑ j : {j : Fin n // IsFreeColumn L j},
      (v j.1 • kernelVector L j.1) (pivotColumn L i) =
      -∑ j : {j : Fin n // IsFreeColumn L j}, rowReduceMatrix L i j.1 * v j.1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Pi.smul_apply, kernelVector_pivotColumn j.2 i, smul_eq_mul, mul_neg, mul_comm]
  rw [hrhs, eq_neg_iff_add_eq_zero, add_comm]
  exact hzero

/-- **The kernel vectors of the free columns span the kernel**: a vector in the kernel is the
combination of them with its own values in the free columns as coefficients. -/
theorem span_kernelVector :
    Submodule.span F (Set.range fun j : {j : Fin n // IsFreeColumn (List.ofFn A) j} =>
      kernelVector (List.ofFn A) j.1) = LinearMap.ker A.mulVecLin := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun v hv => ?_
  · rintro _ ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (mulVec_kernelVector A j.1)
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  rw [eq_sum_smul_kernelVector_of_mulVec_eq_zero A hv]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **The kernel vectors of the free columns are a basis of the kernel**, indexed by the free
columns. -/
noncomputable def freeColumnBasis :
    Module.Basis {j : Fin n // IsFreeColumn (List.ofFn A) j} F (LinearMap.ker A.mulVecLin) :=
  (Module.Basis.span (linearIndependent_kernelVector A)).map
    (LinearEquiv.ofEq _ _ (span_kernelVector A))

@[simp]
theorem coe_freeColumnBasis_apply (j : {j : Fin n // IsFreeColumn (List.ofFn A) j}) :
    (freeColumnBasis A j : Fin n → F) = kernelVector (List.ofFn A) j.1 := by
  simp [freeColumnBasis]

/-- The number of free columns of a matrix: its number of columns less its rank. -/
theorem card_isFreeColumn :
    Fintype.card {j : Fin n // IsFreeColumn (List.ofFn A) j} = n - A.rank := by
  have hpivot : Fintype.card {j : Fin n // ¬IsFreeColumn (List.ofFn A) j} =
      (rowReduce (List.ofFn A)).length := by
    refine (Fintype.card_of_bijective (f := fun i => (⟨pivotColumn (List.ofFn A) i,
      not_isFreeColumn_pivotColumn (List.ofFn A) i⟩ :
        {j : Fin n // ¬IsFreeColumn (List.ofFn A) j})) ⟨?_, ?_⟩).symm.trans (Fintype.card_fin _)
    · exact fun i i' h => pivotColumn_injective _ (Subtype.ext_iff.mp h)
    · rintro ⟨c, hc⟩
      obtain ⟨i, rfl⟩ := (not_isFreeColumn_iff _).mp hc
      exact ⟨i, rfl⟩
  rw [Fintype.card_subtype_compl, Fintype.card_fin, length_rowReduce_ofFn] at hpivot
  have hle : Fintype.card {j : Fin n // IsFreeColumn (List.ofFn A) j} ≤ n :=
    (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
  omega

omit [DecidableEq F] in
/-- **Rank-nullity for the kernel of a matrix**, in the form elimination produces it. -/
theorem finrank_ker_mulVecLin : Module.finrank F (LinearMap.ker A.mulVecLin) = n - A.rank := by
  classical
  rw [Module.finrank_eq_card_basis (freeColumnBasis A), card_isFreeColumn]

/-! ## The kernel basis as a computable list -/

/-- **The kernel basis of a matrix**, as the algorithm produces it: one vector for each free
column of the reduced row echelon form of the rows, in increasing order of that column. -/
@[expose] def kernelBasis : List (Fin n → F) :=
  ((List.finRange n).filter fun j => decide (IsFreeColumn (List.ofFn A) j)).map
    (kernelVector (List.ofFn A))

/-- The entries of `TauCeti.kernelBasis` are the kernel vectors of the free columns. -/
@[simp]
theorem mem_kernelBasis {v : Fin n → F} :
    v ∈ kernelBasis A ↔
      ∃ j, IsFreeColumn (List.ofFn A) j ∧ kernelVector (List.ofFn A) j = v := by
  simp [kernelBasis, List.mem_filter]

/-- `TauCeti.kernelBasis` lists exactly the kernel vectors of the free columns. -/
theorem range_kernelVector_freeColumn_eq_kernelBasis :
    (Set.range fun j : {j : Fin n // IsFreeColumn (List.ofFn A) j} =>
      kernelVector (List.ofFn A) j.1) = {v : Fin n → F | v ∈ kernelBasis A} := by
  ext v
  rw [Set.mem_ofPred_eq, mem_kernelBasis, Set.mem_range]
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

/-- **The vectors the algorithm returns are linearly independent.** -/
theorem linearIndepOn_kernelBasis :
    LinearIndepOn F id {v : Fin n → F | v ∈ kernelBasis A} := by
  rw [← range_kernelVector_freeColumn_eq_kernelBasis]
  exact (linearIndepOn_id_range_iff (linearIndependent_kernelVector A).injective).mpr
    (linearIndependent_kernelVector A)

/-- **Every vector the algorithm returns lies in the kernel.** -/
theorem mulVec_eq_zero_of_mem_kernelBasis {v : Fin n → F} (hv : v ∈ kernelBasis A) :
    A *ᵥ v = 0 := by
  obtain ⟨j, -, rfl⟩ := (mem_kernelBasis A).mp hv
  exact mulVec_kernelVector A j

/-- **The vectors the algorithm returns span the kernel.** -/
theorem span_kernelBasis :
    Submodule.span F {v : Fin n → F | v ∈ kernelBasis A} = LinearMap.ker A.mulVecLin := by
  rw [← range_kernelVector_freeColumn_eq_kernelBasis, span_kernelVector]

/-- **The algorithm returns no vector twice.** -/
theorem nodup_kernelBasis : (kernelBasis A).Nodup := by
  refine List.Nodup.map_on ?_ ((List.nodup_finRange n).filter _)
  intro j hj j' hj' h
  have hjfree : IsFreeColumn (List.ofFn A) j := by simpa using (List.mem_filter.mp hj).2
  by_contra hne
  have := congrFun h j
  rw [kernelVector_apply_of_isFreeColumn hjfree, ite_eq_left rfl,
    kernelVector_apply_of_isFreeColumn hjfree, ite_eq_right hne] at this
  exact one_ne_zero this

/-- **The algorithm returns `n - rank` vectors**: the rank-nullity theorem, counted off the
output. -/
theorem length_kernelBasis : (kernelBasis A).length = n - A.rank := by
  have hnodup :
      ((List.finRange n).filter fun j => decide (IsFreeColumn (List.ofFn A) j)).Nodup :=
    (List.nodup_finRange n).filter _
  have htoFinset :
      ((List.finRange n).filter fun j => decide (IsFreeColumn (List.ofFn A) j)).toFinset =
        Finset.univ.filter (IsFreeColumn (List.ofFn A)) := by
    ext j
    simp
  rw [kernelBasis, List.length_map, ← card_isFreeColumn A, Fintype.card_subtype]
  rw [← List.toFinset_card_of_nodup hnodup, htoFinset]

end TauCeti
