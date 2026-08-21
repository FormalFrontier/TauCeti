/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chain
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# A chain of a finite-type diagram carries at most one multiple edge

In a finite-type diagram the multiple edges at a *single* index are already restricted: an index
carrying one is joined to every other index by at most a single edge
(`TauCeti.IsFiniteType.apply_mul_apply_le_one_of_two_le`), and a triple edge is isolated outright
(`TauCeti.IsFiniteType.apply_eq_zero_of_apply_mul_apply_eq_three`). Neither statement forbids two
double edges lying at a distance from one another, and that is what this file rules out along a
chain: if the first edge of a chain of `m + 3` vertices is double, the last one is single.

The diagram to exclude is a chain whose two extreme edges are double, and there are two of them,
because a Cartan matrix orients its multiple edges: writing the entry `-2` of a double edge as an
arrow, the two arrows either point away from each other towards the chain ends, or both the same way
along the chain. On `l + 1` vertices these are the diagrams of the affine Kac-Moody algebras
`D⁽²⁾ₗ₊₁` and `A⁽²⁾₂ₗ`, hence singular, so the certificate is in each case a genuine null vector:
`TauCeti.twoDoubleEdgeMark`, which is `1` at the first vertex, `2` at every interior vertex, and,
at the last vertex, `1` when the arrows point outwards and `2` when they agree.

A Cartan matrix is read here as `A i j = ⟨αᵢ, αⱼ^∨⟩`, the transpose of Kac's convention, so it is
the *rows* that annihilate this vector, and what its entries list are the **dual labels** of those
two diagrams, `1, 2, …, 2, 1` and `1, 2, …, 2, 2` — equivalently the marks of the dual diagrams
`C⁽¹⁾ₗ` and `A⁽²⁾₂ₗ`, the latter renumbered backwards, which is what the name records.

Unlike the fork bound of `TauCeti.LinearAlgebra.RootSystem.FiniteType.Star` and the double-edge
bound of `TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge`, which leave surviving shapes and
so end in an arithmetic inequality, no member of this family is of finite type, whatever the length
of the chain. That is what makes the conclusion available in the form the classification wants,
`TauCeti.IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le`: a statement about an arbitrary
finite-type matrix rather than about the model diagram. Its hypotheses are the data of a chain of
indices carrying a multiple edge at one end - distinct indices, non-consecutive ones not joined,
the interior edges, those joining the vertices `s` and `s + 1` for `0 < s < m + 1`, single, and the
first edge multiple - and its conclusion is that the last edge is then single. That is exactly what
a path in the diagram of the matrix supplies, and the extraction of such a path from a diagram
carrying two double edges is the step left outside this file.

Note that the ends of the chain need not be the ends of the diagram: the hypotheses say nothing
about indices outside the chain, since finite type passes to principal submatrices
(`TauCeti.IsFiniteType.submatrix`).

## Main definitions

* `TauCeti.twoDoubleEdgeCartanMatrix`: the Cartan matrix of a chain of `m + 3` vertices whose first
  and last edges are double, the boolean argument orienting the last one.
* `TauCeti.twoDoubleEdgeMark`: the dual labels of that diagram, the null vector the exclusion is
  proved with.

## Main results

* `TauCeti.sum_twoDoubleEdgeCartanMatrix_mul_twoDoubleEdgeMark_eq_zero`: the marks are a null
  vector of the diagram.
* `TauCeti.not_isFiniteType_twoDoubleEdgeCartanMatrix`: **no doubly ended chain is of finite
  type**, in either orientation and at every length.
* `TauCeti.IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le`: **at most one edge of a chain
  of a finite-type diagram is multiple**, the form the classification consumes.

## References

This file supplies the "at most one multiple edge" step of the classification of finite-type Cartan
matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, step (5), and
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §4. The two affine diagrams and their
labels are Table Aff 2 of V. G. Kac, *Infinite Dimensional Lie Algebras*, CUP (1990), whose
convention `aᵢⱼ = ⟨αⱼ, αᵢ^∨⟩` is the transpose of the one used here.
-/

namespace TauCeti

variable {m : ℕ} {b : Bool}

/-! ## The doubly ended chain and its marks -/

/-- The **Cartan matrix of a doubly ended chain**: `m + 3` vertices in a row, joined by single
edges except for the first and the last edges, which are double.

The first double edge is oriented once and for all, the entry from the second vertex to the first
being `-2`. The boolean `b` orients the last one: the entry from the vertex `m + 1` to the vertex
`m + 2` is `-2` when `b` is `true`, so that the two double edges point away from each other towards
the chain ends, and the opposite entry is `-2` when `b` is `false`, so that they point the same way
along the chain. In the notation of Kac's tables, read through the transpose, the first diagram is
`D⁽²⁾ₘ₊₃` and the second is `A⁽²⁾₂ₘ₊₄`. -/
def twoDoubleEdgeCartanMatrix (m : ℕ) (b : Bool) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  Matrix.of fun i j ↦
    if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -2
    else if (i : ℕ) = m + 1 ∧ (j : ℕ) = m + 2 then (if b then -2 else -1)
    else if (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 1 then (if b then -1 else -2)
    else chainEntry (i : ℕ) (j : ℕ)

-- `(rfl)`, not `rfl`: the bodies of the definitions in this file are deliberately left unexposed,
-- and the parenthesised form keeps these equations out of the exported definitional-equality
-- check.
lemma twoDoubleEdgeCartanMatrix_def (i j : Fin (m + 3)) :
    twoDoubleEdgeCartanMatrix m b i j =
      if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -2
      else if (i : ℕ) = m + 1 ∧ (j : ℕ) = m + 2 then (if b then -2 else -1)
      else if (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 1 then (if b then -1 else -2)
      else chainEntry (i : ℕ) (j : ℕ) := (rfl)

/-- The entry of the first double edge that carries the arrow. -/
@[simp] lemma twoDoubleEdgeCartanMatrix_one_zero :
    twoDoubleEdgeCartanMatrix m b 1 0 = -2 := by
  simp [twoDoubleEdgeCartanMatrix_def]

/-- The opposite entry of the first double edge. -/
@[simp] lemma twoDoubleEdgeCartanMatrix_zero_one :
    twoDoubleEdgeCartanMatrix m b 0 1 = -1 := by
  simp [twoDoubleEdgeCartanMatrix_def]

/-- The entry of the last double edge, from the vertex `m + 1` to the vertex `m + 2`. -/
@[simp] lemma twoDoubleEdgeCartanMatrix_last_left :
    twoDoubleEdgeCartanMatrix m b ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ = if b then -2 else -1 := by
  simp [twoDoubleEdgeCartanMatrix_def]

/-- The entry of the last double edge, from the vertex `m + 2` to the vertex `m + 1`. -/
@[simp] lemma twoDoubleEdgeCartanMatrix_last_right :
    twoDoubleEdgeCartanMatrix m b ⟨m + 2, by omega⟩ ⟨m + 1, by omega⟩ = if b then -1 else -2 := by
  simp [twoDoubleEdgeCartanMatrix_def]

/-- **The doubly ended chain, entry by entry, as a chain corrected at its two extreme edges.** Away
from the four entries of those two edges the diagram is the chain of `m + 3` vertices, and at each
of the four it is lowered from the chain entry `-1` to `-2` exactly once, on the side the
orientation names. This is the form in which the row sums below are computed. -/
private lemma twoDoubleEdgeCartanMatrix_eq_sub (i j : Fin (m + 3)) :
    twoDoubleEdgeCartanMatrix m b i j
      = chainEntry (i : ℕ) (j : ℕ)
        - (if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then 1 else 0)
        - (if (i : ℕ) = m + 1 ∧ (j : ℕ) = m + 2 then (if b then 1 else 0) else 0)
        - (if (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 1 then (if b then 0 else 1) else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [twoDoubleEdgeCartanMatrix_def, chainEntry_def]
  split_ifs <;> omega

/-- The **marks** of a doubly ended chain: `1` at the first vertex, `2` at every other one, except
that the last vertex also carries `1` when the two double edges point outwards towards the chain
ends.

At the vertices of the chain these are the dual labels of the affine diagram the chain is, the
marks of its dual: `1, 2, …, 2, 1` for `D⁽²⁾ₘ₊₃`, when `b` is `true`, and `1, 2, …, 2, 2` for
`A⁽²⁾₂ₘ₊₄`, when `b` is `false`. It is the dual labels, and so the rows of the matrix, that occur
here because the convention of this repository, `A i j = ⟨αᵢ, αⱼ^∨⟩`, is the transpose of Kac's.
The function is indexed by the vertices `Fin (m + 3)` of the diagram. -/
def twoDoubleEdgeMark (m : ℕ) (b : Bool) (s : Fin (m + 3)) : ℚ :=
  if (s : ℕ) = 0 ∨ (b ∧ (s : ℕ) = m + 2) then 1 else 2

lemma twoDoubleEdgeMark_def (s : Fin (m + 3)) :
    twoDoubleEdgeMark m b s =
      if (s : ℕ) = 0 ∨ (b ∧ (s : ℕ) = m + 2) then 1 else 2 := (rfl)

/-- The first vertex of the chain carries the mark `1`. -/
@[simp] lemma twoDoubleEdgeMark_zero : twoDoubleEdgeMark m b 0 = 1 := by
  rw [twoDoubleEdgeMark_def]
  simp

/-- The last vertex carries the mark `1` exactly when the double edges point outwards. -/
@[simp] lemma twoDoubleEdgeMark_last :
    twoDoubleEdgeMark m b ⟨m + 2, by omega⟩ = if b then 1 else 2 := by
  rw [twoDoubleEdgeMark_def]
  rcases b with _ | _ <;> simp

/-- Every vertex strictly between the two ends carries the mark `2`. -/
@[simp] lemma twoDoubleEdgeMark_interior (s : Fin (m + 3))
    (hzero : 0 < (s : ℕ)) (hlast : (s : ℕ) < m + 2) : twoDoubleEdgeMark m b s = 2 := by
  rw [twoDoubleEdgeMark_def]
  simp [ne_of_gt hzero, ne_of_lt hlast]

/-- The marks are positive, which is what makes them a nonzero certificate. -/
lemma twoDoubleEdgeMark_pos (s : Fin (m + 3)) : 0 < twoDoubleEdgeMark m b s := by
  rw [twoDoubleEdgeMark_def]
  split_ifs <;> norm_num

/-! ## The rows of the diagram at its marks -/

private def twoDoubleEdgeMarkNat (m : ℕ) (b : Bool) (s : ℕ) : ℚ :=
  if s = 0 ∨ (b ∧ s = m + 2) then 1 else 2

/-- The chain part of a row, evaluated at the marks: this is the chain row identity
`TauCeti.sum_range_chainEntry_mul` read on `Fin (m + 3)`, the weight at the vertex `s` being the
mark of `s`. -/
private theorem sum_fin_chainEntry_mul_twoDoubleEdgeMark (i : Fin (m + 3)) :
    ∑ j : Fin (m + 3),
      ((chainEntry (i : ℕ) (j : ℕ) : ℤ) : ℚ) * twoDoubleEdgeMarkNat m b (j : ℕ)
      = 2 * twoDoubleEdgeMarkNat m b (i : ℕ)
        - (if (i : ℕ) = 0 then 0 else twoDoubleEdgeMarkNat m b ((i : ℕ) - 1))
        - (if (i : ℕ) + 1 = m + 3 then 0 else twoDoubleEdgeMarkNat m b ((i : ℕ) + 1)) := by
  have h := sum_range_chainEntry_mul (R := ℚ) (n := m + 3) (m := (i : ℕ)) i.isLt
    (fun u ↦ twoDoubleEdgeMarkNat m b (u - 1))
  rw [Fin.sum_univ_eq_sum_range
    (fun s ↦ ((chainEntry (i : ℕ) s : ℤ) : ℚ) * twoDoubleEdgeMarkNat m b s)]
  simpa using h

/-- **The row identity at a vertex number.** Away from the two ends of the chain the marks are
constant, so the second difference vanishes; at the first vertex the mark is half of its
neighbour's, and at the last one the drop in the mark, when there is one, is exactly compensated by
the double edge. Only the vertex numbers occur here, which is what the row sums of the diagram
reduce to. -/
private lemma twoDoubleEdgeMarkNat_row (m : ℕ) (b : Bool) {s : ℕ} (hs : s < m + 3) :
    2 * twoDoubleEdgeMarkNat m b s - (if s = 0 then 0 else twoDoubleEdgeMarkNat m b (s - 1))
        - (if s + 1 = m + 3 then 0 else twoDoubleEdgeMarkNat m b (s + 1))
        - (if s = 1 then 1 * twoDoubleEdgeMarkNat m b 0 else 0)
        - (if s = m + 1 then
            (if b then (1 : ℚ) else 0) * twoDoubleEdgeMarkNat m b (m + 2) else 0)
        - (if s = m + 2 then
            (if b then (0 : ℚ) else 1) * twoDoubleEdgeMarkNat m b (m + 1) else 0)
      = 0 := by
  rcases b with _ | _ <;> norm_num [twoDoubleEdgeMarkNat] <;> split_ifs <;>
    first
      | (exfalso; omega)
      | norm_num

private lemma sum_fin_ite_and_eq_mul {n r k : ℕ} (i : Fin n) (hk : k < n) (c : ℚ)
    (w : Fin n → ℚ) :
    (∑ j : Fin n, (if (i : ℕ) = r ∧ (j : ℕ) = k then c else 0) * w j) =
      if (i : ℕ) = r then c * w ⟨k, hk⟩ else 0 := by
  by_cases hi : (i : ℕ) = r
  · simp only [hi, true_and, ite_true]
    simpa only [Fin.ext_iff, ite_mul, zero_mul] using
      Fintype.sum_ite_eq' (⟨k, hk⟩ : Fin n) (fun j ↦ c * w j)
  · simp [hi]

private theorem sum_twoDoubleEdgeCartanMatrix_mul_twoDoubleEdgeMarkNat_eq_zero
    (i : Fin (m + 3)) :
    ∑ j : Fin (m + 3), ((twoDoubleEdgeCartanMatrix m b i j : ℤ) : ℚ)
      * twoDoubleEdgeMarkNat m b (j : ℕ) = 0 := by
  have hfirst := sum_fin_ite_and_eq_mul i (k := 0) (r := 1) (by omega) 1
    (fun j ↦ twoDoubleEdgeMarkNat m b (j : ℕ))
  have hlast := sum_fin_ite_and_eq_mul i (k := m + 2) (r := m + 1) (by omega)
    (if b then 1 else 0) (fun j ↦ twoDoubleEdgeMarkNat m b (j : ℕ))
  have hlast' := sum_fin_ite_and_eq_mul i (k := m + 1) (r := m + 2) (by omega)
    (if b then 0 else 1) (fun j ↦ twoDoubleEdgeMarkNat m b (j : ℕ))
  have hsplit : ∀ j : Fin (m + 3), ((twoDoubleEdgeCartanMatrix m b i j : ℤ) : ℚ)
      * twoDoubleEdgeMarkNat m b (j : ℕ)
      = ((chainEntry (i : ℕ) (j : ℕ) : ℤ) : ℚ) * twoDoubleEdgeMarkNat m b (j : ℕ)
        - (if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then (1 : ℚ) else 0)
          * twoDoubleEdgeMarkNat m b (j : ℕ)
        - (if (i : ℕ) = m + 1 ∧ (j : ℕ) = m + 2 then (if b then (1 : ℚ) else 0) else 0)
          * twoDoubleEdgeMarkNat m b (j : ℕ)
        - (if (i : ℕ) = m + 2 ∧ (j : ℕ) = m + 1 then (if b then (0 : ℚ) else 1) else 0)
          * twoDoubleEdgeMarkNat m b (j : ℕ) := by
    intro j
    rw [twoDoubleEdgeCartanMatrix_eq_sub]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, sum_fin_chainEntry_mul_twoDoubleEdgeMark,
    hfirst, hlast, hlast']
  exact twoDoubleEdgeMarkNat_row m b i.isLt

/-- **The marks are a null vector of the doubly ended chain:** every row annihilates them. -/
theorem sum_twoDoubleEdgeCartanMatrix_mul_twoDoubleEdgeMark_eq_zero (i : Fin (m + 3)) :
    ∑ j : Fin (m + 3), ((twoDoubleEdgeCartanMatrix m b i j : ℤ) : ℚ)
      * twoDoubleEdgeMark m b j = 0 := by
  simpa [twoDoubleEdgeMark, twoDoubleEdgeMarkNat] using
    sum_twoDoubleEdgeCartanMatrix_mul_twoDoubleEdgeMarkNat_eq_zero (m := m) (b := b) i

/-- **No doubly ended chain is of finite type**: whatever the length of the chain, and whichever
way the two double edges are oriented, the marks are a nonzero null vector, and a finite-type
matrix admits none.

Together with `TauCeti.IsFiniteType.apply_eq_zero_of_apply_mul_apply_eq_three`, which isolates a
triple edge, this is the whole of the "at most one multiple edge" step of the classification: it is
turned into a statement about an arbitrary finite-type matrix in
`TauCeti.IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le`. -/
theorem not_isFiniteType_twoDoubleEdgeCartanMatrix (m : ℕ) (b : Bool) :
    ¬ IsFiniteType (twoDoubleEdgeCartanMatrix m b) := by
  intro h
  have hzero := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos
    (x := twoDoubleEdgeMark m b) fun i ↦ by
      rw [sum_twoDoubleEdgeCartanMatrix_mul_twoDoubleEdgeMark_eq_zero, mul_zero]
  have hfirst := congrFun hzero (⟨0, by omega⟩ : Fin (m + 3))
  rw [Pi.zero_apply] at hfirst
  exact absurd hfirst (twoDoubleEdgeMark_pos (m := m) (b := b) _).ne'

/-! ### The shortest doubly ended chains

The two diagrams on three vertices, written out; they fix the conventions. They are also the two
diagrams that the classical argument reaches by contracting the chain between the two double edges,
a contraction that is not needed here, since the marks are available at every length.
-/

/-- **The shortest doubly ended chain with the two double edges pointing outwards towards the chain
ends**: the twisted affine diagram `D⁽²⁾₃`, whose dual labels are `1, 2, 1`. -/
theorem twoDoubleEdgeCartanMatrix_zero_true :
    twoDoubleEdgeCartanMatrix 0 true = !![2, -1, 0; -2, 2, -2; 0, -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoDoubleEdgeCartanMatrix_def]

/-- **The shortest doubly ended chain with the two double edges pointing the same way**: the
twisted affine diagram `A⁽²⁾₄`, whose dual labels are `1, 2, 2`. -/
theorem twoDoubleEdgeCartanMatrix_zero_false :
    twoDoubleEdgeCartanMatrix 0 false = !![2, -1, 0; -2, 2, -1; 0, -2, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoDoubleEdgeCartanMatrix_def]

/-! ## Two double edges along a chain of an arbitrary diagram -/

section Chain

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-- **Two nonpositive integers whose product is `2` are `-1` and `-2`**, in one order or the other:
the two entries of a double edge, whose orientation this splits into its two cases. -/
lemma eq_neg_one_and_eq_neg_two_or_of_mul_eq_two {x y : ℤ} (hx : x ≤ 0)
    (hxy : x * y = 2) : (x = -1 ∧ y = -2) ∨ (x = -2 ∧ y = -1) := by
  have hdvd : (-x) ∣ 2 := ⟨-y, by rw [neg_mul_neg, hxy]⟩
  have hle : -x ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
  have hlb : -2 ≤ x := by omega
  interval_cases x <;> omega

/-- **A chain of a finite-type diagram whose first edge points backwards and whose last edge is
double is the doubly ended chain**, as a principal submatrix. The orientation of the last edge is
recorded by the boolean `b`, which the two hypotheses `hlast` and `hlast'` read in the two entries
of that edge. -/
private theorem submatrix_eq_twoDoubleEdgeCartanMatrix (h : IsFiniteType A) {v : ℕ → B}
    (hzero : ∀ s t, s + 1 < t → t < m + 3 → A (v s) (v t) = 0)
    (hsimple : ∀ s, 0 < s → s < m + 1 → A (v s) (v (s + 1)) = -1 ∧ A (v (s + 1)) (v s) = -1)
    (hfirst : A (v 1) (v 0) = -2) (hfirst' : A (v 0) (v 1) = -1)
    (hlast : A (v (m + 1)) (v (m + 2)) = if b then -2 else -1)
    (hlast' : A (v (m + 2)) (v (m + 1)) = if b then -1 else -2) :
    A.submatrix (fun i : Fin (m + 3) ↦ v (i : ℕ)) (fun i : Fin (m + 3) ↦ v (i : ℕ))
      = twoDoubleEdgeCartanMatrix m b := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.submatrix_apply, twoDoubleEdgeCartanMatrix_def]
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
  · -- Below the diagonal of the chain: either the edge from `i` to `i + 1`, or no edge at all.
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hfar | hnear
    · rw [hzero _ _ hfar hj, chainEntry_eq_zero (by omega) (by omega) (by omega)]
      split_ifs <;> omega
    · have hsucc : (j : ℕ) = (i : ℕ) + 1 := by omega
      rw [hsucc, chainEntry_succ_right]
      rcases Nat.eq_zero_or_pos (i : ℕ) with hzero' | hpos
      · rw [hzero', hfirst']
        split_ifs <;> first | omega | simp_all
      rcases Nat.lt_or_ge (i : ℕ) (m + 1) with hmid | htop
      · rw [(hsimple _ hpos hmid).1]
        split_ifs <;> first | omega | simp_all
      · have htop' : (i : ℕ) = m + 1 := by omega
        rw [htop', hlast]
        split_ifs <;> first | omega | simp_all
  · -- The diagonal.
    rw [heq, h.apply_self, chainEntry_self]
    split_ifs <;> omega
  · -- Above the diagonal, the same three cases read backwards.
    rcases Nat.lt_or_ge ((j : ℕ) + 1) (i : ℕ) with hfar | hnear
    · rw [h.apply_eq_zero_symm (hzero _ _ hfar hi),
        chainEntry_eq_zero (by omega) (by omega) (by omega)]
      split_ifs <;> omega
    · have hsucc : (i : ℕ) = (j : ℕ) + 1 := by omega
      rw [hsucc, chainEntry_succ_left]
      rcases Nat.eq_zero_or_pos (j : ℕ) with hzero' | hpos
      · rw [hzero', hfirst]
        split_ifs <;> omega
      rcases Nat.lt_or_ge (j : ℕ) (m + 1) with hmid | htop
      · rw [(hsimple _ hpos hmid).2]
        split_ifs <;> omega
      · have htop' : (j : ℕ) = m + 1 := by omega
        rw [htop', hlast']
        split_ifs <;> omega

/-- **A chain of a finite-type diagram whose first edge points backwards carries no second double
edge.** This is the previous exclusion transported along the chain; the orientation of the first
edge is normalized here, and the general case follows by transposition in
`TauCeti.IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le`. -/
private theorem not_two_le_of_chain_of_apply_eq_neg_two (h : IsFiniteType A) {v : ℕ → B}
    (hv : Set.InjOn v (Set.Iio (m + 3)))
    (hzero : ∀ s t, s + 1 < t → t < m + 3 → A (v s) (v t) = 0)
    (hsimple : ∀ s, 0 < s → s < m + 1 → A (v s) (v (s + 1)) = -1 ∧ A (v (s + 1)) (v s) = -1)
    (hfirst : A (v 1) (v 0) = -2) (hfirst' : A (v 0) (v 1) = -1)
    (hlast : A (v (m + 1)) (v (m + 2)) * A (v (m + 2)) (v (m + 1)) = 2) : False := by
  have hne : v (m + 1) ≠ v (m + 2) := fun hc ↦ by
    simpa using hv (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) hc
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := eq_neg_one_and_eq_neg_two_or_of_mul_eq_two
    (h.apply_le_zero_of_ne hne) hlast
  · -- The two double edges point the same way along the chain.
    refine not_isFiniteType_twoDoubleEdgeCartanMatrix m false ?_
    rw [← submatrix_eq_twoDoubleEdgeCartanMatrix h hzero hsimple hfirst hfirst'
      (by simpa using h1) (by simpa using h2)]
    exact h.submatrix fun i j hij ↦ Fin.ext
      (hv (Set.mem_Iio.2 i.isLt) (Set.mem_Iio.2 j.isLt) hij)
  · -- The two double edges point outwards towards the chain ends.
    refine not_isFiniteType_twoDoubleEdgeCartanMatrix m true ?_
    rw [← submatrix_eq_twoDoubleEdgeCartanMatrix h hzero hsimple hfirst hfirst'
      (by simpa using h1) (by simpa using h2)]
    exact h.submatrix fun i j hij ↦ Fin.ext
      (hv (Set.mem_Iio.2 i.isLt) (Set.mem_Iio.2 j.isLt) hij)

/-- **At most one edge of a chain of a finite-type diagram is multiple.** Let `v 0, …, v (m + 2)`
be distinct indices of a finite-type matrix, non-consecutive ones not joined at all and the
interior edges of the chain - those joining `v s` to `v (s + 1)` for `0 < s < m + 1` - single. If
the first edge, the one joining `v 0` to `v 1`, is multiple, then the last one, joining `v (m + 1)`
to `v (m + 2)`, is single; nothing is assumed about that last edge beforehand.

Nothing is assumed about the indices outside the chain: finite type passes to principal
submatrices, so the chain may sit anywhere inside a larger diagram. The hypotheses are what a path
in the diagram of the matrix provides, the non-adjacency of non-consecutive vertices coming from
the diagram of a finite-type matrix being a forest
(`TauCeti.isAcyclic_diagramGraph`). -/
theorem IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le (h : IsFiniteType A) {v : ℕ → B}
    (hv : Set.InjOn v (Set.Iio (m + 3)))
    (hzero : ∀ s t, s + 1 < t → t < m + 3 → A (v s) (v t) = 0)
    (hsimple : ∀ s, 0 < s → s < m + 1 → A (v s) (v (s + 1)) * A (v (s + 1)) (v s) = 1)
    (hfirst : 2 ≤ A (v 0) (v 1) * A (v 1) (v 0)) :
    A (v (m + 1)) (v (m + 2)) * A (v (m + 2)) (v (m + 1)) ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hvne : ∀ s t, s < m + 3 → t < m + 3 → s ≠ t → v s ≠ v t := fun s t hs ht hst hc ↦
    hst (hv (Set.mem_Iio.2 hs) (Set.mem_Iio.2 ht) hc)
  -- The second edge of the chain is present: it is an interior edge, or, on the shortest chain,
  -- the last edge.
  have hedge12 : A (v 1) (v 2) * A (v 2) (v 1) ≠ 0 := by
    intro hc
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.zero_add] at hcon
      rw [hc] at hcon
      exact absurd hcon (by norm_num)
    · have h1 := hsimple 1 one_pos (by omega)
      norm_num at h1
      rw [hc] at h1
      exact absurd h1 (by norm_num)
  -- So is the edge before the last one, which on the shortest chain is the first edge.
  have hedgeLast : A (v (m + 1)) (v m) * A (v m) (v (m + 1)) ≠ 0 := by
    intro hc
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.zero_add, mul_comm] at hc
      rw [hc] at hfirst
      exact absurd hfirst (by norm_num)
    · have h1 := hsimple m hm (by omega)
      rw [mul_comm] at hc
      rw [hc] at h1
      exact absurd h1 (by norm_num)
  -- Neither extreme edge is triple: a triple edge is isolated, while both of its ends carry a
  -- further edge of the chain.
  have hnot3first : A (v 0) (v 1) * A (v 1) (v 0) ≠ 3 := by
    intro hc
    refine hedge12 ?_
    rw [h.apply_eq_zero_of_apply_mul_apply_eq_three (i := v 1) (j := v 0) (k := v 2)
      (hvne 1 2 (by omega) (by omega) (by omega)) (hvne 0 2 (by omega) (by omega) (by omega))
      (by rw [mul_comm]; exact hc), zero_mul]
  have hnot3last : A (v (m + 1)) (v (m + 2)) * A (v (m + 2)) (v (m + 1)) ≠ 3 := by
    intro hc
    refine hedgeLast ?_
    rw [h.apply_eq_zero_of_apply_mul_apply_eq_three (i := v (m + 1)) (j := v (m + 2)) (k := v m)
      (hvne (m + 1) m (by omega) (by omega) (by omega))
      (hvne (m + 2) m (by omega) (by omega) (by omega)) hc, zero_mul]
  -- So both extreme edges are double, their Cartan product being at most `3` in any case.
  have hfirst2 : A (v 0) (v 1) * A (v 1) (v 0) = 2 := by
    have hmem := h.apply_mul_apply_mem_of_ne (hvne 0 1 (by omega) (by omega) (by omega))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hval | hval | hval | hval
    · rw [hval] at hfirst; exact absurd hfirst (by norm_num)
    · rw [hval] at hfirst; exact absurd hfirst (by norm_num)
    · exact hval
    · exact absurd hval hnot3first
  have hlast2 : A (v (m + 1)) (v (m + 2)) * A (v (m + 2)) (v (m + 1)) = 2 := by
    have hmem := h.apply_mul_apply_mem_of_ne
      (hvne (m + 1) (m + 2) (by omega) (by omega) (by omega))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hval | hval | hval | hval
    · rw [hval] at hcon; exact absurd hcon (by norm_num)
    · rw [hval] at hcon; exact absurd hcon (by norm_num)
    · exact hval
    · exact absurd hval hnot3last
  -- The interior edges are single, so both of their entries are `-1`.
  have hsimple' : ∀ s, 0 < s → s < m + 1 → A (v s) (v (s + 1)) = -1 ∧ A (v (s + 1)) (v s) = -1 := by
    intro s hpos hlt
    have hne := hvne s (s + 1) (by omega) (by omega) (by omega)
    have h1 := h.apply_le_zero_of_ne hne
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 (hsimple s hpos hlt) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1] at h1; exact absurd h1 (by norm_num)
    · exact ⟨e1, e2⟩
  -- Both orientations of the first edge are excluded, the second by transposition.
  have hne01 := hvne 0 1 (by omega) (by omega) (by omega)
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := eq_neg_one_and_eq_neg_two_or_of_mul_eq_two
    (h.apply_le_zero_of_ne hne01) hfirst2
  · exact not_two_le_of_chain_of_apply_eq_neg_two h hv hzero hsimple' h2 h1 hlast2
  · refine not_two_le_of_chain_of_apply_eq_neg_two h.transpose hv
      (fun s t hst ht ↦ h.apply_eq_zero_symm (hzero s t hst ht))
      (fun s hpos hlt ↦ ⟨(hsimple' s hpos hlt).2, (hsimple' s hpos hlt).1⟩) h1 h2 ?_
    rw [Matrix.transpose_apply, Matrix.transpose_apply, mul_comm]
    exact hlast2

end Chain

end TauCeti
