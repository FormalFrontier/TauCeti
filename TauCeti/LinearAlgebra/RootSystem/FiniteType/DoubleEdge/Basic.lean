/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chain
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

public section

/-!
# The double-edge bound for finite-type Cartan matrices

In a finite-type diagram an index carrying a multiple edge is joined to every *other* index by at
most a single edge (`TauCeti.IsFiniteType.apply_mul_apply_le_one_of_two_le`) - a restriction on what
is incident to one endpoint of the edge, not yet a count of the multiple edges of a whole diagram -
and a triple edge is isolated outright
(`TauCeti.IsFiniteType.apply_eq_zero_of_apply_mul_apply_eq_three`), which leaves `G₂`. A double
edge is not isolated. Once the component carrying one has been shown to have no branch vertex - a
step taken outside this file, as noted below - it is two chains, of `p` and of `q` vertices, joined
at their last vertices by that edge, and that is the shape this file takes as given. Which of those
survive is the *chain* half of the "chain/fork length constraints" of the Cartan--Killing
classification, and, like the fork half in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic`, it is an arithmetic constraint:

`2 p q < (p + 1) (q + 1)`,

equivalently `(p - 1) (q - 1) < 2`, whose solutions with both chains nonempty are `q = 1` (the
chains `Cₙ`), `p = 1` (the chains `Bₙ`), and `p = q = 2` (`F₄`).

This file builds that diagram as a matrix, `TauCeti.doubleEdgeCartanMatrix`, out of the chain
entries of `TauCeti.LinearAlgebra.RootSystem.Chain`, and proves the bound. The elimination tool is
the one the fork bound uses: a finite-type matrix admits no nonzero
**subdominant** vector, one whose every coordinate `xᵢ` has `xᵢ · (A x)ᵢ ≤ 0`
(`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos`). The certificate is the vector
of **marks** `TauCeti.doubleEdgeMark`, which grows linearly along each of the two chains towards
the double edge, in steps of `q` on the side of `p` vertices and of `p + 1` on the other. Those two
slopes are chosen so that the marks are annihilated at every vertex of the diagram except the far
end of the second chain, where the row takes the value `(p + 1) (q + 1) - 2 p q`, which is `≤ 0`
exactly when the bound fails.

The critical diagram, where the marks are a genuine null vector, is the extended Dynkin diagram
`F̃₄ = T(3, 2)`; it is recorded as a corollary. The bound is sharp along the two families it leaves:
`TauCeti.isFiniteType_doubleEdgeCartanMatrix_one_right` identifies the diagram at `q = 1` with
Mathlib's `CartanMatrix.C (p + 1)`, so it really is of finite type there, and the case `p = 1`
follows by transposition.

The orientation is fixed once: the entry from the last vertex of the second chain to the last
vertex of the first is `-2`, and the opposite entry is `-1`. The reversed diagram is the transpose
(`TauCeti.doubleEdgeCartanMatrix_transpose`), which finite type is invariant under
(`TauCeti.IsFiniteType.transpose`), and the bound is symmetric in `p` and `q`, so nothing is lost.

As with the fork bound, only the arithmetic constraint is proved here: the step that produces such
a subdiagram from a finite-type diagram carrying a double edge - which is where the absence of a
branch vertex is established - is outside this file.

## Main definitions

* `TauCeti.doubleEdgeCartanMatrix`: the Cartan matrix of two chains, of `p` and of `q` vertices,
  joined by a double edge at their last vertices.
* `TauCeti.doubleEdgeMark`: the marks of that diagram, the test vector the bound is proved with.

## Main results

* `TauCeti.two_mul_mul_lt_succ_mul_succ_of_isFiniteType_doubleEdge` and
  `TauCeti.not_isFiniteType_doubleEdgeCartanMatrix_of_succ_mul_succ_le`: **the double-edge bound**,
  `2 p q < (p + 1) (q + 1)`, and its contrapositive.
* `TauCeti.eq_one_or_eq_one_or_eq_two_two_of_isFiniteType_doubleEdge`: **the admissible shapes**.
  A double-edge diagram of finite type with nonempty chains has `p = 1`, or `q = 1`, or
  `p = q = 2`: the families `Bₙ`, `Cₙ`, and `F₄`.
* `TauCeti.not_isFiniteType_affineF₄`: the critical diagram is not of finite type.
* `TauCeti.isFiniteType_doubleEdgeCartanMatrix_one_right` and
  `TauCeti.isFiniteType_doubleEdgeCartanMatrix_one_left`: the two families the bound leaves are of
  finite type, so the bound is sharp and its hypothesis is not vacuous.

## References

This file supplies the chain half of the "chain/fork length constraints" step of the classification
of finite-type Cartan matrices, Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See J. E. Humphreys, *Introduction to
Lie Algebras and Representation Theory*, §11.4, step (6), where the same linear weighting of the two
chains gives `(p - 1) (q - 1) < 2`, and Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*,
Ch. VI §4.
-/

open scoped Matrix

namespace TauCeti

variable {p q : ℕ}

/-! ## The diagram and its marks -/

/-- The **Cartan matrix of a double-edge chain**: two chains, of `p` and of `q` vertices, whose last
vertices are joined by a double edge. The entry from the second chain to the first is `-2` and the
opposite entry is `-1`, so at `q = 1` this is the Cartan matrix of type `Cₚ₊₁`
(`TauCeti.doubleEdgeCartanMatrix_one_right`). -/
def doubleEdgeCartanMatrix (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℤ :=
  Matrix.of fun v w ↦
    match v, w with
    | .inl v, .inl w => chainEntry v w
    | .inr v, .inr w => chainEntry v w
    | .inl v, .inr w => if (v : ℕ) + 1 = p ∧ (w : ℕ) + 1 = q then -1 else 0
    | .inr v, .inl w => if (v : ℕ) + 1 = q ∧ (w : ℕ) + 1 = p then -2 else 0

-- `(rfl)`, not `rfl`: the bodies of the definitions in this file are deliberately left unexposed,
-- and the parenthesised form keeps these equations out of the exported definitional-equality check.
/-- The first chain is a chain. -/
@[simp] lemma doubleEdgeCartanMatrix_inl_inl (v w : Fin p) :
    doubleEdgeCartanMatrix p q (Sum.inl v) (Sum.inl w) = chainEntry v w := (rfl)

/-- The second chain is a chain. -/
@[simp] lemma doubleEdgeCartanMatrix_inr_inr (v w : Fin q) :
    doubleEdgeCartanMatrix p q (Sum.inr v) (Sum.inr w) = chainEntry v w := (rfl)

/-- The two chains meet only at their last vertices, where the entry is `-1` in this direction. -/
@[simp] lemma doubleEdgeCartanMatrix_inl_inr (v : Fin p) (w : Fin q) :
    doubleEdgeCartanMatrix p q (Sum.inl v) (Sum.inr w)
      = if (v : ℕ) + 1 = p ∧ (w : ℕ) + 1 = q then -1 else 0 := (rfl)

/-- The two chains meet only at their last vertices, where the entry is `-2` in this direction. -/
@[simp] lemma doubleEdgeCartanMatrix_inr_inl (v : Fin q) (w : Fin p) :
    doubleEdgeCartanMatrix p q (Sum.inr v) (Sum.inl w)
      = if (v : ℕ) + 1 = q ∧ (w : ℕ) + 1 = p then -2 else 0 := (rfl)

/-- **Reversing the double edge transposes the matrix.** The two orientations of the double edge
give transposed diagrams, which is exactly the relation between `Bₙ` and `Cₙ`; since finite type is
invariant under transposition (`TauCeti.IsFiniteType.transpose`), one orientation carries all the
information. -/
@[simp] theorem doubleEdgeCartanMatrix_transpose (p q : ℕ) :
    (doubleEdgeCartanMatrix p q)ᵀ
      = (doubleEdgeCartanMatrix q p).submatrix Sum.swap Sum.swap := by
  ext v w
  rcases v with a | a <;> rcases w with b | b <;>
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Sum.swap_inl, Sum.swap_inr,
      doubleEdgeCartanMatrix_inl_inl, doubleEdgeCartanMatrix_inr_inr,
      doubleEdgeCartanMatrix_inl_inr, doubleEdgeCartanMatrix_inr_inl]
  · exact chainEntry_comm _ _
  · exact if_congr and_comm rfl rfl
  · exact if_congr and_comm rfl rfl
  · exact chainEntry_comm _ _

/-- The **marks** of a double-edge chain: the value `s + 1` at the vertex `s` of the first chain,
scaled by `q`, and the value `t + 1` at the vertex `t` of the second chain, scaled by `p + 1`. Both
grow linearly towards the double edge, and the two slopes are in the ratio the double edge asks
for.

In the critical case `p = 3`, `q = 2` they are `2, 4, 6` along the first chain and `4, 8` along the
second, that is, twice the marks `1, 2, 3, 4, 2` of the extended Dynkin diagram `F̃₄` read along
the diagram; the same formula serves in general, since the matrix annihilates them everywhere
except at the far end of the second chain, whatever `p` and `q` are. -/
def doubleEdgeMark (p q : ℕ) : Fin p ⊕ Fin q → ℚ
  | .inl v => (((v : ℕ) : ℚ) + 1) * (q : ℚ)
  | .inr w => (((w : ℕ) : ℚ) + 1) * ((p : ℚ) + 1)

@[simp] lemma doubleEdgeMark_inl (v : Fin p) :
    doubleEdgeMark p q (Sum.inl v) = (((v : ℕ) : ℚ) + 1) * (q : ℚ) := (rfl)

@[simp] lemma doubleEdgeMark_inr (w : Fin q) :
    doubleEdgeMark p q (Sum.inr w) = (((w : ℕ) : ℚ) + 1) * ((p : ℚ) + 1) := (rfl)

/-! ## The rows of the diagram at its marks

Two computations, one for each kind of vertex. A chain annihilates a weight that is linear in the
position away from its two ends, and the far end of the first chain is cancelled by the double
edge; only the far end of the second chain is left, and there the bound is read off.
-/

/-- A chain, evaluated at a weight linear in the position: the row vanishes except at the far end,
where it is `(n + 1) c`. This is `TauCeti.sum_range_chainEntry_mul_affine` at `a = b = c`, the
weight `(w + 1) c` being `c w + c`; the near end contributes nothing because that weight vanishes
one step before the chain starts. -/
private theorem sum_fin_chainEntry_mul_linear {n : ℕ} (m : Fin n) (c : ℚ) :
    ∑ w : Fin n, ((chainEntry (m : ℕ) (w : ℕ) : ℤ) : ℚ) * ((((w : ℕ) : ℚ) + 1) * c)
      = if (m : ℕ) + 1 = n then ((n : ℚ) + 1) * c else 0 := by
  have hcongr : ∀ w : Fin n,
      ((chainEntry (m : ℕ) (w : ℕ) : ℤ) : ℚ) * ((((w : ℕ) : ℚ) + 1) * c)
        = ((chainEntry (m : ℕ) (w : ℕ) : ℤ) : ℚ) * (c * ((w : ℕ) : ℚ) + c) := by
    intro w
    ring
  rw [Finset.sum_congr rfl fun w _ ↦ hcongr w,
    Fin.sum_univ_eq_sum_range
      (fun s ↦ ((chainEntry (m : ℕ) s : ℤ) : ℚ) * (c * (s : ℚ) + c)) n,
    sum_range_chainEntry_mul_affine m.isLt c c]
  rcases eq_or_ne (m : ℕ) 0 with h0 | h0
  · rw [ite_eq_left h0]
    rcases eq_or_ne ((m : ℕ) + 1) n with hm | hm
    · -- A one-vertex chain: the two ends coincide, so `n = 1` and both readings give `2 c`.
      have hnQ : (n : ℚ) = 1 := by rw [← hm, h0]; norm_num
      rw [ite_eq_left hm, ite_eq_left hm, hnQ]
      norm_num
    · rw [ite_eq_right hm, ite_eq_right hm]
      ring
  · rw [ite_eq_right h0]
    rcases eq_or_ne ((m : ℕ) + 1) n with hm | hm
    · rw [ite_eq_left hm, ite_eq_left hm]
      ring
    · rw [ite_eq_right hm, ite_eq_right hm]

/-- The double edge, evaluated at a weight linear in the position: the row at a vertex `v` of one
chain meets the other chain only if `v` is the last vertex of its own, and then only at the far end
of the other, where the weight is `n k`. This is the cross-chain block of both rows below, whose
two uses differ only in the two lengths, in the coefficient `c` and in the slope `k`. -/
private theorem sum_fin_ite_last_mul_linear {m : ℕ} (v : Fin m) (n : ℕ) (c k : ℚ) :
    ∑ w : Fin n, (if (v : ℕ) + 1 = m ∧ (w : ℕ) + 1 = n then c else 0) * ((((w : ℕ) : ℚ) + 1) * k)
      = if (v : ℕ) + 1 = m then c * ((n : ℚ) * k) else 0 := by
  match n with
  | 0 => simp
  | j + 1 =>
    rw [Fin.sum_univ_castSucc]
    have hzero : ∀ i : Fin j,
        (if (v : ℕ) + 1 = m ∧ ((Fin.castSucc i : Fin (j + 1)) : ℕ) + 1 = j + 1 then c else 0)
          * (((((Fin.castSucc i : Fin (j + 1)) : ℕ) : ℚ) + 1) * k) = 0 := by
      intro i
      have hi := i.isLt
      rw [ite_eq_right (by simp only [Fin.val_castSucc]; omega)]
      ring
    rw [Finset.sum_congr rfl fun i _ ↦ hzero i, Finset.sum_const_zero, zero_add, Fin.val_last]
    rcases eq_or_ne ((v : ℕ) + 1) m with hv | hv
    · rw [ite_eq_left ⟨hv, rfl⟩, ite_eq_left hv]
      push_cast
      ring
    · rw [ite_eq_right fun h ↦ hv h.1, ite_eq_right hv]
      ring

/-- **The rows at the first chain annihilate the marks.** Away from the double edge this is the
second difference of a linear weight; at the double edge the first chain contributes `(p + 1) q`
and the double edge subtracts the same amount, which is what fixes the ratio of the two slopes. -/
theorem sum_doubleEdgeCartanMatrix_mul_doubleEdgeMark_inl_eq_zero (v : Fin p) :
    ∑ w, ((doubleEdgeCartanMatrix p q (Sum.inl v) w : ℤ) : ℚ) * doubleEdgeMark p q w = 0 := by
  rw [Fintype.sum_sum_type]
  have hchain : ∑ w : Fin p,
      ((doubleEdgeCartanMatrix p q (Sum.inl v) (Sum.inl w) : ℤ) : ℚ)
        * doubleEdgeMark p q (Sum.inl w)
      = if (v : ℕ) + 1 = p then ((p : ℚ) + 1) * (q : ℚ) else 0 := by
    rw [← sum_fin_chainEntry_mul_linear v (q : ℚ)]
    exact Finset.sum_congr rfl fun w _ ↦ by rw [doubleEdgeCartanMatrix_inl_inl, doubleEdgeMark_inl]
  have hcross : ∑ w : Fin q,
      ((doubleEdgeCartanMatrix p q (Sum.inl v) (Sum.inr w) : ℤ) : ℚ)
        * doubleEdgeMark p q (Sum.inr w)
      = if (v : ℕ) + 1 = p then (-1 : ℚ) * ((q : ℚ) * ((p : ℚ) + 1)) else 0 := by
    rw [← sum_fin_ite_last_mul_linear v q (-1) ((p : ℚ) + 1)]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [doubleEdgeCartanMatrix_inl_inr, doubleEdgeMark_inr]
    split_ifs <;> norm_num
  rw [hchain, hcross]
  split_ifs <;> ring

/-- **The rows at the second chain annihilate the marks away from the double edge**, and at the
double edge they take the value the bound is read off: `(p + 1) (q + 1) - 2 p q`. -/
theorem sum_doubleEdgeCartanMatrix_mul_doubleEdgeMark_inr (w : Fin q) :
    ∑ u, ((doubleEdgeCartanMatrix p q (Sum.inr w) u : ℤ) : ℚ) * doubleEdgeMark p q u
      = if (w : ℕ) + 1 = q then ((p : ℚ) + 1) * ((q : ℚ) + 1) - 2 * (p : ℚ) * (q : ℚ) else 0 := by
  rw [Fintype.sum_sum_type]
  have hcross : ∑ u : Fin p,
      ((doubleEdgeCartanMatrix p q (Sum.inr w) (Sum.inl u) : ℤ) : ℚ)
        * doubleEdgeMark p q (Sum.inl u)
      = if (w : ℕ) + 1 = q then (-2 : ℚ) * ((p : ℚ) * (q : ℚ)) else 0 := by
    rw [← sum_fin_ite_last_mul_linear w p (-2) (q : ℚ)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [doubleEdgeCartanMatrix_inr_inl, doubleEdgeMark_inl]
    split_ifs <;> norm_num
  have hchain : ∑ u : Fin q,
      ((doubleEdgeCartanMatrix p q (Sum.inr w) (Sum.inr u) : ℤ) : ℚ)
        * doubleEdgeMark p q (Sum.inr u)
      = if (w : ℕ) + 1 = q then ((q : ℚ) + 1) * ((p : ℚ) + 1) else 0 := by
    rw [← sum_fin_chainEntry_mul_linear w ((p : ℚ) + 1)]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [doubleEdgeCartanMatrix_inr_inr, doubleEdgeMark_inr]
  rw [hcross, hchain]
  split_ifs <;> ring

/-! ## The bound -/

/-- **The double-edge bound.** Two chains of `p` and `q` vertices joined by a double edge form a
diagram of finite type only if `2 p q < (p + 1) (q + 1)`, that is, only if `(p - 1) (q - 1) < 2`. -/
theorem two_mul_mul_lt_succ_mul_succ_of_isFiniteType_doubleEdge
    (h : IsFiniteType (doubleEdgeCartanMatrix p q)) : 2 * p * q < (p + 1) * (q + 1) := by
  rw [← not_le]
  intro hle
  -- Both chains are nonempty: an empty one leaves a chain, which is of finite type. `hp` indexes
  -- the vertex the marks are read off at, and `hq` is what the value there contradicts.
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · omega
    · exact hp
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · omega
    · exact hq
  have hleQ : ((p : ℚ) + 1) * ((q : ℚ) + 1) ≤ 2 * (p : ℚ) * (q : ℚ) := by exact_mod_cast hle
  have hsub : ∀ i, doubleEdgeMark p q i
      * ∑ j, ((doubleEdgeCartanMatrix p q i j : ℤ) : ℚ) * doubleEdgeMark p q j ≤ 0 := by
    rintro (v | w)
    · rw [sum_doubleEdgeCartanMatrix_mul_doubleEdgeMark_inl_eq_zero, mul_zero]
    · rw [sum_doubleEdgeCartanMatrix_mul_doubleEdgeMark_inr]
      rcases eq_or_ne ((w : ℕ) + 1) q with hw | hw
      · rw [ite_eq_left hw]
        have hmark : (0 : ℚ) ≤ doubleEdgeMark p q (Sum.inr w) := by
          rw [doubleEdgeMark_inr]
          positivity
        have hneg : ((p : ℚ) + 1) * ((q : ℚ) + 1) - 2 * (p : ℚ) * (q : ℚ) ≤ 0 := by linarith
        simpa using mul_le_mul_of_nonneg_left hneg hmark
      · rw [ite_eq_right hw, mul_zero]
  have hzero := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos hsub
  have hcorner := congrFun hzero (Sum.inl ⟨0, hp⟩)
  rw [doubleEdgeMark_inl] at hcorner
  simp only [Nat.cast_zero, zero_add, one_mul, Pi.zero_apply, Nat.cast_eq_zero] at hcorner
  -- The mark at that vertex is `q`, which the second chain being nonempty forbids from vanishing.
  exact absurd hcorner hq.ne'

/-- The contrapositive of `TauCeti.two_mul_mul_lt_succ_mul_succ_of_isFiniteType_doubleEdge`: a
double-edge diagram violating the bound is not of finite type.

This is the shape the classification consumes. A candidate diagram is excluded by exhibiting an
embedded double-edge chain with `(p + 1) (q + 1) ≤ 2 p q`, that is, by
`TauCeti.IsFiniteType.submatrix` along an injection `e` with
`A.submatrix e e = doubleEdgeCartanMatrix p q`. -/
theorem not_isFiniteType_doubleEdgeCartanMatrix_of_succ_mul_succ_le
    (h : (p + 1) * (q + 1) ≤ 2 * p * q) : ¬ IsFiniteType (doubleEdgeCartanMatrix p q) := fun hft ↦
  absurd (two_mul_mul_lt_succ_mul_succ_of_isFiniteType_doubleEdge hft) (not_lt.2 h)

/-- **The admissible double-edge shapes.** A double-edge diagram of finite type whose two chains
are nonempty has one vertex on the second chain (the family `Cₙ`), or one vertex on the first (the
family `Bₙ`), or two on each (`F₄`).

This is the exclusion half of the classification of the diagrams with a double edge. The converse,
that these shapes are the diagrams of actual root systems, is the separate realization target of
the same layer. That the two families are at least of finite type is
`TauCeti.isFiniteType_doubleEdgeCartanMatrix_one_right` and
`TauCeti.isFiniteType_doubleEdgeCartanMatrix_one_left`; the remaining shape,
`TauCeti.doubleEdgeCartanMatrix 2 2`, is the diagram of `F₄`, but nothing here identifies it with
`TauCeti.DynkinType.F4.cartanMatrix`, so its finite type is not established in this file. -/
theorem eq_one_or_eq_one_or_eq_two_two_of_isFiniteType_doubleEdge (hp : 0 < p) (hq : 0 < q)
    (h : IsFiniteType (doubleEdgeCartanMatrix p q)) :
    q = 1 ∨ p = 1 ∨ (p = 2 ∧ q = 2) := by
  have hlt := two_mul_mul_lt_succ_mul_succ_of_isFiniteType_doubleEdge h
  by_contra hc
  push Not at hc
  obtain ⟨hq1, hp1, hpq⟩ := hc
  have hp2 : 2 ≤ p := by omega
  have hq2 : 2 ≤ q := by omega
  -- `p q ≤ p + q` forces `p = q`, and then `p ^ 2 ≤ 2 p` forces `p = 2`.
  have hsum : p * q ≤ p + q := by nlinarith
  have hqp : q ≤ p := by nlinarith
  have hpq' : p ≤ q := by nlinarith
  have hpe : p = q := le_antisymm hpq' hqp
  subst hpe
  have hple : p ≤ 2 := by nlinarith
  exact hpq (by omega) (by omega)

/-- The extended Dynkin diagram `F̃₄`, two chains of three and of two vertices joined by a double
edge, is not of finite type. -/
theorem not_isFiniteType_affineF₄ : ¬ IsFiniteType (doubleEdgeCartanMatrix 3 2) :=
  not_isFiniteType_doubleEdgeCartanMatrix_of_succ_mul_succ_le (by norm_num)

/-! ## Sharpness: the two families the bound leaves

The bound excludes everything outside `Bₙ`, `Cₙ` and `F₄`. That the two families do occur is proved
here, by identifying the diagram at `q = 1` with Mathlib's `CartanMatrix.C`. The third shape,
`TauCeti.doubleEdgeCartanMatrix 2 2`, is left alone: the reindexing that identifies it with the
canonical Cartan matrix of `F₄` belongs to the assembly step of the classification, outside this
file.
-/

/-- **A double-edge chain whose second chain is a single vertex is of type `Cₙ`.** The `n - 1`
vertices of the first chain are the first `n - 1` nodes of `Cₙ`, in order, and the lone vertex is
the last node, at which the double edge of `Cₙ` points. That listing of the vertices in the order
they occur along the diagram is Mathlib's canonical identification `finSumFinEquiv`. -/
theorem doubleEdgeCartanMatrix_one_right (p : ℕ) :
    doubleEdgeCartanMatrix p 1
      = (CartanMatrix.C (p + 1)).submatrix finSumFinEquiv finSumFinEquiv := by
  ext v w
  rcases v with a | a <;> rcases w with b | b <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      doubleEdgeCartanMatrix_inl_inl, doubleEdgeCartanMatrix_inr_inr,
      doubleEdgeCartanMatrix_inl_inr, doubleEdgeCartanMatrix_inr_inl, CartanMatrix.C,
      Matrix.of_apply, chainEntry_def, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] <;>
    split_ifs <;> omega

/-- The double-edge diagrams with a single vertex on the second chain are of finite type: they are
the family `Cₙ`. -/
theorem isFiniteType_doubleEdgeCartanMatrix_one_right (p : ℕ) :
    IsFiniteType (doubleEdgeCartanMatrix p 1) := by
  rw [doubleEdgeCartanMatrix_one_right]
  exact (isFiniteType_cartanMatrix_C (p + 1)).submatrix finSumFinEquiv.injective

/-- The double-edge diagrams with a single vertex on the first chain are of finite type: they are
the family `Bₙ`, the transposes of the previous ones. -/
theorem isFiniteType_doubleEdgeCartanMatrix_one_left (q : ℕ) :
    IsFiniteType (doubleEdgeCartanMatrix 1 q) := by
  have h := (isFiniteType_doubleEdgeCartanMatrix_one_right q).transpose
  rw [doubleEdgeCartanMatrix_transpose] at h
  have hswap : (Sum.swap : Fin q ⊕ Fin 1 → Fin 1 ⊕ Fin q) ∘ Sum.swap = id :=
    funext fun x ↦ Sum.swap_swap x
  have h2 := h.submatrix (e := (Sum.swap : Fin 1 ⊕ Fin q → Fin q ⊕ Fin 1))
    Sum.swap_leftInverse.injective
  rwa [Matrix.submatrix_submatrix, hswap, Matrix.submatrix_id_id] at h2

end TauCeti
