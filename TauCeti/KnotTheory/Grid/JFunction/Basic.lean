/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.Rotation

/-!
# The grid `J`-function

This file adds the finite point-pair count used in the Maslov and Alexander gradings of grid
homology. For finite sets of grid points, `GridPoint.Icount r s t` counts the ordered pairs
`(p, q) ∈ s × t` with `r p q`; `GridPoint.I s t` is its value at the strict southwest relation,
and `GridPoint.J s t` is the symmetrized half-count. Keeping the count parametric in the
relation lets the pairing against markings at the centres of their squares
(`JFunction/Center.lean`), which weakens the comparison, share this API.

The API is deliberately point-set level: later grading definitions apply it to grid-state and
marking point sets, which the Maslov and Alexander gradings are then assembled from.

## Main definitions

* `TauCeti.GridPoint.IsSouthWest`: the strict southwest relation on grid squares.
* `TauCeti.GridPoint.Icount`: the ordered count of pairs of grid points related by a given
  decidable relation.
* `TauCeti.GridPoint.I`: the ordered southwest pair count, `Icount` at the strict southwest
  relation.
* `TauCeti.GridPoint.JNum`: the numerator of the symmetrized `J`-function.
* `TauCeti.GridPoint.J`: the rational-valued symmetrized `J`-function.
* `TauCeti.GridState.J`: the specialized form for a pair of grid states.

## Main results

* `TauCeti.GridPoint.I_image_swap`, `TauCeti.GridPoint.J_image_swap`,
  `TauCeti.GridState.J_transpose`: the southwest counts and the `J`-function are invariant
  under reflecting the point sets across the diagonal.
* `TauCeti.GridPoint.I_image_rev`, `TauCeti.GridPoint.JNum_image_rev`,
  `TauCeti.GridPoint.J_image_rev`, `TauCeti.GridState.J_rotate`: reversing both coordinates of
  the point sets exchanges the two arguments of the ordered count `I`, while the symmetrized
  `JNum` and `J` are invariant.
* `TauCeti.GridPoint.I_graph_eq_card`, `TauCeti.GridState.J_pointSet_eq_card`: graph point-set
  `J`-pairings as column-index counts.

## References

This supplies a prerequisite for `CombinatorialHeegaardFloer/README.md` in TauCetiRoadmap, Lane G.2,
"Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change
formulas across a rectangle." The definition follows Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Chapter 3.2, where `J` is the symmetrization of the northeast/southwest
point-pair count.
-/

public section

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- A grid point is strictly southwest of another when both its column and row coordinates are
strictly smaller. This is the affine point-pair relation used in the grid `J`-function; it is
not the toroidal cyclic order used for rectangles. -/
@[expose] def IsSouthWest (p q : Fin n × Fin n) : Prop :=
  p.1.val < q.1.val ∧ p.2.val < q.2.val

/-- The strict southwest relation has a decidable instance. -/
instance decidableIsSouthWest (p q : Fin n × Fin n) : Decidable (IsSouthWest p q) :=
  inferInstanceAs (Decidable (p.1.val < q.1.val ∧ p.2.val < q.2.val))

/-- The southwest relation in coordinate form. -/
@[simp, grind =]
theorem isSouthWest_iff (p q : Fin n × Fin n) :
    IsSouthWest p q ↔ p.1.val < q.1.val ∧ p.2.val < q.2.val :=
  Iff.rfl

/-- A point is not strictly southwest of itself. -/
theorem not_isSouthWest_self (p : Fin n × Fin n) : ¬ IsSouthWest p p := by
  intro h
  exact (lt_self_iff_false p.1.val).mp h.1

/-- A strictly southwest pair has distinct endpoints. -/
theorem ne_of_isSouthWest {p q : Fin n × Fin n} (h : IsSouthWest p q) : p ≠ q := by
  intro hpq
  subst hpq
  exact not_isSouthWest_self p h

/-- The strict southwest relation is asymmetric. -/
theorem not_isSouthWest_swap {p q : Fin n × Fin n} (h : IsSouthWest p q) :
    ¬ IsSouthWest q p := by
  intro hqp
  exact (not_lt_of_gt h.1) hqp.1

/-- The ordered count of pairs `(p, q) ∈ s × t` related by `r`. The two relations used on grids
are the strict southwest relation `GridPoint.IsSouthWest`, giving the `J`-function of this file,
and the weak product order, giving the pairing of grid points against markings sitting at the
centres of their squares. -/
def Icount (r : (Fin n × Fin n) → (Fin n × Fin n) → Prop) [DecidableRel r]
    (s t : Finset (Fin n × Fin n)) : ℕ :=
  ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) => r pq.1 pq.2).card

variable (r : (Fin n × Fin n) → (Fin n × Fin n) → Prop) [DecidableRel r]

/-- The ordered relation count as the cardinality of the filtered product of point sets. -/
theorem Icount_def (s t : Finset (Fin n × Fin n)) :
    Icount r s t =
      ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) => r pq.1 pq.2).card :=
  by simp only [Icount]

/-- The ordered relation count is zero when the left point set is empty. -/
@[simp]
theorem Icount_empty_left (s : Finset (Fin n × Fin n)) : Icount r ∅ s = 0 := by
  simp [Icount]

/-- The ordered relation count is zero when the right point set is empty. -/
@[simp]
theorem Icount_empty_right (s : Finset (Fin n × Fin n)) : Icount r s ∅ = 0 := by
  simp [Icount]

/-- The ordered relation count of singleton point sets records the single comparison. -/
@[simp]
theorem Icount_singleton_singleton (p q : Fin n × Fin n) :
    Icount r {p} {q} = if r p q then 1 else 0 := by
  simp only [Icount, Finset.singleton_product_singleton, Finset.filter_singleton]
  by_cases h : r p q
  · simp only [h, ite_true, Finset.card_singleton]
  · simp only [h, ite_false, Finset.card_empty]

/-- The ordered relation count is additive in the left point set over disjoint unions. -/
theorem Icount_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    Icount r (s₁ ∪ s₂) t = Icount r s₁ t + Icount r s₂ t := by
  dsimp [Icount]
  rw [Finset.union_product, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inl h))

/-- The ordered relation count is additive in the right point set over disjoint unions. -/
theorem Icount_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    Icount r s (t₁ ∪ t₂) = Icount r s t₁ + Icount r s t₂ := by
  dsimp [Icount]
  rw [Finset.product_union, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inr h))

/-- The ordered relation count after inserting a fresh point on the left. -/
theorem Icount_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    Icount r (insert p s) t = Icount r {p} t + Icount r s t := by
  rw [← Finset.singleton_union, Icount_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The ordered relation count after inserting a fresh point on the right. -/
theorem Icount_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    Icount r s (insert p t) = Icount r s {p} + Icount r s t := by
  rw [← Finset.singleton_union, Icount_union_right]
  exact Finset.disjoint_singleton_left.mpr h

/-- The ordered relation count is monotone in its left point set. -/
theorem Icount_mono_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : s₁ ⊆ s₂) :
    Icount r s₁ t ≤ Icount r s₂ t := by
  dsimp [Icount]
  exact Finset.card_le_card fun pq hpq => by
    simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
    exact ⟨⟨h hpq.1.1, hpq.1.2⟩, hpq.2⟩

/-- The ordered relation count is monotone in its right point set. -/
theorem Icount_mono_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : t₁ ⊆ t₂) :
    Icount r s t₁ ≤ Icount r s t₂ := by
  dsimp [Icount]
  exact Finset.card_le_card fun pq hpq => by
    simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
    exact ⟨⟨hpq.1.1, h hpq.1.2⟩, hpq.2⟩

/-- The reflection map on pairs of grid squares is injective. -/
private theorem prodMap_swap_injective :
    Function.Injective
      (Prod.map (Prod.swap (α := Fin n) (β := Fin n)) (Prod.swap (α := Fin n) (β := Fin n))) :=
  Prod.swap_injective.prodMap Prod.swap_injective

/-- The ordered relation count of a relation invariant under the diagonal reflection is invariant
under reflecting both point sets across the diagonal. -/
theorem Icount_image_swap (hr : ∀ p q : Fin n × Fin n, r p.swap q.swap ↔ r p q)
    (s t : Finset (Fin n × Fin n)) :
    Icount r (s.image Prod.swap) (t.image Prod.swap) = Icount r s t := by
  rw [Icount_def, Icount_def, ← Finset.prodMap_image_product Prod.swap Prod.swap s t,
    Finset.filter_image, Finset.card_image_of_injective _ prodMap_swap_injective]
  congr 1
  exact Finset.filter_congr fun pq _ => hr pq.1 pq.2

/-- The ordered relation count of two graph point sets counts the column pairs whose two
prescribed grid points are related. This graph-level statement does not require either row
assignment to be a permutation. -/
theorem Icount_graph_eq_card (f g : Fin n → Fin n) :
    Icount r (Finset.univ.image fun c : Fin n => (c, f c))
        (Finset.univ.image fun c : Fin n => (c, g c)) =
      (Finset.univ.filter fun p : Fin n × Fin n => r (p.1, f p.1) (p.2, g p.2)).card := by
  classical
  have hff : Function.Injective (fun c : Fin n => (c, f c)) :=
    fun _ _ h => congrArg Prod.fst h
  have hfg : Function.Injective (fun c : Fin n => (c, g c)) :=
    fun _ _ h => congrArg Prod.fst h
  rw [Icount_def,
    ← Finset.prodMap_image_product (fun c : Fin n => (c, f c)) (fun c : Fin n => (c, g c)),
    Finset.filter_image, Finset.card_image_of_injective _ (hff.prodMap hfg),
    Finset.univ_product_univ]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ => Iff.rfl)

/-- The ordered count of pairs `(p, q) ∈ s × t` with `p` strictly southwest of `q`. -/
@[expose] def I (s t : Finset (Fin n × Fin n)) : ℕ :=
  Icount IsSouthWest s t

/-- The ordered southwest count as the cardinality of the filtered product of point sets. -/
theorem I_def (s t : Finset (Fin n × Fin n)) :
    I s t =
      ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) =>
        IsSouthWest pq.1 pq.2).card :=
  Icount_def IsSouthWest s t

/-- Membership in the finite set counted by `GridPoint.I`. -/
theorem mem_filter_product_isSouthWest (s t : Finset (Fin n × Fin n))
  (pq : (Fin n × Fin n) × (Fin n × Fin n)) :
    pq ∈ (s ×ˢ t).filter (fun pq => IsSouthWest pq.1 pq.2) ↔
      pq.1 ∈ s ∧ pq.2 ∈ t ∧ IsSouthWest pq.1 pq.2 := by
  simp only [Finset.mem_filter, Finset.mem_product]
  tauto

/-- The ordered southwest count is zero when the left point set is empty. -/
@[simp]
theorem I_empty_left (s : Finset (Fin n × Fin n)) : I ∅ s = 0 :=
  Icount_empty_left _ s

/-- The ordered southwest count is zero when the right point set is empty. -/
@[simp]
theorem I_empty_right (s : Finset (Fin n × Fin n)) : I s ∅ = 0 :=
  Icount_empty_right _ s

/-- The ordered southwest count of singleton point sets is one exactly for a southwest pair. -/
@[simp]
theorem I_singleton_singleton (p q : Fin n × Fin n) :
    I {p} {q} = if IsSouthWest p q then 1 else 0 :=
  Icount_singleton_singleton _ p q

/-- No point contributes a southwest pair with itself. -/
theorem I_singleton_self (p : Fin n × Fin n) : I {p} {p} = 0 := by
  simp

/-- The ordered southwest count is additive in the left point set over disjoint unions. -/
theorem I_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    I (s₁ ∪ s₂) t = I s₁ t + I s₂ t :=
  Icount_union_left _ h

/-- The ordered southwest count is additive in the right point set over disjoint unions. -/
theorem I_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    I s (t₁ ∪ t₂) = I s t₁ + I s t₂ :=
  Icount_union_right _ h

/-- The ordered southwest count after inserting a fresh point on the left. -/
theorem I_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    I (insert p s) t = I {p} t + I s t :=
  Icount_insert_left _ h

/-- The ordered southwest count after inserting a fresh point on the right. -/
theorem I_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    I s (insert p t) = I s {p} + I s t :=
  Icount_insert_right _ h

/-- The numerator of the symmetrized `J`-function. Keeping the numerator as a natural number is
convenient for parity and integrality lemmas before passing to rational values. -/
@[expose] def JNum (s t : Finset (Fin n × Fin n)) : ℕ :=
  I s t + I t s

/-- The numerator of `J` is the sum of the two ordered southwest counts. -/
theorem JNum_def (s t : Finset (Fin n × Fin n)) : JNum s t = I s t + I t s :=
  rfl

/-- The symmetrized numerator of the `J`-function on a point set with itself is even: it is twice
the ordered southwest count. -/
@[simp]
theorem JNum_self (s : Finset (Fin n × Fin n)) : JNum s s = 2 * I s s := by
  rw [JNum_def, two_mul]

/-- The rational-valued symmetrized grid `J`-function. -/
@[expose] def J (s t : Finset (Fin n × Fin n)) : ℚ :=
  ((JNum s t : ℕ) : ℚ) / 2

/-- The rational-valued `J`-function is half of its symmetrized numerator. -/
theorem J_def (s t : Finset (Fin n × Fin n)) : GridPoint.J s t = ((JNum s t : ℕ) : ℚ) / 2 :=
  rfl

/-- The `J`-function on a point set with itself is an integer, namely the ordered southwest
count. The two southwest comparisons of a pair contribute symmetrically, so the division by two
is exact. -/
@[simp]
theorem J_self (s : Finset (Fin n × Fin n)) : GridPoint.J s s = (I s s : ℚ) := by
  rw [J_def, JNum_self]
  push_cast
  ring

/-- The numerator of `J` is symmetric. -/
theorem JNum_comm (s t : Finset (Fin n × Fin n)) : JNum s t = JNum t s := by
  rw [JNum, JNum, Nat.add_comm]

/-- The grid `J`-function is symmetric. -/
theorem J_comm (s t : Finset (Fin n × Fin n)) : GridPoint.J s t = GridPoint.J t s := by
  simp [GridPoint.J, JNum_comm s t]

/-- The numerator of `J` vanishes when the left point set is empty. -/
@[simp]
theorem JNum_empty_left (s : Finset (Fin n × Fin n)) : JNum ∅ s = 0 := by
  simp [JNum]

/-- The numerator of `J` vanishes when the right point set is empty. -/
@[simp]
theorem JNum_empty_right (s : Finset (Fin n × Fin n)) : JNum s ∅ = 0 := by
  simp [JNum]

/-- The numerator of `J` is additive in the left point set over disjoint unions. -/
theorem JNum_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    JNum (s₁ ∪ s₂) t = JNum s₁ t + JNum s₂ t := by
  simp only [JNum, I_union_left h, I_union_right h]
  ac_rfl

/-- The numerator of `J` is additive in the right point set over disjoint unions. -/
theorem JNum_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    JNum s (t₁ ∪ t₂) = JNum s t₁ + JNum s t₂ := by
  rw [JNum_comm s (t₁ ∪ t₂), JNum_union_left h, JNum_comm t₁ s, JNum_comm t₂ s]

/-- The numerator of `J` after inserting a fresh point on the left. -/
theorem JNum_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    JNum (insert p s) t = JNum {p} t + JNum s t := by
  rw [← Finset.singleton_union, JNum_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The numerator of `J` after inserting a fresh point on the right. -/
theorem JNum_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    JNum s (insert p t) = JNum s {p} + JNum s t := by
  rw [← Finset.singleton_union, JNum_union_right]
  exact Finset.disjoint_singleton_left.mpr h

/-- `J` vanishes when the left point set is empty. -/
@[simp]
theorem J_empty_left (s : Finset (Fin n × Fin n)) : GridPoint.J ∅ s = 0 := by
  simp [GridPoint.J]

/-- `J` vanishes when the right point set is empty. -/
@[simp]
theorem J_empty_right (s : Finset (Fin n × Fin n)) : GridPoint.J s ∅ = 0 := by
  simp [GridPoint.J]

/-- The grid `J`-function is additive in the left point set over disjoint unions. -/
theorem J_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    GridPoint.J (s₁ ∪ s₂) t = GridPoint.J s₁ t + GridPoint.J s₂ t := by
  simp only [GridPoint.J, JNum_union_left h, Nat.cast_add]
  exact add_div ((JNum s₁ t : ℕ) : ℚ) ((JNum s₂ t : ℕ) : ℚ) (2 : ℚ)

/-- The grid `J`-function is additive in the right point set over disjoint unions. -/
theorem J_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    GridPoint.J s (t₁ ∪ t₂) = GridPoint.J s t₁ + GridPoint.J s t₂ := by
  rw [J_comm s (t₁ ∪ t₂), J_union_left h, J_comm t₁ s, J_comm t₂ s]

/-- The grid `J`-function after inserting a fresh point on the left. -/
theorem J_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    GridPoint.J (insert p s) t = GridPoint.J {p} t + GridPoint.J s t := by
  rw [← Finset.singleton_union, J_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The grid `J`-function after inserting a fresh point on the right. -/
theorem J_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    GridPoint.J s (insert p t) = GridPoint.J s {p} + GridPoint.J s t := by
  rw [← Finset.singleton_union, J_union_right]
  exact Finset.disjoint_singleton_left.mpr h

/-- The numerator of `J` on singleton point sets records whether either point is southwest of
the other. -/
@[simp]
theorem JNum_singleton_singleton (p q : Fin n × Fin n) :
    JNum {p} {q} =
      (if IsSouthWest p q then 1 else 0) + (if IsSouthWest q p then 1 else 0) := by
  simp [JNum]

/-- The `J`-function on singleton point sets is half the number of southwest comparisons
between the two points. -/
@[simp]
theorem J_singleton_singleton (p q : Fin n × Fin n) :
    GridPoint.J {p} {q} =
      (((if IsSouthWest p q then 1 else 0) +
        (if IsSouthWest q p then 1 else 0) : ℕ) : ℚ) / 2 := by
  simp [GridPoint.J]

/-- The `J`-function of two comparable singleton point sets is `1 / 2`. -/
theorem J_singleton_singleton_of_isSouthWest_or_isSouthWest {p q : Fin n × Fin n}
    (h : IsSouthWest p q ∨ IsSouthWest q p) :
    GridPoint.J {p} {q} = (1 : ℚ) / 2 := by
  rcases h with hpq | hqp
  · have hpqcoord : p.1.val < q.1.val ∧ p.2.val < q.2.val := by
      simpa using hpq
    have hqpcoord : ¬ (q.1.val < p.1.val ∧ q.2.val < p.2.val) := by
      simpa using not_isSouthWest_swap hpq
    have hqpfin : ¬ (q.1 < p.1 ∧ q.2 < p.2) := by
      intro h
      exact hqpcoord ⟨Fin.lt_def.mp h.1, Fin.lt_def.mp h.2⟩
    simp [J_singleton_singleton, hpqcoord, hqpfin]
  · have hqpcoord : q.1.val < p.1.val ∧ q.2.val < p.2.val := by
      simpa using hqp
    have hpqcoord : ¬ (p.1.val < q.1.val ∧ p.2.val < q.2.val) := by
      simpa using not_isSouthWest_swap hqp
    have hpqfin : ¬ (p.1 < q.1 ∧ p.2 < q.2) := by
      intro h
      exact hpqcoord ⟨Fin.lt_def.mp h.1, Fin.lt_def.mp h.2⟩
    simp [J_singleton_singleton, hpqfin, hqpcoord]

/-- The `J`-function of a singleton with itself is zero. -/
theorem J_singleton_self (p : Fin n × Fin n) : GridPoint.J {p} {p} = 0 := by
  simp [GridPoint.J]

/-- The ordered southwest count is monotone in its left point set. -/
theorem I_mono_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : s₁ ⊆ s₂) :
    I s₁ t ≤ I s₂ t :=
  Icount_mono_left _ h

/-- The ordered southwest count is monotone in its right point set. -/
theorem I_mono_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : t₁ ⊆ t₂) :
    I s t₁ ≤ I s t₂ :=
  Icount_mono_right _ h

/-- The numerator of `J` is monotone in its left point set. -/
theorem JNum_mono_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : s₁ ⊆ s₂) :
    JNum s₁ t ≤ JNum s₂ t :=
  Nat.add_le_add (I_mono_left h) (I_mono_right h)

/-- The numerator of `J` is monotone in its right point set. -/
theorem JNum_mono_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : t₁ ⊆ t₂) :
    JNum s t₁ ≤ JNum s t₂ := by
  rw [JNum_comm s t₁, JNum_comm s t₂]
  exact JNum_mono_left h

/-- The strict southwest relation is invariant under reflecting both points across the diagonal:
exchanging the column and row coordinates of both endpoints exchanges the two strict
inequalities. -/
@[grind =]
theorem isSouthWest_swap (p q : Fin n × Fin n) :
    IsSouthWest (Prod.swap p) (Prod.swap q) ↔ IsSouthWest p q := by
  unfold IsSouthWest
  exact and_comm

/-- The ordered southwest count is invariant under reflecting both point sets across the
diagonal. -/
theorem I_image_swap (s t : Finset (Fin n × Fin n)) :
    I (s.image Prod.swap) (t.image Prod.swap) = I s t :=
  Icount_image_swap _ isSouthWest_swap s t

/-- The numerator of the `J`-function is invariant under reflecting both point sets across the
diagonal. -/
theorem JNum_image_swap (s t : Finset (Fin n × Fin n)) :
    JNum (s.image Prod.swap) (t.image Prod.swap) = JNum s t := by
  rw [JNum_def, JNum_def, I_image_swap, I_image_swap]

/-- The symmetrized grid `J`-function is invariant under reflecting both point sets across the
diagonal. -/
theorem J_image_swap (s t : Finset (Fin n × Fin n)) :
    GridPoint.J (s.image Prod.swap) (t.image Prod.swap) = GridPoint.J s t := by
  rw [J_def, J_def, JNum_image_swap]

/-- Reversing both coordinates of both points of a pair exchanges the two endpoints of the strict
southwest relation: it sends the column and row comparisons to their reverses. -/
@[grind =]
theorem isSouthWest_rev (p q : Fin n × Fin n) :
    IsSouthWest (Prod.map Fin.rev Fin.rev p) (Prod.map Fin.rev Fin.rev q) ↔ IsSouthWest q p := by
  simp only [IsSouthWest, Prod.map_fst, Prod.map_snd]
  have h1 := p.1.isLt
  have h2 := q.1.isLt
  have h3 := p.2.isLt
  have h4 := q.2.isLt
  rw [Fin.val_rev, Fin.val_rev, Fin.val_rev, Fin.val_rev]
  omega

/-- The coordinate-reversal map on grid squares is injective. -/
private theorem prodMap_rev_injective :
    Function.Injective (Prod.map (Fin.rev (n := n)) (Fin.rev (n := n))) :=
  Fin.rev_injective.prodMap Fin.rev_injective

/-- The coordinate-reversal map on pairs of grid squares is injective. -/
private theorem prodMap_prodMap_rev_injective :
    Function.Injective
      (Prod.map (Prod.map (Fin.rev (n := n)) (Fin.rev (n := n)))
        (Prod.map (Fin.rev (n := n)) (Fin.rev (n := n)))) :=
  prodMap_rev_injective.prodMap prodMap_rev_injective

/-- The ordered southwest count is invariant, up to exchanging the two point sets, under reversing
both coordinates of both point sets. The reversal turns each southwest comparison into the
opposite comparison, so the count of southwest pairs from `s` to `t` becomes the count from `t`
to `s`. -/
theorem I_image_rev (s t : Finset (Fin n × Fin n)) :
    I (s.image (Prod.map Fin.rev Fin.rev)) (t.image (Prod.map Fin.rev Fin.rev)) = I t s := by
  classical
  rw [I_def, ← Finset.prodMap_image_product (Prod.map Fin.rev Fin.rev)
      (Prod.map Fin.rev Fin.rev) s t, Finset.filter_image,
    Finset.card_image_of_injective _ prodMap_prodMap_rev_injective]
  rw [I_def, ← Finset.image_swap_product t s, Finset.filter_image,
    Finset.card_image_of_injective _ Prod.swap_injective]
  refine congrArg Finset.card (Finset.filter_congr fun pq _ => ?_)
  simpa using isSouthWest_rev pq.1 pq.2

/-- The numerator of the `J`-function is invariant under reversing both coordinates of both point
sets. The two ordered counts are exchanged by the reversal, and their sum is symmetric. -/
theorem JNum_image_rev (s t : Finset (Fin n × Fin n)) :
    JNum (s.image (Prod.map Fin.rev Fin.rev)) (t.image (Prod.map Fin.rev Fin.rev)) = JNum s t := by
  rw [JNum_def, JNum_def, I_image_rev, I_image_rev, Nat.add_comm]

/-- The symmetrized grid `J`-function is invariant under reversing both coordinates of both point
sets. -/
theorem J_image_rev (s t : Finset (Fin n × Fin n)) :
    GridPoint.J (s.image (Prod.map Fin.rev Fin.rev)) (t.image (Prod.map Fin.rev Fin.rev))
      = GridPoint.J s t := by
  rw [J_def, J_def, JNum_image_rev]

/-- The ordered southwest count of two graph point sets is the number of column pairs `c < d`
where the source row precedes the target row. This graph-level statement does not require either
row assignment to be a permutation. -/
theorem I_graph_eq_card (f g : Fin n → Fin n) :
    GridPoint.I (Finset.univ.image fun c : Fin n => (c, f c))
        (Finset.univ.image fun c : Fin n => (c, g c)) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 < g p.2).card := by
  rw [I, Icount_graph_eq_card]
  exact congrArg Finset.card (Finset.filter_congr fun cd _ => by
    simp only [GridPoint.isSouthWest_iff, Fin.lt_def])

end GridPoint

namespace GridState

variable {n : ℕ}

/-- The grid `J`-function applied to the point sets of two grid states. -/
@[expose] def J (x y : GridState n) : ℚ :=
  GridPoint.J x.pointSet y.pointSet

/-- The state-level grid `J`-function is the point-set `J`-function on state point sets. -/
@[simp]
theorem J_def (x y : GridState n) : GridState.J x y = GridPoint.J x.pointSet y.pointSet :=
  rfl

/-- The state-level grid `J`-function is symmetric. -/
theorem J_comm (x y : GridState n) : GridState.J x y = GridState.J y x :=
  GridPoint.J_comm x.pointSet y.pointSet

/-- The state-level grid `J`-function is invariant under reflecting both states across the
diagonal. -/
theorem J_transpose (x y : GridState n) :
    GridState.J x.transpose y.transpose = GridState.J x y := by
  rw [J_def, J_def, transpose_pointSet, transpose_pointSet, GridPoint.J_image_swap]

/-- The state-level grid `J`-function is invariant under the half-turn rotation of both states. -/
theorem J_rotate (x y : GridState n) :
    GridState.J x.rotate y.rotate = GridState.J x y := by
  rw [J_def, J_def, rotate_pointSet, rotate_pointSet, GridPoint.J_image_rev]

/-- The ordered southwest count of the point sets of two grid states is the number of column
pairs `c < d` at which the source row precedes the target row. -/
theorem I_pointSet_eq_card (x y : GridState n) :
    GridPoint.I x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < y p.2).card := by
  rw [pointSet, pointSet, GridPoint.I_graph_eq_card]

/-- The symmetrized numerator of the grid `J`-function on two state point sets, as a sum of two
column-index counts. -/
theorem JNum_pointSet_eq_card (x y : GridState n) :
    GridPoint.JNum x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < y p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ y p.1 < x p.2).card := by
  rw [GridPoint.JNum_def, I_pointSet_eq_card, I_pointSet_eq_card]

/-- The rational grid `J`-function on two state point sets is half the sum of the two
column-index counts. -/
theorem J_pointSet_eq_card (x y : GridState n) :
    GridState.J x y =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < y p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ y p.1 < x p.2).card : ℕ) : ℚ)
        / 2 := by
  rw [GridState.J_def, GridPoint.J_def, JNum_pointSet_eq_card]

/-- The self southwest count of a grid state is the number of *non-inversions* of its
permutation: column pairs `c < d` whose occupied rows are in the same order. -/
theorem I_self_pointSet_eq_card (x : GridState n) :
    GridPoint.I x.pointSet x.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card :=
  I_pointSet_eq_card x x

/-- The non-inversions and the inversions of a grid state partition the ordered column pairs: the
number of pairs `c < d` with `x c < x d` plus the number with `x d < x c` is the total number of
pairs `c < d`. The state's permutation is injective, so on each ordered column pair exactly one of
the two strict row comparisons holds. -/
theorem card_filter_noninversion_add_card_filter_inversion (x : GridState n) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card := by
  classical
  have hnoninv :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).filter
          fun p => x p.1 < x p.2 :=
    (Finset.filter_filter _ _ _).symm
  have hinv :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).filter
          fun p => ¬ x p.1 < x p.2 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨hlt, hgt⟩
      exact ⟨hlt, not_lt.mpr (le_of_lt hgt)⟩
    · rintro ⟨hlt, hngt⟩
      have hxne : x p.1 ≠ x p.2 := fun h => (ne_of_lt hlt) (x.toPerm.injective h)
      exact ⟨hlt, lt_of_le_of_ne (not_lt.mp hngt) (Ne.symm hxne)⟩
  rw [hnoninv, hinv]
  exact Finset.card_filter_add_card_filter_not _

end GridState

end TauCeti
