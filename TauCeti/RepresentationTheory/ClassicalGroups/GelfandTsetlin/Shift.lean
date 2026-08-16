/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Tableau

/-!
# Determinant shifts of Gelfand-Tsetlin patterns

Tensoring a rational representation of `GL n` by a power of the determinant adds the same integer
to every component of its highest weight.  On a Gelfand-Tsetlin pattern the corresponding operation
adds that integer to every entry in the triangular array.  This file constructs that translation as
an equivalence and uses it to reduce patterns over an arbitrary dominant weight to the polynomial
case.

For a dominant weight `l` of nonzero rank, subtracting its last entry gives the polynomial weight
`l.shift (-l.detShift)`, whose Young diagram is `l.detShiftShape`.  A weight of rank zero has no
last entry; there `TauCeti.DominantWeight.detShift` is `0` and the normalization does nothing, so
the rank-zero case needs no separate treatment below.  The equivalence
`TauCeti.GTPattern.detShiftEquivBoundedSSYT` therefore identifies the patterns with top weight `l`
with the bounded semistandard Young tableaux of that normalized shape.  It is the rational-weight
bridge between the Gelfand-Tsetlin pattern count and the existing pattern-tableau correspondence;
the determinant twist changes no pattern-fiber cardinality.

## Main definitions

* `TauCeti.GTPattern.shift`: add an integer to every informative entry of a pattern.
* `TauCeti.GTPattern.shiftEquiv`: translation of all patterns by a fixed integer.
* `TauCeti.GTPattern.shiftTopWeightEquiv`: translation between the fibers over `l` and `l.shift m`.
* `TauCeti.GTPattern.detShiftEquivBoundedSSYT`: patterns over an arbitrary dominant weight are
  equivalent to bounded semistandard tableaux of its determinant-normalized shape.

## Main results

* `TauCeti.GTPattern.topWeight_shift`: shifting a pattern shifts its top weight.
* `TauCeti.GTPattern.card_topWeight_shift`: determinant translation preserves the pattern count.
* `TauCeti.GTPattern.card_topWeight_eq_card_boundedSSYT_detShiftShape`: the corresponding pattern
  and tableau fibers have the same cardinality.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "Gelfand-Tsetlin patterns" and "the Gelfand-Tsetlin dimension formula".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

namespace TauCeti

namespace GTPattern

variable {n : ℕ}

/-! ### Translation of patterns -/

/-- Add `m` to every informative entry of a Gelfand-Tsetlin pattern.  Entries outside the triangle
remain zero, so the representation of a pattern by an unrestricted function stays extensional. -/
def shift (P : GTPattern n) (m : ℤ) : GTPattern n where
  entry i j := if i < j ∧ j ≤ n then P i j + m else 0
  zeros' h := by
    rw [ite_eq_right]
    omega
  interlacing' := by
    intro i j hij hj
    have hLower : i < j ∧ j ≤ n := by omega
    have hUpperLeft : i < j + 1 ∧ j + 1 ≤ n := by omega
    have hUpperRight : i + 1 < j + 1 ∧ j + 1 ≤ n := by omega
    simp only [ite_eq_left hLower, ite_eq_left hUpperLeft, ite_eq_left hUpperRight]
    exact ⟨add_le_add_left (P.entry_le_entry_succ_row hij hj) m,
      add_le_add_left (P.entry_succ_succ_le_entry hj) m⟩

/-- The value of a shifted pattern before deciding whether the entry is informative. -/
theorem shift_apply (P : GTPattern n) (m : ℤ) (i j : ℕ) :
    P.shift m i j = if i < j ∧ j ≤ n then P i j + m else 0 :=
  (rfl)

/-- On an informative cell, shifting a pattern adds the shift to the entry. -/
@[simp]
theorem shift_apply_of_lt_of_le (P : GTPattern n) (m : ℤ) {i j : ℕ} (hij : i < j)
    (hj : j ≤ n) : P.shift m i j = P i j + m := by
  rw [shift_apply, ite_eq_left ⟨hij, hj⟩]

/-- Outside the triangular array, a shifted pattern still has entry zero. -/
@[simp]
theorem shift_apply_of_not_lt_le (P : GTPattern n) (m : ℤ) {i j : ℕ}
    (h : ¬(i < j ∧ j ≤ n)) : P.shift m i j = 0 := by
  rw [shift_apply, ite_eq_right h]

/-- Shifting by zero does not change a Gelfand-Tsetlin pattern. -/
@[simp]
theorem shift_zero (P : GTPattern n) : P.shift 0 = P := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · rw [shift_apply_of_lt_of_le P 0 h.1 h.2, add_zero]
  · rw [shift_apply_of_not_lt_le P 0 h, P.entry_eq_zero (by omega)]

/-- Successive shifts add their translation parameters. -/
@[simp]
theorem shift_shift (P : GTPattern n) (m m' : ℤ) :
    (P.shift m).shift m' = P.shift (m + m') := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · simp only [shift_apply_of_lt_of_le _ _ h.1 h.2]
    simp only [add_assoc]
  · rw [shift_apply_of_not_lt_le _ _ h, shift_apply_of_not_lt_le _ _ h]

/-- Translation by `m` is a bijection on Gelfand-Tsetlin patterns, with inverse translation by
`-m`. -/
def shiftEquiv (n : ℕ) (m : ℤ) : GTPattern n ≃ GTPattern n where
  toFun P := P.shift m
  invFun P := P.shift (-m)
  left_inv P := by
    simpa only [add_neg_cancel, shift_zero] using shift_shift P m (-m)
  right_inv P := by
    simpa only [neg_add_cancel, shift_zero] using shift_shift P (-m) m

@[simp]
theorem shiftEquiv_apply (n : ℕ) (m : ℤ) (P : GTPattern n) :
    shiftEquiv n m P = P.shift m :=
  (rfl)

@[simp]
theorem shiftEquiv_symm_apply (n : ℕ) (m : ℤ) (P : GTPattern n) :
    (shiftEquiv n m).symm P = P.shift (-m) :=
  (rfl)

/-! ### Top weights and determinant normalization -/

/-- Translating every entry translates the top row by the same integer. -/
@[simp]
theorem topRow_shift (P : GTPattern n) (m : ℤ) :
    (P.shift m).topRow = fun i => P.topRow i + m := by
  funext i
  rw [topRow_apply, shift_apply_of_lt_of_le P m i.2 le_rfl, topRow_apply]

/-- Translating every entry of a pattern translates its top weight, exactly as tensoring the
corresponding representation by a determinant power translates its highest weight. -/
@[simp]
theorem topWeight_shift (P : GTPattern n) (m : ℤ) :
    (P.shift m).topWeight = P.topWeight.shift m := by
  apply Subtype.ext
  funext i
  calc
    ((P.shift m).topWeight : Fin n → ℤ) i = (P.shift m).topRow i :=
      congrFun (topWeight_coe _) i
    _ = P.topRow i + m := congrFun (topRow_shift P m) i
    _ = (P.topWeight : Fin n → ℤ) i + m := by rw [topWeight_coe]
    _ = (P.topWeight.shift m : Fin n → ℤ) i := (DominantWeight.shift_apply _ _ _).symm

/-- Shifting every pattern entry by `m` identifies the patterns of top weight `l` with the patterns
of top weight `l.shift m`. -/
def shiftTopWeightEquiv (l : DominantWeight n) (m : ℤ) :
    {P : GTPattern n // P.topWeight = l} ≃
      {P : GTPattern n // P.topWeight = l.shift m} where
  toFun P := ⟨P.1.shift m, by rw [topWeight_shift, P.2]⟩
  invFun P := ⟨P.1.shift (-m), by
    rw [topWeight_shift, P.2, DominantWeight.shift_shift, add_neg_cancel,
      DominantWeight.shift_zero]⟩
  left_inv P := by
    apply Subtype.ext
    simpa only [add_neg_cancel, shift_zero] using shift_shift P.1 m (-m)
  right_inv P := by
    apply Subtype.ext
    simpa only [neg_add_cancel, shift_zero] using shift_shift P.1 (-m) m

@[simp]
theorem shiftTopWeightEquiv_apply_coe (l : DominantWeight n) (m : ℤ)
    (P : {P : GTPattern n // P.topWeight = l}) :
    (shiftTopWeightEquiv l m P).1 = P.1.shift m :=
  (rfl)

/-- The inverse of `TauCeti.GTPattern.shiftTopWeightEquiv` subtracts the same translation from
every entry. -/
@[simp]
theorem shiftTopWeightEquiv_symm_apply_coe (l : DominantWeight n) (m : ℤ)
    (P : {P : GTPattern n // P.topWeight = l.shift m}) :
    ((shiftTopWeightEquiv l m).symm P).1 = P.1.shift (-m) :=
  (rfl)

/-- A determinant translation does not change the number of Gelfand-Tsetlin patterns over a top
weight. -/
theorem card_topWeight_shift (l : DominantWeight n) (m : ℤ) :
    Nat.card {P : GTPattern n // P.topWeight = l.shift m} =
      Nat.card {P : GTPattern n // P.topWeight = l} :=
  Nat.card_congr (shiftTopWeightEquiv l m).symm

/-- Rephrasing a prescribed shape weight as a pointwise prescription of the top row. -/
private def topWeightFiberEquivTopRow (μ : YoungDiagram) :
    {P : GTPattern n // P.topWeight = weightOfShape n μ} ≃
      {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)} :=
  Equiv.subtypeEquivRight fun P => by
    constructor
    · intro h i
      calc
        P.topRow i = (P.topWeight : Fin n → ℤ) i := congrFun (topWeight_coe P).symm i
        _ = (weightOfShape n μ : Fin n → ℤ) i := congrFun (congrArg Subtype.val h) i
        _ = (μ.rowLen i : ℤ) := weightOfShape_apply _ _ _
    · intro h
      apply Subtype.ext
      funext i
      rw [topWeight_coe, weightOfShape_apply]
      exact h i

@[simp]
private theorem topWeightFiberEquivTopRow_apply_coe (μ : YoungDiagram)
    (P : {P : GTPattern n // P.topWeight = weightOfShape n μ}) :
    (topWeightFiberEquivTopRow μ P).1 = P.1 := by
  rw [topWeightFiberEquivTopRow, Equiv.subtypeEquivRight_apply]

@[simp]
private theorem topWeightFiberEquivTopRow_symm_apply_coe (μ : YoungDiagram)
    (P : {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)}) :
    ((topWeightFiberEquivTopRow μ).symm P).1 = P.1 := by
  rw [topWeightFiberEquivTopRow, Equiv.subtypeEquivRight_symm_apply]

private def shiftedTopWeightFiberEquivShape (l : DominantWeight n) :
    {P : GTPattern n // P.topWeight = l.shift (-l.detShift)} ≃
      {P : GTPattern n // P.topWeight = weightOfShape n l.detShiftShape} :=
  Equiv.subtypeEquivRight fun _ => by
    rw [DominantWeight.weightOfShape_detShiftShape]

@[simp]
private theorem shiftedTopWeightFiberEquivShape_apply_coe (l : DominantWeight n)
    (P : {P : GTPattern n // P.topWeight = l.shift (-l.detShift)}) :
    (shiftedTopWeightFiberEquivShape l P).1 = P.1 := by
  rw [shiftedTopWeightFiberEquivShape, Equiv.subtypeEquivRight_apply]

@[simp]
private theorem shiftedTopWeightFiberEquivShape_symm_apply_coe (l : DominantWeight n)
    (P : {P : GTPattern n // P.topWeight = weightOfShape n l.detShiftShape}) :
    ((shiftedTopWeightFiberEquivShape l).symm P).1 = P.1 := by
  rw [shiftedTopWeightFiberEquivShape, Equiv.subtypeEquivRight_symm_apply]

/-- **Determinant normalization of Gelfand-Tsetlin patterns.**  Patterns whose top weight is an
arbitrary dominant weight `l` correspond to bounded semistandard tableaux of the Young diagram of
`l - l.detShift`.  The first step subtracts `l.detShift` from every pattern entry; the existing
pattern-tableau equivalence then applies to the resulting polynomial top weight. -/
noncomputable def detShiftEquivBoundedSSYT (l : DominantWeight n) :
    {P : GTPattern n // P.topWeight = l} ≃ BoundedSSYT n l.detShiftShape := by
  exact (shiftTopWeightEquiv l (-l.detShift)).trans <|
    (shiftedTopWeightFiberEquivShape l).trans <|
      (topWeightFiberEquivTopRow l.detShiftShape).trans <|
        gtPatternEquivSSYT n l.detShiftShape l.colLen_zero_detShiftShape_le

/-- Determinant normalization sends a pattern to the tableau of the pattern shifted to polynomial
top weight. -/
@[simp]
theorem detShiftEquivBoundedSSYT_apply_coe (l : DominantWeight n)
    (P : {P : GTPattern n // P.topWeight = l}) :
    (detShiftEquivBoundedSSYT l P).1 =
      (P.1.shift (-l.detShift)).toTableau l.colLen_zero_detShiftShape_le
        (fun i => by
          calc
            (P.1.shift (-l.detShift)).topRow i =
                ((P.1.shift (-l.detShift)).topWeight : Fin n → ℤ) i :=
              congrFun (topWeight_coe _).symm i
            _ = (l.shift (-l.detShift) : Fin n → ℤ) i := by rw [topWeight_shift, P.2]
            _ = (weightOfShape n l.detShiftShape : Fin n → ℤ) i :=
              congrFun (congrArg Subtype.val
                (DominantWeight.weightOfShape_detShiftShape l).symm) i
            _ = (l.detShiftShape.rowLen i : ℤ) := weightOfShape_apply _ _ _) := by
  simp only [detShiftEquivBoundedSSYT, Equiv.trans_apply,
    gtPatternEquivSSYT_apply_coe, topWeightFiberEquivTopRow_apply_coe,
    shiftedTopWeightFiberEquivShape_apply_coe, shiftTopWeightEquiv_apply_coe]

/-- The inverse determinant-normalization equivalence shifts the tableau's polynomial pattern back
by the determinant weight. -/
@[simp]
theorem detShiftEquivBoundedSSYT_symm_apply_coe (l : DominantWeight n)
    (T : BoundedSSYT n l.detShiftShape) :
    ((detShiftEquivBoundedSSYT l).symm T).1 =
      (SemistandardYoungTableau.toGTPattern T.1 n).shift l.detShift := by
  simp only [detShiftEquivBoundedSSYT, Equiv.symm_trans_apply,
    gtPatternEquivSSYT_symm_apply_coe, topWeightFiberEquivTopRow_symm_apply_coe,
    shiftedTopWeightFiberEquivShape_symm_apply_coe, shiftTopWeightEquiv_symm_apply_coe,
    neg_neg]

/-- **The rational pattern count reduces to the polynomial tableau count.**  The Gelfand-Tsetlin
patterns over any dominant weight `l` are as numerous as the bounded semistandard tableaux of the
determinant-normalized shape `l.detShiftShape`. -/
theorem card_topWeight_eq_card_boundedSSYT_detShiftShape (l : DominantWeight n) :
    Nat.card {P : GTPattern n // P.topWeight = l} = Nat.card (BoundedSSYT n l.detShiftShape) :=
  Nat.card_congr (detShiftEquivBoundedSSYT l)

end GTPattern

end TauCeti
