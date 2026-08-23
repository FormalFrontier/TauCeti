/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.OfRowLens

/-!
# Dominant weights for the general linear group

The irreducible rational representations of `GL n` are indexed by the weakly decreasing integer
sequences `λ₁ ≥ ⋯ ≥ λₙ`, the **dominant weights** of the diagonal torus.  This file builds that
index type and its dictionary with Young diagrams, before any representation is attached to a
weight: the combinatorics is exactly the bookkeeping that separates the *polynomial*
representations from the general *rational* ones.

Two facts organize the file.  First, the dominant weights with nonnegative entries — the
`TauCeti.DominantWeight.IsPolynomial` ones — are precisely the Young diagrams with at most `n`
rows, an equivalence `TauCeti.shapeEquivPolynomialWeight`.  Second, every dominant weight is a
**determinant twist** of a polynomial one: writing `m = λₙ` for its last entry
(`TauCeti.DominantWeight.detShift`) and subtracting it leaves a weight with nonnegative entries
whose own last entry vanishes, so its Young diagram `TauCeti.DominantWeight.detShiftShape` has at
most `n - 1` rows, and `λ` is recovered from that diagram by shifting back by `m`.  The vanishing
last entry is what makes the pair `(m, μ)` unique: without the row bound the same `λ` is
`μ + m·(1, …, 1)` for many pairs.  Downstream this is the statement that a rational irreducible
is `det^m` tensored with a polynomial one.

The last entry `λₙ` is read through the dedicated accessor `TauCeti.DominantWeight.detShift`,
which is `0` for `n = 0`, so that the empty weight needs no special casing at the use sites.
Being an accessor rather than a shift, it is compatible with `TauCeti.DominantWeight.shift` only
for a nonempty weight (`TauCeti.DominantWeight.detShift_shift`).

## Main definitions

* `TauCeti.DominantWeight`: the weakly decreasing sequences `Fin n → ℤ`.
* `TauCeti.DominantWeight.shift`: translating a weight by an integer multiple of `(1, …, 1)`.
* `TauCeti.DominantWeight.detShift`: the last entry `λₙ`, the determinant-twist exponent.
* `TauCeti.DominantWeight.IsPolynomial`: having nonnegative entries.
* `TauCeti.DominantWeight.shape` and `TauCeti.weightOfShape`: the two directions of the
  dictionary between weights and Young diagrams.
* `TauCeti.DominantWeight.detShiftShape`: the Young diagram of the polynomial part `λ - λₙ`.

## Main results

* `TauCeti.DominantWeight.isPolynomial_iff_zero_le_detShift`: a weight is polynomial as soon as
  its last entry is nonnegative.
* `TauCeti.shapeEquivPolynomialWeight`: the Young diagrams with at most `n` rows are the
  polynomial dominant weights of `GL n`.
* `TauCeti.DominantWeight.shift_weightOfShape_detShiftShape`: the determinant twist
  `λ = μ + λₙ·(1, …, 1)` with `μ = detShiftShape λ`, together with
  `TauCeti.DominantWeight.colLen_zero_detShiftShape_le_pred`, which bounds `μ` by `n - 1` rows.
* `TauCeti.DominantWeight.eq_detShift_and_eq_detShiftShape`: that decomposition is the only one
  whose diagram has at most `n - 1` rows.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, “Dominant weights”, and Layer 4, “The rational character is Laurent”.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

namespace TauCeti

/-- A **dominant weight** for `GL n`: a weakly decreasing sequence `λ₁ ≥ ⋯ ≥ λₙ` of integers.
These index the irreducible rational representations of `GL n`; the ones with nonnegative entries
(`TauCeti.DominantWeight.IsPolynomial`) index the polynomial ones. -/
abbrev DominantWeight (n : ℕ) : Type := {l : Fin n → ℤ // Antitone l}

namespace DominantWeight

variable {n : ℕ}

theorem antitone (l : DominantWeight n) : Antitone l.1 := l.2

/-- Translating a dominant weight by `m·(1, …, 1)`.  On representations this is tensoring with
the `m`-th power of the determinant. -/
@[expose]
def shift (l : DominantWeight n) (m : ℤ) : DominantWeight n :=
  ⟨fun i => l.1 i + m, fun _ _ h => by simpa using l.antitone h⟩

@[simp]
theorem shift_apply (l : DominantWeight n) (m : ℤ) (i : Fin n) : (l.shift m).1 i = l.1 i + m :=
  rfl

@[simp]
theorem shift_zero (l : DominantWeight n) : l.shift 0 = l := by
  ext i; simp

@[simp]
theorem shift_shift (l : DominantWeight n) (m m' : ℤ) :
    (l.shift m).shift m' = l.shift (m + m') := by
  ext i; simp [add_assoc]

/-- The **determinant-twist exponent** of a dominant weight: its last entry `λₙ`, and `0` for the
empty weight. -/
@[expose]
def detShift : {n : ℕ} → DominantWeight n → ℤ
  | 0, _ => 0
  | _ + 1, l => l.1 (Fin.last _)

@[simp]
theorem detShift_eq_zero_of_isEmpty (l : DominantWeight 0) : l.detShift = 0 := rfl

@[simp]
theorem detShift_succ (l : DominantWeight (n + 1)) : l.detShift = l.1 (Fin.last n) := rfl

/-- The determinant-twist exponent is the smallest entry of a dominant weight. -/
theorem detShift_le (l : DominantWeight n) (i : Fin n) : l.detShift ≤ l.1 i := by
  match n, l, i with
  | 0, _, i => exact i.elim0
  | _ + 1, l, i => exact l.antitone (Fin.le_last i)

/-- Shifting a nonempty dominant weight shifts its last entry.  The hypothesis is not decoration:
for `n = 0` the accessor is `0` by convention and the identity fails. -/
@[simp]
theorem detShift_shift (l : DominantWeight (n + 1)) (m : ℤ) :
    (l.shift m).detShift = l.detShift + m := by
  simp

/-- A dominant weight is **polynomial** when all its entries are nonnegative.  These are the
weights of the representations occurring in tensor powers of the standard representation, as
opposed to the general rational ones, which need a negative power of the determinant. -/
def IsPolynomial (l : DominantWeight n) : Prop := ∀ i, 0 ≤ l.1 i

/-- Since a dominant weight decreases, only its last entry has to be tested for polynomiality.
This is not a `simp` lemma: rewriting `IsPolynomial` away would put the `simp` lemmas whose
statement or hypothesis mentions it — `TauCeti.isPolynomial_weightOfShape` and
`TauCeti.weightOfShape_shape` — out of `simp` normal form. -/
theorem isPolynomial_iff_zero_le_detShift (l : DominantWeight n) :
    l.IsPolynomial ↔ 0 ≤ l.detShift := by
  refine ⟨fun h => ?_, fun h i => h.trans (l.detShift_le i)⟩
  match n, l, h with
  | 0, _, _ => simp
  | _ + 1, l, h => exact h _

/-- Subtracting its last entry makes any dominant weight polynomial. -/
theorem isPolynomial_shift_neg_detShift (l : DominantWeight n) :
    (l.shift (-l.detShift)).IsPolynomial := fun i => by
  have h := l.detShift_le i
  simp only [shift_apply]
  omega

/-- The entries of a dominant weight, truncated to `ℕ`, are still weakly decreasing. -/
theorem toNat_antitone (l : DominantWeight n) : Antitone fun i => (l.1 i).toNat :=
  fun _ _ h => Int.toNat_le_toNat (l.antitone h)

/-- The Young diagram of a dominant weight: its `i`-th row has length `λᵢ`.  Negative entries are
truncated to `0`, so this reads off the intended diagram exactly on the polynomial weights, where
`TauCeti.DominantWeight.natCast_rowLen_shape` recovers the entries. -/
def shape (l : DominantWeight n) : YoungDiagram :=
  YoungDiagram.ofRowLensFin (fun i => (l.1 i).toNat) l.toNat_antitone

@[simp]
theorem rowLen_shape (l : DominantWeight n) (i : Fin n) : l.shape.rowLen i = (l.1 i).toNat :=
  YoungDiagram.rowLen_ofRowLensFin _ _ i

@[simp]
theorem rowLen_shape_eq_zero_of_le (l : DominantWeight n) {i : ℕ} (hi : n ≤ i) :
    l.shape.rowLen i = 0 :=
  YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ hi

@[simp]
theorem colLen_zero_shape_le (l : DominantWeight n) : l.shape.colLen 0 ≤ n :=
  YoungDiagram.colLen_zero_ofRowLensFin_le _ _

/-- On a polynomial weight the row lengths of its Young diagram are the entries themselves. -/
theorem natCast_rowLen_shape {l : DominantWeight n} (hl : l.IsPolynomial) (i : Fin n) :
    (l.shape.rowLen i : ℤ) = l.1 i := by
  rw [rowLen_shape, Int.toNat_of_nonneg (hl i)]

/-- The Young diagram of a polynomial weight has `∑ λᵢ` cells. -/
theorem natCast_card_shape {l : DominantWeight n} (hl : l.IsPolynomial) :
    (l.shape.card : ℤ) = ∑ i, l.1 i := by
  have hcard : l.shape.card = ∑ i, (l.1 i).toNat := YoungDiagram.card_ofRowLensFin _ _
  rw [hcard]
  push_cast
  exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hl i)

end DominantWeight

/-- The dominant weight read off the first `n` row lengths of a Young diagram.  It is the weight
intended by `μ` exactly when `μ` has at most `n` rows; a taller diagram is silently truncated. -/
@[expose]
def weightOfShape (n : ℕ) (μ : YoungDiagram) : DominantWeight n :=
  ⟨fun i => (μ.rowLen i : ℤ), fun _ _ h => Int.ofNat_le.mpr (μ.rowLen_anti _ _ h)⟩

@[simp]
theorem weightOfShape_apply (n : ℕ) (μ : YoungDiagram) (i : Fin n) :
    (weightOfShape n μ).1 i = (μ.rowLen i : ℤ) :=
  rfl

@[simp]
theorem isPolynomial_weightOfShape (n : ℕ) (μ : YoungDiagram) :
    (weightOfShape n μ).IsPolynomial := fun _ => Int.natCast_nonneg _

@[simp]
theorem shape_weightOfShape {n : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ n) :
    (weightOfShape n μ).shape = μ := by
  rw [DominantWeight.shape]
  simp only [weightOfShape_apply, Int.toNat_natCast]
  exact YoungDiagram.ofRowLensFin_rowLen μ hμ

@[simp]
theorem weightOfShape_shape {n : ℕ} {l : DominantWeight n} (hl : l.IsPolynomial) :
    weightOfShape n l.shape = l := by
  ext i
  rw [weightOfShape_apply, DominantWeight.natCast_rowLen_shape hl]

/-- **The polynomial weights are the bounded shapes**: the Young diagrams with at most `n` rows
are exactly the dominant weights of `GL n` with nonnegative entries. -/
@[expose]
def shapeEquivPolynomialWeight (n : ℕ) :
    {μ : YoungDiagram // μ.colLen 0 ≤ n} ≃ {l : DominantWeight n // l.IsPolynomial} where
  toFun μ := ⟨weightOfShape n μ.1, isPolynomial_weightOfShape n μ.1⟩
  invFun l := ⟨l.1.shape, DominantWeight.colLen_zero_shape_le l.1⟩
  left_inv μ := Subtype.ext (shape_weightOfShape μ.2)
  right_inv l := Subtype.ext (weightOfShape_shape l.2)

@[simp]
theorem shapeEquivPolynomialWeight_apply_coe (n : ℕ) (μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}) :
    (shapeEquivPolynomialWeight n μ).1 = weightOfShape n μ.1 :=
  rfl

@[simp]
theorem shapeEquivPolynomialWeight_symm_apply_coe (n : ℕ)
    (l : {l : DominantWeight n // l.IsPolynomial}) :
    ((shapeEquivPolynomialWeight n).symm l).1 = l.1.shape :=
  rfl

namespace DominantWeight

variable {n : ℕ}

/-- The Young diagram of the **polynomial part** `λ - λₙ` of a dominant weight: its `i`-th row has
length `λᵢ - λₙ`.  Together with `TauCeti.DominantWeight.detShift` it presents `λ` as a
determinant twist of a polynomial weight. -/
def detShiftShape (l : DominantWeight n) : YoungDiagram := (l.shift (-l.detShift)).shape

@[simp]
theorem rowLen_detShiftShape (l : DominantWeight n) (i : Fin n) :
    l.detShiftShape.rowLen i = (l.1 i - l.detShift).toNat := by
  rw [detShiftShape, rowLen_shape, shift_apply, ← sub_eq_add_neg]

@[simp]
theorem rowLen_detShiftShape_eq_zero_of_le (l : DominantWeight n) {i : ℕ} (hi : n ≤ i) :
    l.detShiftShape.rowLen i = 0 :=
  rowLen_shape_eq_zero_of_le _ hi

/-- The polynomial part of a dominant weight recovers it after shifting back by `λₙ`. -/
theorem natCast_rowLen_detShiftShape_add_detShift (l : DominantWeight n) (i : Fin n) :
    (l.detShiftShape.rowLen i : ℤ) + l.detShift = l.1 i := by
  have h := l.detShift_le i
  rw [rowLen_detShiftShape]
  omega

/-- The weight of the polynomial part of `λ` is `λ` itself, shifted down by `λₙ`. -/
@[simp]
theorem weightOfShape_detShiftShape (l : DominantWeight n) :
    weightOfShape n l.detShiftShape = l.shift (-l.detShift) :=
  weightOfShape_shape (isPolynomial_shift_neg_detShift l)

/-- **The determinant twist**: every dominant weight is the weight of a Young diagram, shifted by
its last entry. -/
theorem shift_weightOfShape_detShiftShape (l : DominantWeight n) :
    (weightOfShape n l.detShiftShape).shift l.detShift = l := by
  rw [weightOfShape_detShiftShape, shift_shift, neg_add_cancel, shift_zero]

/-- The polynomial part of a dominant weight for `GL n` has at most `n - 1` rows: its last entry
is `λₙ - λₙ = 0` when there is one, and the empty weight has the empty diagram.  This is the row
bound that makes the determinant twist unique. -/
theorem colLen_zero_detShiftShape_le_pred (l : DominantWeight n) :
    l.detShiftShape.colLen 0 ≤ n - 1 := by
  cases n with
  | zero => exact colLen_zero_shape_le _
  | succ n =>
    by_contra h
    have hmem : ((n, 0) : ℕ × ℕ) ∈ l.detShiftShape :=
      YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
    have hpos : 0 < l.detShiftShape.rowLen n := YoungDiagram.mem_iff_lt_rowLen.mp hmem
    have hzero : l.detShiftShape.rowLen n = (l.1 (Fin.last n) - l.detShift).toNat :=
      rowLen_detShiftShape l (Fin.last n)
    rw [detShift_succ, sub_self, Int.toNat_zero] at hzero
    omega

/-- The polynomial part of a dominant weight for `GL n` has at most `n` rows, the bound in the
form consumed by the dictionary between weights and Young diagrams. -/
theorem colLen_zero_detShiftShape_le (l : DominantWeight n) : l.detShiftShape.colLen 0 ≤ n :=
  (colLen_zero_detShiftShape_le_pred l).trans (Nat.sub_le n 1)

/-- **Uniqueness of the determinant twist**: a dominant weight for `GL (n + 1)` is
`μ + m·(1, …, 1)` for exactly one integer `m` and one Young diagram `μ` with at most `n` rows,
namely `m = λₙ₊₁` and `μ` its polynomial part.  The row bound is essential: dropping it lets `μ`
and `m` trade a constant against each other. -/
theorem eq_detShift_and_eq_detShiftShape (l : DominantWeight (n + 1)) {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ n) {m : ℤ} (hm : ∀ i : Fin (n + 1), (μ.rowLen i : ℤ) + m = l.1 i) :
    m = l.detShift ∧ μ = l.detShiftShape := by
  have hm' : m = l.detShift := by
    have h := hm (Fin.last n)
    have hlast : μ.rowLen ((Fin.last n : Fin (n + 1)) : ℕ) = 0 :=
      YoungDiagram.rowLen_eq_zero_of_colLen_le hμ
    rw [hlast, Nat.cast_zero, zero_add] at h
    rw [detShift_succ, ← h]
  refine ⟨hm', YoungDiagram.rowLen_injective (funext fun i => ?_)⟩
  by_cases hi : i < n + 1
  · have h : (μ.rowLen i : ℤ) + m = l.1 ⟨i, hi⟩ := hm ⟨i, hi⟩
    have h' : l.detShiftShape.rowLen i = (l.1 ⟨i, hi⟩ - l.detShift).toNat :=
      rowLen_detShiftShape l ⟨i, hi⟩
    rw [hm'] at h
    omega
  · have hni : n ≤ i := Nat.le_of_succ_le (Nat.le_of_not_lt hi)
    rw [rowLen_detShiftShape_eq_zero_of_le _ (Nat.le_of_not_lt hi),
      YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans hni)]

end DominantWeight

end TauCeti
