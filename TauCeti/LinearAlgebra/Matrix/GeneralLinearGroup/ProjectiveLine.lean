/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Borel` is the subgroup every statement below is about, and this module re-exports
-- the `GL` notation together with the coercion of an element of `GL n R` to its matrix.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
-- `TauCeti.diagGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `TauCeti.jordanGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarUnipotent
-- `TauCeti.GL2NonSplitTorusHom` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
-- The action of a group on the cosets of a subgroup occurs in the statements below.
public import Mathlib.GroupTheory.GroupAction.Quotient
-- `Set.ncard` occurs in the statements below.
public import Mathlib.Data.Set.Card
-- Non-public: `Fintype.card_option` is used only inside the scalar count.
import Mathlib.Data.Fintype.Option

/-!
# The cosets of the Borel subgroup of `GL₂`, and how a matrix permutes them

The coset space `GL₂(F) ⧸ B` of the Borel subgroup of invertible upper-triangular matrices is the
**projective line** over `F`: a coset `g B` remembers exactly the line spanned by the first column
of `g`, because right multiplication by an upper-triangular matrix rescales that column. This file
makes the identification concrete by naming one representative per coset,

`TauCeti.GL2Borel.cosetRep none = 1` and `TauCeti.GL2Borel.cosetRep (some t) = !![t, 1; 1, 0]`,

whose first columns are `(1, 0)` and `(t, 1)`, the `q + 1` lines of `F²`. Over a field these
`q + 1` matrices meet every coset exactly once (`TauCeti.GL2Borel.cosetRepEquiv`).

The point of the parametrization is the **fixed-coset count**: `g` fixes the coset of `y` exactly
when `y⁻¹ g y` is upper triangular, and along the representatives above that condition is a single
polynomial equation in `t`. Writing `g = !![p, q; r, s]`, the coset of `cosetRep none` is fixed
exactly when `r = 0`, and the coset of `cosetRep (some t)` exactly when

`q + (p - s) t - r t² = 0`.

Both conditions say that the corresponding line is an eigenline of `g`, which is why the count
depends only on the conjugacy class. It is read off here for the four families of conjugacy classes
of `GL₂(𝔽_q)`: `q + 1` fixed cosets for a scalar matrix, `2` for a diagonal matrix with distinct
entries, `1` for a Jordan block, and `0` for an element of the non-split torus that does not come
from `F`. Those four numbers, less one, are the character values of the Steinberg representation.

Only the scalar count needs `F` to be finite; the other three are the same over any field, and are
stated there. The elliptic case needs none of the parametrization either:
`TauCeti.GL2NonSplitTorus.conj_notMem_gl2Borel` already says that no conjugate of such an element is
upper triangular, so no coset at all is fixed.

## Main definitions

* `TauCeti.GL2Borel.cosetRep`: the `q + 1` coset representatives, indexed by `Option R`.
* `TauCeti.GL2Borel.cosetRepEquiv`: over a field they index the coset space,
  `Option F ≃ GL₂(F) ⧸ B`.
* `TauCeti.GL2Borel.fixedCosetsEquiv`: the cosets fixed by `g` are indexed by the representatives
  whose conjugate of `g` is upper triangular.

## Main results

* `TauCeti.GL2Borel.conj_cosetRep_none_mem_iff` and
  `TauCeti.GL2Borel.conj_cosetRep_some_mem_iff`: the conjugate of `g` by a representative is upper
  triangular exactly when the displayed entry equation holds.
* `TauCeti.GL2Borel.natCard_fixedCosets_scalar`, `TauCeti.GL2Borel.natCard_fixedCosets_diagGL`,
  `TauCeti.GL2Borel.natCard_fixedCosets_jordanGL` and
  `TauCeti.GL2Borel.natCard_fixedCosets_gl2NonSplitTorusHom`: the counts `q + 1`, `2`, `1` and `0`
  for the four families of conjugacy classes of `GL₂(𝔽_q)`.

## References

This supplies the fixed-point counts on the projective line that the character-value formulas of
Layer 9 ("the representation theory of `GL₂(𝔽_q)`") of
`TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md` need. See also W. Fulton and
J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2, and C. Bonnafé,
*Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

namespace TauCeti

open Matrix

universe u

namespace GL2Borel

section CommRing

variable {R : Type u} [CommRing R]

/-- **The coset representatives of the Borel subgroup of `GL₂`**: the identity, whose first column
spans the line `(1, 0)`, and the matrices `!![t, 1; 1, 0]`, whose first columns span the remaining
lines `(t, 1)`. Over a field these meet every coset of `TauCeti.GL2Borel` exactly once
(`TauCeti.GL2Borel.cosetRepEquiv`). -/
def cosetRep : Option R → GL (Fin 2) R
  | none => 1
  | some t =>
    { val := !![t, 1; 1, 0]
      inv := !![0, 1; 1, -t]
      val_inv := by
        rw [Matrix.mul_fin_two, Matrix.one_fin_two]
        congr 1
        simp
      inv_val := by
        rw [Matrix.mul_fin_two, Matrix.one_fin_two]
        congr 1
        simp }

/-- The representative of the coset of the Borel subgroup itself is the identity. -/
@[simp, grind =]
theorem cosetRep_none : cosetRep (none : Option R) = 1 :=
  (rfl)

/-- The matrix underlying the representative indexed by `t`. -/
@[simp, grind =]
theorem coe_cosetRep_some (t : R) :
    ((cosetRep (some t) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![t, 1; 1, 0] :=
  (rfl)

/-- The inverse of `TauCeti.GL2Borel.cosetRep (some t)`, written out. This is deliberately not a
`simp` lemma: `simp` pushes the inverse inside the coercion instead, so its left-hand side is not
in normal form. -/
theorem coe_inv_cosetRep_some (t : R) :
    (((cosetRep (some t))⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; 1, -t] :=
  (rfl)

/-- Conjugating by the representative `TauCeti.GL2Borel.cosetRep none` does nothing, so the
resulting upper-triangularity condition is that of `g` itself: the line `(1, 0)` is an eigenline
exactly when the lower-left entry vanishes. -/
theorem conj_cosetRep_none_mem_iff (g : GL (Fin 2) R) :
    (cosetRep (none : Option R))⁻¹ * g * cosetRep none ∈ GL2Borel R ↔
      (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  rw [cosetRep_none, inv_one, one_mul, mul_one, mem_iff]

/-- The lower-left entry of the conjugate of `g = !![p, q; r, s]` by
`TauCeti.GL2Borel.cosetRep (some t)` is `q + (p - s) t - r t²`. -/
theorem coe_conj_cosetRep_some_apply_one_zero (g : GL (Fin 2) R) (t : R) :
    (((cosetRep (some t))⁻¹ * g * cosetRep (some t) : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 +
        ((g : Matrix (Fin 2) (Fin 2) R) 0 0 - (g : Matrix (Fin 2) (Fin 2) R) 1 1) * t -
        (g : Matrix (Fin 2) (Fin 2) R) 1 0 * t ^ 2 := by
  rw [Units.val_mul, Units.val_mul, coe_inv_cosetRep_some, coe_cosetRep_some]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  ring

/-- **The fixed-coset equation.** Conjugating `g = !![p, q; r, s]` by the representative
`TauCeti.GL2Borel.cosetRep (some t)` makes it upper triangular exactly when
`q + (p - s) t - r t² = 0`, the condition for `(t, 1)` to span an eigenline of `g`. -/
theorem conj_cosetRep_some_mem_iff (g : GL (Fin 2) R) (t : R) :
    (cosetRep (some t))⁻¹ * g * cosetRep (some t) ∈ GL2Borel R ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 +
          ((g : Matrix (Fin 2) (Fin 2) R) 0 0 - (g : Matrix (Fin 2) (Fin 2) R) 1 1) * t -
          (g : Matrix (Fin 2) (Fin 2) R) 1 0 * t ^ 2 = 0 := by
  rw [mem_iff, coe_conj_cosetRep_some_apply_one_zero]

end CommRing

section Field

variable {F : Type u} [Field F]

private theorem cosetRep_quotient_injective :
    Function.Injective fun x : Option F =>
      (QuotientGroup.mk (cosetRep x) : GL (Fin 2) F ⧸ GL2Borel F) := by
  intro x y hxy
  rw [QuotientGroup.eq, mem_iff] at hxy
  obtain _ | s := x <;> obtain _ | t := y
  · rfl
  · rw [cosetRep_none, inv_one, one_mul, coe_cosetRep_some] at hxy
    simp at hxy
  · rw [cosetRep_none, mul_one, coe_inv_cosetRep_some] at hxy
    simp at hxy
  · rw [Units.val_mul, coe_inv_cosetRep_some, coe_cosetRep_some] at hxy
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply] at hxy
    have hst : t = s := by linear_combination hxy
    rw [hst]

private theorem cosetRep_quotient_surjective :
    Function.Surjective fun x : Option F =>
      (QuotientGroup.mk (cosetRep x) : GL (Fin 2) F ⧸ GL2Borel F) := by
  refine QuotientGroup.mk_surjective.forall.2 fun g => ?_
  by_cases hr : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · refine ⟨none, QuotientGroup.eq.2 ?_⟩
    rw [cosetRep_none, inv_one, one_mul, mem_iff]
    exact hr
  · refine ⟨some ((g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 0),
      QuotientGroup.eq.2 ?_⟩
    rw [mem_iff, Units.val_mul, coe_inv_cosetRep_some]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    field_simp
    ring

variable (F) in
/-- **The cosets of the Borel subgroup are the points of the projective line**: the `q + 1`
representatives of `TauCeti.GL2Borel.cosetRep` index the coset space `GL₂(F) ⧸ B`. -/
noncomputable def cosetRepEquiv : Option F ≃ GL (Fin 2) F ⧸ GL2Borel F :=
  Equiv.ofBijective _ ⟨cosetRep_quotient_injective, cosetRep_quotient_surjective⟩

@[simp]
theorem cosetRepEquiv_apply (x : Option F) :
    cosetRepEquiv F x = (QuotientGroup.mk (cosetRep x) : GL (Fin 2) F ⧸ GL2Borel F) :=
  (rfl)

/-- A matrix fixes the coset of `y` exactly when the conjugate `y⁻¹ g y` is upper triangular. -/
theorem smul_quotientMk_eq_iff (g y : GL (Fin 2) F) :
    g • (QuotientGroup.mk y : GL (Fin 2) F ⧸ GL2Borel F) = QuotientGroup.mk y ↔
      y⁻¹ * g * y ∈ GL2Borel F := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, ← Subgroup.inv_mem_iff]
  simp [mul_assoc]

variable (F) in
/-- **The cosets fixed by `g` are indexed by the fixed representatives.** Together with
`TauCeti.GL2Borel.conj_cosetRep_none_mem_iff` and `TauCeti.GL2Borel.conj_cosetRep_some_mem_iff`
this turns a fixed-coset count into the count of solutions of an equation in one variable. -/
noncomputable def fixedCosetsEquiv (g : GL (Fin 2) F) :
    {x : Option F // (cosetRep x)⁻¹ * g * cosetRep x ∈ GL2Borel F} ≃
      {c : GL (Fin 2) F ⧸ GL2Borel F // g • c = c} :=
  (cosetRepEquiv F).subtypeEquiv fun x => by
    rw [cosetRepEquiv_apply, smul_quotientMk_eq_iff]

/-- **The fixed-coset count** is the number of parameters whose representative conjugates `g` into
the Borel subgroup. -/
theorem natCard_fixedCosets_eq_ncard (g : GL (Fin 2) F) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // g • c = c} =
      {x : Option F | (cosetRep x)⁻¹ * g * cosetRep x ∈ GL2Borel F}.ncard := by
  exact (Nat.card_congr (fixedCosetsEquiv F g)).symm

/-- **A diagonal matrix with distinct entries fixes exactly two cosets**, the two coordinate axes:
the equation of `TauCeti.GL2Borel.conj_cosetRep_some_mem_iff` reads `(a - b) t = 0`. -/
theorem natCard_fixedCosets_diagGL {a b : Fˣ} (hab : a ≠ b) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // diagGL ![a, b] • c = c} = 2 := by
  have hab' : (a : F) - (b : F) ≠ 0 := sub_ne_zero.2 fun h => hab (Units.ext h)
  have e00 : ((diagGL ![a, b] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F) := by simp
  have e01 : ((diagGL ![a, b] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simp
  have e10 : ((diagGL ![a, b] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp
  have e11 : ((diagGL ![a, b] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (b : F) := by simp
  rw [natCard_fixedCosets_eq_ncard]
  have hpair : {x : Option F | (cosetRep x)⁻¹ * diagGL ![a, b] * cosetRep x ∈ GL2Borel F} =
      {none, some 0} := by
    ext x
    obtain _ | t := x
    · simp only [Set.mem_ofPred_eq, conj_cosetRep_none_mem_iff, e10, Set.mem_insert_iff,
        Set.mem_singleton_iff, true_or]
    · rw [Set.mem_ofPred_eq, conj_cosetRep_some_mem_iff, e00, e01, e10, e11]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq, Option.some.injEq,
        false_or]
      constructor
      · intro h
        rcases mul_eq_zero.1 (by linear_combination h : ((a : F) - (b : F)) * t = 0) with h' | h'
        · exact absurd h' hab'
        · exact h'
      · rintro rfl
        ring
  rw [hpair, Set.ncard_pair (by simp)]

/-- **A Jordan block fixes exactly one coset**, the line of its single eigenvector: the equation of
`TauCeti.GL2Borel.conj_cosetRep_some_mem_iff` reads `b = 0`, which is excluded. -/
theorem natCard_fixedCosets_jordanGL (a : Fˣ) {b : F} (hb : b ≠ 0) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // jordanGL a b • c = c} = 1 := by
  have e00 : ((jordanGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : F) := by
    rw [coe_jordanGL]; simp
  have e01 : ((jordanGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = b := by
    rw [coe_jordanGL]; simp
  have e10 : ((jordanGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [coe_jordanGL]; simp
  have e11 : ((jordanGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (a : F) := by
    rw [coe_jordanGL]; simp
  rw [natCard_fixedCosets_eq_ncard]
  have hsingle : {x : Option F | (cosetRep x)⁻¹ * jordanGL a b * cosetRep x ∈ GL2Borel F} =
      {none} := by
    ext x
    obtain _ | t := x
    · simp only [Set.mem_ofPred_eq, conj_cosetRep_none_mem_iff, e10, Set.mem_singleton_iff]
    · rw [Set.mem_ofPred_eq, conj_cosetRep_some_mem_iff, e00, e01, e10, e11]
      simp only [Set.mem_singleton_iff, reduceCtorEq, iff_false]
      intro h
      exact hb (by linear_combination h)
  rw [hsingle, Set.ncard_singleton]

section NonSplit

variable {E : Type u} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- **An element of the non-split torus outside `F` fixes no coset at all.** A fixed coset would
exhibit an upper-triangular conjugate, which is exactly what
`TauCeti.GL2NonSplitTorus.conj_notMem_gl2Borel` forbids. This is the elliptic case: the eigenvalues
of such a matrix are a conjugate pair in `E ∖ F`, so it has no eigenline over `F`. -/
theorem natCard_fixedCosets_gl2NonSplitTorusHom {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F // GL2NonSplitTorusHom F E hE x • c = c} = 0 := by
  have hnone : ∀ c : GL (Fin 2) F ⧸ GL2Borel F,
      ¬ GL2NonSplitTorusHom F E hE x • c = c := by
    refine QuotientGroup.mk_surjective.forall.2 fun y hy => ?_
    exact GL2NonSplitTorus.conj_notMem_gl2Borel hE hx y⁻¹
      (by simpa using (smul_quotientMk_eq_iff _ y).1 hy)
  have : IsEmpty {c : GL (Fin 2) F ⧸ GL2Borel F // GL2NonSplitTorusHom F E hE x • c = c} :=
    ⟨fun c => hnone c.1 c.2⟩
  exact Nat.card_of_isEmpty

end NonSplit

end Field

section FiniteField

variable {F : Type u} [Field F] [Fintype F]

/-- **A scalar matrix fixes every coset**, so it fixes all `q + 1` points of the projective line:
the equation of `TauCeti.GL2Borel.conj_cosetRep_some_mem_iff` degenerates to `0 = 0`. -/
theorem natCard_fixedCosets_scalar (u : Fˣ) :
    Nat.card {c : GL (Fin 2) F ⧸ GL2Borel F //
        Matrix.GeneralLinearGroup.scalar (Fin 2) u • c = c} = Fintype.card F + 1 := by
  have e00 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 0 = (u : F) := by simp [Matrix.scalar_apply]
  have e01 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simp [Matrix.scalar_apply]
  have e10 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [Matrix.scalar_apply]
  have e11 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 1 = (u : F) := by simp [Matrix.scalar_apply]
  rw [natCard_fixedCosets_eq_ncard]
  have huniv : {x : Option F | (cosetRep x)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u *
      cosetRep x ∈ GL2Borel F} = Set.univ := by
    ext x
    obtain _ | t := x
    · simp only [Set.mem_ofPred_eq, conj_cosetRep_none_mem_iff, e10, Set.mem_univ]
    · rw [Set.mem_ofPred_eq, conj_cosetRep_some_mem_iff, e00, e01, e10, e11]
      simp only [Set.mem_univ, iff_true]
      ring
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_option]

end FiniteField

end GL2Borel

end TauCeti
