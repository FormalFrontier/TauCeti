/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.Matrix.PosDef
public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# Cartan matrices of finite type

The Cartan-Killing classification is, at bottom, a statement about integer matrices: the Cartan
matrix of a finite crystallographic root system is a generalized Cartan matrix that is
*symmetrizable with positive definite symmetrization*, and only finitely many combinatorial shapes
of such a matrix exist. This file introduces the matrix-level condition, `TauCeti.IsFiniteType`,
develops the tools that eliminate diagrams from the list, and proves that the Cartan matrix of a
base of a finite crystallographic root system satisfies it.

Positive definiteness is asked for over `ℚ`, not over `ℤ`.
`TauCeti.Matrix.posDef_map_intCast` shows that positive definiteness over `ℤ` implies positive
definiteness over `ℚ`, and the rational form is the one downstream arguments use, since a test
vector produced by a diagram computation need not have integer entries. The symmetrizer `d` is
likewise rational: it is the vector of inverse root lengths, which is integral only after clearing
denominators. The symmetrization itself is not redone here: Mathlib packages it over `ℤ` as
`RootPairing.Base.exists_cartanMatrix_diagaonal_mul_posDef`, resting on
`RootPairing.posRootForm_rootFormIn_posDef`.

## Main definitions

* `TauCeti.IsFiniteType`: an integer matrix is a generalized Cartan matrix admitting a positive
  rational symmetrizer whose symmetrization is positive definite.

## Main results

* `TauCeti.isFiniteType_of`: a constructor that does not ask for the symmetric vanishing pattern,
  which the symmetrizer already forces.
* `TauCeti.IsFiniteType.submatrix`: principal submatrices of a finite-type matrix are of finite
  type. This is what lets a forbidden subdiagram rule out a diagram containing it.
* `TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne`: the rank-two bound. For `i ≠ j` the Cartan
  product `A i j * A j i` lies in `{0, 1, 2, 3}`, so every edge of the diagram is single, double or
  triple.
* `TauCeti.IsFiniteType.det_ne_zero`: a finite-type matrix is nonsingular. Since the extended
  Dynkin diagrams have singular Cartan matrices, this is the second elimination tool; the affine
  type `Ã₂` is ruled out in `TauCeti.not_isFiniteType_affineA₂`.
* `TauCeti.isFiniteType_cartanMatrix`: **the Cartan matrix of a base of a finite crystallographic
  root system is of finite type**, and `TauCeti.HasCartanType.isFiniteType`: so is the standard
  Cartan matrix of any Dynkin type realized by such a base.

## References

This file implements the "finite-type condition" item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signature
`isFiniteType_cartanMatrix` in that roadmap's `Suggested.lean`. See V. G. Kac, *Infinite
Dimensional Lie Algebras*, 3rd ed., Chapter 4, for the finite/affine/indefinite trichotomy of
generalized Cartan matrices, and Humphreys, *Introduction to Lie Algebras and Representation
Theory*, Chapter 11, for the classification of the finite-type case.
-/

namespace TauCeti

variable {B : Type*} {A : Matrix B B ℤ}

/-- A finite square integer matrix is **of finite type** when it is a generalized Cartan matrix -
diagonal entries `2`, nonpositive off-diagonal entries, and a symmetric vanishing pattern - which
is symmetrizable with positive definite symmetrization: there is a positive rational vector `d`
making `fun i j ↦ d i * A i j` positive definite (in particular symmetric).

The Cartan matrices of finite root systems are exactly the matrices of this kind, up to
irreducibility; `TauCeti.isFiniteType_cartanMatrix` proves one direction. -/
def IsFiniteType [Fintype B] (A : Matrix B B ℤ) : Prop :=
  (∀ i, A i i = 2) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ (∀ i j, A i j = 0 → A j i = 0) ∧
    ∃ d : B → ℚ, (∀ i, 0 < d i) ∧ (Matrix.of fun i j ↦ d i * (A i j : ℚ)).PosDef

variable [Fintype B]

/-- **Building a finite-type matrix.** The symmetric vanishing pattern demanded by
`TauCeti.IsFiniteType` need not be checked: a positive symmetrizer already forces
`d j * A j i = d i * A i j`, so one entry of a transposed pair vanishes exactly when the other
does. The clause is kept in the definition because it is one of the defining axioms of a
generalized Cartan matrix. -/
theorem isFiniteType_of (h2 : ∀ i, A i i = 2) (hle : ∀ i j, i ≠ j → A i j ≤ 0) {d : B → ℚ}
    (hd : ∀ i, 0 < d i) (hpd : (Matrix.of fun i j ↦ d i * (A i j : ℚ)).PosDef) :
    IsFiniteType A := by
  refine ⟨h2, hle, fun i j hij ↦ ?_, d, hd, hpd⟩
  have hsymm := hpd.isHermitian.apply i j
  simp only [Matrix.of_apply, star_trivial] at hsymm
  rw [hij] at hsymm
  have : ((A j i : ℤ) : ℚ) = 0 := by simpa [(hd j).ne'] using hsymm
  exact_mod_cast this

namespace IsFiniteType

/-- The diagonal entries of a finite-type matrix are `2`. -/
lemma apply_self (h : IsFiniteType A) (i : B) : A i i = 2 := h.1 i

/-- The off-diagonal entries of a finite-type matrix are nonpositive. -/
lemma apply_le_zero_of_ne (h : IsFiniteType A) {i j : B} (hij : i ≠ j) : A i j ≤ 0 := h.2.1 i j hij

/-- The vanishing pattern of a finite-type matrix is symmetric. -/
lemma apply_eq_zero_symm (h : IsFiniteType A) {i j : B} (hij : A i j = 0) : A j i = 0 :=
  h.2.2.1 i j hij

/-- An entry of a finite-type matrix vanishes exactly when its transpose does. -/
lemma apply_eq_zero_iff (h : IsFiniteType A) {i j : B} : A i j = 0 ↔ A j i = 0 :=
  ⟨h.apply_eq_zero_symm, h.apply_eq_zero_symm⟩

/-- The symmetrizer of a finite-type matrix, together with its defining properties. -/
lemma exists_symmetrizer (h : IsFiniteType A) :
    ∃ d : B → ℚ, (∀ i, 0 < d i) ∧ (Matrix.of fun i j ↦ d i * (A i j : ℚ)).PosDef := h.2.2.2

/-- **A principal submatrix of a finite-type matrix is of finite type.** This is the form in which
a forbidden subdiagram excludes every diagram containing it. -/
theorem submatrix {C : Type*} [Fintype C] (h : IsFiniteType A) {e : C → B}
    (he : Function.Injective e) :
    IsFiniteType (A.submatrix e e) := by
  -- Restricting the symmetrizer along the same injection restricts the symmetrization, and
  -- positive definiteness passes to principal submatrices.
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  refine ⟨fun i ↦ h.apply_self _, fun i j hij ↦ h.apply_le_zero_of_ne fun hc ↦ hij (he hc),
    fun i j hij ↦ h.apply_eq_zero_symm hij, d ∘ e, fun i ↦ hd _, ?_⟩
  exact hpd.submatrix he

/-- The rank-two case of the Cartan-product bound, where the quadratic form can be evaluated on an
explicit vector. Testing at `(-A 0 1, 2)` kills the first coordinate of the symmetrization and
leaves `2 * d 1 * (4 - A 0 1 * A 1 0)`. -/
private lemma apply_mul_apply_lt_four_fin_two {A : Matrix (Fin 2) (Fin 2) ℤ} (h : IsFiniteType A) :
    A 0 1 * A 1 0 < 4 := by
  obtain ⟨d, hd, hpd⟩ := h.exists_symmetrizer
  have h₀ : A 0 0 = 2 := h.apply_self 0
  have h₁ : A 1 1 = 2 := h.apply_self 1
  have hx : (![-(A 0 1 : ℚ), 2] : Fin 2 → ℚ) ≠ 0 := fun hc ↦ by
    simpa using congrFun hc 1
  have hq := hpd.dotProduct_mulVec_pos hx
  rw [star_trivial] at hq
  simp only [_root_.dotProduct, _root_.Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, h₀, h₁] at hq
  -- The value of the quadratic form is `2 * d 1 * (4 - A 0 1 * A 1 0)`.
  have hq' : 0 < 2 * d 1 * (4 - (A 0 1 : ℚ) * (A 1 0 : ℚ)) := by push_cast at hq ⊢; linarith
  have hlt : (A 0 1 : ℚ) * (A 1 0 : ℚ) < 4 := by
    nlinarith [hd 1, hq']
  exact_mod_cast hlt

/-- **The Cartan product of two distinct indices of a finite-type matrix is `0`, `1`, `2` or `3`.**
These are exactly the values that name the orders `2, 3, 4, 6` of a product of two simple
reflections. -/
theorem apply_mul_apply_mem_of_ne (h : IsFiniteType A) {i j : B} (hij : i ≠ j) :
    A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
  -- Nonnegativity is the product of two nonpositive entries; the upper bound is the rank-two
  -- computation, applied to the principal submatrix on `{i, j}`.
  have hinj : Function.Injective (![i, j] : Fin 2 → B) := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> simp_all
  have hsub := (h.submatrix hinj).apply_mul_apply_lt_four_fin_two
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hsub
  have hnonneg : 0 ≤ A i j * A j i :=
    mul_nonneg_of_nonpos_of_nonpos (h.apply_le_zero_of_ne hij) (h.apply_le_zero_of_ne hij.symm)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **A finite-type matrix is nonsingular.** This is the elimination tool for the extended Dynkin
diagrams, whose Cartan matrices are singular. -/
theorem det_ne_zero [DecidableEq B] (h : IsFiniteType A) : A.det ≠ 0 := by
  -- The symmetrization is a positive definite matrix over a field, hence invertible, and the
  -- symmetrizer contributes only a nonzero diagonal factor.
  obtain ⟨d, -, hpd⟩ := h.exists_symmetrizer
  have hu : IsUnit (Matrix.diagonal d * A.map (Int.cast : ℤ → ℚ)) := by
    apply Matrix.PosDef.isUnit
    convert hpd using 1
    ext i j
    simp [Matrix.diagonal_mul]
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_diagonal] at hu
  intro hdet
  have hzero : (A.map (Int.cast : ℤ → ℚ)).det = 0 := by
    rw [← Int.cast_det A, hdet, Int.cast_zero]
  rw [hzero, mul_zero] at hu
  simp at hu

end IsFiniteType

/-- **The Cartan matrix of the affine diagram `Ã₂` is not of finite type.** The three-cycle is a
genuine generalized Cartan matrix, symmetric with every Cartan product equal to `1`, so neither the
combinatorial axioms nor the rank-two bound exclude it; it is positive *semi*definite, and it is
`TauCeti.IsFiniteType.det_ne_zero` that rules it out. -/
theorem not_isFiniteType_affineA₂ :
    ¬ IsFiniteType (!![2, -1, -1; -1, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) ℤ) := by
  intro h
  refine h.det_ne_zero ?_
  norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- **The Cartan matrix of a base of a finite crystallographic root system is of finite type.** The
symmetrizer is the vector of inverse root lengths for the canonical form.

Reducedness is not assumed: positive definiteness of the canonical form does not need it. -/
theorem isFiniteType_cartanMatrix [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsCrystallographic] (b : P.Base) :
    IsFiniteType b.cartanMatrix := by
  classical
  -- Mathlib packages the positive definite symmetrization over `ℤ`, and
  -- `TauCeti.Matrix.posDef_map_intCast` carries it over `ℚ`.
  obtain ⟨d, hd, hpd⟩ := b.exists_cartanMatrix_diagaonal_mul_posDef
  refine isFiniteType_of (fun i ↦ b.cartanMatrix_apply_same i)
    (fun i j hij ↦ b.cartanMatrix_le_zero_of_ne i j hij)
    (d := fun i ↦ (d i : ℚ)) (fun i ↦ by exact_mod_cast hd i) ?_
  convert Matrix.posDef_map_intCast hpd using 1
  ext i j
  simp [Matrix.diagonal_mul]

/-- **The standard Cartan matrix of a Dynkin type realized by a base is of finite type.** This is
the shape in which the finite-type condition eliminates candidate Dynkin types. -/
theorem HasCartanType.isFiniteType [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] [P.IsCrystallographic] {b : P.Base} {t : DynkinType}
    (h : HasCartanType P b t) : IsFiniteType t.cartanMatrix := by
  -- Relabelling by the inverse of the matching turns the standard matrix into a principal
  -- submatrix - indeed a reindexing - of the Cartan matrix of the base.
  obtain ⟨e, he⟩ := (hasCartanType_iff_reindex b t).mp h
  rw [← he]
  exact (isFiniteType_cartanMatrix b).submatrix e.symm.injective

end RootPairing

end TauCeti
