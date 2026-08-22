/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.JointEigenvalueSearch
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Eigenrow
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Searching for modular central-character rows

The Dixon--Schneider algorithm applies simultaneous left-eigenvector search to the class-
multiplication matrices.  This file makes that specialization executable for
`TauCeti.ClassData`: `TauCeti.ClassData.centralCharacterSearch` searches the transposed numbered
class matrices, and hence returns eigenvalue tuples rather than arbitrarily scaled eigenvectors.

The main correctness theorem, `TauCeti.ClassData.mem_centralCharacterSearch`, identifies the
output exactly with normalized common eigenrows.  The normalization is not imposed by an extra
filter.  Multiplication by the identity class forces its eigenvalue to be `1`, and evaluating the
other eigenvector equations in the identity coordinate shows that every returned eigenvalue tuple
is the unique normalization of its common eigenvector.

This is the bridge between the generic finite-field search in
`TauCeti.LinearAlgebra.Matrix.JointEigenvalueSearch` and the reduced central-character table in the
Dixon--Schneider pipeline. Nothing here counts the output. Under a general splitting hypothesis the
count is `TauCeti.ClassData.card_centralCharacterSearch`; its good-prime specialization is
`TauCeti.ClassData.card_centralCharacterSearch_of_isGoodDixonPrime`.

## Main definitions

* `TauCeti.ClassData.modularClassMatrix`: a numbered integral class matrix reduced into a field.
* `TauCeti.ClassData.IsModularEigenrow`: the numbered common-eigenrow condition.
* `TauCeti.ClassData.reindexModularRow`: transport from numbered rows to conjugacy-class rows,
  bundled on the normalized eigenrows as `TauCeti.ClassData.modularEigenrowEquiv`.
* `TauCeti.ClassData.centralCharacterSearch`: the executable simultaneous eigenvalue search.

## Main results

* `TauCeti.ClassData.modularClassMatrix_eq_submatrix`: the numbered modular matrices are a
  renumbering of the class-indexed ones, so their theory transports.
* `TauCeti.ClassData.modularClassMatrix_index_one`: the identity-class matrix is the identity.
* `TauCeti.ClassData.IsModularEigenrow.map`: eigenrows are preserved by coefficient-ring maps.
* `TauCeti.ClassData.vecMul_modularClassMatrix_apply_index_one`: the identity coordinate of
  `v ᵥ* Mᵢ` is `v i`.
* `TauCeti.ClassData.mem_centralCharacterSearch`: search membership is exactly the normalized
  common-eigenrow condition.
* `TauCeti.ClassData.mem_centralCharacterSearch_iff_exists_algHom`: a searched tuple is exactly
  the row of an algebra homomorphism out of the modular centre.

## References

This advances Layer 6, "The eigenvector search", of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

open Matrix

namespace ClassData

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G)

section CommRing

variable {F : Type*} [CommRing F]

/-- The `i`-th numbered class-multiplication matrix, reduced from `ℤ` into `F`. -/
@[expose] def modularClassMatrix (i : Fin d.numClasses) :
    Matrix (Fin d.numClasses) (Fin d.numClasses) F :=
  (d.classMultMatrix i).map (Int.cast : ℤ → F)

@[simp]
theorem modularClassMatrix_apply (i j k : Fin d.numClasses) :
    d.modularClassMatrix (F := F) i j k = (d.structureConstant i k j : F) := by
  simp [modularClassMatrix]

/-- **The numbered modular class matrix is a renumbering of the class-indexed one.** This is
`TauCeti.ClassData.classMultMatrix_eq_submatrix` pushed through the reduction map, and is what
transports the class-indexed matrix API to the numbered family. -/
theorem modularClassMatrix_eq_submatrix (i : Fin d.numClasses) :
    d.modularClassMatrix (F := F) i =
      ((TauCeti.classMultMatrix (d.classOf i)).map (Int.cast : ℤ → F)).submatrix
        d.equivConjClasses d.equivConjClasses := by
  rw [modularClassMatrix, d.classMultMatrix_eq_submatrix i, Matrix.submatrix_map]

/-- A numbered row is a common left eigenrow when its eigenvalue for the `i`-th class matrix is
its own `i`-th entry. -/
def IsModularEigenrow (v : Fin d.numClasses → F) : Prop :=
  ∀ i, v ᵥ* d.modularClassMatrix i = v i • v

/-- `TauCeti.ClassData.IsModularEigenrow` restated in its defining vector form, for consumers that
want the literal eigenvector equation without unfolding the definition. -/
theorem isModularEigenrow_def (v : Fin d.numClasses → F) :
    d.IsModularEigenrow v ↔ ∀ i, v ᵥ* d.modularClassMatrix i = v i • v :=
  Iff.rfl

/-- Transport a numbered row along the numbering equivalence to a row indexed by conjugacy
classes. -/
def reindexModularRow (v : Fin d.numClasses → F) : ConjClasses G → F :=
  v ∘ d.equivConjClasses.symm

omit [CommRing F] in
@[simp]
theorem reindexModularRow_classOf (v : Fin d.numClasses → F) (i : Fin d.numClasses) :
    d.reindexModularRow v (d.classOf i) = v i := by
  rw [← d.equivConjClasses_apply i]
  simp only [reindexModularRow, Function.comp_apply, Equiv.symm_apply_apply]

/-- The numbered eigenrow condition in scalar structure-constant form. -/
theorem isModularEigenrow_iff (v : Fin d.numClasses → F) :
    d.IsModularEigenrow v ↔ ∀ i j,
      ∑ k, (d.structureConstant i j k : F) * v k = v i * v j := by
  constructor
  · intro h i j
    have hij := congrFun (h i) j
    rw [Matrix.vecMul_apply_eq_sum] at hij
    simpa only [modularClassMatrix_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hij
  · intro h i
    funext j
    rw [Matrix.vecMul_apply_eq_sum]
    simpa only [modularClassMatrix_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h i j

/-- A numbered common eigenrow remains one after applying a homomorphism of commutative
coefficient rings entrywise. -/
theorem IsModularEigenrow.map {d : ClassData G} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S)
    {v : Fin d.numClasses → R} (h : d.IsModularEigenrow v) :
    d.IsModularEigenrow fun i => f (v i) := by
  rw [d.isModularEigenrow_iff] at h ⊢
  intro i j
  calc
    ∑ k, (d.structureConstant i j k : S) * f (v k) =
        ∑ k, f ((d.structureConstant i j k : R) * v k) := by simp
    _ = f (∑ k, (d.structureConstant i j k : R) * v k) :=
      (map_sum f (fun k => (d.structureConstant i j k : R) * v k) Finset.univ).symm
    _ = f (v i * v j) := congrArg f (h i j)
    _ = f (v i) * f (v j) := map_mul f _ _

/-- Renumbering identifies the executable numbered eigenrow condition with the class-indexed
`TauCeti.IsClassEigenrow` predicate used by the class-algebra API. -/
theorem isModularEigenrow_iff_isClassEigenrow (v : Fin d.numClasses → F) :
    d.IsModularEigenrow v ↔ IsClassEigenrow (d.reindexModularRow v) := by
  rw [d.isModularEigenrow_iff, TauCeti.isClassEigenrow_iff]
  constructor
  · intro h Cᵢ Cⱼ
    obtain ⟨i, rfl⟩ := d.equivConjClasses.surjective Cᵢ
    obtain ⟨j, rfl⟩ := d.equivConjClasses.surjective Cⱼ
    rw [← d.equivConjClasses.sum_comp]
    simpa only [equivConjClasses_apply, reindexModularRow_classOf,
      d.structureConstant_eq] using h i j
  · intro h i j
    have hij := h (d.classOf i) (d.classOf j)
    rw [← d.equivConjClasses.sum_comp] at hij
    simpa only [equivConjClasses_apply, reindexModularRow_classOf,
      d.structureConstant_eq] using hij

/-- **Renumbering matches the normalized numbered eigenrows with the normalized class-indexed
ones**, bundling `TauCeti.ClassData.reindexModularRow` and
`TauCeti.ClassData.isModularEigenrow_iff_isClassEigenrow` as an equivalence.  It is what carries a
count of the class-indexed eigenrows over to the output of the executable search. -/
def modularEigenrowEquiv :
    {a : Fin d.numClasses → F // a (d.index 1) = 1 ∧ d.IsModularEigenrow a} ≃
      {v : ConjClasses G → F // v (ConjClasses.mk (1 : G)) = 1 ∧ IsClassEigenrow v} :=
  (d.equivConjClasses.arrowCongr (Equiv.refl F)).subtypeEquiv fun a =>
    and_congr
      (by
        rw [← d.classOf_index (1 : G)]
        exact iff_of_eq (congrArg (· = 1) (d.reindexModularRow_classOf a (d.index 1))).symm)
      (d.isModularEigenrow_iff_isClassEigenrow a)

@[simp]
theorem coe_modularEigenrowEquiv
    (a : {a : Fin d.numClasses → F // a (d.index 1) = 1 ∧ d.IsModularEigenrow a}) :
    (d.modularEigenrowEquiv a : ConjClasses G → F) =
      d.reindexModularRow (a : Fin d.numClasses → F) := by
  funext C
  obtain ⟨i, rfl⟩ := d.equivConjClasses.surjective C
  simp only [modularEigenrowEquiv, Equiv.subtypeEquiv_apply, Equiv.arrowCongr_apply,
    Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
  rw [d.equivConjClasses_apply, d.reindexModularRow_classOf]

/-- Applying the inverse renumbering equivalence at a numbered class recovers the corresponding
class-indexed entry. -/
@[simp]
theorem modularEigenrowEquiv_symm_apply
    (v : {v : ConjClasses G → F // v (ConjClasses.mk (1 : G)) = 1 ∧ IsClassEigenrow v})
    (i : Fin d.numClasses) :
    (d.modularEigenrowEquiv.symm v : Fin d.numClasses → F) i =
      (v : ConjClasses G → F) (d.classOf i) := by
  simp only [modularEigenrowEquiv, Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply,
    Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm,
    Equiv.refl_apply]
  rw [Equiv.symm_symm, d.equivConjClasses_apply]

/-- The numbered modular class matrix belonging to the identity conjugacy class is the identity
matrix.  This is `TauCeti.classMultMatrix_mk_one`, renumbered. -/
@[simp]
theorem modularClassMatrix_index_one :
    d.modularClassMatrix (F := F) (d.index 1) = 1 := by
  rw [d.modularClassMatrix_eq_submatrix, d.classOf_index, TauCeti.classMultMatrix_mk_one,
    Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.submatrix_one_equiv]

/-- The identity coordinate of `v ᵥ* Mᵢ` is `v i`.  This coordinate is what turns the
eigenvalues found by simultaneous search into a canonically normalized eigenrow.  It is
`TauCeti.vecMul_classMultMatrix_apply` at the class of `1`, renumbered. -/
theorem vecMul_modularClassMatrix_apply_index_one (v : Fin d.numClasses → F)
    (i : Fin d.numClasses) :
    (v ᵥ* d.modularClassMatrix i) (d.index 1) = v i := by
  have hvecMul : v ᵥ* d.modularClassMatrix i =
      (d.reindexModularRow v ᵥ* (TauCeti.classMultMatrix (d.classOf i)).map (Int.cast : ℤ → F)) ∘
        d.equivConjClasses := by
    rw [d.modularClassMatrix_eq_submatrix, Matrix.submatrix_vecMul_equiv]
    simp only [reindexModularRow]
  rw [hvecMul, Function.comp_apply, equivConjClasses_apply, d.classOf_index,
    vecMul_classMultMatrix_apply]
  simp only [structureConstant_mk_one_right, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq' Finset.univ (d.classOf i), Finset.mem_univ,
    ite_true, reindexModularRow_classOf]

end CommRing

section Search

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Search for the simultaneous left-eigenvalue tuples of the numbered modular class matrices.

The generic search is a column-eigenvector search, so the family is transposed here.  The output
is a `Finset`, making this definition directly executable for `ZMod p` and other finite fields. -/
@[expose] def centralCharacterSearch : Finset (Fin d.numClasses → F) :=
  jointEigenvalueSearch fun i => (d.modularClassMatrix i)ᵀ

/-- A tuple returned by `TauCeti.ClassData.centralCharacterSearch` is normalized at the identity
class. -/
theorem apply_index_one_eq_one_of_mem_centralCharacterSearch
    {a : Fin d.numClasses → F} (ha : a ∈ d.centralCharacterSearch) :
    a (d.index 1) = 1 := by
  rw [centralCharacterSearch, mem_jointEigenvalueSearch_transpose] at ha
  obtain ⟨v, hv₀, hv⟩ := ha
  have h := hv (d.index 1)
  rw [d.modularClassMatrix_index_one] at h
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hn
    apply hv₀
    funext j
    exact not_not.mp fun hj => hn ⟨j, hj⟩
  have hj_eq := congrFun h j
  simp only [Matrix.vecMul_one, Pi.smul_apply, smul_eq_mul] at hj_eq
  apply mul_right_cancel₀ hj
  simpa using hj_eq.symm

/-- Every tuple returned by the search satisfies the numbered common-eigenrow equations. -/
theorem isModularEigenrow_of_mem_centralCharacterSearch
    {a : Fin d.numClasses → F} (ha : a ∈ d.centralCharacterSearch) :
    d.IsModularEigenrow a := by
  rw [centralCharacterSearch, mem_jointEigenvalueSearch_transpose] at ha
  obtain ⟨v, hv₀, hv⟩ := ha
  have hv_one : v (d.index 1) ≠ 0 := by
    intro hv_one
    apply hv₀
    funext i
    have hi := congrFun (hv i) (d.index 1)
    rw [d.vecMul_modularClassMatrix_apply_index_one] at hi
    simpa [hv_one] using hi
  have ha_eq : a = (v (d.index 1))⁻¹ • v := by
    funext i
    have hi := congrFun (hv i) (d.index 1)
    rw [d.vecMul_modularClassMatrix_apply_index_one] at hi
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi]
    symm
    calc
      (v (d.index 1))⁻¹ * (a i * v (d.index 1)) =
          a i * ((v (d.index 1))⁻¹ * v (d.index 1)) := by ring
      _ = a i := by rw [inv_mul_cancel₀ hv_one, mul_one]
  have hscaled : ∀ i, ((v (d.index 1))⁻¹ • v) ᵥ* d.modularClassMatrix i =
      a i • ((v (d.index 1))⁻¹ • v) := by
    intro i
    rw [Matrix.smul_vecMul, hv i]
    simp only [smul_smul]
    rw [mul_comm (v (d.index 1))⁻¹]
  intro i
  simpa only [ha_eq] using hscaled i

/-- **Correctness of the modular central-character search.**  A tuple occurs exactly when it is a
normalized common left eigenrow of the numbered class-multiplication matrices.

The forward implication is the normalization argument: any nonzero common eigenvector has a
nonzero identity coordinate, and division by that coordinate gives the eigenvalue tuple.  The
reverse implication feeds the row itself to the generic common-eigenvector search. -/
@[simp]
theorem mem_centralCharacterSearch {a : Fin d.numClasses → F} :
    a ∈ d.centralCharacterSearch ↔
      a (d.index 1) = 1 ∧ d.IsModularEigenrow a := by
  constructor
  · intro ha
    exact ⟨d.apply_index_one_eq_one_of_mem_centralCharacterSearch ha,
      d.isModularEigenrow_of_mem_centralCharacterSearch ha⟩
  · rintro ⟨ha_one, ha⟩
    rw [centralCharacterSearch, mem_jointEigenvalueSearch_transpose]
    refine ⟨a, ?_, ha⟩
    intro h
    have := congrFun h (d.index 1)
    simp [ha_one] at this

/-- **The searched rows are exactly the modular central characters.**  Membership in the
executable search is equivalent to being the values on numbered class sums of an algebra
homomorphism from the centre of `F[G]` to `F`.

This statement does not require the good-prime hypothesis. The exact count under a general
splitting hypothesis is `TauCeti.ClassData.card_centralCharacterSearch`; at a good Dixon prime it is
`TauCeti.ClassData.card_centralCharacterSearch_of_isGoodDixonPrime`. -/
theorem mem_centralCharacterSearch_iff_exists_algHom {a : Fin d.numClasses → F} :
    a ∈ d.centralCharacterSearch ↔
      ∃ φ : Subalgebra.center F (MonoidAlgebra F G) →ₐ[F] F,
        ∀ i, φ (classSumCenter (d.classOf i)) = a i := by
  rw [d.mem_centralCharacterSearch]
  constructor
  · rintro ⟨ha_one, ha⟩
    have ha_class : IsClassEigenrow (d.reindexModularRow a) :=
      (d.isModularEigenrow_iff_isClassEigenrow a).mp ha
    have ha_class_one : d.reindexModularRow a (ConjClasses.mk (1 : G)) = 1 := by
      rw [← d.classOf_index (1 : G), d.reindexModularRow_classOf, ha_one]
    obtain ⟨φ, hφ⟩ :=
      (isClassEigenrow_iff_exists_algHom ha_class_one).mp ha_class
    refine ⟨φ, fun i => ?_⟩
    simpa only [classSumRow_apply, reindexModularRow_classOf] using congrFun hφ (d.classOf i)
  · rintro ⟨φ, hφ⟩
    have hrow : d.reindexModularRow a = classSumRow φ := by
      funext C
      obtain ⟨i, rfl⟩ := d.equivConjClasses.surjective C
      simpa only [equivConjClasses_apply, reindexModularRow_classOf, classSumRow_apply]
        using (hφ i).symm
    constructor
    · have h := classSumRow_mk_one φ
      rw [← hrow, ← d.classOf_index (1 : G), d.reindexModularRow_classOf] at h
      exact h
    · rw [d.isModularEigenrow_iff_isClassEigenrow, hrow]
      exact isClassEigenrow_classSumRow φ

end Search

end ClassData

end TauCeti
