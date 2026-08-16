/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Matrix.scalar` and the `2 × 2` matrix notation occur in the statements below, and
-- `TauCeti.mem_range_scalar_fin_two_iff` is how "non-scalar" is read off the entries.
public import TauCeti.LinearAlgebra.Matrix.Commute
-- `Matrix.det` occurs in the statements below, and `Matrix.det_fin_two_of` in the proofs.
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- `Matrix.trace` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Trace
-- Non-public: the entry identities below are polynomial, and are solved by `ring` and
-- `linear_combination` in the proofs only.
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rational canonical form in size two

A `2 × 2` matrix over a field is scalar or **cyclic**: as soon as it is not scalar some vector `v`
is not an eigenvector, and `v, M *ᵥ v` is then a basis in which `M` becomes the companion matrix
`!![0, -det M; 1, trace M]` of its characteristic polynomial `X² - (trace M) X + det M`. That is
the rational canonical form in size two, proved here at the level of matrices; the conjugacy
classification of `GL₂(F)` it yields is in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses`.

The second column of the conjugating equation is the Cayley-Hamilton identity
`M² = (trace M) • M - (det M) • 1` in disguise. In size two that identity is a four-entry
polynomial identity in the entries, so it is discharged by `ring` here rather than by invoking the
general theory.

Being scalar is spelled `M ∈ Set.range (Matrix.scalar (Fin 2))`, as in
`TauCeti.LinearAlgebra.Matrix.Commute`, and unfolded by
`TauCeti.mem_range_scalar_fin_two_iff`; that file's commutant computation is the companion result,
describing the centralizer of a non-scalar matrix rather than its normal form.

## Main definitions

* `TauCeti.companionFinTwo`: the companion matrix `!![0, -d; 1, t]` of `X² - t X + d`.

## Main results

* `TauCeti.exists_forall_mulVec_ne_smul`: a non-scalar `2 × 2` matrix has a cyclic vector.
* `TauCeti.exists_det_ne_zero_mul_eq_mul_companionFinTwo`: **rational canonical form in size two**,
  a non-scalar `2 × 2` matrix over a field is similar to the companion matrix of its characteristic
  polynomial.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The conjugacy classes (a build target)", which asks for the rational-canonical-form
  classification Mathlib does not have.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

open Matrix

namespace TauCeti

/-! ### The companion matrix of a monic quadratic -/

section CommRing

variable {R : Type*} [CommRing R] (t d : R)

/-- **The companion matrix** `!![0, -d; 1, t]` of the monic quadratic `X² - t X + d`: the matrix of
multiplication by `X` on `R[X] ⧸ (X² - t X + d)` in the basis `1, X`. Its trace is `t` and its
determinant is `d`, so it is the normal form that the classification of `2 × 2` matrices runs
on. -/
def companionFinTwo : Matrix (Fin 2) (Fin 2) R := !![0, -d; 1, t]

@[simp]
theorem det_companionFinTwo : (companionFinTwo t d).det = d := by
  simp [companionFinTwo, Matrix.det_fin_two_of]

@[simp]
theorem trace_companionFinTwo : (companionFinTwo t d).trace = t := by
  simp [companionFinTwo, Matrix.trace_fin_two_of]

/-- **A companion matrix is never scalar**: its lower-left entry is `1`. -/
theorem companionFinTwo_notMem_range_scalar [Nontrivial R] :
    companionFinTwo t d ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rw [mem_range_scalar_fin_two_iff]
  rintro ⟨-, h10, -⟩
  simp [companionFinTwo] at h10

end CommRing

/-! ### Rational canonical form in size two -/

section Field

variable {F : Type*} [Field F] {M : Matrix (Fin 2) (Fin 2) F}

/-- Two vectors of `F²` spanning a degenerate parallelogram are proportional, provided the first is
nonzero. This is the linear independence of `v` and `M *ᵥ v` below, in the form in which the
`2 × 2` determinant supplies it. -/
private theorem exists_eq_smul_of_det_fin_two_eq_zero {v u : Fin 2 → F} (hv : v ≠ 0)
    (hdet : v 0 * u 1 - u 0 * v 1 = 0) : ∃ c : F, u = c • v := by
  have hor : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext (Fin.forall_fin_two.2 ⟨hcon.1, hcon.2⟩))
  rcases hor with h0 | h1
  · refine ⟨u 0 / v 0, funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩ <;>
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h0]
    linear_combination hdet
  · refine ⟨u 1 / v 1, funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩ <;>
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h1]
    linear_combination -hdet

/-- **A non-scalar `2 × 2` matrix has a cyclic vector**: some vector is not an eigenvector. If
every vector were an eigenvector then the two standard basis vectors and their sum would force the
off-diagonal entries to vanish and the two diagonal entries to agree. -/
theorem exists_forall_mulVec_ne_smul (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ v : Fin 2 → F, ∀ c : F, M *ᵥ v ≠ c • v := by
  by_contra hcon
  push Not at hcon
  have key : ∀ v0 v1 c : F, M *ᵥ ![v0, v1] = c • ![v0, v1] →
      M 0 0 * v0 + M 0 1 * v1 = c * v0 ∧ M 1 0 * v0 + M 1 1 * v1 = c * v1 := by
    refine fun v0 v1 c hv => ⟨?_, ?_⟩
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
  obtain ⟨a, ha⟩ := hcon ![1, 0]
  obtain ⟨b, hb⟩ := hcon ![0, 1]
  obtain ⟨c, hc⟩ := hcon ![1, 1]
  obtain ⟨-, ha1⟩ := key 1 0 a ha
  obtain ⟨hb0, -⟩ := key 0 1 b hb
  obtain ⟨hc0, hc1⟩ := key 1 1 c hc
  exact hM (mem_range_scalar_fin_two_iff.2
    ⟨by linear_combination hb0, by linear_combination ha1,
      by linear_combination hc0 - hc1 - hb0 + ha1⟩)

/-- **Rational canonical form in size two.** A non-scalar `2 × 2` matrix `M` over a field is
similar to the companion matrix of its characteristic polynomial `X² - (trace M) X + det M`: in the
basis `v, M *ᵥ v` supplied by a cyclic vector `v` it *is* that companion matrix, the second column
of the identity being Cayley-Hamilton.

The conjugating matrix is produced together with its determinant rather than as an element of
`GL₂`, so that the statement also covers a matrix that is not itself invertible;
`TauCeti.isConj_companionGL` is the group-level form. -/
theorem exists_det_ne_zero_mul_eq_mul_companionFinTwo
    (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ P : Matrix (Fin 2) (Fin 2) F,
      P.det ≠ 0 ∧ M * P = P * companionFinTwo M.trace M.det := by
  obtain ⟨v, hv⟩ := exists_forall_mulVec_ne_smul hM
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv 0 (by simp)
  refine ⟨!![v 0, (M *ᵥ v) 0; v 1, (M *ᵥ v) 1], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    intro hdet
    obtain ⟨c, hc⟩ := exists_eq_smul_of_det_fin_two_eq_zero (u := M *ᵥ v) hv0 hdet
    exact hv c hc
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [companionFinTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec,
        dotProduct, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

end Field

end TauCeti
