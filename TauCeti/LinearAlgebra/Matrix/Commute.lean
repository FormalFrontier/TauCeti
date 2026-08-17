/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.scalar` occurs in the statements below, and the `2 × 2` entry lemma `Fin.sum_univ_two`
-- in the proofs.
public import Mathlib.LinearAlgebra.Matrix.Notation
-- Non-public: the entry equations are solved by `linear_combination` and `ring`, in the proofs
-- only.
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The commutant of a `2 × 2` matrix

A `2 × 2` matrix over a field is **regular** as soon as it is not scalar: it is then cyclic
(nonderogatory), and the matrices commuting with it are exactly the polynomials in it. In size `2`
those polynomials are the affine combinations `a • 1 + b • M`, so the commutant of a non-scalar
`M : Matrix (Fin 2) (Fin 2) F` is the two-dimensional algebra `F[M]` — in particular it is
commutative.

Mathlib's `Matrix.mem_range_scalar_iff_commute_transvectionStruct` describes the matrices commuting
with *everything*; what is proved here is the commutant of a *single* matrix, in size two, read off
the three independent entry equations of `M * N = N * M` by splitting on which of the two
off-diagonal entries or the diagonal difference is nonzero.

Being scalar is recorded over a semiring; only the commutant computation itself, which divides by a
matrix entry, needs a field.

## Main results

* `TauCeti.mem_range_scalar_fin_two_iff`: a `2 × 2` matrix is scalar exactly when its off-diagonal
  entries vanish and its two diagonal entries agree.
* `TauCeti.commute_fin_two_iff`: a matrix commutes with a non-scalar `2 × 2` matrix `M` exactly when
  it is of the form `a • 1 + b • M`.
* `TauCeti.commute_of_commute_fin_two`: two matrices commuting with a common non-scalar `2 × 2`
  matrix commute with each other.

## References

The commutant is used to compute centralizers in `GL₂` in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer`, for the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
Layer 9, "The conjugacy classes (a build target)".
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} {M N P : Matrix (Fin 2) (Fin 2) F}

section Semiring

variable [Semiring F]

/-- A `2 × 2` matrix is scalar exactly when its off-diagonal entries vanish and its two diagonal
entries agree. -/
theorem mem_range_scalar_fin_two_iff :
    M ∈ Set.range (Matrix.scalar (Fin 2)) ↔ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [Matrix.scalar_apply]
  · rintro ⟨h01, h10, h00⟩
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h00]

/-- A `2 × 2` matrix is `a • 1 + b • M` as soon as its four entries are. -/
private theorem eq_scalar_add_smul_fin_two {a b : F} (h00 : N 0 0 = a + b * M 0 0)
    (h01 : N 0 1 = b * M 0 1) (h10 : N 1 0 = b * M 1 0) (h11 : N 1 1 = a + b * M 1 1) :
    N = Matrix.scalar (Fin 2) a + b • M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h00, h01, h10, h11]

end Semiring

section Field

variable [Field F]

/-- **The commutant of a non-scalar `2 × 2` matrix.** A matrix commutes with a non-scalar
`M : Matrix (Fin 2) (Fin 2) F` exactly when it lies in the two-dimensional subalgebra spanned by
`1` and `M`; equivalently, a non-scalar `2 × 2` matrix is cyclic, so its commutant is `F[M]`.

The hypothesis is necessary: everything commutes with a scalar matrix. -/
theorem commute_fin_two_iff (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) :
    Commute M N ↔ ∃ a b : F, N = Matrix.scalar (Fin 2) a + b • M := by
  constructor
  · intro h
    -- The entry equations of `M * N = N * M`; only three of the four are used.
    have key : ∀ i j : Fin 2,
        M i 0 * N 0 j + M i 1 * N 1 j = N i 0 * M 0 j + N i 1 * M 1 j := fun i j => by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h.eq i) j
    have e00 := key 0 0
    have e01 := key 0 1
    have e10 := key 1 0
    -- Being non-scalar, `M` has a nonzero off-diagonal entry or distinct diagonal entries.
    rw [mem_range_scalar_fin_two_iff] at hM
    push Not at hM
    by_cases h01 : M 0 1 = 0
    · by_cases h10 : M 1 0 = 0
      · -- `M` is diagonal with distinct entries: everything commuting with it is diagonal.
        have hdiag : M 0 0 - M 1 1 ≠ 0 := sub_ne_zero.mpr (hM h01 h10)
        obtain ⟨b, hb⟩ : ∃ b : F, b * (M 0 0 - M 1 1) = N 0 0 - N 1 1 :=
          ⟨(N 0 0 - N 1 1) / (M 0 0 - M 1 1), div_mul_cancel₀ _ hdiag⟩
        have hN01 : N 0 1 = 0 :=
          mul_right_cancel₀ hdiag (by linear_combination e01 + (N 0 0 - N 1 1) * h01)
        have hN10 : N 1 0 = 0 :=
          mul_right_cancel₀ hdiag (by linear_combination -e10 + (N 0 0 - N 1 1) * h10)
        exact ⟨N 0 0 - b * M 0 0, b, eq_scalar_add_smul_fin_two (by ring)
          (by rw [hN01, h01, mul_zero]) (by rw [hN10, h10, mul_zero])
          (by linear_combination hb)⟩
      · -- The lower-left entry is nonzero and determines the coefficient of `M`.
        obtain ⟨b, hb⟩ : ∃ b : F, b * M 1 0 = N 1 0 := ⟨N 1 0 / M 1 0, div_mul_cancel₀ _ h10⟩
        exact ⟨N 0 0 - b * M 0 0, b, eq_scalar_add_smul_fin_two (by ring)
          (mul_left_cancel₀ h10 (by linear_combination -e00 - M 0 1 * hb)) hb.symm
          (mul_left_cancel₀ h10 (by linear_combination -e10 + (M 0 0 - M 1 1) * hb))⟩
    · -- The upper-right entry is nonzero and determines the coefficient of `M`.
      obtain ⟨b, hb⟩ : ∃ b : F, b * M 0 1 = N 0 1 := ⟨N 0 1 / M 0 1, div_mul_cancel₀ _ h01⟩
      exact ⟨N 0 0 - b * M 0 0, b, eq_scalar_add_smul_fin_two (by ring) hb.symm
        (mul_left_cancel₀ h01 (by linear_combination e00 - M 1 0 * hb))
        (mul_left_cancel₀ h01 (by linear_combination e01 + (M 0 0 - M 1 1) * hb))⟩
  · rintro ⟨a, b, rfl⟩
    exact ((Matrix.scalar_commute a (Commute.all a) M).symm).add_right
      ((Commute.refl M).smul_right b)

/-- Two matrices commuting with a common non-scalar `2 × 2` matrix commute with each other: both
lie in the commutative algebra `F[M]`. -/
theorem commute_of_commute_fin_two (hM : M ∉ Set.range (Matrix.scalar (Fin 2)))
    (hN : Commute M N) (hP : Commute M P) : Commute N P := by
  obtain ⟨a, b, rfl⟩ := (commute_fin_two_iff hM).mp hN
  obtain ⟨c, d, rfl⟩ := (commute_fin_two_iff hM).mp hP
  have hs : ∀ x : F, Commute (Matrix.scalar (Fin 2) x) M :=
    fun x => Matrix.scalar_commute x (Commute.all x) M
  have h1 : Commute (Matrix.scalar (Fin 2) a) (Matrix.scalar (Fin 2) c) :=
    Matrix.scalar_commute a (Commute.all a) _
  have h2 : Commute (Matrix.scalar (Fin 2) a) (d • M) := (hs a).smul_right d
  have h3 : Commute (b • M) (Matrix.scalar (Fin 2) c) := (hs c).symm.smul_left b
  have h4 : Commute (b • M) (d • M) := ((Commute.refl M).smul_right d).smul_left b
  exact (h1.add_right h2).add_left (h3.add_right h4)

end Field

end TauCeti
