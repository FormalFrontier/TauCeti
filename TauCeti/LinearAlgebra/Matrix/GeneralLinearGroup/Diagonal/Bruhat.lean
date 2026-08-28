/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The Bruhat Weyl element and the Borel subgroup are compared with the diagonal normalizer below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
-- The monomial description of the diagonal normalizer supplies its permutation quotient.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# The diagonal normalizer and the Bruhat data of `GL₂`

This file aligns upper-triangular Bruhat data with the diagonal normalizer. For `GLₙ`, an
upper-triangular monomial matrix is diagonal, and hence

`Bₙ ⊓ N(Tₙ) = Tₙ`.

Specializing to `GL₂`, the Weyl element used in the Bruhat decomposition is the permutation
matrix of the transposition, so it lies in `N(T)` and induces the nontrivial element of its
permutation quotient. In particular,

`B ⊓ N(T) = T`,

where `B` is the standard Borel subgroup. This is the kernel identification in the
rank-one `(B, N)`-pair: the already-established quotient `N(T) / T ≃ S₂` can equivalently be
written with `B ⊓ N(T)` as its denominator.

The assumption `Nontrivial kˣ` in the intersection theorems is necessary for the full
group-theoretic normalizer. For example, over `𝔽₂` the diagonal torus of `GL₂` is trivial, so
its normalizer is all of `GL₂` and the displayed rank-one intersection would instead be `B`.

## Main results

* `TauCeti.gl2WeylElement_eq_permutationGL_swap`: the Bruhat Weyl element is the permutation
  matrix of the transposition.
* `TauCeti.gl2WeylElement_mem_normalizer_diagonalTorus`: the Weyl element normalizes the diagonal
  torus.
* `TauCeti.diagonalNormalizerPerm_gl2WeylElement`: the Weyl element induces the transposition on
  the coordinate lines.
* `TauCeti.UpperTriangularGroup.inf_normalizer_diagonalTorus_eq`: in every dimension, the
  intersection of the upper-triangular subgroup with the diagonal normalizer is the diagonal
  torus.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 26.2–26.3 and 28.1.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Sections 8.3–8.4.

This advances Layer 7, "Bruhat decomposition and BN-pairs / Tits systems", of the
ReductiveGroups roadmap by identifying the intersection subgroup, including in the rank-one
`GL₂` example.
-/

public section

open Matrix

namespace TauCeti

universe u

noncomputable section

section WeylElement

variable (R : Type u) [Semiring R]

/-- The Weyl element in the Bruhat decomposition of `GL₂` is the permutation matrix of the
transposition of the two coordinate lines. -/
theorem gl2WeylElement_eq_permutationGL_swap :
    GL2WeylElement R = permutationGL (k := R) (Equiv.swap 0 1) := by
  apply Units.ext
  rw [permutationGL_coe, coe_gl2WeylElement]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Equiv.Perm.permMatrix]

/-- The Bruhat Weyl element normalizes the diagonal torus. -/
theorem gl2WeylElement_mem_normalizer_diagonalTorus :
    GL2WeylElement R ∈
      Subgroup.normalizer (diagonalTorus R 2 : Set (GL (Fin 2) R)) := by
  rw [gl2WeylElement_eq_permutationGL_swap]
  exact permutationGL_mem_normalizer (Equiv.swap 0 1)

end WeylElement

section Field

variable {k : Type u} [Field k]

variable [Nontrivial kˣ]

/-- The coordinate permutation induced by the Bruhat Weyl element is the transposition. -/
theorem diagonalNormalizerPerm_gl2WeylElement :
    diagonalNormalizerPerm (k := k) (n := 2)
        ⟨GL2WeylElement k,
          gl2WeylElement_mem_normalizer_diagonalTorus (R := k)⟩ =
      Equiv.swap 0 1 := by
  simpa only [gl2WeylElement_eq_permutationGL_swap] using
    diagonalNormalizerPerm_permutationGL (k := k) (n := 2) (Equiv.swap 0 1)

end Field

section UpperTriangular

section CommRing

variable {R : Type u} [CommRing R] {n : ℕ}

namespace UpperTriangularGroup

/-- Every diagonal matrix is upper triangular, so the diagonal torus lies in the standard
upper-triangular subgroup. -/
theorem diagonalTorus_le :
    diagonalTorus R n ≤ upperTriangularGroup (Fin n) R := by
  intro g hg
  obtain ⟨d, rfl⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
  rw [mem_iff]
  intro i j hji
  rw [diagGL_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)

end UpperTriangularGroup

end CommRing

section Field

variable {k : Type u} [Field k] [Nontrivial kˣ] {n : ℕ}

namespace UpperTriangularGroup

/-- A diagonal-normalizer element that is upper triangular is diagonal. Equivalently, an
upper-triangular monomial matrix cannot carry a nontrivial coordinate permutation. -/
theorem mem_diagonalTorus_of_mem
    (g : Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)))
    (hg : (g : GL (Fin n) k) ∈ upperTriangularGroup (Fin n) k) :
    (g : GL (Fin n) k) ∈ diagonalTorus k n := by
  obtain ⟨d, σ, hfactor⟩ := mem_normalizer_diagonalTorus_iff_exists.mp g.property
  have hupper := mem_iff.mp hg
  have hle (ι : Fin n) : σ ι ≤ ι := by
    by_contra h
    have hzero := hupper (lt_of_not_ge h)
    have hentry := congrArg
      (fun x : GL (Fin n) k ↦ (x : Matrix (Fin n) (Fin n) k) (σ ι) ι) hfactor
    rw [hzero] at hentry
    simp only [Units.val_mul, diagGL_coe, permutationGL_coe, Matrix.diagonal_mul] at hentry
    have hperm : (σ⁻¹.permMatrix k) (σ ι) ι = 1 := by
      simp [Equiv.Perm.permMatrix]
    rw [hperm, mul_one] at hentry
    exact Units.ne_zero (d (σ ι)) hentry.symm
  have hσ : σ = 1 := by
    by_contra hne
    have hstrict : ∃ ι ∈ Finset.univ, (σ ι).val < ι.val := by
      have hnot : ¬ ∀ ι, σ ι = ι := by
        intro h
        apply hne
        apply Equiv.ext
        intro ι
        simpa using h ι
      obtain ⟨ι, hι⟩ := not_forall.mp hnot
      exact ⟨ι, Finset.mem_univ _,
        lt_of_le_of_ne (hle ι) fun hval ↦ hι (Fin.ext hval)⟩
    have hsum : (∑ ι : Fin n, (σ ι).val) = ∑ ι : Fin n, ι.val :=
      Equiv.sum_comp σ fun ι : Fin n ↦ ι.val
    have hsumlt : (∑ ι : Fin n, (σ ι).val) < ∑ ι : Fin n, ι.val :=
      Finset.sum_lt_sum (fun ι _ ↦ hle ι) hstrict
    exact hsumlt.ne hsum
  rw [hσ, map_one, mul_one] at hfactor
  exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨d, hfactor.symm⟩

/-- Over a field with at least two units, the intersection of the upper-triangular subgroup of
`GLₙ` with the normalizer of the diagonal torus is exactly the diagonal torus. -/
theorem inf_normalizer_diagonalTorus_eq :
    upperTriangularGroup (Fin n) k ⊓
        Subgroup.normalizer (diagonalTorus k n : Set (GL (Fin n) k)) =
      diagonalTorus k n := by
  apply le_antisymm
  · intro g hg
    exact mem_diagonalTorus_of_mem ⟨g, hg.2⟩ hg.1
  · intro g hg
    exact ⟨diagonalTorus_le hg, Subgroup.le_normalizer hg⟩

end UpperTriangularGroup

end Field

end UpperTriangular

end

end TauCeti
