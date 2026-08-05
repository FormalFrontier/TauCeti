/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The diagonal torus of the general linear group

`TauCeti.diagGL` embeds a family of units `t : Fin n → kˣ` as the invertible diagonal matrix with
entries `t i`.  This file gathers its image into a subgroup

`TauCeti.diagonalTorus k n = (TauCeti.diagGL : (Fin n → kˣ) →* GL (Fin n) k).range`,

the **diagonal torus** of `GL n k`, and proves what makes it a *maximal* torus.

Three descriptions of the same subgroup are given.  It is the range of `diagGL`, so it is
isomorphic as a group to the coordinatewise units `Fin n → kˣ`
(`TauCeti.diagonalTorusEquiv`).  It is cut out inside `GL n k` by a condition on matrix entries:
an invertible matrix lies in it exactly when it is diagonal (`TauCeti.mem_diagonalTorus_iff`),
the point being that invertibility upgrades the diagonal entries of a diagonal matrix to units
(`TauCeti.isUnit_apply_of_isDiag`, from `ClassicalGroups/Diagonal.lean`).  And it is its own
centralizer
(`TauCeti.centralizer_diagonalTorus`), so it is a maximal abelian subgroup: no larger subgroup of
`GL n k` contains it and is commutative.

Self-centralization needs two hypotheses, both genuine.  The ring must have no zero divisors: an
off-diagonal entry `g i j` of a centralizing matrix satisfies `g i j * (t i - t j) = 0` for
diagonal entries `t i ≠ t j`, and it vanishes because the second factor is nonzero — not because
that factor is invertible, which it need not be (`TauCeti.apply_eq_zero_of_commute_diagonal`).
And the unit group must have two distinct elements, since a diagonal matrix can only separate the
coordinate lines it distinguishes; two units already suffice, because only one pair of
coordinates is separated at a time.  That hypothesis cannot be dropped: over a ring with only one
unit, such as `𝔽₂`, the torus is trivial (`TauCeti.diagonalTorus_eq_bot`) while its centralizer
is the whole of `GL n k` (`TauCeti.centralizer_diagonalTorus_eq_top`).

Finally the action of the torus on the coordinate lines `k ∙ eᵢ` of the standard representation
is recorded: each `eᵢ` is an eigenvector of every torus element, with eigenvalue the `i`-th
diagonal entry (`TauCeti.stdRep_apply_basisFun_of_mem_diagonalTorus`), so each line is stable
(`TauCeti.map_stdRep_span_basisFun`).  Over a general `k` these lines are not yet the *weight
spaces* of the torus: that identification needs the coordinate characters to be pairwise
distinct, and it fails outright when the torus is trivial, as it is over `𝔽₂`.

## Main definitions

* `TauCeti.diagonalTorus`: the subgroup of invertible diagonal matrices in `GL n k`.
* `TauCeti.diagonalTorusEquiv`: the identification `(Fin n → kˣ) ≃* diagonalTorus k n`.

## Main statements

* `TauCeti.mem_diagonalTorus_iff`: membership in the torus is diagonality of the matrix.
* `TauCeti.centralizer_diagonalTorus`: the diagonal torus is its own centralizer.
* `TauCeti.centralizer_diagonalTorus_eq_top`: the sharpness of the hypothesis there.
* `TauCeti.map_stdRep_span_basisFun`: the coordinate lines of the standard representation are
  stable under the diagonal torus.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {n : ℕ}

/-- The **diagonal torus** of `GL n k`: the image of the coordinatewise units under `diagGL`. -/
def diagonalTorus (k : Type u) [CommRing k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  MonoidHom.range (diagGL (k := k) (n := n))

/-- A family of units gives an element of the diagonal torus.  This is not a `simp` lemma:
`mem_diagonalTorus_iff` already reduces the membership to `Matrix.isDiag_diagonal`. -/
theorem diagGL_mem_diagonalTorus (t : Fin n → kˣ) : diagGL t ∈ diagonalTorus k n :=
  ⟨t, rfl⟩

/-- Every element of the diagonal torus comes from a family of units. -/
theorem exists_diagGL_eq {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) :
    ∃ t : Fin n → kˣ, diagGL t = g :=
  hg

/-- An invertible matrix lies in the diagonal torus exactly when it is a diagonal matrix. -/
@[simp]
theorem mem_diagonalTorus_iff {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ (g : Matrix (Fin n) (Fin n) k).IsDiag := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · intro hg
    refine ⟨fun i => (isUnit_apply_of_isDiag hg i).unit, Units.ext ?_⟩
    rw [diagGL_coe]
    simp only [IsUnit.unit_spec]
    exact hg.diagonal_diag

/-- The matrix of an element of the diagonal torus is diagonal. -/
theorem isDiag_of_mem_diagonalTorus {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) :
    (g : Matrix (Fin n) (Fin n) k).IsDiag :=
  mem_diagonalTorus_iff.mp hg

/-- Off-diagonal entries of an element of the diagonal torus vanish. -/
theorem apply_eq_zero_of_mem_diagonalTorus {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n)
    {i j : Fin n} (hij : i ≠ j) : (g : Matrix (Fin n) (Fin n) k) i j = 0 :=
  isDiag_of_mem_diagonalTorus hg hij

/-- The diagonal torus is the group of coordinatewise units. -/
noncomputable def diagonalTorusEquiv (k : Type u) [CommRing k] (n : ℕ) :
    (Fin n → kˣ) ≃* diagonalTorus k n :=
  MonoidHom.ofInjective diagGL_injective

/-- Reading the diagonal entries of a torus element and embedding them back is the identity. -/
@[simp]
theorem diagGL_diagonalTorusEquiv_symm_apply (g : diagonalTorus k n) :
    diagGL ((diagonalTorusEquiv k n).symm g) = (g : GL (Fin n) k) :=
  congrArg Subtype.val ((diagonalTorusEquiv k n).apply_symm_apply g)

/-- The identification of the torus with the coordinatewise units is `diagGL`. -/
@[simp]
theorem coe_diagonalTorusEquiv_apply (t : Fin n → kˣ) :
    (diagonalTorusEquiv k n t : GL (Fin n) k) = diagGL t := by
  have h := diagGL_diagonalTorusEquiv_symm_apply (diagonalTorusEquiv k n t)
  rw [MulEquiv.symm_apply_apply] at h
  exact h.symm

/-- The `i`-th coordinate character of a torus element is its `(i, i)` matrix entry. -/
@[simp]
theorem coe_diagonalTorusEquiv_symm_apply (g : diagonalTorus k n) (i : Fin n) :
    (((diagonalTorusEquiv k n).symm g i : kˣ) : k) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i := by
  conv_rhs => rw [← diagGL_diagonalTorusEquiv_symm_apply g, diagGL_coe]
  rw [Matrix.diagonal_apply_eq]

/-- The diagonal torus is commutative: diagonal matrices multiply coordinatewise. -/
instance instIsMulCommutativeDiagonalTorus : IsMulCommutative (diagonalTorus k n) :=
  ⟨⟨by
    rintro ⟨-, t, rfl⟩ ⟨-, s, rfl⟩
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm]⟩⟩

/-- The determinant of an element of the diagonal torus is the product of its diagonal entries. -/
theorem det_of_mem_diagonalTorus {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) :
    (Matrix.GeneralLinearGroup.det g : k) = ∏ i, (g : Matrix (Fin n) (Fin n) k) i i := by
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    ← (isDiag_of_mem_diagonalTorus hg).diagonal_diag, Matrix.det_diagonal]
  simp [Matrix.diag]

/-- An element centralizing the diagonal torus commutes, as a matrix, with every diagonal matrix
of units. -/
theorem commute_diagonal_of_mem_centralizer {g : GL (Fin n) k}
    (hg : g ∈ Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k))) (t : Fin n → kˣ) :
    Commute (Matrix.diagonal fun i => (t i : k)) (g : Matrix (Fin n) (Fin n) k) := by
  have hcomm : Commute (diagGL t) g :=
    Subgroup.mem_centralizer_iff.mp hg _ (diagGL_mem_diagonalTorus t)
  have h : ((diagGL t * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((g * diagGL t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := congrArg _ hcomm.eq
  rwa [Units.val_mul, Units.val_mul, diagGL_coe] at h

section NoZeroDivisors

variable [NoZeroDivisors k] [Nontrivial kˣ]

/-- **The diagonal torus is its own centralizer**, hence a maximal abelian subgroup of `GL n k`.
Two distinct units `u ≠ v` are all the argument needs: for `i ≠ j` the family taking the value
`u` at `i` and `v` elsewhere gives a diagonal matrix separating those two coordinates, which
kills the `(i, j)` entry of anything commuting with it. -/
theorem centralizer_diagonalTorus :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = diagonalTorus k n := by
  refine le_antisymm (fun g hg => mem_diagonalTorus_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  obtain ⟨u, v, huv⟩ := exists_pair_ne kˣ
  refine apply_eq_zero_of_commute_diagonal
    (commute_diagonal_of_mem_centralizer hg fun m => if m = i then u else v) ?_
  rw [if_pos rfl, if_neg (Ne.symm hij)]
  exact fun h => huv (Units.ext h)

/-- A commutative subgroup of `GL n k` containing the diagonal torus equals it: this is the
maximality of the torus among abelian subgroups. -/
theorem eq_diagonalTorus_of_le_of_isMulCommutative (H : Subgroup (GL (Fin n) k))
    [IsMulCommutative H] (hle : diagonalTorus k n ≤ H) :
    H = diagonalTorus k n :=
  le_antisymm
    (by
      rw [← centralizer_diagonalTorus (k := k) (n := n)]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

end NoZeroDivisors

section Subsingleton

variable [Subsingleton kˣ]

/-- Over a ring with only one unit, such as `𝔽₂`, the diagonal torus is trivial. -/
theorem diagonalTorus_eq_bot : diagonalTorus k n = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro - ⟨t, rfl⟩
  rw [Subgroup.mem_bot, Subsingleton.elim t 1, map_one]

/-- Over a ring with only one unit the centralizer of the diagonal torus is the whole group, so
the hypothesis `Nontrivial kˣ` of `TauCeti.centralizer_diagonalTorus` cannot be dropped: there
the torus is trivial by `TauCeti.diagonalTorus_eq_bot`, while its centralizer is all of
`GL n k`. -/
theorem centralizer_diagonalTorus_eq_top :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  rw [diagonalTorus_eq_bot, SetLike.mem_coe, Subgroup.mem_bot] at hh
  rw [hh, one_mul, mul_one]

end Subsingleton

section StandardRepresentation

/-- Every standard basis vector is an eigenvector of every element of the diagonal torus, with
eigenvalue the corresponding diagonal entry.  The eigenvalue is the `i`-th coordinate character
of the torus, read off `diagGL` through `TauCeti.diagonalTorusEquiv`. -/
theorem stdRep_apply_basisFun_of_mem_diagonalTorus {g : GL (Fin n) k}
    (hg : g ∈ diagonalTorus k n) (i : Fin n) :
    stdRep k n g (Pi.basisFun k (Fin n) i) =
      (g : Matrix (Fin n) (Fin n) k) i i • Pi.basisFun k (Fin n) i := by
  obtain ⟨t, rfl⟩ := exists_diagGL_eq hg
  rw [stdRep_diagGL_apply_basisFun, diagGL_coe, Matrix.diagonal_apply_eq]

/-- Each coordinate line of the standard representation is stable under the diagonal torus, a
torus element acting on it by the invertible scalar given by its `i`-th diagonal entry. -/
theorem map_stdRep_span_basisFun {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) (i : Fin n) :
    Submodule.map (stdRep k n g) (Submodule.span k {Pi.basisFun k (Fin n) i}) =
      Submodule.span k {Pi.basisFun k (Fin n) i} := by
  rw [Submodule.map_span, Set.image_singleton, stdRep_apply_basisFun_of_mem_diagonalTorus hg i]
  exact Submodule.span_singleton_smul_eq (isUnit_apply_of_isDiag
    (isDiag_of_mem_diagonalTorus hg) i) _

end StandardRepresentation

end TauCeti
