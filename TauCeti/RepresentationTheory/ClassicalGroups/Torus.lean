/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal
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

Self-centralization is proved under two hypotheses, neither of them idle.  The absence of zero
divisors is a sufficient hypothesis rather than a necessary one: an off-diagonal entry `g i j` of
a centralizing matrix satisfies `g i j * (t i - t j) = 0` for diagonal entries `t i ≠ t j`, and
`NoZeroDivisors k` is what cancels the second factor — not invertibility of that factor, which it
need not have (`TauCeti.apply_eq_zero_of_commute_diagonal`).  All the argument asks of the ring is
that the two units it separates the coordinates with differ by a regular element.  The second
hypothesis, that the unit group has two distinct elements, is there because a diagonal matrix can
only separate the coordinate lines it distinguishes; two units already suffice, because only one
pair of coordinates is separated at a time.  That one cannot simply be dropped, and what happens
without it is recorded here: over a ring with only one unit, such as `𝔽₂`, the torus is trivial
(`TauCeti.diagonalTorus_eq_bot`) while its centralizer is the whole of `GL n k`
(`TauCeti.centralizer_diagonalTorus_eq_top`).  These two subgroups differ, so self-centralization
genuinely fails, exactly when `GL n k` is itself nontrivial — over `𝔽₂` that is the case for
`n ≥ 2`, while for `n ≤ 1` the whole group is trivial and the conclusion survives for want of
anything to contradict it.

Finally the action of the torus on the coordinate lines `k ∙ eᵢ` of the standard representation
is recorded: every torus element scales `eᵢ` by its `i`-th diagonal entry
(`TauCeti.stdRep_apply_basisFun_of_mem_diagonalTorus`), so each line is stable
(`TauCeti.map_stdRep_span_basisFun`).  Over a general `k` these lines are not yet the *weight
spaces* of the torus: that identification needs the coordinate characters to be pairwise
distinct, and it fails outright when the torus is trivial, as it is over `𝔽₂`.

## Main definitions

* `TauCeti.diagonalTorus`: the subgroup of invertible diagonal matrices in `GL n k`.
* `TauCeti.diagonalTorusEquiv`: the identification `(Fin n → kˣ) ≃* diagonalTorus k n`.

## Main statements

* `TauCeti.mem_diagonalTorus_iff`: membership in the torus is diagonality of the matrix.
* `TauCeti.centralizer_diagonalTorus`: the diagonal torus is its own centralizer.
* `TauCeti.centralizer_diagonalTorus_eq_top`: over a ring with a single unit the centralizer is
  instead the whole group.
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

/-- The diagonal torus is the group of coordinatewise units. -/
noncomputable def diagonalTorusEquiv (k : Type u) [CommRing k] (n : ℕ) :
    (Fin n → kˣ) ≃* diagonalTorus k n :=
  MonoidHom.ofInjective diagGL_injective

/-- The torus element attached to a family of units is `diagGL t`. -/
@[simp]
theorem coe_diagonalTorusEquiv_apply (t : Fin n → kˣ) :
    ((diagonalTorusEquiv k n t : diagonalTorus k n) : GL (Fin n) k) = diagGL t :=
  MonoidHom.ofInjective_apply diagGL_injective

/-- The `i`-th coordinate character of a torus element is its `(i, i)` matrix entry. -/
@[simp]
theorem coe_diagonalTorusEquiv_symm_apply (g : diagonalTorus k n) (i : Fin n) :
    (((diagonalTorusEquiv k n).symm g i : kˣ) : k) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i := by
  have h : diagGL ((diagonalTorusEquiv k n).symm g) = (g : GL (Fin n) k) :=
    MonoidHom.apply_ofInjective_symm diagGL_injective g
  conv_rhs => rw [← h, diagGL_coe]
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
    Subgroup.mem_centralizer_iff.mp hg _ (MonoidHom.mem_range.mpr ⟨t, rfl⟩)
  have h : ((diagGL t * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((g * diagGL t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := congrArg _ hcomm.eq
  rwa [Units.val_mul, Units.val_mul, diagGL_coe] at h

section NoZeroDivisors

variable [NoZeroDivisors k] [Nontrivial kˣ]

/-- **The diagonal torus is its own centralizer**, hence a maximal abelian subgroup of `GL n k`. -/
theorem centralizer_diagonalTorus :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = diagonalTorus k n := by
  refine le_antisymm (fun g hg => mem_diagonalTorus_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  obtain ⟨u, v, huv⟩ := exists_pair_ne kˣ
  refine apply_eq_zero_of_commute_diagonal
    (commute_diagonal_of_mem_centralizer hg fun m => if m = i then u else v) ?_
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hij)]
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

/-- Over a ring with only one unit the centralizer of the diagonal torus is the whole group,
while the torus itself is trivial by `TauCeti.diagonalTorus_eq_bot`.  So the hypothesis
`Nontrivial kˣ` of `TauCeti.centralizer_diagonalTorus` cannot simply be dropped: the two
subgroups differ as soon as `GL n k` is nontrivial, as it is over `𝔽₂` for `n ≥ 2`.  For `n ≤ 1`
the group is trivial and the present theorem says nothing more than `⊤ = ⊥`. -/
theorem centralizer_diagonalTorus_eq_top :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = ⊤ := by
  refine eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  rw [diagonalTorus_eq_bot, SetLike.mem_coe, Subgroup.mem_bot] at hh
  rw [hh, one_mul, mul_one]

end Subsingleton

section StandardRepresentation

/-- An element of the diagonal torus scales the standard basis vector `eᵢ` by its `(i, i)` matrix
entry, the `i`-th coordinate character of the torus read off `diagGL` through
`TauCeti.diagonalTorusEquiv`.  This is an eigen-relation rather than an eigenvector statement:
over the zero ring `eᵢ` itself vanishes. -/
theorem stdRep_apply_basisFun_of_mem_diagonalTorus {g : GL (Fin n) k}
    (hg : g ∈ diagonalTorus k n) (i : Fin n) :
    stdRep k n g (Pi.basisFun k (Fin n) i) =
      (g : Matrix (Fin n) (Fin n) k) i i • Pi.basisFun k (Fin n) i := by
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hg
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
