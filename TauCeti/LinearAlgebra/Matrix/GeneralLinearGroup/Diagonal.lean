/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `GL` and `Matrix.GeneralLinearGroup.det` occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `MulEquiv.piUnits` identifies the units of a product with the product of the units, and is what
-- makes the diagonal embedding a homomorphism.
public import Mathlib.Algebra.Group.Pi.Units
-- `Matrix.IsDiag` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.IsDiag
-- `Subgroup.centralizer` occurs in the statements below.
public import Mathlib.GroupTheory.Subgroup.Centralizer
-- `Nat.card` occurs in the statement of `TauCeti.natCard_diagonalTorus`.
public import Mathlib.SetTheory.Cardinal.Finite
-- Non-public: `Nat.card_units`, the number of units of a `GroupWithZero`, is used only inside the
-- proof of `TauCeti.natCard_diagonalTorus`, so downstream importers do not pay for it.
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Diagonal elements of the general linear group, and the diagonal torus

A family of units `t : Fin n → kˣ` is the diagonal of an invertible diagonal matrix, and this
assignment is a group homomorphism `TauCeti.diagGL : (Fin n → kˣ) →* GL (Fin n) k`. Its entries,
its determinant and its injectivity are recorded here, together with two facts about diagonal
matrices proper: invertibility of a diagonal matrix upgrades its diagonal entries to units, and a
matrix commuting with a diagonal matrix has no entries away from the diagonal wherever that
diagonal matrix separates two coordinates.

The image of `diagGL` is gathered into a subgroup

`TauCeti.diagonalTorus k n = (TauCeti.diagGL : (Fin n → kˣ) →* GL (Fin n) k).range`,

the **diagonal torus** of `GL n k`, and what makes it a *maximal* torus is proved.

Three descriptions of the same subgroup are given.  It is the range of `diagGL`, so it is
isomorphic as a group to the coordinatewise units `Fin n → kˣ`
(`TauCeti.diagonalTorusEquiv`), whence its order `(q - 1)ⁿ` over a division ring with `q` elements
(`TauCeti.natCard_diagonalTorus`).  It is cut out inside `GL n k` by a condition on matrix entries:
an invertible matrix lies in it exactly when it is diagonal (`TauCeti.mem_diagonalTorus_iff`),
the point being that invertibility upgrades the diagonal entries of a diagonal matrix to units
(`TauCeti.isUnit_apply_of_isDiag`).  And it is its own centralizer
(`TauCeti.centralizer_diagonalTorus`), so it is a maximal abelian subgroup: no larger subgroup of
`GL n k` contains it and is commutative.

The embedding, the torus, the equivalence and the membership criterion ask only that `k` be a
semiring; commutativity of `k` enters with the self-centralization and with the determinant,
cancellation by nonzero elements with the self-centralization as well, and the order asks for a
division ring, where the nonzero elements are exactly the units.

Self-centralization is proved under two hypotheses, neither of them idle.  Cancellation is a
sufficient hypothesis rather than a necessary one: an off-diagonal entry `g i j` of a centralizing
matrix satisfies `g i j * t i = g i j * t j` for diagonal entries `t i ≠ t j`, and
`IsCancelMulZero k` is what forces that entry to vanish — no subtraction is involved, so a
commutative semiring suffices, and the two diagonal entries need not differ by a unit
(`TauCeti.apply_eq_zero_of_commute_diagonal`).  Over a ring, `IsCancelMulZero` is exactly
`NoZeroDivisors`.  The second
hypothesis, that the unit group has two distinct elements, is there because a diagonal matrix can
only separate the coordinate lines it distinguishes; two units already suffice, because only one
pair of coordinates is separated at a time.  That one cannot simply be dropped, and what happens
without it is recorded here: over a ring with only one unit, such as `𝔽₂`, the torus is trivial
(`TauCeti.diagonalTorus_eq_bot`) while its centralizer is the whole of `GL n k`
(`TauCeti.centralizer_diagonalTorus_eq_top`).  These two subgroups differ, so self-centralization
genuinely fails, exactly when `GL n k` is itself nontrivial — over `𝔽₂` that is the case for
`n ≥ 2`, while for `n ≤ 1` the whole group is trivial and the conclusion survives for want of
anything to contradict it.

The action of the torus on the coordinate lines of the standard representation is in
`TauCeti.RepresentationTheory.ClassicalGroups.Torus`.

## Main definitions

* `TauCeti.diagGL` embeds a family of units as an invertible diagonal matrix.
* `TauCeti.diagonalTorus`: the subgroup of invertible diagonal matrices in `GL n k`.
* `TauCeti.diagonalTorusEquiv`: the identification `(Fin n → kˣ) ≃* diagonalTorus k n`.

## Main statements

* `TauCeti.isUnit_apply_of_isDiag`: the diagonal entries of an invertible diagonal matrix are
  units.
* `TauCeti.isDiag_of_commute_diagonal`: a matrix commuting with a diagonal matrix of pairwise
  distinct entries is itself diagonal.
* `TauCeti.mem_diagonalTorus_iff`: membership in the torus is diagonality of the matrix.
* `TauCeti.natCard_diagonalTorus`: the torus has `(q - 1)ⁿ` elements over a division ring with `q`
  elements.
* `TauCeti.centralizer_diagonalTorus`: the diagonal torus is its own centralizer.
* `TauCeti.centralizer_diagonalTorus_eq_top`: over a ring with a single unit the centralizer is
  instead the whole group.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layers 1 and 3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} {n : ℕ}

section Semiring

variable [Semiring k]

/-- Coordinatewise units embed in `GL n k` as diagonal matrices. -/
def diagGL : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

/-- The matrix underlying `diagGL t` is the diagonal matrix with entries `t i`. -/
@[simp]
theorem diagGL_coe (t : Fin n → kˣ) : (diagGL t : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun i => (t i : k) := by
  rfl

/-- The entries of `diagGL t` vanish off the diagonal and equal `t i` on it. -/
@[simp]
theorem diagGL_apply (t : Fin n → kˣ) (i j : Fin n) :
    diagGL t i j = if i = j then (t i : k) else 0 := by
  rw [diagGL_coe]
  exact Matrix.diagonal_apply ..

/-- The diagonal embedding is injective. -/
theorem diagGL_injective : Function.Injective (diagGL (k := k) (n := n)) := by
  intro t s h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) h
  simpa using this

/-- The diagonal entries of an invertible diagonal matrix are units: the inverse matrix supplies
the inverse entry, because for a diagonal matrix each of the two products defining invertibility
collapses on the diagonal to a single term.

(Mathlib's `Matrix.isUnit_diagonal` says the same thing over a `CommRing`, where it is proved
through the adjugate; the fact itself needs no commutativity, and the diagonal torus below is a
subgroup of `GL n k` already over a semiring.) -/
theorem isUnit_apply_of_isDiag {ι : Type*} [Fintype ι] [DecidableEq ι] {g : GL ι k}
    (hg : (g : Matrix ι ι k).IsDiag) (i : ι) : IsUnit ((g : Matrix ι ι k) i i) := by
  refine ⟨⟨(g : Matrix ι ι k) i i, ((g⁻¹ : GL ι k) : Matrix ι ι k) i i, ?_, ?_⟩, rfl⟩
  · have h : ((g : Matrix ι ι k) * ((g⁻¹ : GL ι k) : Matrix ι ι k)) i i =
        (1 : Matrix ι ι k) i i := by rw [g.mul_inv]
    rwa [Matrix.mul_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun b _ hb => by rw [hg (Ne.symm hb), zero_mul]), Matrix.one_apply_eq] at h
  · have h : (((g⁻¹ : GL ι k) : Matrix ι ι k) * (g : Matrix ι ι k)) i i =
        (1 : Matrix ι ι k) i i := by rw [g.inv_mul]
    rwa [Matrix.mul_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      (fun b _ hb => by rw [hg hb, mul_zero]), Matrix.one_apply_eq] at h

/-- The **diagonal torus** of `GL n k`: the image of the coordinatewise units under `diagGL`. -/
def diagonalTorus (k : Type u) [Semiring k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  MonoidHom.range (diagGL (k := k) (n := n))

/-- Membership in the diagonal torus, read off its definition as a range: an element lies in it
exactly when it is `diagGL t` for a family of units `t`. -/
theorem mem_diagonalTorus_iff_exists_diagGL {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ ∃ t : Fin n → kˣ, diagGL t = g :=
  MonoidHom.mem_range

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
noncomputable def diagonalTorusEquiv (k : Type u) [Semiring k] (n : ℕ) :
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

end Semiring

section CommSemiring

variable [CommSemiring k]

/-- The diagonal torus is commutative: diagonal matrices multiply coordinatewise.  This is where
commutativity of `k` is first needed: `kˣ` is commutative only then. -/
instance instIsMulCommutativeDiagonalTorus : IsMulCommutative (diagonalTorus k n) :=
  ⟨⟨by
    rintro ⟨-, t, rfl⟩ ⟨-, s, rfl⟩
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm]⟩⟩

section IsCancelMulZero

variable [IsCancelMulZero k]

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix commuting with a diagonal matrix has vanishing `(i, j)` entry whenever the diagonal
matrix separates the coordinates `i` and `j`. -/
theorem apply_eq_zero_of_commute_diagonal {t : ι → k} {g : Matrix ι ι k}
    (hg : Commute (Matrix.diagonal t) g) {i j : ι} (hij : t i ≠ t j) : g i j = 0 := by
  have hentry : (Matrix.diagonal t * g) i j = (g * Matrix.diagonal t) i j := by rw [hg.eq]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  -- `hentry : t i * g i j = g i j * t j`; cancelling `g i j` on the left would give `t i = t j`.
  by_contra h
  exact hij (mul_left_cancel₀ h (by rw [mul_comm (g i j) (t i)]; exact hentry))

/-- **A matrix commuting with a diagonal matrix of pairwise distinct entries is diagonal.** -/
theorem isDiag_of_commute_diagonal {t : ι → k} (ht : Function.Injective t)
    {g : Matrix ι ι k} (hg : Commute (Matrix.diagonal t) g) : g.IsDiag :=
  fun _ _ hij => apply_eq_zero_of_commute_diagonal hg (ht.ne hij)

end Diagonal

variable [Nontrivial kˣ]

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

end IsCancelMulZero

end CommSemiring

variable [CommRing k]

/-- The determinant of a diagonal matrix is the product of its diagonal entries. -/
@[simp]
theorem det_diagGL (t : Fin n → kˣ) :
    Matrix.GeneralLinearGroup.det (diagGL t) = ∏ i, t i := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL_coe, Matrix.det_diagonal]

/-- The determinant of an element of the diagonal torus is the product of its diagonal entries. -/
theorem det_of_mem_diagonalTorus {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) :
    (Matrix.GeneralLinearGroup.det g : k) = ∏ i, (g : Matrix (Fin n) (Fin n) k) i i := by
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    ← (isDiag_of_mem_diagonalTorus hg).diagonal_diag, Matrix.det_diagonal]
  simp [Matrix.diag]

/-- **The order of the diagonal torus**: over a division ring with `q` elements it has `(q - 1)ⁿ`
elements, one invertible scalar per diagonal entry.  Over an infinite division ring both sides
vanish. -/
theorem natCard_diagonalTorus (k : Type u) [DivisionRing k] (n : ℕ) :
    Nat.card (diagonalTorus k n) = (Nat.card k - 1) ^ n := by
  rw [← Nat.card_congr (diagonalTorusEquiv k n).toEquiv, Nat.card_fun, Nat.card_units,
    Nat.card_fin]

end TauCeti
