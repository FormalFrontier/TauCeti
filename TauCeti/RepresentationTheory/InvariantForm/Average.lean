/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Averaging a bilinear form over a finite group

Summing a bilinear form over the orbit of a representation of a finite group,
`∑_g B (σ g ·) (σ g ·)`, makes it invariant: this is the standard construction that produces
invariant forms out of arbitrary ones.  No division by `|G|` is performed, so the construction
needs no invertibility of the group order -- the sum is already invariant, and the averaged form
of a symmetric form is symmetric.

Over `ℝ` the construction also produces a *nonzero* invariant symmetric form on any nontrivial
finite-dimensional representation: average the coordinate dot product read in a basis.  Positivity
is what makes the average nonzero -- the sum of the nonnegative numbers `B₀ (σ g x) (σ g x)` is at
least its term at `g = 1`, which is positive -- so it is the ordering of `ℝ`, not a division by
`|G|`, that does the work.

## Main definitions

* `Representation.averageForm`: the average of a bilinear form over a finite group.

## Main results

* `Representation.isInvariantForm_averageForm`: the average of a bilinear form is invariant.
* `Representation.isSymm_averageForm`: the average of a symmetric form is symmetric.
* `Representation.exists_isInvariantForm_isSymm_ne_zero`: **a real representation of a finite group
  on a nontrivial finite-dimensional space carries a nonzero invariant symmetric form.**

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 7: the invariant symmetric form that the value `+1` of the Frobenius-Schur indicator is
  characterized by, here for a representation realizable over `ℝ`.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

open LinearMap (BilinForm)

open TauCeti

namespace Representation

open TauCeti.Representation

/-! ### Averaging a bilinear form over a finite group -/

section Average

variable {k G W : Type*} [CommSemiring k] [Group G] [Fintype G] [AddCommMonoid W] [Module k W]

/-- The **average** of a bilinear form over a finite group: `∑_g B (σ g ·) (σ g ·)`.  No division
by `|G|` is performed, so no invertibility of the group order is needed; the sum is already
invariant. -/
def averageForm (σ : Representation k G W) (B : BilinForm k W) : BilinForm k W :=
  ∑ g : G, B.comp (σ g) (σ g)

@[simp]
theorem averageForm_apply (σ : Representation k G W) (B : BilinForm k W) (x y : W) :
    averageForm σ B x y = ∑ g : G, B (σ g x) (σ g y) := by
  simp [averageForm, BilinForm.comp_apply]

/-- The average of a bilinear form over a finite group is invariant: reindexing the sum by right
translation absorbs the group element. -/
theorem isInvariantForm_averageForm (σ : Representation k G W) (B : BilinForm k W) :
    IsInvariantForm σ (averageForm σ B) := by
  rw [isInvariantForm_iff]
  intro h x y
  simp only [averageForm_apply]
  refine Eq.trans ?_ (Fintype.sum_equiv (Equiv.mulRight h)
    (fun g : G => B (σ (g * h) x) (σ (g * h) y)) (fun g : G => B (σ g x) (σ g y))
    fun g => rfl)
  exact Finset.sum_congr rfl fun g _ => by
    simp only [map_mul, Module.End.mul_apply]

/-- The average of a symmetric bilinear form is symmetric. -/
theorem isSymm_averageForm {σ : Representation k G W} {B : BilinForm k W} (hB : B.IsSymm) :
    (averageForm σ B).IsSymm :=
  ⟨fun x y => by
    simpa only [averageForm_apply] using
      Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hB.eq (σ g x) (σ g y)⟩

end Average

/-! ### A nonzero invariant symmetric form on a real representation -/

section RealAverage

variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module ℝ W]

/-- **A real representation of a finite group carries a nonzero invariant symmetric form.**  Take
the dot product read in a basis and average it over the group; averaging preserves symmetry, and
the average of a positive semidefinite form is at least its value at the identity, hence still
positive definite.  This is the real input to the orthogonality of a representation with a real
form. -/
theorem exists_isInvariantForm_isSymm_ne_zero (σ : Representation ℝ G W)
    [FiniteDimensional ℝ W] [Nontrivial W] :
    ∃ B : BilinForm ℝ W, IsInvariantForm σ B ∧ B.IsSymm ∧ B ≠ 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set b := Module.finBasis ℝ W with hb
  set B₀ : BilinForm ℝ W := Matrix.toBilin b 1 with hB₀
  have hB₀apply : ∀ x y : W, B₀ x y = ∑ i, b.repr x i * b.repr y i := by
    intro x y
    simp [hB₀, Matrix.toBilin_apply, Matrix.one_apply, Finset.sum_ite_eq]
  have hB₀symm : B₀.IsSymm :=
    ⟨fun x y => by
      simpa only [hB₀apply] using
        Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => mul_comm _ _⟩
  have hB₀nonneg : ∀ x : W, 0 ≤ B₀ x x := fun x => by
    rw [hB₀apply]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine ⟨averageForm σ B₀, isInvariantForm_averageForm σ B₀, isSymm_averageForm hB₀symm, ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  have hpos : 0 < B₀ x x := by
    rw [hB₀apply]
    obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hx (b.repr.injective ?_)
      rw [map_zero]
      ext j
      simp [hcon j]
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  have hle : B₀ (σ 1 x) (σ 1 x) ≤ averageForm σ B₀ x x := by
    rw [averageForm_apply]
    exact Finset.single_le_sum (f := fun g : G => B₀ (σ g x) (σ g x))
      (fun g _ => hB₀nonneg _) (Finset.mem_univ 1)
  intro hzero
  rw [map_one] at hle
  simp only [Module.End.one_apply] at hle
  rw [hzero] at hle
  simp only [LinearMap.zero_apply] at hle
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

end RealAverage

end Representation
