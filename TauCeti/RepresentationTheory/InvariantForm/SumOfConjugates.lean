/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import TauCeti.RepresentationTheory.InvariantForm

/-!
# Summing a bilinear form over the conjugates of a representation

Summing a bilinear form over the orbit of a representation of a finite group,
`∑_g B (σ g ·) (σ g ·)`, makes it invariant: this is the standard construction that produces
invariant forms out of arbitrary ones.  No division by `|G|` is performed -- as in Mathlib's
`MonoidAlgebra.sumOfConjugates` for a linear map, the undivided sum is the construction, and it
needs no invertibility of the group order.  The sum over the conjugates of a symmetric form is
symmetric.

Over an ordered field the construction also produces a *nonzero* invariant symmetric form on any
nontrivial finite-dimensional representation: sum the coordinate dot product read in a basis.
Positivity is what makes the sum nonzero -- the sum of the nonnegative numbers
`B₀ (σ g x) (σ g x)` is at least its term at `g = 1`, which is positive -- so it is the ordering of
the field, not a division by `|G|`, that does the work.

## Main definitions

* `Representation.sumOfConjugatesForm`: the sum of a bilinear form over the conjugates of a
  representation of a finite group.

## Main results

* `Representation.sumOfConjugatesForm_eq_norm`: that sum is the `Representation.norm` of the form
  for the conjugation action of `G` on bilinear forms.
* `Representation.isInvariantForm_sumOfConjugatesForm`: that sum is invariant.
* `Representation.isSymm_sumOfConjugatesForm`: that sum is symmetric if the form is.
* `Representation.exists_isInvariantForm_isSymm_ne_zero`: **a representation of a finite group on a
  nontrivial finite-dimensional space over an ordered field carries a nonzero invariant symmetric
  form.**

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

/-! ### Summing a bilinear form over a finite group -/

section Monoid

variable {k G W : Type*} [CommSemiring k] [Monoid G] [Fintype G] [AddCommMonoid W] [Module k W]

/-- The **sum of a bilinear form over the conjugates** of a representation of a finite monoid,
`∑_g B (σ g ·) (σ g ·)`.  No division by `|G|` is performed, so no invertibility of the monoid order
is needed; when `G` is a group the plain sum is already invariant
(`Representation.isInvariantForm_sumOfConjugatesForm`), being the `Representation.norm` of `B` for
the conjugation action of `G` on bilinear forms.  The name follows Mathlib's
`MonoidAlgebra.sumOfConjugates`, the same undivided sum for a linear map. -/
def sumOfConjugatesForm (σ : Representation k G W) (B : BilinForm k W) : BilinForm k W :=
  ∑ g : G, B.comp (σ g) (σ g)

@[simp]
theorem sumOfConjugatesForm_apply (σ : Representation k G W) (B : BilinForm k W) (x y : W) :
    sumOfConjugatesForm σ B x y = ∑ g : G, B (σ g x) (σ g y) := by
  simp [sumOfConjugatesForm, BilinForm.comp_apply]

/-- The sum over the conjugates of a symmetric bilinear form is symmetric. -/
theorem isSymm_sumOfConjugatesForm {σ : Representation k G W} {B : BilinForm k W} (hB : B.IsSymm) :
    (sumOfConjugatesForm σ B).IsSymm :=
  ⟨fun x y => by
    simpa only [sumOfConjugatesForm_apply] using
      Finset.sum_congr rfl fun g (_ : g ∈ Finset.univ) => hB.eq (σ g x) (σ g y)⟩

end Monoid

section Group

variable {k G W : Type*} [CommSemiring k] [Group G] [Fintype G] [AddCommMonoid W] [Module k W]

/-- **The conjugate sum of a form is the norm of the form** for the conjugation action of `G` on
bilinear forms, `Representation.linHom σ σ.dual`: the two sums differ only by the reindexing
`g ↦ g⁻¹`, since the conjugation action moves `σ g⁻¹` into both arguments. -/
theorem sumOfConjugatesForm_eq_norm (σ : Representation k G W) (B : BilinForm k W) :
    sumOfConjugatesForm σ B = norm (linHom σ σ.dual) B := by
  ext x y
  rw [sumOfConjugatesForm_apply, norm]
  simp only [LinearMap.sum_apply, linHom_apply, LinearMap.coe_comp, Function.comp_apply,
    dual_apply, Module.Dual.transpose_apply]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp

/-- The sum of a bilinear form over the conjugates of a representation of a finite group is
invariant: it is a norm for the conjugation action of `G` on bilinear forms
(`Representation.sumOfConjugatesForm_eq_norm`), and a norm is fixed by that action. -/
@[simp]
theorem isInvariantForm_sumOfConjugatesForm (σ : Representation k G W) (B : BilinForm k W) :
    IsInvariantForm σ (sumOfConjugatesForm σ B) := by
  rw [isInvariantForm_iff, sumOfConjugatesForm_eq_norm]
  intro h x y
  simpa only [linHom_apply, LinearMap.coe_comp, Function.comp_apply, dual_apply,
    Module.Dual.transpose_apply, inv_inv] using
    DFunLike.congr_fun (DFunLike.congr_fun (self_norm_apply (linHom σ σ.dual) h⁻¹ B) x) y

end Group

/-! ### A nonzero invariant symmetric form over an ordered field -/

section OrderedField

variable {k G W : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [Group G] [Finite G]
  [AddCommGroup W] [Module k W]

/-- **A representation of a finite group over an ordered field carries a nonzero invariant
symmetric form.**  Take the dot product read in a basis and sum it over the conjugates; that sum
preserves symmetry, and it dominates its term at `g = 1`, which is the value `B₀ x x` of the dot
product itself and is positive for `x ≠ 0`.  So the sum does not vanish.  This is the input over
`ℝ` to the orthogonality of a representation with a real form. -/
theorem exists_isInvariantForm_isSymm_ne_zero (σ : Representation k G W)
    [FiniteDimensional k W] [Nontrivial W] :
    ∃ B : BilinForm k W, IsInvariantForm σ B ∧ B.IsSymm ∧ B ≠ 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set b := Module.finBasis k W with hb
  set B₀ : BilinForm k W := Matrix.toBilin b 1 with hB₀
  have hB₀apply : ∀ x y : W, B₀ x y = ⇑(b.repr x) ⬝ᵥ ⇑(b.repr y) := by
    intro x y
    simp [hB₀, Matrix.toBilin_apply, Matrix.one_apply, Finset.sum_ite_eq, dotProduct]
  have hB₀symm : B₀.IsSymm := (Matrix.isSymm_toBilin_iff_isSymm b).mpr Matrix.isSymm_one
  have hB₀nonneg : ∀ x : W, 0 ≤ B₀ x x := fun x => by
    rw [hB₀apply, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine ⟨sumOfConjugatesForm σ B₀, isInvariantForm_sumOfConjugatesForm σ B₀,
    isSymm_sumOfConjugatesForm hB₀symm, ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  have hpos : 0 < B₀ x x := by
    refine (hB₀nonneg x).lt_of_ne (Ne.symm ?_)
    rw [hB₀apply, ne_eq, dotProduct_self_eq_zero, Finsupp.coe_eq_zero]
    exact fun h => hx (b.repr.map_eq_zero_iff.mp h)
  have hle : B₀ x x ≤ sumOfConjugatesForm σ B₀ x x := by
    rw [sumOfConjugatesForm_apply]
    simpa using Finset.single_le_sum (f := fun g : G => B₀ (σ g x) (σ g x))
      (fun g _ => hB₀nonneg _) (Finset.mem_univ 1)
  intro hzero
  rw [hzero] at hle
  simp only [LinearMap.zero_apply] at hle
  exact absurd (hpos.trans_le hle) (lt_irrefl 0)

end OrderedField

end Representation
