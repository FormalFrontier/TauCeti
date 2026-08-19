/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative

/-!
# Jordan decomposition of commuting products

The multiplicative Jordan decomposition respects products of commuting linear automorphisms.
More precisely, if `g` and `h` commute, then every Jordan factor of `g` commutes with every
Jordan factor of `h`, and the semisimple and unipotent parts of `g * h` are the products of the
corresponding parts.

The key input is that the semisimple part is a polynomial in the original automorphism. The
cross-commutation statements then reduce the product formula to uniqueness of the multiplicative
Jordan decomposition.

This supplies a structural compatibility for the Jordan decomposition in Layer 4 of the
ReductiveGroups roadmap.

## Main declarations

* `LinearMap.GeneralLinearGroup.commute_semisimplePart_semisimplePart_of_commute`: semisimple
  parts of commuting automorphisms commute.
* `LinearMap.GeneralLinearGroup.commute_unipotentPart_unipotentPart_of_commute`: unipotent parts
  of commuting automorphisms commute.
* `LinearMap.GeneralLinearGroup.jordanDecomposition_mul_of_commute`: the ordered decomposition
  of a commuting product is the componentwise product.
* `LinearMap.GeneralLinearGroup.semisimplePart_mul_of_commute` and
  `LinearMap.GeneralLinearGroup.unipotentPart_mul_of_commute`: the two factor formulas.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace LinearMap.GeneralLinearGroup

open Module

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [PerfectField K] [FiniteDimensional K V]

private theorem commute_semisimplePart_right_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    Commute (semisimplePart g) h := by
  apply Commute.units_of_val
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute
    (coe_semisimplePart_mem_adjoin g) hgh.units_val.symm).symm

/-- The semisimple parts of two commuting linear automorphisms commute. -/
theorem commute_semisimplePart_semisimplePart_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    Commute (semisimplePart g) (semisimplePart h) := by
  apply Commute.units_of_val
  exact Algebra.commute_of_mem_adjoin_singleton_of_commute
    (coe_semisimplePart_mem_adjoin h)
    ((Algebra.commute_of_mem_adjoin_singleton_of_commute
      (coe_semisimplePart_mem_adjoin g) hgh.units_val.symm).symm)

private theorem unipotentPart_eq_inv_mul (g : GeneralLinearGroup K V) :
    unipotentPart g = (semisimplePart g)⁻¹ * g := by
  apply mul_left_cancel (a := semisimplePart g)
  rw [semisimplePart_mul_unipotentPart]
  simp

/-- The semisimple part of the first of two commuting automorphisms commutes with the unipotent
part of the second. -/
theorem commute_semisimplePart_unipotentPart_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    Commute (semisimplePart g) (unipotentPart h) := by
  rw [unipotentPart_eq_inv_mul]
  exact (commute_semisimplePart_semisimplePart_of_commute hgh).inv_right.mul_right
    (commute_semisimplePart_right_of_commute hgh)

/-- The unipotent part of the first of two commuting automorphisms commutes with the semisimple
part of the second. -/
theorem commute_unipotentPart_semisimplePart_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    Commute (unipotentPart g) (semisimplePart h) :=
  (commute_semisimplePart_unipotentPart_of_commute hgh.symm).symm

/-- The unipotent parts of two commuting linear automorphisms commute. -/
theorem commute_unipotentPart_unipotentPart_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    Commute (unipotentPart g) (unipotentPart h) := by
  rw [unipotentPart_eq_inv_mul, unipotentPart_eq_inv_mul]
  exact ((commute_semisimplePart_semisimplePart_of_commute hgh).inv_left.inv_right.mul_left
      ((commute_semisimplePart_right_of_commute hgh.symm).symm.inv_right)).mul_right
    ((commute_semisimplePart_right_of_commute hgh).inv_left.mul_left hgh)

/-- The Jordan decomposition of a product of commuting linear automorphisms is the
componentwise product of their Jordan decompositions. -/
theorem jordanDecomposition_mul_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    jordanDecomposition (g * h) =
      (semisimplePart g * semisimplePart h,
        unipotentPart g * unipotentPart h) := by
  symm
  apply (eq_jordanDecomposition_iff (g * h) _ _).2
  refine ⟨(isSemisimple_semisimplePart g).mul_of_commute
      (isSemisimple_semisimplePart h)
      (commute_semisimplePart_semisimplePart_of_commute hgh),
    (isUnipotent_unipotentPart g).mul_of_commute
      (isUnipotent_unipotentPart h)
      (commute_unipotentPart_unipotentPart_of_commute hgh), ?_, ?_⟩
  · exact ((commute_semisimplePart_unipotentPart g).mul_left
      (commute_unipotentPart_semisimplePart_of_commute hgh).symm).mul_right
      ((commute_semisimplePart_unipotentPart_of_commute hgh).mul_left
        (commute_semisimplePart_unipotentPart h))
  · calc
      g * h = (semisimplePart g * unipotentPart g) *
          (semisimplePart h * unipotentPart h) := by
            rw [semisimplePart_mul_unipotentPart, semisimplePart_mul_unipotentPart]
      _ = (semisimplePart g * semisimplePart h) *
          (unipotentPart g * unipotentPart h) := by
            rw [mul_assoc, ← mul_assoc (unipotentPart g)]
            rw [(commute_unipotentPart_semisimplePart_of_commute hgh).eq]
            simp only [mul_assoc]

/-- The semisimple part of a product of commuting automorphisms is the product of their
semisimple parts. -/
theorem semisimplePart_mul_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    semisimplePart (g * h) = semisimplePart g * semisimplePart h :=
  by
    rw [semisimplePart_def (g * h)]
    exact congrArg Prod.fst (jordanDecomposition_mul_of_commute hgh)

/-- The unipotent part of a product of commuting automorphisms is the product of their
unipotent parts. -/
theorem unipotentPart_mul_of_commute
    {g h : GeneralLinearGroup K V} (hgh : Commute g h) :
    unipotentPart (g * h) = unipotentPart g * unipotentPart h :=
  by
    rw [unipotentPart_def (g * h)]
    exact congrArg Prod.snd (jordanDecomposition_mul_of_commute hgh)

end LinearMap.GeneralLinearGroup
