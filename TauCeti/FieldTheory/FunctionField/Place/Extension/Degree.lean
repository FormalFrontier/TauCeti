/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-!
# The degree of a place over the place below it

Let `F' / F` be an algebraic extension of fields, both with the same field of constants `k`, and
let `P'` be a place of `F' / k` lying over the place `P = P'|_F` of `F / k`. The residue fields
then form a tower `k ⊆ F_P ⊆ F'_{P'}`, so the multiplicativity of `Module.finrank` reads

`deg P' = deg P · f(P' ∣ P)`.

This is the same-constant-field case of Stichtenoth, *Algebraic Function Fields and Codes*, 2nd
ed., Corollary 3.1.14, where the general form is cross-multiplied as
`[k' : k] · deg P' = deg P · f(P' ∣ P)`. The extra factor cannot be written here: the residue
field of a place of `F' / k'` is a `k'`-algebra, and the `k`-algebra structure needed to speak of
`Module.finrank k F'_{P'}` at all comes with the constant-field extension theory.

## Main results

* `TauCeti.Place.degree_eq_degree_restrict_mul_relativeDegree`: `deg P' = deg P · f(P' ∣ P)`.
* `TauCeti.Place.degree_restrict_le`: hence `deg P ≤ deg P'`, the form consumed when a
  finiteness statement about places of `F` is transported to `F'`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

public section

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral F F'] (k F) (P' : Place k F')

/-- The constants act on the valuation ring of `P'` through the valuation ring of the place
below it, so the residue fields inherit a tower over `k`. -/
instance instIsScalarTowerIntegers : IsScalarTower k (P'.restrict k F).integers P'.integers :=
  .of_algebraMap_eq fun c ↦ Subtype.ext <| by
    rw [coe_algebraMap_integers, coe_algebraMap_constants, coe_algebraMap_constants,
      ← IsScalarTower.algebraMap_apply k F F']

/-- **The degree of a place over the place below it** (Stichtenoth, Corollary 3.1.14 in the
same-constant-field case): `deg P' = deg P · f(P' ∣ P)`, by multiplicativity of `finrank` along
the tower of residue fields `k ⊆ F_P ⊆ F'_{P'}`. -/
theorem degree_eq_degree_restrict_mul_relativeDegree :
    P'.degree = (P'.restrict k F).degree * relativeDegree k F P' := by
  rw [degree_eq_finrank, degree_eq_finrank, relativeDegree_def,
    Module.finrank_mul_finrank k (P'.restrict k F).ResidueField P'.ResidueField]

/-- A place is at least as large as the place below it: `deg P ≤ deg P'`.  Finiteness of the
extension guards the junk value of the relative degree. -/
theorem degree_restrict_le [FiniteDimensional F F'] :
    (P'.restrict k F).degree ≤ P'.degree := by
  rw [degree_eq_degree_restrict_mul_relativeDegree k F P']
  exact Nat.le_mul_of_pos_right _ (one_le_relativeDegree k F P')

end Place

end TauCeti
