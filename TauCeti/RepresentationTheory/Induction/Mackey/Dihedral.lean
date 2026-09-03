/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Character
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
public import TauCeti.RepresentationTheory.Induction.Mackey.LinearCharacter

/-!
# Inducing a linear character from the rotation subgroup of a dihedral group

The dihedral group `DihedralGroup n` has a rotation subgroup of index `2`, cyclic and so
commutative by `TauCeti.dihedralRotationsMulEquiv`, and every representation induced from it has
twice the dimension it was induced from. Inducing a **linear** character `ψ` of the rotations
therefore produces a two-dimensional representation, and this file settles, over an algebraically
closed field of characteristic zero, when it is irreducible: exactly when `ψ` is not its own
inverse.

The criterion is the Mackey irreducibility criterion for a linear character of a normal subgroup
(`TauCeti.simple_indFDRep_ofLinearCharacter_iff`), which asks that no element `s` outside the
subgroup stabilize `ψ`. For the dihedral group the conjugation is completely explicit: by
`TauCeti.conjNormal_eq_inv_of_notMem_dihedralRotations` an element outside the rotation subgroup
inverts every rotation, so `{}^s ψ = ψ⁻¹` for *every* such `s`, and the criterion collapses to the
single condition `ψ ≠ ψ⁻¹`, that some value of `ψ` is not a square root of `1`. That condition is
not only sufficient but necessary, so the result is an `iff`.

The concrete instance carried out below is `n = 4`: the character sending the rotation `r 1` of
`D₄` to `i` has `ψ(r 1)² = -1 ≠ 1`, so it induces a two-dimensional irreducible representation
of `D₄` over `ℂ`.

## Main definitions

* `TauCeti.dihedralGroupFourRotationChar`: a faithful linear character of the rotation subgroup
  of `D₄`, sending `r 1` to `i`.

## Main statements

* `TauCeti.simple_indFDRep_ofLinearCharacter_dihedralRotations_iff`: **over an algebraically
  closed field of characteristic zero, inducing a linear character of the rotation subgroup is
  irreducible exactly when the character is not its own inverse.**
* `TauCeti.finrank_indFDRep_ofLinearCharacter_dihedralRotations`: the induced representation is
  two-dimensional, over any field.
* `TauCeti.dihedralGroupFourRotationChar_injective`: that character of `D₄` is faithful.
* `TauCeti.simple_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar`: **the representation
  of `D₄` over `ℂ` induced from that faithful linear character is irreducible**, the Mackey
  criterion certifying it.
* `TauCeti.finrank_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar`: it is
  two-dimensional; with the previous statement this is the two-dimensional irreducible of `D₄`.

## Implementation notes

`TauCeti.dihedralRotationChar`, the character of the rotation subgroup attached to an `n`-th root
of unity, is pure group theory and lives with the rotation subgroup in
`TauCeti.GroupTheory.SpecificGroups.Dihedral.Character`; only its consequences for induced
representations are here.

The irreducibility criterion is stated over an algebraically closed field of characteristic zero,
which is what `TauCeti.simple_indFDRep_ofLinearCharacter_iff` asks for, and its coefficient field
is moreover constrained to `Type` rather than `Type*`, that criterion placing the field and the
group in a common universe and `DihedralGroup n` living in `Type`. The dimension count asks for
neither: it holds over any field, in any universe.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 5.3 and Chapter 7.4.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

section Dimension

variable {k : Type u} [Field k] {n : ℕ}

/-- **The induced representation is two-dimensional**: the rotation subgroup has index `2` and a
linear character is one-dimensional. -/
theorem finrank_indFDRep_ofLinearCharacter_dihedralRotations (ψ : dihedralRotations n →* kˣ) :
    Module.finrank k (indFDRep (FDRep.ofLinearCharacter ψ)) = 2 := by
  rw [finrank_indFDRep_ofLinearCharacter, index_dihedralRotations]

end Dimension

section Irreducibility

variable {k : Type} [Field k] {n : ℕ} [NeZero n] [IsAlgClosed k] [CharZero k]

/-- **Over an algebraically closed field of characteristic zero, inducing a linear character of the
rotation subgroup of a dihedral group is irreducible exactly when the character is not its own
inverse.** Conjugation by any reflection inverts the character, so the Mackey criterion for the
normal rotation subgroup asks precisely that `ψ⁻¹ ≠ ψ`, which is that some value of `ψ` fails to
square to `1`. -/
theorem simple_indFDRep_ofLinearCharacter_dihedralRotations_iff (ψ : dihedralRotations n →* kˣ) :
    Simple (indFDRep (FDRep.ofLinearCharacter ψ)) ↔ ∃ x, ψ x ^ 2 ≠ 1 := by
  rw [simple_indFDRep_ofLinearCharacter_iff]
  -- Conjugation by any `s` outside the rotations inverts `ψ`, so `ψ ({}^s x) ≠ ψ x` says exactly
  -- that `ψ x` is not its own inverse; only the existence of such an `x` is left on either side.
  have key : ∀ {s : DihedralGroup n}, s ∉ dihedralRotations n →
      ∀ x : dihedralRotations n, (ψ (MulAut.conjNormal s x) ≠ ψ x ↔ ψ x ^ 2 ≠ 1) := by
    intro s hs x
    rw [conjNormal_eq_inv_of_notMem_dihedralRotations hs, map_inv, ne_eq, ne_eq,
      inv_eq_iff_mul_eq_one, ← sq]
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ s hs => ⟨x, (key hs x).mpr hx⟩⟩
  obtain ⟨x, hx⟩ := h (DihedralGroup.sr 0) (sr_notMem_dihedralRotations 0)
  exact ⟨x, (key (sr_notMem_dihedralRotations 0) x).mp hx⟩

end Irreducibility

section DihedralFour

private theorem isPrimitiveRoot_unitI :
    IsPrimitiveRoot (Units.mk0 Complex.I Complex.I_ne_zero) 4 :=
  IsPrimitiveRoot.coe_units_iff.mp (by
    rw [Units.val_mk0]
    exact Complex.isPrimitiveRoot_I)

/-- **A faithful linear character of the rotation subgroup of `D₄`**, sending the rotation `r 1`
to the primitive fourth root of unity `i`. -/
noncomputable def dihedralGroupFourRotationChar : dihedralRotations 4 →* ℂˣ :=
  dihedralRotationChar isPrimitiveRoot_unitI.pow_eq_one

/-- The value of `TauCeti.dihedralGroupFourRotationChar` at a rotation is the corresponding power
of `i`. -/
@[simp]
theorem coe_dihedralGroupFourRotationChar_r (i : ZMod 4) :
    (dihedralGroupFourRotationChar ⟨DihedralGroup.r i, r_mem_dihedralRotations i⟩ : ℂ) =
      Complex.I ^ i.val := by
  rw [dihedralGroupFourRotationChar, dihedralRotationChar_r, Units.val_pow_eq_pow_val,
    Units.val_mk0]

/-- `TauCeti.dihedralGroupFourRotationChar` sends the generating rotation to `i`. -/
theorem coe_dihedralGroupFourRotationChar_r_one :
    (dihedralGroupFourRotationChar ⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩ : ℂ) =
      Complex.I := by
  rw [coe_dihedralGroupFourRotationChar_r, ZMod.val_one_eq_one_mod]
  norm_num

/-- **`TauCeti.dihedralGroupFourRotationChar` is faithful**: `i` is a *primitive* fourth root of
unity, so this is `TauCeti.dihedralRotationChar_injective`. -/
theorem dihedralGroupFourRotationChar_injective :
    Function.Injective dihedralGroupFourRotationChar :=
  dihedralRotationChar_injective isPrimitiveRoot_unitI

/-- **The representation of `D₄` induced from a faithful linear character of its rotation subgroup
is irreducible**, by the Mackey criterion: conjugation by a reflection sends `i` to `-i`. -/
theorem simple_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar :
    Simple (indFDRep (FDRep.ofLinearCharacter dihedralGroupFourRotationChar)) := by
  refine (simple_indFDRep_ofLinearCharacter_dihedralRotations_iff dihedralGroupFourRotationChar).mpr
    ⟨⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩, fun hc => ?_⟩
  have h : (Complex.I) ^ 2 = 1 := by
    rw [← coe_dihedralGroupFourRotationChar_r_one, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  rw [Complex.I_sq] at h
  exact absurd h (by norm_num)

/-- **The induced representation of `D₄` is two-dimensional**, so with
`TauCeti.simple_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar` it is a two-dimensional
irreducible representation of `D₄`. -/
theorem finrank_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar :
    Module.finrank ℂ (indFDRep (FDRep.ofLinearCharacter dihedralGroupFourRotationChar)) = 2 :=
  finrank_indFDRep_ofLinearCharacter_dihedralRotations dihedralGroupFourRotationChar

end DihedralFour

end TauCeti
