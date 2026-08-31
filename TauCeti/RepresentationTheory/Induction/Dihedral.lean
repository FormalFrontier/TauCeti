/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.RepresentationTheory.Induction.Mackey.LinearCharacter

/-!
# Inducing a linear character from the rotation subgroup of a dihedral group

The dihedral group `DihedralGroup n` has an abelian rotation subgroup of index `2`, so every
representation induced from it has twice the dimension it was induced from. Inducing a **linear**
character `ψ` of the rotations therefore produces a two-dimensional representation, and this file
settles when it is irreducible: exactly when `ψ` is not its own inverse.

The criterion is the Mackey irreducibility criterion for a linear character of a normal subgroup
(`TauCeti.simple_indFDRep_ofLinearCharacter_iff`), which asks that no element `s` outside the
subgroup stabilize `ψ`. For the dihedral group the conjugation is completely explicit: by
`TauCeti.inv_mul_mul_of_notMem_dihedralRotations` an element outside the rotation subgroup inverts
every rotation, so `{}^s ψ = ψ⁻¹` for *every* such `s`, and the criterion collapses to the single
condition `ψ ≠ ψ⁻¹`, that some value of `ψ` is not a square root of `1`. That condition is not only
sufficient but necessary, so the result is an `iff`.

The concrete instance the roadmap asks for is `n = 4`: the character sending the rotation `r 1` of
`D₄` to `i` has `ψ(r 1)² = -1 ≠ 1`, so it induces the two-dimensional irreducible representation
of `D₄`.

## Main definitions

* `TauCeti.dihedralRotationChar`: the linear character of the rotation subgroup sending `r i` to
  `ζ ^ i`, for `ζ` an `n`-th root of unity.
* `TauCeti.dihedralFourChar`: the faithful linear character of the rotation subgroup of `D₄`
  sending `r 1` to `i`.

## Main statements

* `TauCeti.simple_indFDRep_ofLinearCharacter_dihedralRotations_iff`: **inducing a linear
  character of the rotation subgroup is irreducible exactly when the character is not its own
  inverse.**
* `TauCeti.finrank_indFDRep_ofLinearCharacter_dihedralRotations`: the induced representation is
  two-dimensional.
* `TauCeti.dihedralFourChar_injective`: that character is faithful.
* `TauCeti.simple_indFDRep_dihedralFourChar`: **the two-dimensional irreducible representation of
  `D₄` is induced from a faithful linear character of its rotation subgroup**, the Mackey criterion
  certifying the irreducibility.

## Implementation notes

`TauCeti.dihedralRotationChar` takes the coordinate of a rotation along
`TauCeti.dihedralRotationsEquiv` and reads it through `ZMod.val`, so that its values are
natural-number powers of `ζ`; multiplicativity is then the statement that the exponent may be
reduced modulo `n`, which is Mathlib's `pow_eq_pow_of_modEq`. Taking `ζ` in an arbitrary monoid
costs nothing and keeps the construction independent of the coefficient field.

The coefficient field of the irreducibility criterion is constrained to `Type` rather than `Type*`:
`TauCeti.simple_indFDRep_ofLinearCharacter_iff` places the field and the group in a common
universe, and `DihedralGroup n` lives in `Type`.

## References

This is the "`D₄` dihedral induction" worked example of
[the induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md):
"`Ind` from the cyclic subgroup `⟨r⟩` of order `4` in `D₄ = DihedralGroup 4`, applied to a faithful
linear character of `⟨r⟩` (one sending `r` to a primitive fourth root of unity), produces the
`2`-dimensional irreducible of `D₄`; the Mackey criterion certifies its irreducibility."

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 5.3 and Chapter 7.4.
-/

public section

open CategoryTheory

namespace TauCeti

section RotationChar

variable {M : Type*} [Monoid M] {n : ℕ} {ζ : M}

variable [NeZero n]

/-- **The linear character of the rotation subgroup attached to an `n`-th root of unity** `ζ`:
the rotation `r i` is sent to `ζ ^ i`, the exponent being the canonical representative of `i` in
`ZMod n`. -/
def dihedralRotationChar (hζ : ζ ^ n = 1) : dihedralRotations n →* M where
  toFun x := ζ ^ (Multiplicative.toAdd (dihedralRotationsEquiv n x)).val
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, toAdd_mul, ZMod.val_add]
    rw [pow_eq_pow_of_modEq (Nat.mod_modEq _ n) hζ, pow_add]

@[simp]
theorem dihedralRotationChar_apply (hζ : ζ ^ n = 1) (x : dihedralRotations n) :
    dihedralRotationChar hζ x = ζ ^ (Multiplicative.toAdd (dihedralRotationsEquiv n x)).val :=
  (rfl)

/-- The character sends the rotation `r i` to `ζ ^ i`. -/
theorem dihedralRotationChar_r (hζ : ζ ^ n = 1) (i : ZMod n) :
    dihedralRotationChar hζ ⟨DihedralGroup.r i, r_mem_dihedralRotations i⟩ = ζ ^ i.val := by
  rw [dihedralRotationChar_apply, dihedralRotationsEquiv_r, toAdd_ofAdd]

end RotationChar

section Conjugation

variable {M : Type*} [Group M] {n : ℕ}

/-- **Conjugating a character of the rotation subgroup by a reflection inverts it**: `{}^s ψ = ψ⁻¹`
for every `s` outside the rotation subgroup. This is
`TauCeti.inv_mul_mul_of_notMem_dihedralRotations` transported along `ψ`, and it is why the Mackey
criterion below reads off a single condition on `ψ`. -/
theorem apply_conjNormal_of_notMem_dihedralRotations (ψ : dihedralRotations n →* M)
    {s : DihedralGroup n} (hs : s ∉ dihedralRotations n) (x : dihedralRotations n) :
    ψ (MulAut.conjNormal s x) = (ψ x)⁻¹ := by
  have hs' : s⁻¹ ∉ dihedralRotations n := fun h => hs (by simpa using inv_mem h)
  have hx : MulAut.conjNormal s x = x⁻¹ := by
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    simpa using inv_mul_mul_of_notMem_dihedralRotations hs' x.2
  rw [hx, map_inv]

end Conjugation

section Induction

variable {k : Type} [Field k] {n : ℕ} [NeZero n]

/-- **The induced representation is two-dimensional**: the rotation subgroup has index `2` and a
linear character is one-dimensional. -/
theorem finrank_indFDRep_ofLinearCharacter_dihedralRotations (ψ : dihedralRotations n →* kˣ) :
    Module.finrank k (indFDRep (FDRep.ofLinearCharacter ψ)) = 2 := by
  rw [finrank_indFDRep, index_dihedralRotations]
  simp

variable [IsAlgClosed k] [CharZero k]

/-- **Inducing a linear character of the rotation subgroup of a dihedral group is irreducible
exactly when the character is not its own inverse.** Conjugation by any reflection inverts the
character, so the Mackey criterion for the normal rotation subgroup asks precisely that `ψ⁻¹ ≠ ψ`,
which is that some value of `ψ` fails to square to `1`. -/
theorem simple_indFDRep_ofLinearCharacter_dihedralRotations_iff (ψ : dihedralRotations n →* kˣ) :
    Simple (indFDRep (FDRep.ofLinearCharacter ψ)) ↔ ∃ x, ψ x ^ 2 ≠ 1 := by
  rw [simple_indFDRep_ofLinearCharacter_iff]
  -- Conjugation by any `s` outside the rotations inverts `ψ`, so `ψ ({}^s x) ≠ ψ x` says exactly
  -- that `ψ x` is not its own inverse; only the existence of such an `x` is left on either side.
  have key : ∀ {s : DihedralGroup n}, s ∉ dihedralRotations n →
      ∀ x : dihedralRotations n, (ψ (MulAut.conjNormal s x) ≠ ψ x ↔ ψ x ^ 2 ≠ 1) := by
    intro s hs x
    rw [apply_conjNormal_of_notMem_dihedralRotations ψ hs x, ne_eq, ne_eq,
      inv_eq_iff_mul_eq_one, ← sq]
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ s hs => ⟨x, (key hs x).mpr hx⟩⟩
  obtain ⟨x, hx⟩ := h (DihedralGroup.sr 0) (sr_notMem_dihedralRotations 0)
  exact ⟨x, (key (sr_notMem_dihedralRotations 0) x).mp hx⟩

end Induction

section DihedralFour

private theorem unitI_pow_four : (Units.mk0 Complex.I Complex.I_ne_zero) ^ 4 = 1 :=
  Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact Complex.isPrimitiveRoot_I.pow_eq_one)

/-- **The faithful linear character of the rotation subgroup of `D₄`** sending the rotation `r 1`
to the primitive fourth root of unity `i`. -/
noncomputable def dihedralFourChar : dihedralRotations 4 →* ℂˣ :=
  dihedralRotationChar unitI_pow_four

/-- The value of `TauCeti.dihedralFourChar` at a rotation is the corresponding power of `i`. -/
@[simp]
theorem dihedralFourChar_r (i : ZMod 4) :
    (dihedralFourChar ⟨DihedralGroup.r i, r_mem_dihedralRotations i⟩ : ℂ) = Complex.I ^ i.val := by
  rw [dihedralFourChar, dihedralRotationChar_r, Units.val_pow_eq_pow_val, Units.val_mk0]

/-- `TauCeti.dihedralFourChar` sends the generating rotation to `i`. -/
theorem dihedralFourChar_r_one :
    (dihedralFourChar ⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩ : ℂ) = Complex.I := by
  rw [dihedralFourChar_r, ZMod.val_one_eq_one_mod]
  norm_num

/-- **`TauCeti.dihedralFourChar` is faithful**: `i` is a *primitive* fourth root of unity, so no
nontrivial rotation is sent to `1`. -/
theorem dihedralFourChar_injective : Function.Injective dihedralFourChar := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, hx⟩ h
  obtain ⟨i, rfl⟩ := mem_dihedralRotations_iff.mp hx
  have hI : Complex.I ^ i.val = 1 := by
    rw [← dihedralFourChar_r i, h, Units.val_one]
  have hi : i.val = 0 :=
    Nat.eq_zero_of_dvd_of_lt ((Complex.isPrimitiveRoot_I.pow_eq_one_iff_dvd _).mp hI)
      (ZMod.val_lt i)
  obtain rfl : i = 0 := (ZMod.val_eq_zero i).mp hi
  exact Subtype.ext DihedralGroup.one_def.symm

/-- **The representation of `D₄` induced from a faithful linear character of its rotation subgroup
is irreducible**, by the Mackey criterion: conjugation by a reflection sends `i` to `-i`. -/
theorem simple_indFDRep_dihedralFourChar :
    Simple (indFDRep (FDRep.ofLinearCharacter dihedralFourChar)) := by
  refine (simple_indFDRep_ofLinearCharacter_dihedralRotations_iff dihedralFourChar).mpr
    ⟨⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩, fun hc => ?_⟩
  have h : (Complex.I) ^ 2 = 1 := by
    rw [← dihedralFourChar_r_one, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  rw [Complex.I_sq] at h
  exact absurd h (by norm_num)

/-- **The induced representation of `D₄` is two-dimensional**, so it is *the* two-dimensional
irreducible representation of `D₄`. -/
theorem finrank_indFDRep_dihedralFourChar :
    Module.finrank ℂ (indFDRep (FDRep.ofLinearCharacter dihedralFourChar)) = 2 :=
  finrank_indFDRep_ofLinearCharacter_dihedralRotations dihedralFourChar

end DihedralFour

end TauCeti
