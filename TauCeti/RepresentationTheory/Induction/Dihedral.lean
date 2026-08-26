/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.RepresentationTheory.Induction.Mackey.Irreducible
public import TauCeti.RepresentationTheory.LinearCharacter

/-!
# Inducing a linear character from the rotation subgroup of a dihedral group

The dihedral group `DihedralGroup n` has an abelian rotation subgroup of index `2`, so every
representation induced from it has twice the dimension it was induced from. Inducing a **linear**
character `ψ` of the rotations therefore produces a two-dimensional representation, and this file
settles when it is irreducible: exactly when `ψ` is not its own inverse.

The criterion is the Mackey irreducibility criterion for a normal subgroup
(`TauCeti.simple_indFDRep_iff_of_normal`), which asks that no conjugate `{}^s ψ` with `s` outside
the subgroup be isomorphic to `ψ`. For the dihedral group the conjugation is completely explicit:
by `TauCeti.inv_mul_mul_of_notMem_dihedralRotations` an element outside the rotation subgroup
inverts every rotation, so `{}^s ψ = ψ⁻¹` for *every* such `s`, and the criterion collapses to the
single condition `ψ ≠ ψ⁻¹`, that some value of `ψ` is not a square root of `1`. Because a linear
character is determined by the representation it carries, the condition is not only sufficient but
necessary, and the result is an `iff`.

The concrete instance the roadmap asks for is `n = 4`: the character sending the rotation `r 1` of
`D₄` to `i` has `ψ(r 1)² = -1 ≠ 1`, so it induces the two-dimensional irreducible representation
of `D₄`.

## Main definitions

* `TauCeti.dihedralRotationChar`: the linear character of the rotation subgroup sending `r i` to
  `ζ ^ i`, for `ζ` an `n`-th root of unity.
* `TauCeti.dihedralFourChar`: the faithful linear character of the rotation subgroup of `D₄`
  sending `r 1` to `i`.

## Main statements

* `TauCeti.simple_indFDRep_ofLinearChar_dihedralRotations_iff`: **inducing a linear character of
  the rotation subgroup is irreducible exactly when the character is not its own inverse.**
* `TauCeti.finrank_indFDRep_ofLinearChar_dihedralRotations`: the induced representation is
  two-dimensional.
* `TauCeti.dihedralFourChar_injective`: that character is faithful.
* `TauCeti.simple_indFDRep_dihedralFourChar`: **the two-dimensional irreducible representation of
  `D₄` is induced from a faithful linear character of its rotation subgroup**, the Mackey criterion
  certifying the irreducibility.

## Implementation notes

`TauCeti.dihedralRotationChar` reads the exponent through `ZMod.val`, so that its values are
natural-number powers of `ζ`; multiplicativity is then the statement that the exponent may be
reduced modulo `n`, which is `TauCeti.pow_mod_of_pow_eq_one`. Taking `ζ` in an arbitrary monoid
costs nothing and keeps the construction independent of the coefficient field.

The coefficient field of the irreducibility criterion is constrained to `Type` rather than `Type*`:
`TauCeti.simple_indFDRep_iff_of_normal` places the field and the group in a common universe, and
`DihedralGroup n` lives in `Type`.

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

/-- A power of a root of unity depends only on the exponent modulo the exponent that annihilates
it. Mathlib's `pow_mod_orderOf` is the case `n = orderOf ζ`; here `n` is any exponent with
`ζ ^ n = 1`, which is what the `ZMod n` indexing of the dihedral rotations hands over. -/
theorem pow_mod_of_pow_eq_one (hζ : ζ ^ n = 1) (m : ℕ) : ζ ^ (m % n) = ζ ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

variable [NeZero n]

/-- **The linear character of the rotation subgroup attached to an `n`-th root of unity** `ζ`:
the rotation `r i` is sent to `ζ ^ i`, the exponent being the canonical representative of `i` in
`ZMod n`. -/
def dihedralRotationChar (hζ : ζ ^ n = 1) : dihedralRotations n →* M where
  toFun x := ζ ^ (dihedralRotIdx (x : DihedralGroup n)).val
  map_one' := by
    change ζ ^ (dihedralRotIdx (1 : DihedralGroup n)).val = 1
    rw [DihedralGroup.one_def, dihedralRotIdx_r, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    change ζ ^ (dihedralRotIdx ((x : DihedralGroup n) * (y : DihedralGroup n))).val = _
    rw [dihedralRotIdx_mul x.2 y.2, ZMod.val_add, pow_mod_of_pow_eq_one hζ, pow_add]

@[simp]
theorem dihedralRotationChar_apply (hζ : ζ ^ n = 1) (i : ZMod n) :
    dihedralRotationChar hζ ⟨DihedralGroup.r i, r_mem_dihedralRotations i⟩ = ζ ^ i.val := by
  change ζ ^ (dihedralRotIdx (DihedralGroup.r i)).val = _
  rw [dihedralRotIdx_r]

end RotationChar

section Conjugation

variable {M : Type*} [Group M] {n : ℕ}

/-- **Conjugating a character of the rotation subgroup by a reflection inverts it**: `{}^s ψ = ψ⁻¹`
for every `s` outside the rotation subgroup. This is
`TauCeti.inv_mul_mul_of_notMem_dihedralRotations` transported along `ψ`, and it is why the Mackey
criterion below reads off a single condition on `ψ`. -/
theorem apply_conjNormal_of_notMem_dihedralRotations (ψ : dihedralRotations n →* M)
    {s : DihedralGroup n} (hs : s ∉ dihedralRotations n) (x : dihedralRotations n) :
    ψ (MulAut.conjNormal s⁻¹ x) = (ψ x)⁻¹ := by
  have hx : MulAut.conjNormal s⁻¹ x = x⁻¹ := by
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, inv_inv]
    exact inv_mul_mul_of_notMem_dihedralRotations hs x.2
  rw [hx, map_inv]

end Conjugation

section Induction

variable {k : Type} [Field k] {n : ℕ} [NeZero n]

/-- **The induced representation is two-dimensional**: the rotation subgroup has index `2` and a
linear character is one-dimensional. -/
theorem finrank_indFDRep_ofLinearChar_dihedralRotations (ψ : dihedralRotations n →* kˣ) :
    Module.finrank k (indFDRep (FDRep.of (Representation.ofLinearChar ψ))) = 2 := by
  rw [finrank_indFDRep, index_dihedralRotations]
  simp

variable [IsAlgClosed k] [CharZero k]

/-- **Inducing a linear character of the rotation subgroup of a dihedral group is irreducible
exactly when the character is not its own inverse.** Conjugation by any reflection inverts the
character, so the Mackey criterion for the normal rotation subgroup asks precisely that `ψ⁻¹ ≠ ψ`,
which is that some value of `ψ` fails to square to `1`. -/
theorem simple_indFDRep_ofLinearChar_dihedralRotations_iff (ψ : dihedralRotations n →* kˣ) :
    Simple (indFDRep (FDRep.of (Representation.ofLinearChar ψ))) ↔ ∃ x, ψ x ^ 2 ≠ 1 := by
  rw [simple_indFDRep_iff_of_normal]
  constructor
  · rintro ⟨-, h⟩
    by_contra hc
    push Not at hc
    -- Every value of `ψ` squares to `1`, so the conjugate character is `ψ` again and the
    -- conjugate representation is literally the same object.
    refine (h (DihedralGroup.sr 0) (sr_notMem_dihedralRotations 0)).false (eqToIso ?_)
    have hψ : ψ.comp (MulAut.conjNormal (DihedralGroup.sr (0 : ZMod n))⁻¹ :
        MulAut (dihedralRotations n)).toMonoidHom = ψ :=
      MonoidHom.ext fun x => by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          apply_conjNormal_of_notMem_dihedralRotations ψ (sr_notMem_dihedralRotations 0) x,
          inv_eq_iff_mul_eq_one, ← sq]
        exact hc x
    change FDRep.of ((Representation.ofLinearChar ψ).comp _) = _
    rw [Representation.ofLinearChar_comp, hψ]
  · rintro ⟨x, hx⟩
    refine ⟨inferInstance, fun s hs => ⟨fun e => hx ?_⟩⟩
    -- The conjugate object is the representation of the conjugate character, and isomorphic
    -- linear characters are equal.
    have hobj : conjNormalFDRep s (FDRep.of (Representation.ofLinearChar ψ)) =
        FDRep.of (Representation.ofLinearChar (ψ.comp
          (MulAut.conjNormal s⁻¹ : MulAut (dihedralRotations n)).toMonoidHom)) := by
      change FDRep.of ((Representation.ofLinearChar ψ).comp _) = _
      rw [Representation.ofLinearChar_comp]
    have hcomp := congrArg (fun φ : dihedralRotations n →* kˣ => φ x)
      (Representation.eq_of_nonempty_iso_ofLinearChar ⟨eqToIso hobj.symm ≪≫ e⟩)
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      apply_conjNormal_of_notMem_dihedralRotations ψ hs x] at hcomp
    rw [sq, ← inv_eq_iff_mul_eq_one]
    exact hcomp

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
theorem dihedralFourChar_r (i : ZMod 4) :
    (dihedralFourChar ⟨DihedralGroup.r i, r_mem_dihedralRotations i⟩ : ℂ) = Complex.I ^ i.val := by
  rw [dihedralFourChar, dihedralRotationChar_apply, Units.val_pow_eq_pow_val]
  rfl

/-- `TauCeti.dihedralFourChar` sends the generating rotation to `i`. -/
theorem dihedralFourChar_r_one :
    (dihedralFourChar ⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩ : ℂ) = Complex.I := by
  rw [dihedralFourChar_r, show (1 : ZMod 4).val = 1 from rfl, pow_one]

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
    Simple (indFDRep (FDRep.of (Representation.ofLinearChar dihedralFourChar))) := by
  refine (simple_indFDRep_ofLinearChar_dihedralRotations_iff dihedralFourChar).mpr
    ⟨⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩, fun hc => ?_⟩
  have h : (Complex.I) ^ 2 = 1 := by
    rw [← dihedralFourChar_r_one, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  rw [Complex.I_sq] at h
  exact absurd h (by norm_num)

/-- **The induced representation of `D₄` is two-dimensional**, so it is *the* two-dimensional
irreducible representation of `D₄`. -/
theorem finrank_indFDRep_dihedralFourChar :
    Module.finrank ℂ (indFDRep (FDRep.of (Representation.ofLinearChar dihedralFourChar))) = 2 :=
  finrank_indFDRep_ofLinearChar_dihedralRotations dihedralFourChar

end DihedralFour

end TauCeti
