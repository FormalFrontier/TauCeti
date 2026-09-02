/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The Teichmüller lift of a Henselian local ring with finite residue field

Let `R` be a Henselian local ring whose residue field `k` is finite, of cardinality `q`. Reduction
`Rˣ → kˣ` then has a canonical multiplicative section: over each `x : kˣ` there is exactly one
`q - 1`-st root of unity of `R`, because `X ^ (q - 1) - 1` has `x` as a simple root over `k`. That
section is the *Teichmüller lift* `teichmuller R : kˣ →* Rˣ`, and it identifies `kˣ` with the group
`μ_{q-1}(R)` of `q - 1`-st roots of unity of `R`.

The whole construction is Hensel's lemma applied to `X ^ (q - 1) - 1`: existence is
`HenselianLocalRing.is_henselian` and uniqueness is
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`, the two halves of the simple-root lifting
property. Multiplicativity of the section is then forced, since a product of two roots of unity
lifting `x` and `y` is a root of unity lifting `x * y`.

Mathlib's `Perfection.teichmuller₀` is a different construction of a related map: it needs `R` to
be adically complete and produces a map out of the perfection of `R ⧸ I`, with no uniqueness
statement and no description of its image. The characterization and the identification of the image
below are the content of this milestone, and they are the simple-root uniqueness of
`X ^ (q - 1) - 1`, so nothing is gained by routing the construction through the perfection; the
Henselian hypothesis used here is also weaker than adic completeness.

The hypotheses hold for the integers `𝒪[K]` of a nonarchimedean local field `K`: Mathlib's
`IsNonarchimedeanLocalField` provides `IsAdicComplete 𝓂[K] 𝒪[K]`, hence `HenselianLocalRing 𝒪[K]`
through `TauCeti.IsAdicComplete.henselianLocalRing`, together with `Finite 𝓀[K]`.

## Main results

* `TauCeti.IsLocalRing.existsUnique_pow_card_sub_one_eq_one_and_residue_eq`: over each unit of the
  residue field lies exactly one `q - 1`-st root of unity of `R`.
* `TauCeti.IsLocalRing.teichmuller`: the Teichmüller lift `kˣ →* Rˣ`.
* `TauCeti.IsLocalRing.teichmuller_eq_iff`: the characterization of its values.
* `TauCeti.IsLocalRing.eq_teichmuller`: it is the only multiplicative section of reduction whose
  values are `q - 1`-st roots of unity.
* `TauCeti.IsLocalRing.range_teichmuller`: its image is exactly `μ_{q-1}(R)`.
* `TauCeti.IsLocalRing.rootsOfUnityMulEquivUnitsResidueField`: reduction is an isomorphism
  `μ_{q-1}(R) ≃* kˣ`.
* `TauCeti.IsLocalRing.card_rootsOfUnity`: consequently `μ_{q-1}(R)` has exactly `q - 1` elements.

## References

* J.-P. Serre, *Corps Locaux*, II §4.
* J. Neukirch, *Algebraic Number Theory*, II §5.
-/

public section

namespace TauCeti.IsLocalRing

open Polynomial _root_.IsLocalRing

variable (R : Type*) [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]

/-- Over a Henselian local ring with finite residue field of cardinality `q`, each unit `x` of the
residue field is the residue of exactly one solution of `y ^ (q - 1) = 1`. -/
theorem existsUnique_pow_card_sub_one_eq_one_and_residue_eq (x : (ResidueField R)ˣ) :
    ∃! y : R, y ^ (Nat.card (ResidueField R) - 1) = 1 ∧ residue R y = x := by
  have := Fintype.ofFinite (ResidueField R)
  have hcard : Nat.card (ResidueField R) = Fintype.card (ResidueField R) := Nat.card_eq_fintype_card
  set n := Nat.card (ResidueField R) - 1 with hn
  have hn0 : n ≠ 0 := by
    have := Fintype.one_lt_card (α := ResidueField R)
    omega
  set f : R[X] := X ^ n - 1 with hf
  have hfmonic : f.Monic := by simpa [hf] using monic_X_pow_sub_C (1 : R) hn0
  have heval : ∀ a : R, eval a f = a ^ n - 1 := by intro a; simp [hf]
  have hderiv : ∀ a : R, eval a (derivative f) = (n : R) * a ^ (n - 1) := by
    intro a; simp [hf, derivative_X_pow]
  -- `q = 0` in the residue field, so the leading coefficient `q - 1` of the derivative is `-1`
  have hcast : ((n : ℕ) : ResidueField R) = -1 := by
    rw [hn, hcard, Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero]
    simp
  -- hence every lift of a unit of the residue field is a simple root of `f` modulo `𝔪`
  have hunit : ∀ a : R, residue R a = (x : ResidueField R) → IsUnit (eval a (derivative f)) := by
    intro a ha
    rw [← residue_ne_zero_iff_isUnit, hderiv, map_mul, map_pow, ha, map_natCast, hcast]
    simp [x.ne_zero]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : R, residue R a₀ = (x : ResidueField R) :=
    Ideal.Quotient.mk_surjective _
  obtain ⟨a, haroot, hasub⟩ :=
    HenselianLocalRing.is_henselian f hfmonic a₀ (by
      rw [← residue_eq_zero_iff, heval, map_sub, map_pow, ha₀, map_one, hn, hcard,
        FiniteField.pow_card_sub_one_eq_one _ x.ne_zero, sub_self]) (hunit a₀ ha₀)
  have haresidue : residue R a = (x : ResidueField R) := by
    have h : residue R (a - a₀) = 0 := (residue_eq_zero_iff _).2 hasub
    rw [map_sub, sub_eq_zero] at h
    rw [h, ha₀]
  refine ⟨a, ⟨?_, haresidue⟩, ?_⟩
  · rw [← sub_eq_zero, ← heval]
    exact haroot
  · rintro b ⟨hb1, hb2⟩
    refine _root_.IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f) ?_ haroot ?_
      (hunit b hb2)
    · rw [heval, hb1, sub_self]
    · rw [← residue_ne_zero_iff_isUnit, map_sub, hb2, haresidue, sub_self]
      simp

private theorem existsUnique_units_pow_card_sub_one_eq_one (x : (ResidueField R)ˣ) :
    ∃! u : Rˣ, u ^ (Nat.card (ResidueField R) - 1) = 1 ∧ residue R (u : R) = x := by
  obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := existsUnique_pow_card_sub_one_eq_one_and_residue_eq R x
  have hyu : IsUnit y := (residue_ne_zero_iff_isUnit y).1 (by rw [hy2]; exact x.ne_zero)
  refine ⟨hyu.unit, ⟨Units.ext (by simpa using hy1), by simpa using hy2⟩, ?_⟩
  rintro v ⟨hv1, hv2⟩
  refine Units.ext ?_
  rw [IsUnit.unit_spec]
  exact hy3 _ ⟨by rw [← Units.val_pow_eq_pow_val, hv1, Units.val_one], hv2⟩

private noncomputable def teichmullerFun (x : (ResidueField R)ˣ) : Rˣ :=
  (existsUnique_units_pow_card_sub_one_eq_one R x).choose

private theorem teichmullerFun_spec (x : (ResidueField R)ˣ) :
    teichmullerFun R x ^ (Nat.card (ResidueField R) - 1) = 1 ∧
      residue R (teichmullerFun R x : R) = x :=
  (existsUnique_units_pow_card_sub_one_eq_one R x).choose_spec.1

private theorem teichmullerFun_eq {x : (ResidueField R)ˣ} {u : Rˣ}
    (h1 : u ^ (Nat.card (ResidueField R) - 1) = 1) (h2 : residue R (u : R) = x) :
    teichmullerFun R x = u :=
  (existsUnique_units_pow_card_sub_one_eq_one R x).unique (teichmullerFun_spec R x) ⟨h1, h2⟩

/-- The **Teichmüller lift** of a Henselian local ring `R` with finite residue field `k` of
cardinality `q`: the multiplicative section of reduction `Rˣ → kˣ` that sends `x` to the unique
`q - 1`-st root of unity of `R` above `x`. -/
noncomputable def teichmuller : (ResidueField R)ˣ →* Rˣ where
  toFun := teichmullerFun R
  map_one' := teichmullerFun_eq R (one_pow _) (by simp)
  map_mul' x y := by
    refine teichmullerFun_eq R ?_ ?_
    · rw [mul_pow, (teichmullerFun_spec R x).1, (teichmullerFun_spec R y).1, one_mul]
    · rw [Units.val_mul, map_mul, (teichmullerFun_spec R x).2, (teichmullerFun_spec R y).2]
      simp

/-- The Teichmüller lift takes its values in the `q - 1`-st roots of unity. -/
@[simp] theorem teichmuller_pow_card_sub_one (x : (ResidueField R)ˣ) :
    teichmuller R x ^ (Nat.card (ResidueField R) - 1) = 1 := (teichmullerFun_spec R x).1

/-- The Teichmüller lift is a section of reduction. -/
@[simp] theorem residue_teichmuller (x : (ResidueField R)ˣ) :
    residue R (teichmuller R x : R) = x := (teichmullerFun_spec R x).2

/-- The Teichmüller lift is a section of reduction, read in the unit group of the residue field. -/
@[simp] theorem unitsMap_residue_teichmuller (x : (ResidueField R)ˣ) :
    Units.map (residue R : R →* ResidueField R) (teichmuller R x) = x :=
  Units.ext (by simp)

/-- The Teichmüller lift of `x` is the unique root of unity of order dividing `q - 1` above `x`. -/
theorem teichmuller_eq_iff {x : (ResidueField R)ˣ} {u : Rˣ} :
    teichmuller R x = u ↔
      u ^ (Nat.card (ResidueField R) - 1) = 1 ∧ residue R (u : R) = x := by
  refine ⟨?_, fun h => teichmullerFun_eq R h.1 h.2⟩
  rintro rfl
  exact ⟨teichmuller_pow_card_sub_one R x, residue_teichmuller R x⟩

/-- The Teichmüller lift is injective, being a section of reduction. -/
theorem teichmuller_injective : Function.Injective (teichmuller R) := fun x y h =>
  Units.ext (by rw [← residue_teichmuller R x, h, residue_teichmuller])

/-- The Teichmüller lift is the only multiplicative section of reduction all of whose values are
`q - 1`-st roots of unity. -/
theorem eq_teichmuller (s : (ResidueField R)ˣ →* Rˣ) (hsec : ∀ x, residue R (s x : R) = x)
    (htor : ∀ x, s x ^ (Nat.card (ResidueField R) - 1) = 1) : s = teichmuller R :=
  MonoidHom.ext fun x => ((teichmuller_eq_iff R).2 ⟨htor x, hsec x⟩).symm

/-- The image of the Teichmüller lift is the group `μ_{q-1}(R)` of `q - 1`-st roots of unity. -/
theorem range_teichmuller :
    (teichmuller R).range = rootsOfUnity (Nat.card (ResidueField R) - 1) R := by
  ext u
  simp only [MonoidHom.mem_range, mem_rootsOfUnity]
  refine ⟨?_, fun h => ⟨Units.map (residue R : R →* ResidueField R) u, ?_⟩⟩
  · rintro ⟨x, rfl⟩
    exact teichmuller_pow_card_sub_one R x
  · exact teichmullerFun_eq R h (by simp)

/-- Reduction is an isomorphism from the group `μ_{q-1}(R)` of `q - 1`-st roots of unity of `R`
onto the unit group of the residue field, with the Teichmüller lift as its inverse. -/
noncomputable def rootsOfUnityMulEquivUnitsResidueField :
    rootsOfUnity (Nat.card (ResidueField R) - 1) R ≃* (ResidueField R)ˣ :=
  MonoidHom.toMulEquiv
    ((Units.map (residue R : R →* ResidueField R)).comp
      (rootsOfUnity (Nat.card (ResidueField R) - 1) R).subtype)
    ((teichmuller R).codRestrict _ fun x =>
      (mem_rootsOfUnity _ _).2 (teichmuller_pow_card_sub_one R x))
    (by
      ext u
      exact congrArg Units.val (teichmullerFun_eq R ((mem_rootsOfUnity _ _).1 u.2) (by simp)))
    (by ext x; simp)

@[simp] theorem coe_rootsOfUnityMulEquivUnitsResidueField
    (u : rootsOfUnity (Nat.card (ResidueField R) - 1) R) :
    (rootsOfUnityMulEquivUnitsResidueField R u : ResidueField R) = residue R (u : Rˣ) := (rfl)

@[simp] theorem rootsOfUnityMulEquivUnitsResidueField_symm_apply (x : (ResidueField R)ˣ) :
    ((rootsOfUnityMulEquivUnitsResidueField R).symm x : Rˣ) = teichmuller R x := (rfl)

/-- A Henselian local ring with residue field of cardinality `q` has exactly `q - 1` roots of unity
of order dividing `q - 1`, as many as the residue field has units. -/
theorem card_rootsOfUnity :
    Nat.card (rootsOfUnity (Nat.card (ResidueField R) - 1) R) =
      Nat.card (ResidueField R) - 1 := by
  rw [Nat.card_congr (rootsOfUnityMulEquivUnitsResidueField R).toEquiv, Nat.card_units]

end TauCeti.IsLocalRing
