/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import TauCeti.RingTheory.Ideal.OneAdd.Localisation
public import TauCeti.RingTheory.Ideal.Operations

/-!
# The subgroups `1 + I` of the unit group, and their graded pieces

For an ideal `I` of a commutative ring `R`, the units congruent to `1` modulo `I` form a subgroup
`Ideal.oneAddSubgroup I` of `Rˣ`; its elements are exactly the units lying in the submonoid
`Ideal.oneAdd I` of `R`. This file develops that subgroup and computes the successive quotients
of the filtration it defines, which is where the arithmetic content lies:

* if `I` lies in the Jacobson radical, reduction identifies `Rˣ ⧸ (1 + I)` with `(R ⧸ I)ˣ`;
* if moreover `I * I ≤ J`, then `u ↦ u - 1` is a *homomorphism* from `1 + I` to the additive
  group of the image of `I` in `R ⧸ J`, and it identifies `(1 + I) ⧸ (1 + J)` with that additive
  group.

The two statements are genuinely different: the depth-zero quotient is multiplicative and the
deeper ones are additive, the multiplication `(1 + a)(1 + b) = 1 + (a + b + ab)` becoming addition
exactly because the correction term `ab` lies in `I * I ≤ J`.

Specializing to a discrete valuation ring `R` with maximal ideal `𝔪` and residue field `𝓀`, and
to `I = 𝔪 ^ n`, `J = 𝔪 ^ (n + 1)` with `n ≠ 0`, gives the two graded pieces of the unit
filtration together with the indices `[Rˣ : 1 + 𝔪] = #𝓀ˣ` and
`[1 + 𝔪 ^ n : 1 + 𝔪 ^ (n + 1)] = #𝓀`. Mathlib's `IsNonarchimedeanLocalField` supplies
`IsDiscreteValuationRing 𝒪[K]` and `Finite 𝓀[K]`, so those two indices read `q - 1` and `q` at the
integer ring of a nonarchimedean local field.

## Main definitions

* `Ideal.oneAddSubgroup`: the subgroup `1 + I` of `Rˣ`.
* `Ideal.oneAddSubgroupHom`: the homomorphism `u ↦ u - 1` from `1 + I` to the image of `I` in
  `R ⧸ J`, available when `I * I ≤ J`.
* `Ideal.unitsQuotientOneAddSubgroupEquiv`: `Rˣ ⧸ (1 + I) ≃* (R ⧸ I)ˣ`.
* `Ideal.oneAddSubgroupQuotientEquiv`: `(1 + I) ⧸ (1 + J)` is the image of `I` in `R ⧸ J`.
* `IsDiscreteValuationRing.oneAddSubgroupQuotientEquivResidueField`:
  `(1 + 𝔪 ^ n) ⧸ (1 + 𝔪 ^ (n + 1))` is the additive group of the residue field, for `n ≠ 0`.

## Main results

* `Ideal.oneAddSubgroup_eq_ker`: `1 + I` is the kernel of `Rˣ → (R ⧸ I)ˣ`.
* `Ideal.ker_oneAddSubgroupHom` and `Ideal.surjective_oneAddSubgroupHom`: the two halves of the
  graded identification.
* `IsLocalRing.index_oneAddSubgroup_maximalIdeal`: `[Rˣ : 1 + 𝔪] = #𝓀ˣ`.
* `IsDiscreteValuationRing.relIndex_oneAddSubgroup_maximalIdeal_pow`:
  `[1 + 𝔪 ^ n : 1 + 𝔪 ^ (n + 1)] = #𝓀` for `n ≠ 0`.

## Implementation notes

Mathlib's `ValuationSubring.principalUnitGroup` is the case `I = 𝔪` of `Ideal.oneAddSubgroup`,
read inside the fraction field rather than inside `Rˣ`, and
`ValuationSubring.unitsModPrincipalUnitsEquivResidueFieldUnits` is the corresponding depth-zero
quotient; `Ideal.unitsQuotientOneAddSubgroupEquiv` below is that computation for an arbitrary
ideal inside the Jacobson radical of an arbitrary commutative ring; its surjectivity input is
Mathlib's `isLocalHom_of_le_jacobson_bot` together with
`IsLocalRing.surjective_units_map_of_local_ringHom`. The additive identification of
`𝔪 ^ n ⧸ 𝔪 ^ (n + 1)` with the residue field is Mathlib's `Ideal.quotEquivPowQuotPowSucc`, not
reproved here.

The homomorphisms and equivalences built from Mathlib combinators are `@[expose]`d, so that the
characteristic lemmas naming their values hold definitionally.

## References

* J.-P. Serre, *Local Fields*, IV §2.
* J. Neukirch, *Algebraic Number Theory*, II §3 and II §5.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- **The units congruent to `1` modulo `I`.** This is the subgroup `1 + I` of `Rˣ`; membership is
written as `(u : R) - 1 ∈ I`, so that no representative has to be produced. -/
def oneAddSubgroup (I : Ideal R) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    have hab : (a : R) * b - 1 = ((a : R) - 1) * b + ((b : R) - 1) := by ring
    exact hab ▸ I.add_mem (I.mul_mem_right _ ha) hb
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hmul : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hinv : ((a⁻¹ : Rˣ) : R) - 1 = -(((a : R) - 1) * ((a⁻¹ : Rˣ) : R)) := by
      rw [sub_mul, hmul, one_mul]; ring
    exact hinv ▸ I.neg_mem (I.mul_mem_right _ ha)

variable {I J : Ideal R}

@[simp]
theorem mem_oneAddSubgroup {u : Rˣ} : u ∈ I.oneAddSubgroup ↔ (u : R) - 1 ∈ I := Iff.rfl

theorem mem_oneAddSubgroup_iff_val_mem_oneAdd {u : Rˣ} :
    u ∈ I.oneAddSubgroup ↔ (u : R) ∈ I.oneAdd := by
  simp only [mem_oneAddSubgroup, mem_oneAdd]
  refine ⟨fun h ↦ ⟨_, h, by ring⟩, ?_⟩
  rintro ⟨a, ha, h⟩
  simpa [h] using ha

theorem oneAddSubgroup_mono : Monotone (oneAddSubgroup : Ideal R → Subgroup Rˣ) :=
  fun _ _ hIJ _ hu ↦ hIJ hu

@[simp]
theorem oneAddSubgroup_bot : (⊥ : Ideal R).oneAddSubgroup = ⊥ := by
  ext u
  rw [mem_oneAddSubgroup, Ideal.mem_bot, sub_eq_zero, Units.val_eq_one, Subgroup.mem_bot]

@[simp]
theorem oneAddSubgroup_top : (⊤ : Ideal R).oneAddSubgroup = ⊤ := by
  ext u
  simp

/-- `1 + I` is the kernel of reduction `Rˣ → (R ⧸ I)ˣ`. -/
theorem oneAddSubgroup_eq_ker (I : Ideal R) :
    I.oneAddSubgroup = (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker := by
  ext u
  rw [mem_oneAddSubgroup, MonoidHom.mem_ker, Units.ext_iff, Units.val_one, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk I),
    Ideal.Quotient.eq]

section Jacobson

variable (hI : I ≤ jacobson (⊥ : Ideal R))
include hI

/-- Every element of `1 + I` is a unit once `I` lies in the Jacobson radical, so
`Ideal.oneAddSubgroup I` really does exhaust `1 + I`. -/
theorem exists_val_eq_one_add {a : R} (ha : a ∈ I) :
    ∃ u : I.oneAddSubgroup, ((u : Rˣ) : R) = 1 + a := by
  have hu : IsUnit (1 + a) := isUnit_of_sub_one_mem_jacobson_bot _ (by simpa using hI ha)
  exact ⟨⟨hu.unit, by simpa [hu.unit_spec] using ha⟩, hu.unit_spec⟩

/-- **Reduction is surjective on units.** For `I` inside the Jacobson radical every unit of
`R ⧸ I` lifts to a unit of `R`. -/
theorem surjective_units_map_quotient_mk :
    Function.Surjective (Units.map (Ideal.Quotient.mk I).toMonoidHom) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (isLocalHom_of_le_jacobson_bot I hI)

/-- **The depth-zero graded piece.** Reduction identifies `Rˣ ⧸ (1 + I)` with `(R ⧸ I)ˣ`. -/
@[expose]
noncomputable def unitsQuotientOneAddSubgroupEquiv : Rˣ ⧸ I.oneAddSubgroup ≃* (R ⧸ I)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (oneAddSubgroup_eq_ker I)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_units_map_quotient_mk hI))

@[simp]
theorem unitsQuotientOneAddSubgroupEquiv_mk (u : Rˣ) :
    unitsQuotientOneAddSubgroupEquiv hI (QuotientGroup.mk u) =
      Units.map (Ideal.Quotient.mk I).toMonoidHom u := rfl

theorem index_oneAddSubgroup : I.oneAddSubgroup.index = Nat.card (R ⧸ I)ˣ := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (unitsQuotientOneAddSubgroupEquiv hI).toEquiv

end Jacobson

section Graded

/-- **Multiplication in `1 + I` is addition modulo `J`**, as soon as `I * I ≤ J`: the correction
term in `(1 + a)(1 + b) = 1 + (a + b + ab)` lies in `I * I`. -/
theorem quotient_mk_mul_sub_one (h : I * I ≤ J) {a b : Rˣ}
    (ha : a ∈ I.oneAddSubgroup) (hb : b ∈ I.oneAddSubgroup) :
    Ideal.Quotient.mk J (((a * b : Rˣ) : R) - 1) =
      Ideal.Quotient.mk J ((a : R) - 1) + Ideal.Quotient.mk J ((b : R) - 1) := by
  rw [← map_add, Ideal.Quotient.eq, Units.val_mul]
  have hexp : (a : R) * (b : R) - 1 - (((a : R) - 1) + ((b : R) - 1)) =
      ((a : R) - 1) * ((b : R) - 1) := by ring
  rw [hexp]
  exact h (Ideal.mul_mem_mul ha hb)

/-- **The graded map `u ↦ u - 1`.** When `I * I ≤ J`, sending a unit `u ≡ 1 mod I` to the class of
`u - 1` in `R ⧸ J` turns multiplication into addition. Its values lie in the image of `I`. -/
@[expose]
def oneAddSubgroupHom (I J : Ideal R) (h : I * I ≤ J) :
    I.oneAddSubgroup →* Multiplicative (I.map (Ideal.Quotient.mk J)) :=
  MonoidHom.mk'
    (fun u ↦ Multiplicative.ofAdd ⟨Ideal.Quotient.mk J (((u : Rˣ) : R) - 1),
      Ideal.mem_map_of_mem _ (mem_oneAddSubgroup.mp u.2)⟩)
    fun a b ↦ by
      rw [← ofAdd_add]
      exact congrArg Multiplicative.ofAdd (Subtype.ext (quotient_mk_mul_sub_one h a.2 b.2))

@[simp]
theorem oneAddSubgroupHom_apply_coe (h : I * I ≤ J) (u : I.oneAddSubgroup) :
    ((Multiplicative.toAdd (oneAddSubgroupHom I J h u) :
        I.map (Ideal.Quotient.mk J)) : R ⧸ J) =
      Ideal.Quotient.mk J (((u : Rˣ) : R) - 1) := rfl

theorem oneAddSubgroupHom_eq_one_iff (h : I * I ≤ J) (u : I.oneAddSubgroup) :
    oneAddSubgroupHom I J h u = 1 ↔ ((u : Rˣ) : R) - 1 ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← oneAddSubgroupHom_apply_coe h u]
  exact ⟨fun hu ↦ by rw [hu]; rfl, fun hu ↦ Multiplicative.toAdd.injective (Subtype.ext hu)⟩

/-- The kernel of `u ↦ u - 1` is the next step `1 + J` of the filtration. -/
theorem ker_oneAddSubgroupHom (h : I * I ≤ J) :
    (oneAddSubgroupHom I J h).ker = J.oneAddSubgroup.subgroupOf I.oneAddSubgroup := by
  ext u
  rw [MonoidHom.mem_ker, oneAddSubgroupHom_eq_one_iff, Subgroup.mem_subgroupOf,
    mem_oneAddSubgroup]

theorem surjective_oneAddSubgroupHom (h : I * I ≤ J) (hI : I ≤ jacobson (⊥ : Ideal R)) :
    Function.Surjective (oneAddSubgroupHom I J h) := by
  intro y
  obtain ⟨a, ha, hay⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
    (Multiplicative.toAdd y).2
  obtain ⟨u, hu⟩ := exists_val_eq_one_add hI ha
  refine ⟨u, Multiplicative.toAdd.injective (Subtype.ext ?_)⟩
  rw [oneAddSubgroupHom_apply_coe, hu, add_sub_cancel_left, hay]

/-- **The deeper graded pieces.** For `I * I ≤ J` with `I` inside the Jacobson radical, `u ↦ u - 1`
identifies `(1 + I) ⧸ (1 + J)` with the additive group of the image of `I` in `R ⧸ J`. -/
@[expose]
noncomputable def oneAddSubgroupQuotientEquiv (h : I * I ≤ J)
    (hI : I ≤ jacobson (⊥ : Ideal R)) :
    I.oneAddSubgroup ⧸ J.oneAddSubgroup.subgroupOf I.oneAddSubgroup ≃*
      Multiplicative (I.map (Ideal.Quotient.mk J)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_oneAddSubgroupHom h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (surjective_oneAddSubgroupHom h hI))

@[simp]
theorem oneAddSubgroupQuotientEquiv_mk (h : I * I ≤ J) (hI : I ≤ jacobson (⊥ : Ideal R))
    (u : I.oneAddSubgroup) :
    oneAddSubgroupQuotientEquiv h hI (QuotientGroup.mk u) = oneAddSubgroupHom I J h u := rfl

end Graded

end Ideal

namespace IsLocalRing

open Ideal

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The index of `1 + 𝔪` in `Rˣ` is the number of units of the residue field, that is `q - 1` when
the residue field is finite of order `q`. -/
theorem index_oneAddSubgroup_maximalIdeal :
    (maximalIdeal R).oneAddSubgroup.index = Nat.card (ResidueField R)ˣ :=
  Ideal.index_oneAddSubgroup (maximalIdeal_le_jacobson _)

end IsLocalRing

namespace IsDiscreteValuationRing

open Ideal IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The deeper graded pieces of the unit filtration of a discrete valuation ring.** For `n ≠ 0`
the quotient `(1 + 𝔪 ^ n) ⧸ (1 + 𝔪 ^ (n + 1))` is the additive group of the residue field; the
identification of `𝔪 ^ n ⧸ 𝔪 ^ (n + 1)` with the residue field is Mathlib's
`Ideal.quotEquivPowQuotPowSucc`. -/
noncomputable def oneAddSubgroupQuotientEquivResidueField {n : ℕ} (hn : n ≠ 0) :
    (maximalIdeal R ^ n).oneAddSubgroup ⧸
        (maximalIdeal R ^ (n + 1)).oneAddSubgroup.subgroupOf
          (maximalIdeal R ^ n).oneAddSubgroup ≃*
      Multiplicative (ResidueField R) :=
  (Ideal.oneAddSubgroupQuotientEquiv (Ideal.pow_mul_pow_le_pow_succ _ hn)
      ((Ideal.pow_le_self hn).trans (maximalIdeal_le_jacobson _))).trans
    (AddEquiv.toMultiplicative
      (((Ideal.quotEquivPowQuotPowSucc (IsPrincipalIdealRing.principal (maximalIdeal R))
          IsDiscreteValuationRing.not_a_field' n).trans
        (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow (maximalIdeal R) n)).toAddEquiv)).symm

/-- The index of `1 + 𝔪 ^ (n + 1)` in `1 + 𝔪 ^ n` is the order of the residue field. -/
theorem relIndex_oneAddSubgroup_maximalIdeal_pow {n : ℕ} (hn : n ≠ 0) :
    (maximalIdeal R ^ (n + 1)).oneAddSubgroup.relIndex (maximalIdeal R ^ n).oneAddSubgroup =
      Nat.card (ResidueField R) := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_congr
    ((oneAddSubgroupQuotientEquivResidueField R hn).toEquiv.trans Multiplicative.toAdd)

end IsDiscreteValuationRing
