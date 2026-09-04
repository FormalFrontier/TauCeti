/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic
public import TauCeti.FieldTheory.SquareClassGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Multiplicative square classes

This file relates the literal quotient `Kˣ ⧸ (Kˣ)²` to the additive square-class group used by
the multiquadratic development. The multiplicative quotient is convenient for products and for
cardinality formulas, while `SquareClassGroup K` carries the canonical `ZMod 2`-module structure.
The comparison with `ElementaryTwoQuotient Kˣ` reuses the generic functorial quotient developed
for commutative groups.

Both presentations are functorial in field homomorphisms. Their canonical equivalence identifies
the class of a unit on the multiplicative side with `squareClass` on the additive side, so results
may move between the two conventions without choosing representatives.

## Main definitions and results

* `TauCeti.MultiplicativeSquareClassGroup`: the literal quotient `Kˣ ⧸ (Kˣ)²`.
* `TauCeti.multiplicativeSquareClassEquiv`: its canonical multiplicative equivalence with
  `Multiplicative (SquareClassGroup K)`.
* `TauCeti.elementaryTwoQuotientEquivSquareClassGroup`: the `ZMod 2`-linear comparison with the
  generic elementary-two quotient.
* `TauCeti.multiplicativeSquareClassMap` and `TauCeti.squareClassMap`: pushforward of square
  classes along a field homomorphism, in the two conventions.
* `TauCeti.natCard_multiplicativeSquareClassGroup`: equality of the cardinalities of the two
  presentations.
-/

public section

namespace TauCeti

variable {K L F : Type*} [Field K] [Field L] [Field F]

/-- The multiplicative square-class group, as the literal quotient of the unit group by its
subgroup of squares. -/
abbrev MultiplicativeSquareClassGroup (K : Type*) [Field K] : Type _ :=
  Kˣ ⧸ Subgroup.square Kˣ

private theorem square_le_comap_unitsMap (f : K →+* L) :
    Subgroup.square Kˣ ≤ (Subgroup.square Lˣ).comap (Units.map f.toMonoidHom) := by
  intro u hu
  exact hu.map (Units.map f.toMonoidHom)

private theorem squareClassHom_surjective :
    Function.Surjective (squareClassHom (K := K)) := by
  intro x
  obtain ⟨u, rfl⟩ :=
    (QuotientAddGroup.mk'_surjective (Subgroup.square Kˣ).toAddSubgroup) x
  refine ⟨Additive.toMul u, ?_⟩
  rw [squareClassHom_apply, squareClass_def]
  rfl

private theorem squareClassHom_ker :
    (squareClassHom (K := K)).ker = Subgroup.square Kˣ := by
  ext u
  simp only [MonoidHom.mem_ker, squareClassHom_apply, ofAdd_eq_one,
    squareClass_eq_zero_iff, Subgroup.mem_square]

/-- The canonical equivalence from the literal multiplicative quotient of units by squares to
the multiplicative form of the additive square-class group. -/
noncomputable def multiplicativeSquareClassEquiv :
    MultiplicativeSquareClassGroup K ≃* Multiplicative (SquareClassGroup K) :=
  QuotientGroup.liftEquiv (G := Kˣ) (H := Multiplicative (SquareClassGroup K))
    (Subgroup.square Kˣ) (squareClassHom_surjective (K := K))
      (squareClassHom_ker (K := K)).symm

/-- The canonical equivalence sends the class of a unit to its additive square class. -/
@[simp]
theorem multiplicativeSquareClassEquiv_mk (u : Kˣ) :
    multiplicativeSquareClassEquiv (QuotientGroup.mk u) =
      Multiplicative.ofAdd (squareClass u) := by
  rw [multiplicativeSquareClassEquiv, QuotientGroup.liftEquiv_mk, squareClassHom_apply]

/-- A unit has trivial class in the multiplicative square-class group if and only if it is a
square. -/
@[simp]
theorem multiplicativeSquareClass_mk_eq_one_iff (u : Kˣ) :
    (QuotientGroup.mk u : MultiplicativeSquareClassGroup K) = 1 ↔ IsSquare u := by
  rw [← (multiplicativeSquareClassEquiv (K := K)).injective.eq_iff,
    multiplicativeSquareClassEquiv_mk, map_one, ofAdd_eq_one, squareClass_eq_zero_iff]

/-- The generic elementary-two quotient of the unit group is canonically `ZMod 2`-linearly
equivalent to the square-class group. -/
noncomputable def elementaryTwoQuotientEquivSquareClassGroup :
    ElementaryTwoQuotient Kˣ ≃ₗ[ZMod 2] SquareClassGroup K :=
  LinearEquiv.ofBijective
    ((elementaryTwoQuotientEquivSquareQuotient Kˣ).toAddMonoidHom.toZModLinearMap 2)
    (by
      simpa only [AddMonoidHom.coe_toZModLinearMap, AddEquiv.coe_toAddMonoidHom] using
        (elementaryTwoQuotientEquivSquareQuotient Kˣ).bijective)

/-- The generic elementary-two class of a unit corresponds to its square class. -/
@[simp]
theorem elementaryTwoQuotientEquivSquareClassGroup_mk (u : Kˣ) :
    elementaryTwoQuotientEquivSquareClassGroup (elementaryTwoQuotientMk u) = squareClass u := by
  rw [elementaryTwoQuotientEquivSquareClassGroup, LinearEquiv.ofBijective_apply,
    AddMonoidHom.coe_toZModLinearMap]
  simpa only [AddEquiv.coe_toAddMonoidHom, squareClass_def] using
    elementaryTwoQuotientEquivSquareQuotient_mk Kˣ u

/-- Pushforward on multiplicative square classes along a field homomorphism. -/
def multiplicativeSquareClassMap (f : K →+* L) :
    MultiplicativeSquareClassGroup K →* MultiplicativeSquareClassGroup L :=
  QuotientGroup.map (Subgroup.square Kˣ) (Subgroup.square Lˣ)
    (Units.map f.toMonoidHom) (square_le_comap_unitsMap f)

/-- Pushforward sends the class of a unit to the class of its image. -/
@[simp]
theorem multiplicativeSquareClassMap_mk (f : K →+* L) (u : Kˣ) :
    multiplicativeSquareClassMap f (QuotientGroup.mk u) =
      QuotientGroup.mk (Units.map f.toMonoidHom u) := by
  rw [multiplicativeSquareClassMap, QuotientGroup.map_mk]

/-- Pushforward on multiplicative square classes preserves identity field homomorphisms. -/
@[simp]
theorem multiplicativeSquareClassMap_id :
    multiplicativeSquareClassMap (RingHom.id K) = MonoidHom.id _ := by
  apply DFunLike.ext _ _
  intro x
  induction x using QuotientGroup.induction_on with
  | _ u =>
    rw [MonoidHom.id_apply, multiplicativeSquareClassMap_mk]
    congr 1

/-- Pushforward on multiplicative square classes preserves composition of field homomorphisms. -/
@[simp]
theorem multiplicativeSquareClassMap_comp (g : L →+* F) (f : K →+* L) :
    multiplicativeSquareClassMap (g.comp f) =
      (multiplicativeSquareClassMap g).comp (multiplicativeSquareClassMap f) := by
  apply DFunLike.ext _ _
  intro x
  induction x using QuotientGroup.induction_on with
  | _ u =>
    rw [MonoidHom.comp_apply, multiplicativeSquareClassMap_mk,
      multiplicativeSquareClassMap_mk, multiplicativeSquareClassMap_mk]
    congr 1

/-- Pushforward on the additive square-class groups along a field homomorphism, transported from
the generic functorial map on elementary-two quotients. -/
noncomputable def squareClassMap (f : K →+* L) : SquareClassGroup K →ₗ[ZMod 2] SquareClassGroup L :=
  (elementaryTwoQuotientEquivSquareClassGroup (K := L)).toLinearMap.comp
    ((elementaryTwoQuotientMap (Units.map f.toMonoidHom)).comp
      (elementaryTwoQuotientEquivSquareClassGroup (K := K)).symm.toLinearMap)

/-- Pushforward sends the additive square class of a unit to the class of its image. -/
@[simp]
theorem squareClassMap_apply (f : K →+* L) (u : Kˣ) :
    squareClassMap f (squareClass u) = squareClass (Units.map f.toMonoidHom u) := by
  have hu : (elementaryTwoQuotientEquivSquareClassGroup (K := K)).symm (squareClass u) =
      elementaryTwoQuotientMk u := by
    apply (elementaryTwoQuotientEquivSquareClassGroup (K := K)).injective
    rw [LinearEquiv.apply_symm_apply, elementaryTwoQuotientEquivSquareClassGroup_mk]
  rw [squareClassMap, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, hu, elementaryTwoQuotientMap_mk,
    elementaryTwoQuotientEquivSquareClassGroup_mk]

/-- The canonical equivalence between the two square-class conventions commutes with pushforward
along a field homomorphism. -/
theorem multiplicativeSquareClassEquiv_map (f : K →+* L)
    (x : MultiplicativeSquareClassGroup K) :
    multiplicativeSquareClassEquiv (multiplicativeSquareClassMap f x) =
      Multiplicative.ofAdd (squareClassMap f (multiplicativeSquareClassEquiv x).toAdd) := by
  induction x using QuotientGroup.induction_on with
  | _ u => simp

/-- Pushforward on additive square classes preserves identity field homomorphisms. -/
@[simp]
theorem squareClassMap_id : squareClassMap (RingHom.id K) = LinearMap.id := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ u =>
    have hu : (↑u : SquareClassGroup K) = squareClass u.toMul := by
      rw [squareClass_def, ofMul_toMul]
    rw [LinearMap.id_apply, hu, squareClassMap_apply]
    congr 1

/-- Pushforward on additive square classes preserves composition of field homomorphisms. -/
@[simp]
theorem squareClassMap_comp (g : L →+* F) (f : K →+* L) :
    squareClassMap (g.comp f) = (squareClassMap g).comp (squareClassMap f) := by
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ u =>
    have hu : (↑u : SquareClassGroup K) = squareClass u.toMul := by
      rw [squareClass_def, ofMul_toMul]
    rw [LinearMap.comp_apply, hu, squareClassMap_apply,
      squareClassMap_apply, squareClassMap_apply]
    congr 1

/-- The multiplicative and additive presentations of the square-class group are finite
simultaneously. -/
theorem finite_multiplicativeSquareClassGroup_iff :
    Finite (MultiplicativeSquareClassGroup K) ↔ Finite (SquareClassGroup K) :=
  (multiplicativeSquareClassEquiv (K := K)).toEquiv.finite_iff

/-- The multiplicative and additive presentations of the square-class group have the same
`Nat.card`. -/
theorem natCard_multiplicativeSquareClassGroup :
    Nat.card (MultiplicativeSquareClassGroup K) = Nat.card (SquareClassGroup K) :=
  Nat.card_congr (multiplicativeSquareClassEquiv (K := K)).toEquiv

end TauCeti
