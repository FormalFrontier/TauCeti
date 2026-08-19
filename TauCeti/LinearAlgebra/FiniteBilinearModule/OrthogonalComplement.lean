/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Basic

/-!
# Orthogonal complements in finite bilinear modules

This file develops the cardinality and double-complement theory of subgroups of a finite
bilinear module.  For a subgroup `H` of a possibly degenerate module `A`, the radical is the
only obstruction to recovering `H` from its orthogonal complement:

```text
H⊥⊥ = H + rad(A).
```

The proof first quotients the pairing by its radical.  The induced finite bilinear module is
nondegenerate, so restriction of characters shows that `|H| |H⊥| = |A|`.  Applying this
identity in the radical quotient gives the general double-complement formula.  In particular,
for a nondegenerate module, double orthogonal complementation is the identity and a Lagrangian
subgroup has order whose square is the order of the ambient group.

## Main declarations

* `TauCeti.FiniteBilinearModule.quotientOfLeRadical`: the quotient by a subgroup of the radical.
* `TauCeti.FiniteBilinearModule.radicalQuotient`: the nondegenerate quotient by the radical.
* `TauCeti.FiniteBilinearModule.orthogonalComplement_orthogonalComplement`: the formula
  `H⊥⊥ = H ⊔ rad(A)`.
* `TauCeti.FiniteBilinearModule.IsNondegenerate.card_mul_card_orthogonalComplement`: the
  cardinality identity `|H| |H⊥| = |A|` for a nondegenerate module.
* `TauCeti.FiniteBilinearModule.IsLagrangian.card_sq`: a Lagrangian has squared order `|A|`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti.FiniteBilinearModule

universe u

variable (A : FiniteBilinearModule.{u})

/-! ## Quotient by a subgroup of the radical -/

private theorem toIntSubmodule_le_ker_toBilin {K : AddSubgroup A} (hK : K ≤ A.radical) :
    K.toIntSubmodule ≤ A.toBilin.ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  rw [LinearMap.zero_apply, A.toBilin_apply]
  exact A.mem_radical_iff x |>.mp (hK hx) y

/-- The underlying additive quotient of a finite bilinear module by a subgroup of its radical. -/
private abbrev QuotientOfLeRadical (K : AddSubgroup A) := A.carrier ⧸ K.toIntSubmodule

private noncomputable def quotientOfLeRadicalBilin (K : AddSubgroup A) (hK : K ≤ A.radical) :
    A.QuotientOfLeRadical K →ₗ[ℤ] A.QuotientOfLeRadical K →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.IsRefl.liftQ₂ A.toBilin K.toIntSubmodule A.isRefl_toBilin
    (A.toIntSubmodule_le_ker_toBilin hK)

/-- The finite bilinear module obtained by quotienting by a subgroup of the radical.

The pairing descends precisely because vectors of the subgroup pair trivially with everything,
so the quotient by the radical itself is the special case `K = rad(A)` below. -/
noncomputable def quotientOfLeRadical (K : AddSubgroup A) (hK : K ≤ A.radical) :
    FiniteBilinearModule where
  carrier := A.QuotientOfLeRadical K
  finite := Finite.of_surjective K.toIntSubmodule.mkQ K.toIntSubmodule.mkQ_surjective
  pairing :=
    { toFun := fun x ↦ (A.quotientOfLeRadicalBilin K hK x).toAddMonoidHom
      map_zero' := by
        exact congrArg LinearMap.toAddMonoidHom (map_zero (A.quotientOfLeRadicalBilin K hK))
      map_add' := by
        intro x y
        exact congrArg LinearMap.toAddMonoidHom (map_add (A.quotientOfLeRadicalBilin K hK) x y) }
  pairing_comm := by
    intro x y
    induction x using Submodule.Quotient.induction_on with | H x =>
    induction y using Submodule.Quotient.induction_on with | H y =>
    -- `CharacterModule` is an opaque `def` alias for additive homomorphisms, so its evaluation
    -- cannot be simplified to the quotient bilinear map by a public rewrite lemma.
    change A.quotientOfLeRadicalBilin K hK (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = A.quotientOfLeRadicalBilin K hK (Submodule.Quotient.mk y)
        (Submodule.Quotient.mk x)
    rw [quotientOfLeRadicalBilin, LinearMap.liftQ₂_mk, LinearMap.liftQ₂_mk,
      A.toBilin_apply, A.toBilin_apply]
    exact A.pairing_comm x y

/-- The quotient map onto the quotient by a subgroup of the radical. -/
noncomputable def quotientOfLeRadicalMk (K : AddSubgroup A) (hK : K ≤ A.radical) :
    A →+ A.quotientOfLeRadical K hK :=
  K.toIntSubmodule.mkQ.toAddMonoidHom

/-- The quotient pairing is represented by the original pairing on representatives. -/
@[simp]
theorem quotientOfLeRadical_pairing_mk (K : AddSubgroup A) (hK : K ≤ A.radical) (x y : A) :
    (A.quotientOfLeRadical K hK).pairing (A.quotientOfLeRadicalMk K hK x)
      (A.quotientOfLeRadicalMk K hK y) = A.pairing x y := by
  -- Unfold the opaque `CharacterModule` alias to expose evaluation of the quotient lift.
  change A.quotientOfLeRadicalBilin K hK (Submodule.Quotient.mk x)
    (Submodule.Quotient.mk y) = A.pairing x y
  rw [quotientOfLeRadicalBilin, LinearMap.liftQ₂_mk, A.toBilin_apply]

/-- The quotient map by a subgroup of the radical is surjective. -/
theorem quotientOfLeRadicalMk_surjective (K : AddSubgroup A) (hK : K ≤ A.radical) :
    Function.Surjective (A.quotientOfLeRadicalMk K hK) :=
  K.toIntSubmodule.mkQ_surjective

/-- The kernel of the quotient map by a subgroup of the radical is that subgroup. -/
@[simp]
theorem quotientOfLeRadicalMk_ker (K : AddSubgroup A) (hK : K ≤ A.radical) :
    (A.quotientOfLeRadicalMk K hK).ker = K :=
  (congrArg Submodule.toAddSubgroup K.toIntSubmodule.ker_mkQ).trans
    K.toIntSubmodule_toAddSubgroup

/-! ## Quotient by the radical -/

/-- The finite bilinear module obtained by quotienting by the radical. -/
noncomputable def radicalQuotient : FiniteBilinearModule :=
  A.quotientOfLeRadical A.radical le_rfl

/-- The quotient map from a finite bilinear module to its radical quotient. -/
noncomputable def radicalQuotientMk : A →+ radicalQuotient A :=
  A.quotientOfLeRadicalMk A.radical le_rfl

/-- The quotient pairing is represented by the original pairing on representatives. -/
@[simp]
theorem radicalQuotient_pairing_mk (x y : A) :
    (radicalQuotient A).pairing (radicalQuotientMk A x) (radicalQuotientMk A y) =
      A.pairing x y :=
  A.quotientOfLeRadical_pairing_mk A.radical le_rfl x y

/-- The quotient map to the radical quotient is surjective. -/
theorem radicalQuotientMk_surjective : Function.Surjective (radicalQuotientMk A) :=
  A.quotientOfLeRadicalMk_surjective A.radical le_rfl

/-- The kernel of the radical quotient map is the radical. -/
@[simp]
theorem radicalQuotientMk_ker : (radicalQuotientMk A).ker = A.radical :=
  A.quotientOfLeRadicalMk_ker A.radical le_rfl

/-- Quotienting a finite bilinear module by its radical produces a nondegenerate module. -/
theorem isNondegenerate_radicalQuotient : (radicalQuotient A).IsNondegenerate := by
  apply (radicalQuotient A).isNondegenerate_of_injective
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := radicalQuotientMk_surjective A x
  rw [← AddMonoidHom.mem_ker, radicalQuotientMk_ker]
  rw [A.mem_radical_iff]
  intro y
  have hxy := DFunLike.congr_fun hx (radicalQuotientMk A y)
  calc
    A.pairing x y =
        (radicalQuotient A).pairing (radicalQuotientMk A x) (radicalQuotientMk A y) :=
      (radicalQuotient_pairing_mk A x y).symm
    _ = (0 : CharacterModule (radicalQuotient A)) (radicalQuotientMk A y) := hxy
    _ = 0 := rfl

/-! ## Character restriction and cardinality -/

/-- Pair an element of `A` against a subgroup `H`, regarded as a character of `H`. -/
def pairingRestrict (H : AddSubgroup A) : A →+ CharacterModule H where
  toFun x :=
    { toFun := fun y ↦ A.pairing x y
      map_zero' := A.pairing_zero_right x
      map_add' := fun y z ↦ A.pairing_add_right x (y : A) (z : A) }
  map_zero' := by ext y; exact A.pairing_zero_left y
  map_add' x y := by ext z; exact A.pairing_add_left x y z

/-- Evaluating the restricted pairing is evaluating the original pairing on the subtype. -/
@[simp]
theorem pairingRestrict_apply (H : AddSubgroup A) (x : A) (y : H) :
    A.pairingRestrict H x y = A.pairing x y :=
  (rfl)

/-- The kernel of the restricted pairing is the orthogonal complement. -/
@[simp]
theorem pairingRestrict_ker (H : AddSubgroup A) :
    (A.pairingRestrict H).ker = A.orthogonalComplement H := by
  ext x
  rw [AddMonoidHom.mem_ker, A.mem_orthogonalComplement_iff]
  exact ⟨fun hx y hy ↦ DFunLike.congr_fun hx ⟨y, hy⟩,
    fun hx ↦ CharacterModule.ext H fun (y : H) ↦ hx y y.2⟩

/-- In a nondegenerate finite bilinear module, every character of a subgroup is pairing with an
element of the ambient module. -/
theorem IsNondegenerate.pairingRestrict_surjective (hA : A.IsNondegenerate)
    (H : AddSubgroup A) : Function.Surjective (A.pairingRestrict H) := by
  intro c
  obtain ⟨d, hd⟩ := CharacterModule.dual_surjective_of_injective
    H.toIntSubmodule.subtype (Submodule.injective_subtype H.toIntSubmodule) c
  obtain ⟨x, hx⟩ := hA.bijective.2 d
  refine ⟨x, CharacterModule.ext H fun y ↦ ?_⟩
  rw [pairingRestrict_apply]
  rw [DFunLike.congr_fun hx (y : A)]
  have hy := DFunLike.congr_fun hd y
  exact hy

/-- In a nondegenerate finite bilinear module, the orders of a subgroup and its orthogonal
complement multiply to the order of the ambient module. -/
theorem IsNondegenerate.card_mul_card_orthogonalComplement (hA : A.IsNondegenerate)
    (H : AddSubgroup A) :
    Nat.card H * Nat.card (A.orthogonalComplement H) = Nat.card A := by
  have hs := IsNondegenerate.pairingRestrict_surjective A hA H
  have hindex : (A.pairingRestrict H).ker.index = Nat.card H := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs]
    simpa using natCard_characterModule H
  rw [mul_comm, ← A.pairingRestrict_ker H, ← hindex]
  exact (A.pairingRestrict H).ker.card_mul_index

/-- Double orthogonal complementation is the identity in a nondegenerate finite bilinear module. -/
theorem IsNondegenerate.orthogonalComplement_orthogonalComplement
    (hA : A.IsNondegenerate) (H : AddSubgroup A) :
    A.orthogonalComplement (A.orthogonalComplement H) = H := by
  symm
  apply AddSubgroup.eq_of_le_of_card_ge
    (A.le_orthogonalComplement_orthogonalComplement H)
  have hH := IsNondegenerate.card_mul_card_orthogonalComplement A hA H
  have hHperp := IsNondegenerate.card_mul_card_orthogonalComplement A hA
    (A.orthogonalComplement H)
  rw [mul_comm] at hHperp
  have hcard : Nat.card H =
      Nat.card (A.orthogonalComplement (A.orthogonalComplement H)) := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := A.orthogonalComplement H))
    exact hH.trans hHperp.symm
  exact hcard.symm.le

/-- Orthogonal complementation commutes with mapping to the radical quotient. -/
@[simp]
theorem orthogonalComplement_map_radicalQuotient (H : AddSubgroup A) :
    (radicalQuotient A).orthogonalComplement (H.map (radicalQuotientMk A)) =
      (A.orthogonalComplement H).map (radicalQuotientMk A) := by
  ext x
  obtain ⟨x, rfl⟩ := radicalQuotientMk_surjective A x
  constructor
  · intro hx
    refine ⟨x, ?_, rfl⟩
    refine (A.mem_orthogonalComplement_iff H x).mpr ?_
    intro y hy
    have hxy := (radicalQuotient A).mem_orthogonalComplement_iff
      (H.map (radicalQuotientMk A)) (radicalQuotientMk A x) |>.mp hx
      (radicalQuotientMk A y) ⟨y, hy, rfl⟩
    simpa using hxy
  · rintro ⟨z, hz, hzx⟩
    rw [(radicalQuotient A).mem_orthogonalComplement_iff]
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hzw := A.mem_orthogonalComplement_iff H z |>.mp hz w hw
    rw [← hzx]
    simpa using hzw

/-- For every subgroup of a finite bilinear module, the double orthogonal complement is the
subgroup enlarged by the radical. -/
@[simp]
theorem orthogonalComplement_orthogonalComplement (H : AddSubgroup A) :
    A.orthogonalComplement (A.orthogonalComplement H) = H ⊔ A.radical := by
  apply le_antisymm
  · intro x hx
    have hxq : radicalQuotientMk A x ∈
        (radicalQuotient A).orthogonalComplement
          ((radicalQuotient A).orthogonalComplement (H.map (radicalQuotientMk A))) := by
      rw [(radicalQuotient A).mem_orthogonalComplement_iff]
      intro y hy
      rw [orthogonalComplement_map_radicalQuotient] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact radicalQuotient_pairing_mk A x z ▸
        (A.mem_orthogonalComplement_iff (A.orthogonalComplement H) x |>.mp hx z hz)
    rw [IsNondegenerate.orthogonalComplement_orthogonalComplement
      (radicalQuotient A) A.isNondegenerate_radicalQuotient] at hxq
    rw [← A.radicalQuotientMk_ker, ← AddSubgroup.comap_map_eq]
    exact hxq
  · refine sup_le (A.le_orthogonalComplement_orthogonalComplement H) ?_
    intro x hx
    rw [A.mem_orthogonalComplement_iff]
    intro y _
    exact A.mem_radical_iff x |>.mp hx y

/-- A Lagrangian subgroup of a nondegenerate finite bilinear module has squared order equal to the
order of the ambient group. -/
theorem IsLagrangian.card_sq (hH : A.IsLagrangian H) (hA : A.IsNondegenerate) :
    Nat.card H ^ 2 = Nat.card A := by
  have hEq := A.isLagrangian_def H |>.mp hH
  have hcard : Nat.card H = Nat.card (A.orthogonalComplement H) :=
    Nat.card_congr (AddEquiv.addSubgroupCongr hEq).toEquiv
  calc
    Nat.card H ^ 2 = Nat.card H * Nat.card H := pow_two _
    _ = Nat.card H * Nat.card (A.orthogonalComplement H) := congrArg _ hcard
    _ = Nat.card A := IsNondegenerate.card_mul_card_orthogonalComplement A hA H

end TauCeti.FiniteBilinearModule
