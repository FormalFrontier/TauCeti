/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import TauCeti.Algebra.Ring.Units
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.NoncommRing

/-!
# The Jacobson radical, and semiprimary rings, are left-right symmetric

`Ring.jacobson R` is the intersection of the maximal *left* ideals of `R`, so nothing about the
definition is symmetric in the two sides. Mathlib knows the resulting ideal is two-sided, but it
does not record the sharper statement that the *same* ideal is cut out by the maximal right
ideals, and consequently it leaves the transfer of `IsSemiprimaryRing` to the opposite ring as a
`proof_wanted` in `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`, annotated "Need
left-right symmetry of Jacobson radical".

This file supplies that symmetry and the two consequences it was wanted for. The route is the
elementwise description of the radical: `x` lies in `Ring.jacobson R` exactly when `1 + y * x` is
a unit for every `y`, and hence, by `TauCeti.isUnit_one_add_mul_comm`, exactly when `1 + x * y` is
a unit for every `y`. The second description is the first one read in `Rᵐᵒᵖ`, so the radical of
the opposite ring is the opposite of the radical.

Mathlib proves the elementwise description only over a commutative ring
(`Ideal.mem_jacobson_bot`), where left-right symmetry is vacuous; the noncommutative statement
here is what carries the content. The one extra step over the commutative case is that membership
in the radical only supplies a *left* inverse for `1 + y * x`, so the argument has to promote that
left inverse to a two-sided one.

## Main results

* `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left` and
  `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_right`: the two elementwise descriptions of
  the Jacobson radical of a ring.
* `TauCeti.Ring.op_mem_jacobson_mulOpposite_iff`: `MulOpposite.op x` lies in `Ring.jacobson Rᵐᵒᵖ`
  exactly when `x` lies in `Ring.jacobson R` -- the left-right symmetry, in membership form.
* `TauCeti.Ring.quotientJacobsonMulOppositeRingEquiv`: the resulting identification
  `Rᵐᵒᵖ ⧸ Ring.jacobson Rᵐᵒᵖ ≃+* (R ⧸ Ring.jacobson R)ᵐᵒᵖ`.
* `TauCeti.isSemiprimaryRing_mulOpposite_iff` and `TauCeti.IsSemiprimaryRing.mulOpposite`:
  semiprimarity passes to the opposite ring.
* `TauCeti.IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite`: a left
  Artinian ring is right Noetherian exactly when it is right Artinian, the statement that
  `WedderburnArtin.lean` records as waiting on the same symmetry.
-/

public section

namespace TauCeti

open MulOpposite

variable (R : Type*) [Ring R]

namespace Ring

variable {R}

/-- Membership in the Jacobson radical, unfolded: `x` lies in `Ring.jacobson R` exactly when
`1 + y * x` has a left inverse for every `y`.

This is `Ideal.mem_jacobson_iff` at the zero ideal, rearranged. Only a left inverse is available
at this stage; `TauCeti.Ring.mem_jacobson_iff_isUnit_one_add_mul_left` upgrades it to a two-sided
one. -/
theorem mem_jacobson_iff_exists_mul_eq_one {x : R} :
    x ∈ Ring.jacobson R ↔ ∀ y : R, ∃ z : R, z * (1 + y * x) = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  refine forall_congr' fun y => exists_congr fun z => ?_
  have h : z * (1 + y * x) = z * y * x + z := by noncomm_ring
  rw [Ideal.mem_bot, sub_eq_zero, h]

/-- The Jacobson radical of a ring is `{x | ∀ y, IsUnit (1 + y * x)}`.

Mathlib's `Ideal.mem_jacobson_bot` is this statement over a commutative ring. -/
theorem mem_jacobson_iff_isUnit_one_add_mul_left {x : R} :
    x ∈ Ring.jacobson R ↔ ∀ y : R, IsUnit (1 + y * x) := by
  rw [mem_jacobson_iff_exists_mul_eq_one]
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · -- A left inverse `z` of `1 + y * x` is again of the form `1 + y' * x`, so it has a left
    -- inverse `w` in turn; then `w = w * (z * (1 + y * x)) = 1 + y * x`, which makes `z` a
    -- two-sided inverse of `1 + y * x`.
    obtain ⟨z, hz⟩ := h y
    have hexp : z * (1 + y * x) = z * y * x + z := by noncomm_ring
    have h1 : z * y * x + z = 1 := by rw [← hexp]; exact hz
    have hz' : 1 + -(z * y) * x = z := by
      have key : 1 + -(z * y) * x - z = 1 - (z * y * x + z) := by noncomm_ring
      rwa [h1, sub_self, sub_eq_zero] at key
    obtain ⟨w, hw⟩ := h (-(z * y))
    rw [hz'] at hw
    have hwz : w = 1 + y * x :=
      calc w = w * (z * (1 + y * x)) := by rw [hz, mul_one]
        _ = w * z * (1 + y * x) := by rw [mul_assoc]
        _ = 1 + y * x := by rw [hw, one_mul]
    exact ⟨⟨1 + y * x, z, by rw [← hwz]; exact hw, hz⟩, rfl⟩
  · obtain ⟨u, hu⟩ := h y
    exact ⟨↑u⁻¹, by rw [← hu]; exact u.inv_mul⟩

/-- The right-handed description of the Jacobson radical: it is also `{x | ∀ y, IsUnit (1 + x*y)}`.

This is where the left-right symmetry enters: the two descriptions differ only by the swap
`TauCeti.isUnit_one_add_mul_comm`. -/
theorem mem_jacobson_iff_isUnit_one_add_mul_right {x : R} :
    x ∈ Ring.jacobson R ↔ ∀ y : R, IsUnit (1 + x * y) :=
  mem_jacobson_iff_isUnit_one_add_mul_left.trans
    (forall_congr' fun _ => isUnit_one_add_mul_comm)

/-- **Left-right symmetry of the Jacobson radical**: the intersection of the maximal left ideals
of `Rᵐᵒᵖ` is the opposite of the intersection of the maximal left ideals of `R`, which is to say
that the Jacobson radical of `R` is also the intersection of its maximal right ideals. -/
theorem op_mem_jacobson_mulOpposite_iff {x : R} :
    op x ∈ Ring.jacobson Rᵐᵒᵖ ↔ x ∈ Ring.jacobson R := by
  rw [mem_jacobson_iff_isUnit_one_add_mul_left, mem_jacobson_iff_isUnit_one_add_mul_right,
    op_surjective.forall]
  exact forall_congr' fun y => by rw [← op_one, ← op_mul, ← op_add, isUnit_op]

/-- `TauCeti.Ring.op_mem_jacobson_mulOpposite_iff` phrased for an element of `Rᵐᵒᵖ`. -/
@[simp]
theorem mem_jacobson_mulOpposite_iff {X : Rᵐᵒᵖ} :
    X ∈ Ring.jacobson Rᵐᵒᵖ ↔ X.unop ∈ Ring.jacobson R :=
  op_mem_jacobson_mulOpposite_iff (x := X.unop)

/-- The Jacobson radical of `Rᵐᵒᵖ` is, as a set, the `op`-image of the Jacobson radical of `R`. -/
theorem coe_jacobson_mulOpposite (R : Type*) [Ring R] :
    (Ring.jacobson Rᵐᵒᵖ : Set Rᵐᵒᵖ) = unop ⁻¹' (Ring.jacobson R) :=
  Set.ext fun _ => mem_jacobson_mulOpposite_iff

/-- The symmetry passes to the powers of the radical: `op` reverses products, so a product of `n`
elements of `Ring.jacobson R` is the opposite of a product of `n` elements of
`Ring.jacobson Rᵐᵒᵖ`, taken in the other order. -/
theorem op_mem_jacobson_pow (n : ℕ) (x : R) (hx : x ∈ Ring.jacobson R ^ n) :
    op x ∈ Ring.jacobson Rᵐᵒᵖ ^ n := by
  induction n generalizing x with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    rw [Submodule.pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [op_mul, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (op_mem_jacobson_mulOpposite_iff.mpr hb) (ih a ha)
    · rw [op_add]
      exact Ideal.add_mem _ ha hb

/-- The converse direction of `TauCeti.Ring.op_mem_jacobson_pow`. -/
theorem unop_mem_jacobson_pow (n : ℕ) (X : Rᵐᵒᵖ) (hX : X ∈ Ring.jacobson Rᵐᵒᵖ ^ n) :
    X.unop ∈ Ring.jacobson R ^ n := by
  induction n generalizing X with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    rw [Submodule.pow_succ] at hX
    refine Submodule.mul_induction_on hX (fun A hA B hB => ?_) (fun A B hA hB => ?_)
    · rw [unop_mul, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (mem_jacobson_mulOpposite_iff.mp hB) (ih A hA)
    · rw [unop_add]
      exact Ideal.add_mem _ hA hB

variable (R)

/-- Nilpotence of the Jacobson radical is left-right symmetric: the two radicals have the same
vanishing powers. -/
theorem isNilpotent_jacobson_mulOpposite_iff :
    IsNilpotent (Ring.jacobson Rᵐᵒᵖ) ↔ IsNilpotent (Ring.jacobson R) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, eq_bot_iff.mpr fun x hx => ?_⟩
    have hx' := op_mem_jacobson_pow n x hx
    rw [hn] at hx'
    simpa [Ideal.mem_bot] using hx'
  · rintro ⟨n, hn⟩
    refine ⟨n, eq_bot_iff.mpr fun X hX => ?_⟩
    have hX' := unop_mem_jacobson_pow n X hX
    rw [hn] at hX'
    simpa [Ideal.mem_bot] using hX'

/-- Reduction modulo the Jacobson radical commutes with passing to the opposite ring. -/
noncomputable def quotientJacobsonMulOppositeRingEquiv :
    Rᵐᵒᵖ ⧸ Ring.jacobson Rᵐᵒᵖ ≃+* (R ⧸ Ring.jacobson R)ᵐᵒᵖ := by
  let f : Rᵐᵒᵖ →+* (R ⧸ Ring.jacobson R)ᵐᵒᵖ := RingHom.op (Ideal.Quotient.mk (Ring.jacobson R))
  have hf : Function.Surjective f := fun Y => by
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective Y.unop
    exact ⟨op x, by simp [f, hx]⟩
  have hker : RingHom.ker f = Ring.jacobson Rᵐᵒᵖ := by
    ext X
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)

/-- Semisimplicity of the quotient by the Jacobson radical is left-right symmetric. -/
theorem isSemisimpleRing_quotient_jacobson_mulOpposite_iff :
    IsSemisimpleRing (Rᵐᵒᵖ ⧸ Ring.jacobson Rᵐᵒᵖ) ↔ IsSemisimpleRing (R ⧸ Ring.jacobson R) :=
  (quotientJacobsonMulOppositeRingEquiv R).isSemisimpleRing_iff.trans
    isSemisimpleRing_mulOpposite_iff

end Ring

/-- **Semiprimarity is left-right symmetric**, discharging Mathlib's `proof_wanted`
`isSemiprimaryRing_mulOpposite_iff`. -/
theorem isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R := by
  rw [isSemiprimaryRing_iff, isSemiprimaryRing_iff,
    Ring.isSemisimpleRing_quotient_jacobson_mulOpposite_iff,
    Ring.isNilpotent_jacobson_mulOpposite_iff]

/-- The opposite of a semiprimary ring is semiprimary, discharging Mathlib's `proof_wanted`
`IsSemiprimaryRing.mulOpposite`. -/
instance IsSemiprimaryRing.mulOpposite [IsSemiprimaryRing R] : IsSemiprimaryRing Rᵐᵒᵖ :=
  (isSemiprimaryRing_mulOpposite_iff R).mpr ‹_›

/-- For a left Artinian ring, being right Noetherian and being right Artinian coincide: the
opposite ring is semiprimary, so Hopkins-Levitzki applies to it. This is the `example` that
`Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean` leaves open. -/
theorem IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ :=
  IsSemiprimaryRing.isNoetherian_iff_isArtinian

end TauCeti
