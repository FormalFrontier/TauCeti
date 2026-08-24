/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantField
public import TauCeti.FieldTheory.FunctionField.Divisor.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Existence
public import TauCeti.FieldTheory.FunctionField.Place.Zeros

/-!
# Principal divisors of an algebraic function field

The **principal divisor** of a nonzero function `z` of an algebraic function field `F / k` is the
finite formal sum

`div z = ∑_P ord_P z · P`

of its zeros and poles, weighted by their orders.  It is a finite sum because a function of an
algebraic function field has only finitely many zeros and poles
(`TauCeti.Place.finite_setOf_ord_ne_zero`), and it is additive in `z` because `ord_P` is.  This
file constructs it, splits it into its zero and pole divisors, and characterizes the functions
with trivial divisor as the constants.  It is Stichtenoth, *Algebraic Function Fields and
Codes*, 2nd ed., Definition 1.4.2.  Its consequences for Riemann–Roch spaces are
`TauCeti.FieldTheory.FunctionField.RiemannRoch.Principal`.

The formal side is not rebuilt: the group `Divisor k F` and its degree are
`TauCeti.FieldTheory.FunctionField.Divisor.Basic`, and the passage from a family of order
functions to principal divisors, the subgroup they form, and linear equivalence is the
existing `TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem` API.  What is new here is the
order system of the places of a function field, and the function-field statements that need
the places themselves.

## Main definitions

* `TauCeti.Place.orderSystem`: the places of `F / k` with their order functions, as an
  `OrderSystem` on `Additive Fˣ`.  Its finiteness condition is Stichtenoth, Corollary 1.3.4.
* `TauCeti.Divisor.principal` and `TauCeti.Divisor.principalHom`: `div z` for `z : Fˣ`, and its
  packaging as a group homomorphism `Additive Fˣ →+ Divisor k F` (Definition 1.4.2).
* `TauCeti.Divisor.zeros` and `TauCeti.Divisor.poles`: the zero divisor `(z)₀ = (div z)⁺` and
  the pole divisor `(z)_∞ = (div z)⁻` (Definition 1.4.2).

## Main results

* `TauCeti.Divisor.zeros_sub_poles`: `div z = (z)₀ - (z)_∞`, with both parts effective.
* `TauCeti.Divisor.principal_eq_zero_iff_mem_algebraicClosure`: `div z = 0` exactly when `z` is
  a constant, and `TauCeti.Divisor.principal_eq_zero_iff`: over an exact constant field, exactly
  when `z ∈ kˣ`.
* `TauCeti.Divisor.linearlyEquivalent_iff`: two divisors are linearly equivalent exactly when
  their difference is the divisor of a function (Definition 1.4.3).

## Implementation notes

`div` is defined on `Fˣ`, not on `F` with a nonzero hypothesis: the roadmap pins it as a group
homomorphism, and `Additive Fˣ →+ Divisor k F` is that statement.  For a nonzero `f : F` the
divisor is `div (Units.mk0 f hf)`, and `TauCeti.Divisor.coeff_principal` reads its coefficients
back as orders of the underlying function.

The function-field hypothesis `IsFunctionField k F` is an explicit argument rather than a
typeclass, following the rest of this directory; it is what makes the support finite, so it
cannot be avoided in the definition.  Since it is a `Prop`, two spellings of it give the same
divisor.

The degree of a principal divisor is **not** computed here: `deg (div z) = 0` is the product
formula (Stichtenoth, Theorem 1.4.11), which needs `deg (z)₀ = [F : k(z)]` and is separate work.
Everything in this file is independent of it.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

/-- The order of vanishing at a place, as a homomorphism out of the additivized group of units
`Additive Fˣ`.  Restricting to units is what makes it additive: `ord_P` is only additive away
from the junk value `ord_P 0 = 0`. -/
noncomputable def ordAddMonoidHom (P : Place k F) : Additive Fˣ →+ ℤ :=
  AddMonoidHom.mk' (fun z => P.ord ((Additive.toMul z : Fˣ) : F)) fun z w => by
    simpa only [toMul_add, Units.val_mul] using
      P.ord_mul (Units.ne_zero _) (Units.ne_zero _)

@[simp]
theorem ordAddMonoidHom_apply (P : Place k F) (z : Fˣ) :
    P.ordAddMonoidHom (Additive.ofMul z) = P.ord (z : F) := by
  simp [ordAddMonoidHom]

/-- **The places of an algebraic function field, as an order system.**  The points are the
places, the group is `Additive Fˣ`, and the order at a place is `ord_P`.  The finiteness
condition is Stichtenoth, Corollary 1.3.4: a function has finitely many zeros and poles. -/
noncomputable def orderSystem (hF : IsFunctionField k F) :
    WeilDivisor.OrderSystem (Place k F) (Additive Fˣ) where
  ord P := P.ordAddMonoidHom
  finite_support z := by
    refine (finite_setOf_ord_ne_zero hF ((Additive.toMul z : Fˣ) : F)).subset fun P hP => ?_
    exact hP

@[simp]
theorem orderSystem_ord (hF : IsFunctionField k F) (P : Place k F) (z : Fˣ) :
    (orderSystem hF).ord P (Additive.ofMul z) = P.ord (z : F) := by
  rw [orderSystem, ordAddMonoidHom_apply]

end Place

namespace Divisor

/-! ### The principal divisor -/

/-- **The principal-divisor homomorphism** `div : Fˣ →+ Divisor k F` of an algebraic function
field, in its additivized form (Stichtenoth, Definition 1.4.2). -/
noncomputable def principalHom (hF : IsFunctionField k F) :
    Additive Fˣ →+ Divisor k F :=
  (Place.orderSystem hF).principalHom

/-- **The principal divisor** `div z = ∑_P ord_P z · P` of a nonzero function (Stichtenoth,
Definition 1.4.2). -/
noncomputable def principal (hF : IsFunctionField k F) (z : Fˣ) : Divisor k F :=
  principalHom hF (Additive.ofMul z)

@[simp]
theorem principalHom_ofMul (hF : IsFunctionField k F) (z : Fˣ) :
    principalHom hF (Additive.ofMul z) = principal hF z := by
  rw [principal]

theorem principalHom_apply (hF : IsFunctionField k F) (z : Additive Fˣ) :
    principalHom hF z = principal hF (Additive.toMul z) := by
  rw [← principalHom_ofMul, ofMul_toMul]

/-- The coefficient of a place in `div z` is the order of `z` there. -/
@[simp]
theorem coeff_principal (hF : IsFunctionField k F) (z : Fˣ) (P : Place k F) :
    (principal hF z).coeff P = P.ord (z : F) := by
  rw [principal, principalHom, WeilDivisor.OrderSystem.principalHom_apply,
    WeilDivisor.OrderSystem.coeff_principalDivisor, Place.orderSystem_ord]

theorem mem_support_principal_iff (hF : IsFunctionField k F) {z : Fˣ} {P : Place k F} :
    P ∈ (principal hF z).support ↔ P.ord (z : F) ≠ 0 := by
  rw [WeilDivisor.mem_support_iff, coeff_principal]

@[simp]
theorem principal_one (hF : IsFunctionField k F) : principal hF (1 : Fˣ) = 0 :=
  map_zero (principalHom hF)

theorem principal_mul (hF : IsFunctionField k F) (y z : Fˣ) :
    principal hF (y * z) = principal hF y + principal hF z :=
  map_add (principalHom hF) (Additive.ofMul y) (Additive.ofMul z)

@[simp]
theorem principal_inv (hF : IsFunctionField k F) (z : Fˣ) :
    principal hF z⁻¹ = -principal hF z :=
  map_neg (principalHom hF) (Additive.ofMul z)

theorem principal_div (hF : IsFunctionField k F) (y z : Fˣ) :
    principal hF (y / z) = principal hF y - principal hF z :=
  map_sub (principalHom hF) (Additive.ofMul y) (Additive.ofMul z)

theorem principal_zpow (hF : IsFunctionField k F) (z : Fˣ) (n : ℤ) :
    principal hF (z ^ n) = n • principal hF z := by
  rw [principal, ofMul_zpow, map_zsmul, principalHom_ofMul]

/-- The principal divisor of a function is the principal divisor of the order system of the
places of `F / k`. -/
theorem principalDivisor_eq (hF : IsFunctionField k F) (z : Additive Fˣ) :
    (Place.orderSystem hF).principalDivisor z = principal hF (Additive.toMul z) := by
  rw [principal, principalHom, WeilDivisor.OrderSystem.principalHom_apply, ofMul_toMul]

/-- **Linear equivalence, in terms of functions**: two divisors are linearly equivalent exactly
when their difference is the divisor of a function.  This is the multiplicative reading of
`TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem.LinearlyEquivalent` for the order system of
places (Stichtenoth, Definition 1.4.3). -/
theorem linearlyEquivalent_iff (hF : IsFunctionField k F) {A B : Divisor k F} :
    (Place.orderSystem hF).LinearlyEquivalent A B ↔ ∃ z : Fˣ, principal hF z = A - B := by
  rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff_exists_principalDivisor]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨Additive.toMul g, by rwa [← principalDivisor_eq]⟩
  · rintro ⟨z, hz⟩
    exact ⟨Additive.ofMul z, by rwa [principalDivisor_eq, toMul_ofMul]⟩

/-- The divisor of a function algebraic over the constants is trivial: such a function has
neither zeros nor poles. -/
theorem principal_eq_zero_of_isAlgebraic (hF : IsFunctionField k F) {z : Fˣ}
    (hz : IsAlgebraic k (z : F)) : principal hF z = 0 :=
  WeilDivisor.ext fun P => by
    rw [coeff_principal, P.ord_eq_zero_of_isAlgebraic hz, WeilDivisor.coeff_zero]

/-- **A function has trivial divisor exactly when it is a constant.**  One direction is that
constants are units at every place; the other is that a function lying in every valuation ring
is algebraic over `k` (`TauCeti.Place.mem_algebraicClosure_iff_forall_mem_integers`). -/
theorem principal_eq_zero_iff_mem_algebraicClosure (hF : IsFunctionField k F) (z : Fˣ) :
    principal hF z = 0 ↔ (z : F) ∈ algebraicClosure k F := by
  refine ⟨fun h => ?_, fun h => principal_eq_zero_of_isAlgebraic hF (mem_algebraicClosure_iff.mp h)⟩
  rw [Place.mem_algebraicClosure_iff_forall_mem_integers hF]
  intro P
  have hP : (principal hF z).coeff P = 0 := by rw [h, WeilDivisor.coeff_zero]
  rw [coeff_principal] at hP
  exact P.mem_integers_iff_ord_nonneg.mpr hP.ge

/-- **Stichtenoth, Definition 1.4.2**, over an exact constant field: `div z = 0` exactly when
`z ∈ kˣ`.  This is where exactness of the constant field enters — over `ℝ ⊆ ℂ(x)` the function
`i` has trivial divisor without being a constant of `ℝ`. -/
theorem principal_eq_zero_iff (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (z : Fˣ) : principal hF z = 0 ↔ ∃ c : k, algebraMap k F c = (z : F) := by
  rw [principal_eq_zero_iff_mem_algebraicClosure hF,
    algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mpr hex]
  simp [IntermediateField.mem_bot]

/-! ### The zero divisor and the pole divisor -/

/-- **The zero divisor** `(z)₀ = (div z)⁺` of a nonzero function (Stichtenoth,
Definition 1.4.2): its zeros, with multiplicities. -/
noncomputable def zeros (hF : IsFunctionField k F) (z : Fˣ) : Divisor k F :=
  (principal hF z)⁺

/-- **The pole divisor** `(z)_∞ = (div z)⁻` of a nonzero function (Stichtenoth,
Definition 1.4.2): its poles, with multiplicities. -/
noncomputable def poles (hF : IsFunctionField k F) (z : Fˣ) : Divisor k F :=
  (principal hF z)⁻

@[simp]
theorem coeff_zeros (hF : IsFunctionField k F) (z : Fˣ) (P : Place k F) :
    (zeros hF z).coeff P = P.ord (z : F) ⊔ 0 := by
  rw [zeros, WeilDivisor.coeff_posPart, coeff_principal]

@[simp]
theorem coeff_poles (hF : IsFunctionField k F) (z : Fˣ) (P : Place k F) :
    (poles hF z).coeff P = -P.ord (z : F) ⊔ 0 := by
  rw [poles, WeilDivisor.coeff_negPart, coeff_principal]

/-- A place lies in the support of the zero divisor exactly when it is a zero of `z`. -/
theorem mem_support_zeros_iff (hF : IsFunctionField k F) {z : Fˣ} {P : Place k F} :
    P ∈ (zeros hF z).support ↔ 0 < P.ord (z : F) := by
  rw [WeilDivisor.mem_support_iff, coeff_zeros]
  omega

/-- A place lies in the support of the pole divisor exactly when it is a pole of `z`. -/
theorem mem_support_poles_iff (hF : IsFunctionField k F) {z : Fˣ} {P : Place k F} :
    P ∈ (poles hF z).support ↔ P.ord (z : F) < 0 := by
  rw [WeilDivisor.mem_support_iff, coeff_poles]
  omega

@[simp]
theorem isEffective_zeros (hF : IsFunctionField k F) (z : Fˣ) :
    WeilDivisor.IsEffective (zeros hF z) :=
  WeilDivisor.isEffective_posPart _

@[simp]
theorem isEffective_poles (hF : IsFunctionField k F) (z : Fˣ) :
    WeilDivisor.IsEffective (poles hF z) :=
  WeilDivisor.isEffective_negPart _

/-- **The divisor of a function splits into its zeros and its poles**: `div z = (z)₀ - (z)_∞`. -/
theorem zeros_sub_poles (hF : IsFunctionField k F) (z : Fˣ) :
    zeros hF z - poles hF z = principal hF z :=
  posPart_sub_negPart (principal hF z)

/-- The poles of a function are the zeros of its inverse. -/
theorem poles_eq_zeros_inv (hF : IsFunctionField k F) (z : Fˣ) :
    poles hF z = zeros hF z⁻¹ :=
  WeilDivisor.ext fun P => by rw [coeff_poles, coeff_zeros, Units.val_inv_eq_inv_val, P.ord_inv]

/-- Zeros and poles never meet: no place is both. -/
theorem support_zeros_disjoint_poles (hF : IsFunctionField k F) (z : Fˣ) :
    Disjoint (zeros hF z).support (poles hF z).support :=
  WeilDivisor.support_posPart_disjoint_negPart _

end Divisor

end TauCeti
