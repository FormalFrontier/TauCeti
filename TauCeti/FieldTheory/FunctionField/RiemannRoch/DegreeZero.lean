/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula

/-!
# Riemann–Roch spaces of degree-zero divisors

For an algebraic function field, an effective divisor of degree zero is zero.  Consequently, a
degree-zero divisor `D` has a nonzero function in its Riemann–Roch space exactly when `D` is
principal.  Over an exact constant field this is equivalent to `ℓ(D) = 1`; otherwise the same
argument identifies `ℓ(D)` with the degree of the full constant field.

These are the degree-zero statements of Stichtenoth, *Algebraic Function Fields and Codes*,
second edition, Corollary 1.4.12(c).  They use the product formula through invariance of degree
under linear equivalence.

## Main results

* `TauCeti.riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero`: `L(D)` is nonzero
  exactly when a degree-zero `D` is principal.
* `TauCeti.Divisor.dim_eq_finrank_algebraicClosure_iff_exists_principal_eq_of_degree_eq_zero`:
  in that case `ℓ(D)` is the degree of the full constant field, and only then.
* `TauCeti.Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero`: a degree-zero divisor
  has `ℓ(D) ≥ 1` exactly when it is principal.
* `TauCeti.Divisor.dim_eq_one_iff_exists_principal_eq_of_degree_eq_zero`: over an exact constant
  field, `D` is principal exactly when `ℓ(D) = 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, GTM 254, Springer,
  2009, Corollary 1.4.12(c).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A degree-zero divisor has a nonzero Riemann–Roch space exactly when it is principal
(Stichtenoth, Corollary 1.4.12(c)).

Indeed, a nonzero function in `L(D)` makes `D` linearly equivalent to an effective divisor.
The product formula preserves degree under this equivalence, and an effective divisor of degree
zero is zero. -/
theorem riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    riemannRochSpace D ≠ ⊥ ↔ ∃ z : Fˣ, Divisor.principal hF z = D := by
  rw [riemannRochSpace_ne_bot_iff hF]
  constructor
  · rintro ⟨E, hE, hDE⟩
    have hEdeg : Divisor.degree E = 0 :=
      (Divisor.degree_eq_of_linearlyEquivalent hF hDE).symm.trans hD
    have hE0 : E = 0 := (Divisor.degree_eq_zero_iff hF hE).mp hEdeg
    obtain ⟨z, hz⟩ := (Divisor.linearlyEquivalent_iff hF).mp hDE
    rw [hE0, sub_zero] at hz
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    refine ⟨0, le_rfl, (Divisor.linearlyEquivalent_iff hF).mpr ⟨z, ?_⟩⟩
    simp

/-- A degree-zero divisor has zero divisor class exactly when its Riemann–Roch space is nonzero. -/
theorem riemannRochSpace_ne_bot_iff_divisorClass_eq_zero_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    riemannRochSpace D ≠ ⊥ ↔ (Place.orderSystem hF).divisorClass D = 0 := by
  rw [riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero hF hD,
    WeilDivisor.OrderSystem.divisorClass_eq_zero_iff,
    WeilDivisor.OrderSystem.mem_principalSubgroup]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨Additive.ofMul z, ?_⟩
    rw [Divisor.principalDivisor_eq, toMul_ofMul]
    exact hz
  · rintro ⟨z, hz⟩
    refine ⟨Additive.toMul z, ?_⟩
    rw [← Divisor.principalDivisor_eq]
    exact hz

/-- If a divisor is principal, its Riemann–Roch dimension equals the degree of the full constant
field.  This statement does not require the divisor to have degree zero: the product formula
already guarantees that for principal divisors. -/
theorem Divisor.dim_eq_finrank_algebraicClosure_of_exists_principal_eq
    (hF : IsFunctionField k F) {D : Divisor k F}
    (hD : ∃ z : Fˣ, Divisor.principal hF z = D) :
    Divisor.dim D = Module.finrank k (algebraicClosure k F) := by
  obtain ⟨z, rfl⟩ := hD
  have hlin : (Place.orderSystem hF).LinearlyEquivalent (Divisor.principal hF z)
      (0 : Divisor k F) :=
    (Divisor.linearlyEquivalent_iff hF).mpr ⟨z, by simp⟩
  rw [Divisor.dim_eq_of_linearlyEquivalent hF hlin, Divisor.dim_zero hF]

/-- For a degree-zero divisor, `ℓ(D)` equals the degree of the full constant field exactly when
`D` is principal.  A nonprincipal degree-zero divisor has `L(D) = 0`, while a principal one has a
Riemann–Roch space obtained from `L(0)` by multiplication by a nonzero function. -/
theorem Divisor.dim_eq_finrank_algebraicClosure_iff_exists_principal_eq_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    Divisor.dim D = Module.finrank k (algebraicClosure k F) ↔
      ∃ z : Fˣ, Divisor.principal hF z = D := by
  constructor
  · intro hdim
    apply (riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero hF hD).mp
    intro hbot
    have hconstants : 0 < Module.finrank k (algebraicClosure k F) := by
      let _ := hF.finiteDimensional_algebraicClosure
      exact Module.finrank_pos
    rw [Divisor.dim_def, hbot, finrank_bot] at hdim
    omega
  · exact Divisor.dim_eq_finrank_algebraicClosure_of_exists_principal_eq hF

/-- A degree-zero divisor has Riemann–Roch dimension at least one exactly when it is principal
(Stichtenoth, Corollary 1.4.12(c)).  Exactness of the constant field is unnecessary for this
form: the full constant field always contributes at least one dimension. -/
theorem Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    1 ≤ Divisor.dim D ↔ ∃ z : Fˣ, Divisor.principal hF z = D := by
  constructor
  · intro hdim
    apply (riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero hF hD).mp
    intro hbot
    rw [Divisor.dim_def, hbot, finrank_bot] at hdim
    omega
  · intro hprincipal
    rw [Divisor.dim_eq_finrank_algebraicClosure_of_exists_principal_eq hF hprincipal]
    let _ := hF.finiteDimensional_algebraicClosure
    exact Module.finrank_pos

/-- Over an exact constant field, a degree-zero divisor is principal exactly when its
Riemann–Roch dimension is one (Stichtenoth, Corollary 1.4.12(c)). -/
theorem Divisor.dim_eq_one_iff_exists_principal_eq_of_degree_eq_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {D : Divisor k F} (hD : Divisor.degree D = 0) :
    Divisor.dim D = 1 ↔ ∃ z : Fˣ, Divisor.principal hF z = D := by
  rw [← isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.mp hex]
  exact Divisor.dim_eq_finrank_algebraicClosure_iff_exists_principal_eq_of_degree_eq_zero hF hD

/-- Over an exact constant field, a degree-zero divisor has Riemann–Roch dimension either zero or
one.  The second case is characterized by
`Divisor.dim_eq_one_iff_exists_principal_eq_of_degree_eq_zero`. -/
theorem Divisor.dim_eq_zero_or_one_of_degree_eq_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {D : Divisor k F} (hD : Divisor.degree D = 0) :
    Divisor.dim D = 0 ∨ Divisor.dim D = 1 := by
  by_cases hprincipal : ∃ z : Fˣ, Divisor.principal hF z = D
  · exact Or.inr <|
      (Divisor.dim_eq_one_iff_exists_principal_eq_of_degree_eq_zero hF hex hD).mpr hprincipal
  · left
    have hbot : riemannRochSpace D = ⊥ := not_ne_iff.mp <|
      mt (riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero hF hD).mp hprincipal
    rw [Divisor.dim_def, hbot, finrank_bot]

end TauCeti
