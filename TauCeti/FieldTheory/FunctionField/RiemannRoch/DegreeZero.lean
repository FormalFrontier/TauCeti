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
principal, equivalently when its divisor class is zero.  In general this is equivalent to
`ℓ(D) = [algebraicClosure k F : k]`; over an exact constant field it specializes to
`ℓ(D) = 1`.

These are the degree-zero statements of Stichtenoth, *Algebraic Function Fields and Codes*,
second edition, Corollary 1.4.12(c).  They use the product formula through invariance of degree
under linear equivalence.

## Main results

* `TauCeti.riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero`: `L(D)` is nonzero
  exactly when a degree-zero `D` is principal.
* `TauCeti.riemannRochSpace_ne_bot_iff_divisorClass_eq_zero_of_degree_eq_zero`: equivalently,
  a degree-zero divisor has nonzero `L(D)` exactly when its divisor class is zero.
* `TauCeti.Divisor.dim_eq_finrank_algebraicClosure_iff_exists_principal_eq_of_degree_eq_zero`:
  in that case `ℓ(D)` is the degree of the full constant field, and only then.
* `TauCeti.Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero`: a degree-zero divisor
  has `ℓ(D) ≥ 1` exactly when it is principal.
* `TauCeti.Divisor.dim_eq_one_iff_exists_principal_eq_of_degree_eq_zero`: over an exact constant
  field, `D` is principal exactly when `ℓ(D) = 1`.
* `TauCeti.Divisor.dim_eq_zero_or_finrank_algebraicClosure_of_degree_eq_zero`: in general the
  dimension is zero or the degree of the full constant field; over an exact constant field,
  `TauCeti.Divisor.dim_eq_zero_or_one_of_degree_eq_zero` gives the zero-or-one dichotomy.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, GTM 254, Springer,
  2009, Corollary 1.4.12(c).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A degree-zero divisor has zero divisor class exactly when its Riemann–Roch space is nonzero. -/
theorem riemannRochSpace_ne_bot_iff_divisorClass_eq_zero_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    riemannRochSpace D ≠ ⊥ ↔ (Place.orderSystem hF).divisorClass D = 0 := by
  rw [riemannRochSpace_ne_bot_iff hF]
  let S := Place.orderSystem hF
  have hcriterion :=
    S.nonempty_completeLinearSystem_iff_divisorClass_eq_zero_of_weightedDegree_zero
      (fun P ↦ by exact_mod_cast P.one_le_degree_of_isFunctionField hF)
      (Place.isWeightedDegreeZero_orderSystem hF)
      (by
        rw [WeilDivisor.weightedDegree_apply]
        rw [Divisor.degree_apply] at hD
        exact hD)
  simpa only [Set.nonempty_def, WeilDivisor.OrderSystem.mem_completeLinearSystem,
    WeilDivisor.isEffective_iff_zero_le] using hcriterion

/-- A degree-zero divisor has a nonzero Riemann–Roch space exactly when it is principal
(Stichtenoth, Corollary 1.4.12(c)). -/
theorem riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    riemannRochSpace D ≠ ⊥ ↔ ∃ z : Fˣ, Divisor.principal hF z = D := by
  rw [riemannRochSpace_ne_bot_iff_divisorClass_eq_zero_of_degree_eq_zero hF hD,
    Divisor.divisorClass_eq_zero_iff hF]

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
    rw [← Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF]
    have hconstants : 0 < Module.finrank k (algebraicClosure k F) := by
      let _ := hF.finiteDimensional_algebraicClosure
      exact Module.finrank_pos
    omega
  · rintro ⟨z, rfl⟩
    exact Divisor.dim_principal hF z

/-- A degree-zero divisor has Riemann–Roch dimension at least one exactly when it is principal
(Stichtenoth, Corollary 1.4.12(c)).  Exactness of the constant field is unnecessary for this
form: the full constant field always contributes at least one dimension. -/
theorem Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    1 ≤ Divisor.dim D ↔ ∃ z : Fˣ, Divisor.principal hF z = D := by
  rw [Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF,
    riemannRochSpace_ne_bot_iff_exists_principal_eq_of_degree_eq_zero hF hD]

/-- Over an exact constant field, a degree-zero divisor is principal exactly when its
Riemann–Roch dimension is one (Stichtenoth, Corollary 1.4.12(c)). -/
theorem Divisor.dim_eq_one_iff_exists_principal_eq_of_degree_eq_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {D : Divisor k F} (hD : Divisor.degree D = 0) :
    Divisor.dim D = 1 ↔ ∃ z : Fˣ, Divisor.principal hF z = D := by
  rw [← isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.mp hex]
  exact Divisor.dim_eq_finrank_algebraicClosure_iff_exists_principal_eq_of_degree_eq_zero hF hD

/-- A degree-zero divisor has Riemann–Roch dimension either zero or the degree of the full
constant field. -/
theorem Divisor.dim_eq_zero_or_finrank_algebraicClosure_of_degree_eq_zero
    (hF : IsFunctionField k F) {D : Divisor k F} (hD : Divisor.degree D = 0) :
    Divisor.dim D = 0 ∨ Divisor.dim D = Module.finrank k (algebraicClosure k F) := by
  rcases Nat.eq_zero_or_pos (Divisor.dim D) with h | h
  · exact Or.inl h
  · exact Or.inr <|
      (Divisor.dim_eq_finrank_algebraicClosure_iff_exists_principal_eq_of_degree_eq_zero hF hD).mpr
        ((Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero hF hD).mp h)

/-- Over an exact constant field, a degree-zero divisor has Riemann–Roch dimension either zero or
one. -/
theorem Divisor.dim_eq_zero_or_one_of_degree_eq_zero
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {D : Divisor k F} (hD : Divisor.degree D = 0) :
    Divisor.dim D = 0 ∨ Divisor.dim D = 1 := by
  rw [← isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.mp hex]
  exact Divisor.dim_eq_zero_or_finrank_algebraicClosure_of_degree_eq_zero hF hD

end TauCeti
