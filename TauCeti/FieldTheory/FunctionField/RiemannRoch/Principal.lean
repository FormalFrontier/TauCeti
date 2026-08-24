/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# Riemann–Roch spaces and principal divisors

The Riemann–Roch space `L(D)` of a divisor of an algebraic function field `F / k` is defined by
a pole bound; the divisor of a function turns that bound into the single inequality
`div f + D ≥ 0`.  This file reads `L(D)` through the principal-divisor homomorphism
`TauCeti.Divisor.principal`: it gives the divisor form of membership, and proves that
multiplication by a nonzero function `z` is a `k`-linear isomorphism `L(A) ≅ L(A - div z)`,
so that `ℓ` depends only on the linear equivalence class of a divisor.  It is Stichtenoth,
*Algebraic Function Fields and Codes*, 2nd ed., Definition 1.4.4 and Lemma 1.4.6.

## Main results

* `TauCeti.mem_riemannRochSpace_units_iff`: `z ∈ L(D)` is `div z + D ≥ 0`, the divisor form of
  the pole bound defining `L(D)`.
* `TauCeti.riemannRochSpaceEquivSubPrincipal`: **Stichtenoth, Lemma 1.4.6** —
  multiplication by `z` is a `k`-linear isomorphism `L(A) ≅ L(A - div z)`; hence
  `TauCeti.Divisor.dim_eq_of_linearlyEquivalent`, `ℓ` is an invariant of the linear equivalence
  class of a divisor.
* `TauCeti.Divisor.dim_principal`: the dimension of a principal divisor is the degree of the
  full constant field over `k`.
* `TauCeti.riemannRochSpace_ne_bot_iff`: `L(D) ≠ 0` exactly when `D` is linearly equivalent to
  an effective divisor (Remark 1.4.5(b)).

None of this needs the product formula `deg (div z) = 0` (Stichtenoth, Theorem 1.4.11), which is
separate work; every statement here is independent of it.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The divisor form of membership in `L(D)`**: a nonzero function lies in `L(D)` exactly when
`div f + D` is effective, which is how Stichtenoth states Definition 1.4.4. -/
theorem mem_riemannRochSpace_units_iff (hF : IsFunctionField k F) {D : Divisor k F} {z : Fˣ} :
    (z : F) ∈ riemannRochSpace D ↔ 0 ≤ Divisor.principal hF z + D := by
  rw [mem_riemannRochSpace_iff_neg_le_ord (Units.ne_zero z), WeilDivisor.le_iff]
  refine forall_congr' fun P => ?_
  rw [WeilDivisor.coeff_zero, WeilDivisor.coeff_add, Divisor.coeff_principal]
  omega

/-- Multiplying by `z` moves `L(A)` into `L(A - div z)`: the poles of `z * f` are bounded by
those of `f` together with the poles `z` contributes. -/
theorem mul_mem_riemannRochSpace_sub_principal (hF : IsFunctionField k F) (z : Fˣ)
    {A : Divisor k F} {f : F} (hf : f ∈ riemannRochSpace A) :
    (z : F) * f ∈ riemannRochSpace (A - Divisor.principal hF z) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = f := ⟨Units.mk0 f hf0, rfl⟩
  rw [← Units.val_mul, mem_riemannRochSpace_units_iff hF, Divisor.principal_mul]
  have hcancel : Divisor.principal hF z + Divisor.principal hF u +
      (A - Divisor.principal hF z) = Divisor.principal hF u + A := by abel
  rw [hcancel]
  exact (mem_riemannRochSpace_units_iff hF).mp hf

/-- **Stichtenoth, Lemma 1.4.6**: multiplication by a nonzero function `z` is a `k`-linear
isomorphism `L(A) ≅ L(A - div z)`.

This is the whole content of the invariance of `ℓ` under linear equivalence: any two linearly
equivalent divisors differ by a principal divisor, and this isomorphism handles that difference.
It needs no product formula, so it is available before `deg (div z) = 0`. -/
noncomputable def riemannRochSpaceEquivSubPrincipal (hF : IsFunctionField k F) (z : Fˣ)
    (A : Divisor k F) :
    riemannRochSpace A ≃ₗ[k] riemannRochSpace (A - Divisor.principal hF z) := by
  have hback : ∀ f ∈ riemannRochSpace (A - Divisor.principal hF z),
      ((z⁻¹ : Fˣ) : F) * f ∈ riemannRochSpace A := by
    intro f hf
    have h := mul_mem_riemannRochSpace_sub_principal hF z⁻¹ hf
    rwa [Divisor.principal_inv, sub_neg_eq_add, sub_add_cancel] at h
  refine (z.mulLeftLinearEquiv k F).ofSubmodules _ _ (le_antisymm ?_ ?_)
  · rintro f ⟨g, hg, rfl⟩
    exact mul_mem_riemannRochSpace_sub_principal hF z hg
  · intro f hf
    refine ⟨(z.mulLeftLinearEquiv k F).symm f, ?_, ?_⟩
    · exact hback f hf
    · exact (z.mulLeftLinearEquiv k F).apply_symm_apply f

/-- The Riemann–Roch-space equivalence acts by multiplication by `z`. -/
@[simp]
theorem riemannRochSpaceEquivSubPrincipal_apply (hF : IsFunctionField k F) (z : Fˣ)
    (A : Divisor k F) (f : riemannRochSpace A) :
    (riemannRochSpaceEquivSubPrincipal hF z A f : F) = (z : F) * (f : F) := by
  rw [riemannRochSpaceEquivSubPrincipal, LinearEquiv.ofSubmodules_apply,
    Units.mulLeftLinearEquiv_apply]

/-- The inverse Riemann–Roch-space equivalence acts by multiplication by `z⁻¹`. -/
@[simp]
theorem riemannRochSpaceEquivSubPrincipal_symm_apply (hF : IsFunctionField k F) (z : Fˣ)
    (A : Divisor k F) (f : riemannRochSpace (A - Divisor.principal hF z)) :
    ((riemannRochSpaceEquivSubPrincipal hF z A).symm f : F) = (z⁻¹ : Fˣ) * (f : F) := by
  rw [riemannRochSpaceEquivSubPrincipal, LinearEquiv.ofSubmodules_symm_apply,
    Units.symm_mulLeftLinearEquiv_apply]

/-- `ℓ(A - div z) = ℓ(A)`: the dimension of a Riemann–Roch space is unchanged by subtracting a
principal divisor. -/
theorem Divisor.dim_sub_principal (hF : IsFunctionField k F) (z : Fˣ) (A : Divisor k F) :
    Divisor.dim (A - Divisor.principal hF z) = Divisor.dim A := by
  rw [Divisor.dim_def, Divisor.dim_def]
  exact ((riemannRochSpaceEquivSubPrincipal hF z A).finrank_eq).symm

/-- **`ℓ` is an invariant of the divisor class** (Stichtenoth, Lemma 1.4.6): linearly equivalent
divisors have Riemann–Roch spaces of the same dimension. -/
theorem Divisor.dim_eq_of_linearlyEquivalent (hF : IsFunctionField k F) {A B : Divisor k F}
    (h : (Place.orderSystem hF).LinearlyEquivalent A B) :
    Divisor.dim A = Divisor.dim B := by
  obtain ⟨z, hz⟩ := (Divisor.linearlyEquivalent_iff hF).mp h
  have hB : B = A - Divisor.principal hF z := by rw [hz]; abel
  rw [hB, Divisor.dim_sub_principal]

/-- The Riemann–Roch dimension of a principal divisor is the degree of the full constant field. -/
@[simp]
theorem Divisor.dim_principal (hF : IsFunctionField k F) (z : Fˣ) :
    Divisor.dim (Divisor.principal hF z) = Module.finrank k (algebraicClosure k F) := by
  have hlin : (Place.orderSystem hF).LinearlyEquivalent (Divisor.principal hF z)
      (0 : Divisor k F) :=
    (Divisor.linearlyEquivalent_iff hF).mpr ⟨z, by simp⟩
  rw [Divisor.dim_eq_of_linearlyEquivalent hF hlin, Divisor.dim_zero hF]

/-- Over an exact constant field, the Riemann–Roch dimension of a principal divisor is one. -/
theorem Divisor.dim_principal_of_isIntegrallyClosedIn (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (z : Fˣ) :
    Divisor.dim (Divisor.principal hF z) = 1 := by
  rw [Divisor.dim_principal hF, isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one.mp hex]

/-- **A Riemann–Roch space is nonzero exactly when its divisor is linearly equivalent to an
effective divisor** (Stichtenoth, Remark 1.4.5(b)).  A nonzero `f ∈ L(D)` makes `div f + D`
effective and equivalent to `D`; conversely, if `D - D'` is the divisor of `z` with `D'`
effective, then `z⁻¹` is a nonzero element of `L(D)`. -/
theorem riemannRochSpace_ne_bot_iff (hF : IsFunctionField k F) {D : Divisor k F} :
    riemannRochSpace D ≠ ⊥ ↔
      ∃ D' : Divisor k F, 0 ≤ D' ∧ (Place.orderSystem hF).LinearlyEquivalent D D' := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨f, hf, hf0⟩
    refine ⟨Divisor.principal hF (Units.mk0 f hf0) + D, ?_, ?_⟩
    · exact (mem_riemannRochSpace_units_iff hF (z := Units.mk0 f hf0)).mp hf
    · refine (Divisor.linearlyEquivalent_iff hF).mpr ⟨(Units.mk0 f hf0)⁻¹, ?_⟩
      rw [Divisor.principal_inv]
      abel
  · rintro ⟨D', hD', hequiv⟩
    obtain ⟨z, hz⟩ := (Divisor.linearlyEquivalent_iff hF).mp hequiv
    refine ⟨((z⁻¹ : Fˣ) : F), ?_, Units.ne_zero _⟩
    refine (mem_riemannRochSpace_units_iff hF).mpr ?_
    rw [Divisor.principal_inv, hz]
    have hcancel : -(D - D') + D = D' := by abel
    rw [hcancel]
    exact hD'

end TauCeti
