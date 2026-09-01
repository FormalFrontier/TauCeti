/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent

/-!
# Specialization of Laurent modules

This file supplies the algebraic specializations of a Laurent module at `q = 1` and `q = -1`.
For a Laurent-module `M` and a ring homomorphism `ev : ℤ[q,q⁻¹] →+* ℤ`, the specialization is
the scalar extension `ℤ ⊗[ℤ[q,q⁻¹]] M`, with the first tensor factor viewed through `ev`.

The two distinguished evaluations are `laurentEvalOne` and `laurentEvalNegOne`.  The resulting
maps record that a Laurent shift becomes the identity at `q = 1` and multiplication by
`(-1)^n` at `q = -1`.  No comparison with an ungraded category is built in: such a comparison
needs the extra forgetful and Ext data described in the Grothendieck-groups roadmap.

## Main definitions

* `TauCeti.LaurentSpecialization`: specialization of a Laurent module along a ring homomorphism.
* `TauCeti.specializeOf` and `TauCeti.specializeLift`: its canonical map and universal factor.
* `TauCeti.SpecializeAtOne` and `TauCeti.SpecializeAtNegOne`: the two algebraic specializations.

## Main results

* `TauCeti.specializeOf_smul`: the defining scalar relation in the specialization.
* `TauCeti.specializeAtOne_T_smul` and `TauCeti.specializeAtNegOne_T_smul`: the shift laws at
  `q = 1` and `q = -1`.

The tensor-product presentation is the standard scalar-extension construction from Weibel,
*The K-book*, Chapter II, §1.  The evaluation convention and the warning that specialization may
change nondegeneracy follow Dancso--Licata, "Koszul algebras and flow lattices", §3.1.
-/

public section

namespace TauCeti

open LaurentPolynomial

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The algebraic base change of a Laurent module along `ev`. -/
abbrev LaurentSpecialization (ev : LaurentPolynomial ℤ →+* ℤ) (M : Type*)
    [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  letI := Module.compHom ℤ ev
  TensorProduct (LaurentPolynomial ℤ) ℤ M

/-- The canonical map from a Laurent module to its specialization. -/
noncomputable def specializeOf (ev : LaurentPolynomial ℤ →+* ℤ) (M : Type*)
    [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] : M →+ LaurentSpecialization ev M :=
  letI := Module.compHom ℤ ev
  ((TensorProduct.mk (LaurentPolynomial ℤ) ℤ M) 1).toAddMonoidHom

/-- A map is compatible with specialization along `ev` when it intertwines Laurent scalars with
the integer action obtained by evaluating them. -/
def IsLaurentLinearAt (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] : Prop :=
  ∀ r x, f (r • x) = ev r • f x

/-- The unique additive map out of a specialization whose composite with `specializeOf` is `f`.

The compatibility hypothesis is precisely the relation imposed by the tensor product; no
bijectivity or comparison with another category is inferred. -/
noncomputable def specializeLift (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentLinearAt ev f) :
    LaurentSpecialization ev M →+ N :=
  let _ : Module (LaurentPolynomial ℤ) N := Module.compHom N ev
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  let g : ℤ →ₗ[LaurentPolynomial ℤ] M →ₗ[LaurentPolynomial ℤ] N :=
    LinearMap.mk₂ (LaurentPolynomial ℤ) (fun z m => z • f m)
      (by
        intro z₁ z₂ m
        change (z₁ + z₂) • f m = z₁ • f m + z₂ • f m
        rw [add_smul])
      (by
        intro r z m
        change (ev r * z) • f m = ev r • (z • f m)
        rw [mul_smul])
      (by
        intro z m₁ m₂
        rw [map_add, smul_add])
      (by
        intro r z m
        rw [hf]
        change z • (ev r • f m) = ev r • (z • f m)
        rw [← mul_smul, ← mul_smul, mul_comm])
  (TensorProduct.lift g).toAddMonoidHom

/-- The lift agrees with the original map on the canonical representatives. -/
@[simp]
theorem specializeLift_of (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentLinearAt ev f) (x : M) :
    specializeLift ev f hf (specializeOf ev M x) = f x := by
  let _ : Module (LaurentPolynomial ℤ) N := Module.compHom N ev
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  rw [show specializeOf ev M x = (1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x by rfl]
  simp [specializeLift]

/-- Any additive map with the same values on canonical representatives is this lift. -/
theorem specializeLift_unique (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentLinearAt ev f)
    (g : LaurentSpecialization ev M →+ N)
    (hg : ∀ x, g (specializeOf ev M x) = f x) :
    g = specializeLift ev f hf := by
  let _ : Module (LaurentPolynomial ℤ) N := Module.compHom N ev
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  apply AddMonoidHom.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
      have htmul : z ⊗ₜ[LaurentPolynomial ℤ] x =
          z • ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) := by
        calc
          z ⊗ₜ[LaurentPolynomial ℤ] x =
              (z • (1 : ℤ)) ⊗ₜ[LaurentPolynomial ℤ] x := by
                rw [smul_eq_mul, mul_one]
          _ = (1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] (z • x) :=
            TensorProduct.smul_tmul z 1 x
          _ = z • ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) :=
            TensorProduct.tmul_smul z 1 x
      calc
        g (z ⊗ₜ[LaurentPolynomial ℤ] x) =
            g (z • ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x)) := congrArg g htmul
        _ = z • g ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) := map_zsmul g z _
        _ = z • f x := by rw [show ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) =
            specializeOf ev M x by rfl, hg]
        _ = z • specializeLift ev f hf ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) := by
          rw [show ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) = specializeOf ev M x by rfl,
            specializeLift_of]
        _ = specializeLift ev f hf (z • ((1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x)) :=
          (map_zsmul (specializeLift ev f hf) z _).symm
        _ = specializeLift ev f hf (z ⊗ₜ[LaurentPolynomial ℤ] x) := congrArg _ htmul.symm
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The scalar relation defining Laurent specialization. -/
@[simp]
theorem specializeOf_smul (ev : LaurentPolynomial ℤ →+* ℤ) (r : LaurentPolynomial ℤ) (x : M)
    [Module (LaurentPolynomial ℤ) M] :
    specializeOf ev M (r • x) = ev r • specializeOf ev M x := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  change 1 ⊗ₜ[LaurentPolynomial ℤ] (r • x) = ev r • (1 ⊗ₜ[LaurentPolynomial ℤ] x)
  rw [TensorProduct.tmul_smul]
  rfl

/-- Evaluation of a Laurent monomial at `q = 1`. -/
noncomputable def laurentEvalOne : LaurentPolynomial ℤ →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)

/-- At `q = 1`, every Laurent monomial evaluates to `1`. -/
@[simp]
theorem laurentEvalOne_T (n : ℤ) : laurentEvalOne (T n) = 1 := by
  rw [laurentEvalOne, LaurentPolynomial.eval₂_T]
  simp

/-- Evaluation of a Laurent monomial at `q = -1`. -/
noncomputable def laurentEvalNegOne : LaurentPolynomial ℤ →+* ℤ :=
  LaurentPolynomial.eval₂ (RingHom.id ℤ) (-1 : ℤˣ)

/-- The `q = -1` evaluation of a Laurent monomial is its sign `(-1)^n`. -/
@[simp]
theorem laurentEvalNegOne_T (n : ℤ) : laurentEvalNegOne (T n) = (n.negOnePow : ℤ) := by
  rw [laurentEvalNegOne, LaurentPolynomial.eval₂_T]
  rfl

/-- The specialization of a Laurent module at `q = 1`. -/
abbrev SpecializeAtOne (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  LaurentSpecialization laurentEvalOne M

/-- The specialization of a Laurent module at `q = -1`. -/
abbrev SpecializeAtNegOne (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  LaurentSpecialization laurentEvalNegOne M

/-- At `q = 1`, every Laurent shift has the same specialized class. -/
theorem specializeAtOne_T_smul (n : ℤ) (x : M) [Module (LaurentPolynomial ℤ) M] :
    specializeOf laurentEvalOne M ((T n : LaurentPolynomial ℤ) • x) =
      specializeOf laurentEvalOne M x := by
  rw [specializeOf_smul (M := M), laurentEvalOne_T]
  simp

/-- At `q = -1`, a Laurent shift acts by its sign on the specialized class. -/
theorem specializeAtNegOne_T_smul (n : ℤ) (x : M) [Module (LaurentPolynomial ℤ) M] :
    specializeOf laurentEvalNegOne M ((T n : LaurentPolynomial ℤ) • x) =
      (n.negOnePow : ℤ) • specializeOf laurentEvalNegOne M x := by
  rw [specializeOf_smul (M := M), laurentEvalNegOne_T]

end TauCeti
