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
* `TauCeti.SpecializationAtOne`: specialization at `q = 1`.
* `TauCeti.SpecializationAtNegOne`: specialization at `q = -1`.

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

/-- The tensor representative of the canonical specialization map. -/
@[simp]
theorem specializeOf_eq_tmul (ev : LaurentPolynomial ℤ →+* ℤ) (x : M)
    [Module (LaurentPolynomial ℤ) M] :
    specializeOf ev M x =
      (let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
       (1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  rfl

/-- A map is compatible with specialization along `ev` when it intertwines Laurent scalars with
the integer action obtained by evaluating them. -/
def IsLaurentSemilinear (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] : Prop :=
  ∀ r x, f (r • x) = ev r • f x

/-- The unique additive map out of a specialization whose composite with `specializeOf` is `f`.

The compatibility hypothesis is precisely the relation imposed by the tensor product; no
bijectivity or comparison with another category is inferred. -/
noncomputable def specializeLift (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentSemilinear ev f) :
    LaurentSpecialization ev M →+ N :=
  let _ : Module (LaurentPolynomial ℤ) N := Module.compHom N ev
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  let g : ℤ →ₗ[LaurentPolynomial ℤ] M →ₗ[LaurentPolynomial ℤ] N :=
    LinearMap.mk₂ (LaurentPolynomial ℤ) (fun z m => z • f m)
      (by
        intro z₁ z₂ m
        -- The outer `Module.compHom` action on `ℤ` is evaluation followed by multiplication.
        change (z₁ + z₂) • f m = z₁ • f m + z₂ • f m
        rw [add_smul])
      (by
        intro r z m
        -- The outer `Module.compHom` action on `ℤ` is evaluation followed by multiplication.
        change (ev r * z) • f m = ev r • (z • f m)
        rw [mul_smul])
      (by
        intro z m₁ m₂
        rw [map_add, smul_add])
      (by
        intro r z m
        rw [hf]
        -- The target module is also induced by `ev`, so its scalar action unfolds here.
        change z • (ev r • f m) = ev r • (z • f m)
        rw [← mul_smul, ← mul_smul, mul_comm])
  TensorProduct.liftAddHom
    (LinearMap.toAddMonoidHom'.comp g.toAddMonoidHom)
    (by
      intro r z m
      -- This is the balancing relation after unfolding both `Module.compHom` actions.
      change (ev r * z) • f m = z • (f (r • m))
      rw [hf, smul_smul, mul_comm])

/-- The lift agrees with the original map on the canonical representatives. -/
@[simp]
theorem specializeLift_of (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentSemilinear ev f) (x : M) :
    specializeLift ev f hf
        (let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
         (1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] x) = f x := by
  let _ : Module (LaurentPolynomial ℤ) N := Module.compHom N ev
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  simp [specializeLift]

/-- Any additive map with the same values on canonical representatives is this lift. -/
theorem specializeLift_unique (ev : LaurentPolynomial ℤ →+* ℤ) (f : M →+ N)
    [Module (LaurentPolynomial ℤ) M] (hf : IsLaurentSemilinear ev f)
    (g : LaurentSpecialization ev M →+ N)
    (hg : ∀ x, g (specializeOf ev M x) = f x) :
    g = specializeLift ev f hf := by
  let _ : Module (LaurentPolynomial ℤ) N := Module.compHom N ev
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  let b : ℤ →ₗ[LaurentPolynomial ℤ] M →ₗ[LaurentPolynomial ℤ] N :=
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
  have hg_tmul (z : ℤ) (x : M) :
      g (z ⊗ₜ[LaurentPolynomial ℤ] x) = z • f x := by
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
      _ = z • f x := by rw [← specializeOf_eq_tmul, hg]
  -- The compatibility hypothesis makes an arbitrary additive map out of the tensor product
  -- linear for the evaluation-induced Laurent action.
  let g' : LaurentSpecialization ev M →ₗ[LaurentPolynomial ℤ] N :=
    { g with
      map_smul' := by
        intro r y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul z x =>
            change g (r • (z ⊗ₜ[LaurentPolynomial ℤ] x)) =
              ev r • g (z ⊗ₜ[LaurentPolynomial ℤ] x)
            calc
              g (r • (z ⊗ₜ[LaurentPolynomial ℤ] x)) =
                  g (z ⊗ₜ[LaurentPolynomial ℤ] (r • x)) :=
                congrArg g (TensorProduct.tmul_smul r z x).symm
              _ = z • f (r • x) := hg_tmul z (r • x)
              _ = z • (ev r • f x) := by rw [hf]
              _ = ev r • (z • f x) := by rw [smul_comm]
              _ = ev r • g (z ⊗ₜ[LaurentPolynomial ℤ] x) := by rw [hg_tmul]
        | add x y hx hy =>
            calc
              g (r • (x + y)) = g (r • x + r • y) := by rw [smul_add]
              _ = g (r • x) + g (r • y) := g.map_add _ _
              _ = ev r • g x + ev r • g y := congrArg₂ (· + ·) hx hy
              _ = ev r • (g x + g y) := (smul_add _ _ _).symm
              _ = ev r • g (x + y) := by rw [g.map_add] }
  have huniq : g' = TensorProduct.lift b := by
    apply TensorProduct.lift.unique
    intro z x
    change g (z ⊗ₜ[LaurentPolynomial ℤ] x) = z • f x
    exact hg_tmul z x
  have huniq' := congrArg LinearMap.toAddMonoidHom huniq
  change g = (TensorProduct.lift b).toAddMonoidHom at huniq'
  -- `liftAddHom` is definitionally the additive part of `TensorProduct.lift`; extensionality
  -- on tensors makes this bridge explicit rather than relying on that conversion.
  have hbridge : (TensorProduct.lift b).toAddMonoidHom = specializeLift ev f hf := by
    apply AddMonoidHom.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp [specializeLift, b, TensorProduct.lift, TensorProduct.liftAux]
    | tmul z x => simp [specializeLift, b, TensorProduct.lift, TensorProduct.liftAux]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  exact huniq'.trans hbridge

/-- The scalar relation defining Laurent specialization. -/
@[simp]
theorem specializeOf_smul (ev : LaurentPolynomial ℤ →+* ℤ) (r : LaurentPolynomial ℤ) (x : M)
    [Module (LaurentPolynomial ℤ) M] :
    (let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
     (1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] (r • x)) =
      ev r • specializeOf ev M x := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ ev
  -- Unfolding `specializeOf` and the induced integer action exposes the tensor relation.
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
abbrev SpecializationAtOne (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  LaurentSpecialization laurentEvalOne M

/-- The specialization of a Laurent module at `q = -1`. -/
abbrev SpecializationAtNegOne (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] :=
  LaurentSpecialization laurentEvalNegOne M

/-- At `q = 1`, every Laurent shift has the same specialized class. -/
theorem specializeAtOne_T_smul (n : ℤ) (x : M) [Module (LaurentPolynomial ℤ) M] :
    (let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ laurentEvalOne
     (1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] ((T n : LaurentPolynomial ℤ) • x)) =
      specializeOf laurentEvalOne M x := by
  rw [specializeOf_smul (M := M), laurentEvalOne_T]
  simp

/-- At `q = -1`, a Laurent shift acts by its sign on the specialized class. -/
theorem specializeAtNegOne_T_smul (n : ℤ) (x : M) [Module (LaurentPolynomial ℤ) M] :
    (let _ : Module (LaurentPolynomial ℤ) ℤ := Module.compHom ℤ laurentEvalNegOne
     (1 : ℤ) ⊗ₜ[LaurentPolynomial ℤ] ((T n : LaurentPolynomial ℤ) • x)) =
      (n.negOnePow : ℤ) • specializeOf laurentEvalNegOne M x := by
  rw [specializeOf_smul (M := M), laurentEvalNegOne_T]

end TauCeti
