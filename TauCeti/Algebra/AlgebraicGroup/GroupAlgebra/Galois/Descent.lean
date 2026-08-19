/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Automorphism actions on group algebras

Let `L` be a `k`-algebra and let its group of `k`-algebra automorphisms act linearly on an
abelian group `M` through a representation `rho`. The coordinate algebra `L[Multiplicative M]`
of the diagonalizable group `D(M)` admits a simultaneous action on coefficients and exponents:

```text
σ ⬝ (a X^m) = σ(a) X^(ρ(σ) m).
```

This file constructs that action by `k`-algebra automorphisms and records both its coefficient
formula and its semilinearity over `L`, together with its compatibility with the counit,
comultiplication, and antipode. The construction needs no Galois hypothesis. For a finite Galois
extension `L/k`, it supplies the semilinear descent datum used to descend `D(M)`; when `M` is a
finite-rank free lattice, `D(M)` is a split torus.

## Main declarations

* `TauCeti.GaloisDescent.groupAlgebraAction`: the automorphism action on the group algebra by
  `k`-algebra automorphisms.
* `TauCeti.GaloisDescent.groupAlgebraAction_single`: its value on a monomial.
* `TauCeti.GaloisDescent.coeff_groupAlgebraAction`: its coefficient formula.
* `TauCeti.GaloisDescent.groupAlgebraAction_smul`: semilinearity over the coefficient algebra.
* `TauCeti.GaloisDescent.groupAlgebraActionSemilinearEquiv`: the semilinear action.
* `TauCeti.GaloisDescent.groupAlgebraTensorActionSemilinearEquiv`: its tensor-square action.
* `TauCeti.GaloisDescent.counit_groupAlgebraAction`: compatibility with the counit.
* `TauCeti.GaloisDescent.comul_groupAlgebraAction`: compatibility with comultiplication.
* `TauCeti.GaloisDescent.antipode_groupAlgebraAction`: compatibility with the antipode.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.

This is the automorphism-action step used for semilinear descent in Layer 4, "Tori: split and
non-split", of the ReductiveGroups roadmap. Taking invariants and identifying their scalar
extension with the original split coordinate Hopf algebra remain subsequent steps.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

scoped[TauCeti.GaloisDescent] attribute [instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open scoped TauCeti.GaloisDescent

variable {k L M : Type*} [CommSemiring k] [CommSemiring L] [Algebra k L]
variable [AddCommGroup M]

/-- The exponent-lattice action in multiplicative notation, bundled as a homomorphism. -/
private noncomputable def exponentAction
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (L ≃ₐ[k] L) →* MulAut (Multiplicative M) where
  toFun sigma :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ M
      (rho.asGroupHom sigma)).toAddEquiv.toMultiplicative
  map_one' := by
    ext m
    exact congrArg
      (fun f : M →ₗ[ℤ] M => Multiplicative.ofAdd (f m.toAdd)) (map_one rho)
  map_mul' sigma tau := by
    ext m
    exact congrArg
      (fun f : M →ₗ[ℤ] M => Multiplicative.ofAdd (f m.toAdd)) (map_mul rho sigma tau)

@[simp]
private theorem exponentAction_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (m : Multiplicative M) :
    exponentAction rho sigma m = Multiplicative.ofAdd (rho sigma m.toAdd) := by
  exact congrArg (fun f : M →ₗ[ℤ] M => Multiplicative.ofAdd (f m.toAdd))
    (Representation.asGroupHom_apply rho sigma)

@[simp]
private theorem exponentAction_symm_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (m : Multiplicative M) :
    (exponentAction rho sigma).symm m =
      Multiplicative.ofAdd (rho sigma⁻¹ m.toAdd) := by
  have hinv : (↑((rho.asGroupHom sigma)⁻¹) : M →ₗ[ℤ] M) = rho sigma⁻¹ := by
    rw [← map_inv, Representation.asGroupHom_apply]
  exact congrArg (fun f : M →ₗ[ℤ] M => Multiplicative.ofAdd (f m.toAdd)) hinv

/-- Coefficient and exponent changes commute on a monoid algebra. -/
private theorem coefficientAction_commute_exponentAction
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma tau : L ≃ₐ[k] L) :
    Commute
      (MonoidAlgebra.mapRangeAlgAut k (Multiplicative M) sigma)
      (MonoidAlgebra.domCongrAut (R := k) (A := L) (exponentAction rho tau)) := by
  apply AlgEquiv.ext
  intro x
  ext m
  simp

/-- The simultaneous coefficient and exponent action, bundled as a homomorphism to the group of
`k`-algebra automorphisms. For finite Galois `L/k`, this is a semilinear descent datum. -/
noncomputable def groupAlgebraAction
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    (L ≃ₐ[k] L) →* (MonoidAlgebra L (Multiplicative M) ≃ₐ[k]
      MonoidAlgebra L (Multiplicative M)) :=
  ((MonoidAlgebra.mapRangeAlgAut k (Multiplicative M)).noncommCoprod
      ((MonoidAlgebra.domCongrAut (R := k) (A := L)).comp (exponentAction rho))
      (coefficientAction_commute_exponentAction rho)).comp
    { toFun := fun sigma ↦ (sigma, sigma)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

/-- The bundled automorphism action sends a monomial by acting on its coefficient and exponent. -/
@[simp]
theorem groupAlgebraAction_single
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (m : Multiplicative M) (a : L) :
    groupAlgebraAction rho sigma (MonoidAlgebra.single m a) =
      MonoidAlgebra.single (Multiplicative.ofAdd (rho sigma m.toAdd)) (sigma a) := by
  simp [groupAlgebraAction]

/-- The coefficient formula for the bundled automorphism action. -/
@[simp]
theorem coeff_groupAlgebraAction
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (x : MonoidAlgebra L (Multiplicative M)) (m : Multiplicative M) :
    (groupAlgebraAction rho sigma x).coeff m =
      sigma (x.coeff (Multiplicative.ofAdd (rho sigma⁻¹ m.toAdd))) := by
  simp [groupAlgebraAction]

/-- The automorphism action is semilinear over `L`: scalars are twisted by the same
automorphism. -/
@[simp]
theorem groupAlgebraAction_smul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (a : L) (x : MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraAction rho sigma (a • x) =
      sigma a • groupAlgebraAction rho sigma x := by
  simp [Algebra.smul_def, MonoidAlgebra.coe_algebraMap]

/-- The automorphism action packaged as a semilinear equivalence over its automorphism of `L`.

Consumers stating this type should use `open scoped TauCeti.GaloisDescent` to activate the
inverse-pair instances associated to a ring equivalence. -/
noncomputable def groupAlgebraActionSemilinearEquiv
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L) :
    MonoidAlgebra L (Multiplicative M) ≃ₛₗ[(sigma.toRingEquiv : L →+* L)]
      MonoidAlgebra L (Multiplicative M) :=
  { (groupAlgebraAction rho sigma).toAddEquiv with
    map_smul' := groupAlgebraAction_smul rho sigma }

/-- The underlying map of the semilinear equivalence is the bundled automorphism action. -/
@[simp]
theorem groupAlgebraActionSemilinearEquiv_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (x : MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraActionSemilinearEquiv rho sigma x = groupAlgebraAction rho sigma x :=
  by
    rw [groupAlgebraActionSemilinearEquiv]
    rfl

/-- On the tensor square of the coordinate algebra, the automorphism acts on both tensor
factors. -/
noncomputable def groupAlgebraTensorActionSemilinearEquiv
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L) :
    ((MonoidAlgebra L (Multiplicative M)) ⊗[L]
        (MonoidAlgebra L (Multiplicative M))) ≃ₛₗ[(sigma.toRingEquiv : L →+* L)]
      ((MonoidAlgebra L (Multiplicative M)) ⊗[L]
        (MonoidAlgebra L (Multiplicative M))) :=
  TensorProduct.congr (groupAlgebraActionSemilinearEquiv rho sigma)
    (groupAlgebraActionSemilinearEquiv rho sigma)

/-- The semilinear tensor action evaluates on a pure tensor by acting on both factors. -/
@[simp]
theorem groupAlgebraTensorActionSemilinearEquiv_tmul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (x y : MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraTensorActionSemilinearEquiv rho sigma (x ⊗ₜ[L] y) =
      groupAlgebraAction rho sigma x ⊗ₜ[L] groupAlgebraAction rho sigma y := by
  rw [groupAlgebraTensorActionSemilinearEquiv, TensorProduct.congr_tmul]
  simp only [groupAlgebraActionSemilinearEquiv_apply]

/-- The tensor-square action is semilinear over the coefficient field. -/
@[simp]
theorem groupAlgebraTensorActionSemilinearEquiv_smul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (a : L)
    (t : MonoidAlgebra L (Multiplicative M) ⊗[L]
      MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraTensorActionSemilinearEquiv rho sigma (a • t) =
      sigma a • groupAlgebraTensorActionSemilinearEquiv rho sigma t :=
  (groupAlgebraTensorActionSemilinearEquiv rho sigma).map_smulₛₗ a t

/-- The tensor-square action preserves the multiplicative identity. -/
@[simp]
theorem groupAlgebraTensorActionSemilinearEquiv_map_one
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L) :
    groupAlgebraTensorActionSemilinearEquiv rho sigma 1 = 1 := by
  rw [Algebra.TensorProduct.one_def,
    groupAlgebraTensorActionSemilinearEquiv_tmul]
  simp

/-- The tensor-square action preserves multiplication. -/
@[simp]
theorem groupAlgebraTensorActionSemilinearEquiv_map_mul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (x y : MonoidAlgebra L (Multiplicative M) ⊗[L]
      MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraTensorActionSemilinearEquiv rho sigma (x * y) =
      groupAlgebraTensorActionSemilinearEquiv rho sigma x *
        groupAlgebraTensorActionSemilinearEquiv rho sigma y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | tmul x₁ x₂ =>
      induction y using TensorProduct.induction_on with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | tmul y₁ y₂ =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul,
            groupAlgebraTensorActionSemilinearEquiv_tmul, map_mul]
      | add y₁ y₂ hy₁ hy₂ => simp only [mul_add, map_add, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ => simp only [add_mul, map_add, hx₁, hx₂]

/-- The tensor-square action of the identity automorphism is the identity. -/
@[simp]
theorem groupAlgebraTensorActionSemilinearEquiv_one
    (rho : Representation ℤ (L ≃ₐ[k] L) M)
    (t : MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraTensorActionSemilinearEquiv rho 1 t = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul x y =>
      rw [groupAlgebraTensorActionSemilinearEquiv_tmul]
      simp
  | add x y hx hy => rw [map_add, hx, hy]

/-- The tensor-square action of a product is the composite of the two actions. -/
@[simp]
theorem groupAlgebraTensorActionSemilinearEquiv_mul
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma tau : L ≃ₐ[k] L)
    (t : MonoidAlgebra L (Multiplicative M) ⊗[L] MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraTensorActionSemilinearEquiv rho (sigma * tau) t =
      groupAlgebraTensorActionSemilinearEquiv rho sigma
        (groupAlgebraTensorActionSemilinearEquiv rho tau t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x y =>
      rw [groupAlgebraTensorActionSemilinearEquiv_tmul,
        groupAlgebraTensorActionSemilinearEquiv_tmul,
        groupAlgebraTensorActionSemilinearEquiv_tmul]
      simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The automorphism action commutes with the counit, with the scalar output acted on by the
automorphism. -/
@[simp]
theorem counit_groupAlgebraAction
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (x : MonoidAlgebra L (Multiplicative M)) :
    Coalgebra.counit (R := L) (groupAlgebraAction rho sigma x) =
      sigma (Coalgebra.counit (R := L) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a => simp

/-- The automorphism action commutes with the antipode. -/
@[simp]
theorem antipode_groupAlgebraAction
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (x : MonoidAlgebra L (Multiplicative M)) :
    HopfAlgebra.antipode L (groupAlgebraAction rho sigma x) =
      groupAlgebraAction rho sigma (HopfAlgebra.antipode L x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a => simp

/-- The semilinear automorphism action commutes with comultiplication after acting on both tensor
factors. -/
@[simp]
theorem comul_groupAlgebraAction
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (sigma : L ≃ₐ[k] L)
    (x : MonoidAlgebra L (Multiplicative M)) :
    Coalgebra.comul (R := L) (groupAlgebraAction rho sigma x) =
      groupAlgebraTensorActionSemilinearEquiv rho sigma
        (Coalgebra.comul (R := L) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a =>
      simp only [MonoidAlgebra.comul_single, CommSemiring.comul_apply,
        TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply, groupAlgebraAction_single]
      rw [groupAlgebraTensorActionSemilinearEquiv_tmul]
      simp

end TauCeti.GaloisDescent
