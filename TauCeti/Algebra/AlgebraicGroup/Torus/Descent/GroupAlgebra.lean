/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Galois descent data on group algebras

Let `L/k` be a finite Galois field extension and let the Galois group `Gal(L/k)` act linearly
on an abelian group `M`. The split torus with character lattice `M` has coordinate algebra
`L[Multiplicative M]`. Its descent datum acts simultaneously on coefficients and exponents:

```text
sigma * (a * X^m) = sigma(a) * X^(sigma * m).
```

This file constructs that action by `k`-algebra automorphisms and records both its coefficient
formula and its semilinearity over `L`. The construction is generic in the integral
representation on `M`; applying it to the finite Galois representation attached to a Galois
lattice is the algebraic input for descending a split torus.

## Main declarations

* `TauCeti.GaloisDescent.groupAlgebraAction`: the Galois action on the group algebra by
  `k`-algebra automorphisms.
* `TauCeti.GaloisDescent.groupAlgebraAction_single`: its value on a monomial.
* `TauCeti.GaloisDescent.groupAlgebraAction_coeff`: its coefficient formula.
* `TauCeti.GaloisDescent.groupAlgebraAction_smul`: semilinearity over the extension field.
* `TauCeti.GaloisDescent.comul_groupAlgebraAction`: compatibility with comultiplication.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Corollary 12.24.

This is the semilinear descent-datum step in Layer 4, "Tori: split and non-split", of the
ReductiveGroups roadmap. Taking invariants and identifying their scalar extension with the
original split coordinate Hopf algebra remain subsequent steps.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {k L M : Type u} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup M]

/-- The additive automorphism of the exponent lattice supplied by a representation element. -/
private noncomputable def exponentAddEquiv
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k)) : M ≃+ M where
  toFun := rho sigma
  invFun := rho sigma⁻¹
  left_inv x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  right_inv x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  map_add' := map_add (rho sigma)

@[simp]
private theorem exponentAddEquiv_apply
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k)) (m : M) :
    exponentAddEquiv rho sigma m = rho sigma m :=
  rfl

@[simp]
private theorem exponentAddEquiv_symm_apply
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k)) (m : M) :
    (exponentAddEquiv rho sigma).symm m = rho sigma⁻¹ m :=
  rfl

/-- The exponent-lattice automorphism in multiplicative notation. -/
private noncomputable def exponentMulEquiv
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k)) :
    Multiplicative M ≃* Multiplicative M :=
  (exponentAddEquiv rho sigma).toMultiplicative

@[simp]
private theorem exponentMulEquiv_apply
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (m : Multiplicative M) :
    exponentMulEquiv rho sigma m = Multiplicative.ofAdd (rho sigma m.toAdd) :=
  rfl

@[simp]
private theorem exponentMulEquiv_symm_apply
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (m : Multiplicative M) :
    (exponentMulEquiv rho sigma).symm m = Multiplicative.ofAdd (rho sigma⁻¹ m.toAdd) :=
  rfl

/-- The semilinear Galois automorphism of a split-torus coordinate algebra. It applies the
Galois automorphism to each coefficient and the given integral representation to each
exponent. -/
private noncomputable def groupAlgebraActionAlgEquiv
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k)) :
    MonoidAlgebra L (Multiplicative M) ≃ₐ[k] MonoidAlgebra L (Multiplicative M) :=
  (MonoidAlgebra.mapAlgEquiv k (Multiplicative M) sigma).trans
    (MonoidAlgebra.domCongr k L (exponentMulEquiv rho sigma))

/-- The descent automorphism sends `a * X^m` to `sigma(a) * X^(rho(sigma)m)`. -/
@[simp]
private theorem groupAlgebraActionAlgEquiv_single
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (m : Multiplicative M) (a : L) :
    groupAlgebraActionAlgEquiv rho sigma (MonoidAlgebra.single m a) =
      MonoidAlgebra.single (Multiplicative.ofAdd (rho sigma m.toAdd)) (sigma a) := by
  simp [groupAlgebraActionAlgEquiv]

/-- Coefficients of the descent automorphism are obtained by applying `sigma` to the coefficient
at the inverse translate of the exponent. -/
@[simp]
private theorem groupAlgebraActionAlgEquiv_coeff
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (x : MonoidAlgebra L (Multiplicative M)) (m : Multiplicative M) :
    (groupAlgebraActionAlgEquiv rho sigma x).coeff m =
      sigma (x.coeff (Multiplicative.ofAdd (rho sigma⁻¹ m.toAdd))) := by
  simp [groupAlgebraActionAlgEquiv]

/-- The Galois descent datum on a split-torus coordinate algebra, bundled as a homomorphism to
its group of `k`-algebra automorphisms. -/
noncomputable def groupAlgebraAction
    [FiniteDimensional k L] [IsGalois k L] (rho : Representation ℤ Gal(L/k) M) :
    Gal(L/k) →* (MonoidAlgebra L (Multiplicative M) ≃ₐ[k]
      MonoidAlgebra L (Multiplicative M)) where
  toFun := groupAlgebraActionAlgEquiv rho
  map_one' := by
    ext x m
    simp
  map_mul' sigma tau := by
    ext x m
    simp [mul_inv_rev]

variable [FiniteDimensional k L] [IsGalois k L]

/-- The bundled Galois action sends a monomial by acting on its coefficient and exponent. -/
@[simp]
theorem groupAlgebraAction_single
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (m : Multiplicative M) (a : L) :
    groupAlgebraAction rho sigma (MonoidAlgebra.single m a) =
      MonoidAlgebra.single (Multiplicative.ofAdd (rho sigma m.toAdd)) (sigma a) := by
  exact groupAlgebraActionAlgEquiv_single rho sigma m a

/-- The coefficient formula for the bundled Galois action. -/
@[simp]
theorem groupAlgebraAction_coeff
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (x : MonoidAlgebra L (Multiplicative M)) (m : Multiplicative M) :
    (groupAlgebraAction rho sigma x).coeff m =
      sigma (x.coeff (Multiplicative.ofAdd (rho sigma⁻¹ m.toAdd))) := by
  exact groupAlgebraActionAlgEquiv_coeff rho sigma x m

/-- The descent action is semilinear over `L`: scalars are twisted by the same Galois
automorphism. -/
theorem groupAlgebraAction_smul
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (a : L) (x : MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraAction rho sigma (a • x) =
      sigma a • groupAlgebraAction rho sigma x := by
  simp [Algebra.smul_def, MonoidAlgebra.coe_algebraMap]

/-- The Galois action packaged as a semilinear equivalence over its automorphism of `L`. -/
noncomputable def groupAlgebraActionSemilinearEquiv
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k)) :
    MonoidAlgebra L (Multiplicative M) ≃ₛₗ[(sigma.toRingEquiv : L →+* L)]
      MonoidAlgebra L (Multiplicative M) :=
  { (groupAlgebraAction rho sigma).toAddEquiv with
    map_smul' := groupAlgebraAction_smul rho sigma }

/-- The underlying map of the semilinear equivalence is the bundled Galois action. -/
@[simp]
theorem groupAlgebraActionSemilinearEquiv_apply
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (x : MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraActionSemilinearEquiv rho sigma x = groupAlgebraAction rho sigma x :=
  (rfl)

/-- On the tensor square of the coordinate algebra, the descent datum acts on both tensor
factors. -/
noncomputable def groupAlgebraTensorActionSemilinearEquiv
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k)) :
    ((MonoidAlgebra L (Multiplicative M)) ⊗[L]
        (MonoidAlgebra L (Multiplicative M))) ≃ₛₗ[(sigma.toRingEquiv : L →+* L)]
      ((MonoidAlgebra L (Multiplicative M)) ⊗[L]
        (MonoidAlgebra L (Multiplicative M))) :=
  TensorProduct.congr (groupAlgebraActionSemilinearEquiv rho sigma)
    (groupAlgebraActionSemilinearEquiv rho sigma)

/-- The semilinear tensor action evaluates on a pure tensor by acting on both factors. -/
@[simp]
theorem groupAlgebraTensorActionSemilinearEquiv_tmul
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (x y : MonoidAlgebra L (Multiplicative M)) :
    groupAlgebraTensorActionSemilinearEquiv rho sigma (x ⊗ₜ[L] y) =
      groupAlgebraAction rho sigma x ⊗ₜ[L] groupAlgebraAction rho sigma y := by
  rw [groupAlgebraTensorActionSemilinearEquiv, TensorProduct.congr_tmul]
  rfl

/-- The descent datum commutes with the counit, with the scalar output acted on by the Galois
automorphism. -/
@[simp]
theorem counit_groupAlgebraAction
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (x : MonoidAlgebra L (Multiplicative M)) :
    Coalgebra.counit (R := L) (groupAlgebraAction rho sigma x) =
      sigma (Coalgebra.counit (R := L) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a => simp

/-- The descent datum commutes with the antipode. -/
@[simp]
theorem antipode_groupAlgebraAction
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
    (x : MonoidAlgebra L (Multiplicative M)) :
    HopfAlgebra.antipode L (groupAlgebraAction rho sigma x) =
      groupAlgebraAction rho sigma (HopfAlgebra.antipode L x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m a => simp

/-- The semilinear descent datum commutes with comultiplication after acting on both tensor
factors. -/
@[simp]
theorem comul_groupAlgebraAction
    (rho : Representation ℤ Gal(L/k) M) (sigma : Gal(L/k))
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
