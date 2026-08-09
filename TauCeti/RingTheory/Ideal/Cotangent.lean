/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Extension.Basic

/-!
# Cotangent spaces of augmented algebras

For an augmentation `f : A →ₐ[R] R`, the action of `A` on
`ker(f) / ker(f)²` factors through `f`. Consequently, if the augmentation ideal is finitely
generated over `A`, then its cotangent space is finite over `R`.

## Main declarations

* `TauCeti.AlgHom.smul_eq_map_smul`: the ambient scalar action factors through the augmentation.
* `TauCeti.AlgHom.finite_cotangent_ker_of_fg`: finite generation of the augmentation ideal gives
  finiteness of its cotangent space over the base.
* `TauCeti.AlgHom.finite_cotangent_ker`: the noetherian specialization.

## References

* Mathlib's `Algebra.Extension.Cotangent.finite` provides the generic cotangent-space finiteness
  result used here.
-/

public section

namespace TauCeti

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- On `ker(f) / ker(f)²`, multiplication by `a : A` agrees with scalar multiplication by
`f a : R`, for an augmentation `f : A →ₐ[R] R`. -/
@[simp]
theorem smul_eq_map_smul (f : A →ₐ[R] R) (a : A)
    (x : (RingHom.ker f.toRingHom).Cotangent) :
    a • x = f a • x := by
  let I := RingHom.ker f.toRingHom
  have ha : a - algebraMap R A (f a) ∈ I := by
    simp [I]
  have hzero : (a - algebraMap R A (f a)) • x = 0 :=
    Ideal.Cotangent.smul_eq_zero_of_mem ha x
  rw [sub_smul, sub_eq_zero, algebraMap_smul] at hzero
  exact hzero

/-- The cotangent space of an augmentation with finitely generated kernel is finite over the
base. -/
theorem finite_cotangent_ker_of_fg (f : A →ₐ[R] R)
    (h : (RingHom.ker f.toRingHom).FG) :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent := by
  let algAR : Algebra A R := f.toAlgebra
  let P : Algebra.Extension R R :=
    { Ring := A
      algebra₂ := algAR
      isScalarTower := @IsScalarTower.of_algebraMap_eq' R A R _ _ _ _ algAR _
        f.comp_algebraMap.symm
      σ := algebraMap R A
      algebraMap_σ := f.commutes }
  have hP : P.ker.FG := h
  let _ : Module.Finite R P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) hP
  exact Module.Finite.equiv
    (P.cotangentEquivCotangentKer.restrictScalars R)

/-- The cotangent space at an augmented point of a noetherian algebra is finite over the base.

The augmentation hypothesis is encoded by the codomain of `f`: because `f` is an `R`-algebra
homomorphism, it is a retraction of `algebraMap R A`. -/
theorem finite_cotangent_ker (f : A →ₐ[R] R) [IsNoetherianRing A] :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent :=
  finite_cotangent_ker_of_fg f (RingHom.ker f.toRingHom).fg_of_isNoetherianRing

end AlgHom

end TauCeti
