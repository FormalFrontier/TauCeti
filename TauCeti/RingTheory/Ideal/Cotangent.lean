/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Extension.Basic

/-!
# Cotangent spaces of augmented algebras

For an augmentation `f : A →ₐ[R] R`, if the augmentation ideal is finitely generated over
`A`, then its cotangent space is finite over `R`.

## Main declarations

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
  -- The extension's `A → R` algebra map is the augmentation `f` by construction.
  have hker : P.ker = RingHom.ker f.toRingHom := by
    ext x
    change f x = 0 ↔ f x = 0
    rfl
  have hP : P.ker.FG := by
    rw [hker]
    exact h
  let _ : Module.Finite R P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) hP
  rw [← hker]
  exact Module.Finite.equiv (P.cotangentEquivCotangentKer.restrictScalars R)

/-- The cotangent space at an augmented point of a noetherian algebra is finite over the base.

The augmentation hypothesis is encoded by the codomain of `f`: because `f` is an `R`-algebra
homomorphism, it is a retraction of `algebraMap R A`. -/
theorem finite_cotangent_ker (f : A →ₐ[R] R) [IsNoetherianRing A] :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent :=
  finite_cotangent_ker_of_fg f (RingHom.ker f.toRingHom).fg_of_isNoetherianRing

end AlgHom

end TauCeti
