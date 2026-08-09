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
  let P : Algebra.Extension R R :=
    Algebra.Extension.ofSurjective f (fun r ↦ ⟨algebraMap R A r, f.commutes r⟩)
  have hmap : algebraMap P.Ring R = f.toRingHom := by
    exact RingHom.algebraMap_toAlgebra f.toRingHom
  have hker : P.ker = RingHom.ker f.toRingHom := congrArg RingHom.ker hmap
  have hP : P.ker.FG := by
    rw [hker]
    exact h
  let _ : Module.Finite R P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) hP
  have hfinite : Module.Finite R P.ker.Cotangent :=
    Module.Finite.equiv (P.cotangentEquivCotangentKer.restrictScalars R)
  exact Module.Finite.equiv
    ((Ideal.Cotangent.equivOfEq P.ker (RingHom.ker f.toRingHom) hker).restrictScalars R)

/-- The cotangent space at an augmented point of a noetherian algebra is finite over the base.

The augmentation hypothesis is encoded by the codomain of `f`: because `f` is an `R`-algebra
homomorphism, it is a retraction of `algebraMap R A`. -/
theorem finite_cotangent_ker (f : A →ₐ[R] R) [IsNoetherianRing A] :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent :=
  finite_cotangent_ker_of_fg f (RingHom.ker f.toRingHom).fg_of_isNoetherianRing

end AlgHom

end TauCeti
