/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Frobenius on the points of an affine group

Let `H` be a Hopf algebra over `ℤ` and let `A` be a commutative ring of exponential
characteristic `p`. Post-composition with Mathlib's `iterateFrobenius A p n` sends an `A`-valued
point `f : H →ₐ[ℤ] A` to the point `h ↦ f(h) ^ (p ^ n)`. Functoriality of convolution makes this
a group endomorphism of the points represented by `H`.

This is the field-endomorphism part of the pinned Chevalley--Demazure interface in Layer 9 of the
ReductiveGroups roadmap. Once a pinned group's integral coordinate Hopf algebra is constructed,
`frobeniusPoints p n` supplies the `p ^ n`-power endomorphism on its points over an algebraic
closure. The construction itself needs neither algebraic closedness nor finite type.

## Main definitions and results

* `TauCeti.HopfAlgebra.frobeniusPoints` is the induced group endomorphism on convolution points.
* `TauCeti.HopfAlgebra.frobeniusPoints_apply_apply` identifies its action with the
  `p ^ n`-power map.
* `TauCeti.HopfAlgebra.frobeniusPoints_add` gives the iteration law.
* `TauCeti.HopfAlgebra.mapValue_frobeniusPoints` proves naturality in the value algebra.

## References

The construction post-composes with Mathlib's `iterateFrobenius`, whose laws supply every proof
here, and reuses Tau Ceti's convolution-valued functor of points. It advances the “points over an
algebraically closed field” target in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`; that
target explicitly requests the `q`-power Frobenius as its first field-endomorphism case.
-/

public section

open WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable (p n : ℕ)
variable {H : Type u} [Semiring H] [_root_.HopfAlgebra ℤ H]
variable {A : Type v} [CommRing A] [ExpChar A p]

/-- The `p ^ n`-power Frobenius endomorphism on the group of `A`-valued points represented by
the integral Hopf algebra `H`.

It post-composes a point with the iterated Frobenius of `A`, regarded as a `ℤ`-algebra
endomorphism; passing through `ℤ` is what makes it act on the `ℤ`-valued functor of points of an
integral affine group scheme. -/
noncomputable def frobeniusPoints :
    WithConv (H →ₐ[ℤ] A) →* WithConv (H →ₐ[ℤ] A) :=
  AlgHom.mapValue (iterateFrobenius A p n).toIntAlgHom

/-- Frobenius on points is post-composition with the iterated Frobenius of the value algebra. -/
@[simp] theorem frobeniusPoints_apply (f : WithConv (H →ₐ[ℤ] A)) :
    frobeniusPoints p n f =
      toConv ((iterateFrobenius A p n).toIntAlgHom.comp f.ofConv) := by
  rw [frobeniusPoints, AlgHom.mapValue_apply]

/-- Pointwise, the `n`-fold Frobenius sends an `A`-valued point `f` to
`h ↦ f(h) ^ (p ^ n)`.

This is not a `simp` lemma: `frobeniusPoints_apply` and `RingHom.toIntAlgHom_coe` already
rewrite the left-hand side to `iterateFrobenius A p n (f.ofConv h)`, so the statement is not in
simp-normal form. -/
theorem frobeniusPoints_apply_apply (f : WithConv (H →ₐ[ℤ] A)) (h : H) :
    (frobeniusPoints p n f).ofConv h = f.ofConv h ^ p ^ n := by
  rw [frobeniusPoints_apply, ofConv_toConv, AlgHom.comp_apply, RingHom.toIntAlgHom_apply,
    iterateFrobenius_def]

/-- The zeroth Frobenius iterate is the identity on points. -/
@[simp] theorem frobeniusPoints_zero :
    frobeniusPoints p 0 (H := H) (A := A) = MonoidHom.id _ := by
  have : (iterateFrobenius A p 0).toIntAlgHom = AlgHom.id ℤ A :=
    AlgHom.ext (iterateFrobenius_zero_apply A p)
  rw [frobeniusPoints, this, AlgHom.mapValue_id]

/-- Frobenius iterates add under composition on the group of points. -/
theorem frobeniusPoints_add (m : ℕ) :
    frobeniusPoints p (n + m) (H := H) (A := A) =
      (frobeniusPoints p n).comp (frobeniusPoints p m) := by
  have : (iterateFrobenius A p (n + m)).toIntAlgHom =
      (iterateFrobenius A p n).toIntAlgHom.comp (iterateFrobenius A p m).toIntAlgHom :=
    AlgHom.ext (iterateFrobenius_add_apply A p n m)
  rw [frobeniusPoints, frobeniusPoints, frobeniusPoints, this, AlgHom.mapValue_comp]

variable {B : Type w} [CommRing B] [ExpChar B p]

/-- Naturality of Frobenius on points in the value algebra: Frobenius commutes with *every*
homomorphism `φ : A →ₐ[ℤ] B` of value algebras, so post-composing a point by `φ` before or after
applying the `n`-fold Frobenius gives the same point. -/
theorem mapValue_frobeniusPoints (φ : A →ₐ[ℤ] B) :
    (AlgHom.mapValue (H := H) φ).comp (frobeniusPoints p n (H := H) (A := A)) =
      (frobeniusPoints p n (H := H) (A := B)).comp (AlgHom.mapValue (H := H) φ) := by
  have : φ.comp (iterateFrobenius A p n).toIntAlgHom =
      (iterateFrobenius B p n).toIntAlgHom.comp φ :=
    AlgHom.ext fun a => φ.toRingHom.map_iterateFrobenius p a n
  rw [frobeniusPoints, frobeniusPoints, ← AlgHom.mapValue_comp, ← AlgHom.mapValue_comp, this]

end HopfAlgebra

end TauCeti
