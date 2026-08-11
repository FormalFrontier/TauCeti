/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Frobenius on convolution points

Let `H` be a bialgebra over `ℤ` and let `A` be a commutative ring of exponential
characteristic `p`. Post-composition with Mathlib's `iterateFrobenius A p n` sends an `A`-valued
point `f : H →ₐ[ℤ] A` to the point `h ↦ f(h) ^ (p ^ n)`. Functoriality of convolution makes this
a monoid endomorphism of the points represented by `H`. When `H` is a Hopf algebra, these
convolution points form a group. If `H` is also commutative, they are the points of the affine
group scheme `Spec H`.

This is the field-endomorphism part of the pinned Chevalley--Demazure interface in Layer 9 of the
ReductiveGroups roadmap. Once a pinned group's integral coordinate Hopf algebra is constructed,
`iterateFrobeniusPoints p n` supplies the `p ^ n`-power endomorphism on its points over an
algebraic closure. The construction itself needs neither algebraic closedness nor finite type.

## Main definitions and results

* `TauCeti.Bialgebra.iterateFrobeniusPoints` is the induced monoid endomorphism on convolution
  points.
* `TauCeti.Bialgebra.iterateFrobeniusPoints_apply_apply` identifies its action with the
  `p ^ n`-power map.
* `TauCeti.Bialgebra.iterateFrobeniusPoints_zero` identifies the zeroth iterate.
* `TauCeti.Bialgebra.iterateFrobeniusPoints_add` gives the iteration law.
* `TauCeti.Bialgebra.iterateFrobeniusPoints_comm` proves naturality in the value algebra.

## Implementation notes

The construction post-composes with Mathlib's `iterateFrobenius`, whose laws supply every proof
here, and reuses Tau Ceti's convolution-valued functor of points. It advances the “points over an
algebraically closed field” target in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`; that
target explicitly requests the `q`-power Frobenius as its first field-endomorphism case.
-/

public section

open WithConv

namespace TauCeti

namespace Bialgebra

universe u v w

variable (p n : ℕ)
variable {H : Type u} [Semiring H] [_root_.Bialgebra ℤ H]
variable {A : Type v} [CommRing A] [ExpChar A p]

/-- The `p ^ n`-power Frobenius endomorphism on the monoid of `A`-valued points represented by
the integral bialgebra `H`.

It post-composes a point with the iterated Frobenius of `A`, regarded as a `ℤ`-algebra
endomorphism. Frobenius is only a ring homomorphism, not an `A`-algebra homomorphism; regarding
it as its canonical `ℤ`-algebra homomorphism lets `AlgHom.mapValue` act at base `ℤ`. -/
noncomputable def iterateFrobeniusPoints :
    WithConv (H →ₐ[ℤ] A) →* WithConv (H →ₐ[ℤ] A) :=
  AlgHom.mapValue (iterateFrobenius A p n).toIntAlgHom

/-- Frobenius on points is post-composition with the iterated Frobenius of the value algebra. -/
theorem iterateFrobeniusPoints_apply (f : WithConv (H →ₐ[ℤ] A)) :
    iterateFrobeniusPoints p n f =
      toConv ((iterateFrobenius A p n).toIntAlgHom.comp f.ofConv) := by
  rw [iterateFrobeniusPoints, AlgHom.mapValue_apply]

/-- Pointwise, the `n`-fold Frobenius sends an `A`-valued point `f` to
`h ↦ f(h) ^ (p ^ n)`.

This is the simp-normal form of a value of `iterateFrobeniusPoints`; `iterateFrobeniusPoints_apply`
is deliberately not a `simp` lemma, since rewriting with it would leave the left-hand side at the
implementation-level `iterateFrobenius` expression instead. -/
@[simp] theorem iterateFrobeniusPoints_apply_apply (f : WithConv (H →ₐ[ℤ] A)) (h : H) :
    (iterateFrobeniusPoints p n f).ofConv h = f.ofConv h ^ p ^ n := by
  rw [iterateFrobeniusPoints_apply, ofConv_toConv, AlgHom.comp_apply, RingHom.toIntAlgHom_apply,
    iterateFrobenius_def]

/-- The zeroth Frobenius iterate is the identity on points. -/
@[simp] theorem iterateFrobeniusPoints_zero :
    iterateFrobeniusPoints p 0 (H := H) (A := A) = MonoidHom.id _ := by
  have : (iterateFrobenius A p 0).toIntAlgHom = AlgHom.id ℤ A := by
    ext x
    exact iterateFrobenius_zero_apply A p x
  rw [iterateFrobeniusPoints, this, AlgHom.mapValue_id]

/-- Frobenius iterates add under composition on the monoid of points. -/
theorem iterateFrobeniusPoints_add (m : ℕ) :
    iterateFrobeniusPoints p (n + m) (H := H) (A := A) =
      (iterateFrobeniusPoints p n).comp (iterateFrobeniusPoints p m) := by
  have : (iterateFrobenius A p (n + m)).toIntAlgHom =
      (iterateFrobenius A p n).toIntAlgHom.comp (iterateFrobenius A p m).toIntAlgHom := by
    ext x
    exact iterateFrobenius_add_apply A p n m x
  rw [iterateFrobeniusPoints, iterateFrobeniusPoints, iterateFrobeniusPoints, this,
    AlgHom.mapValue_comp]

variable {B : Type w} [CommRing B] [ExpChar B p]

/-- Naturality of Frobenius on points in the value algebra: Frobenius commutes with every
homomorphism `φ : A →ₐ[ℤ] B` into a value algebra of the same exponential characteristic `p`, so
post-composing a point by `φ` before or after applying the `n`-fold Frobenius gives the same
point. -/
theorem iterateFrobeniusPoints_comm (φ : A →ₐ[ℤ] B) :
    (AlgHom.mapValue (H := H) φ).comp (iterateFrobeniusPoints p n (H := H) (A := A)) =
      (iterateFrobeniusPoints p n (H := H) (A := B)).comp (AlgHom.mapValue (H := H) φ) := by
  have : φ.comp (iterateFrobenius A p n).toIntAlgHom =
      (iterateFrobenius B p n).toIntAlgHom.comp φ := by
    ext x
    exact φ.toRingHom.map_iterateFrobenius p x n
  rw [iterateFrobeniusPoints, iterateFrobeniusPoints, ← AlgHom.mapValue_comp,
    ← AlgHom.mapValue_comp, this]

end Bialgebra

end TauCeti
