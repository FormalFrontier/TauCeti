/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* `TauCeti.Bialgebra.mapValue_comp_iterateFrobeniusPoints` proves naturality in the value algebra.

## Implementation notes

The construction post-composes with Mathlib's `iterateFrobenius`, whose laws supply every proof
here, and reuses Tau Ceti's convolution-valued functor of points. Those laws are equalities of
ring homomorphisms, while `AlgHom.mapValue` consumes `ℤ`-algebra homomorphisms; Mathlib has
`RingHom.toIntAlgHom_coe` and `toIntAlgHom_apply` but no identity or composition lemma for
`RingHom.toIntAlgHom`, so three private lemmas below record its functoriality and transport the
Mathlib equalities into `AlgHom`. This file advances the “points over an algebraically closed
field” target in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`; that target explicitly
requests the `q`-power Frobenius as its first field-endomorphism case.
-/

public section

open WithConv

namespace TauCeti

namespace Bialgebra

universe u v w

section ToIntAlgHom

variable {R : Type*} {S : Type*} {T : Type*} [Ring R] [Ring S] [Ring T]

/-- `RingHom.toIntAlgHom` sends the identity ring homomorphism to the identity `ℤ`-algebra
homomorphism. Kept private: it is a wrapper identity used only to transport Mathlib's ring
homomorphism equalities into `AlgHom`. -/
private lemma toIntAlgHom_id : (RingHom.id R).toIntAlgHom = AlgHom.id ℤ R :=
  AlgHom.ext fun _ ↦ rfl

/-- `RingHom.toIntAlgHom` preserves composition. Kept private: it is a wrapper identity used only
to transport Mathlib's ring homomorphism equalities into `AlgHom`. -/
private lemma toIntAlgHom_comp (f : S →+* T) (g : R →+* S) :
    (f.comp g).toIntAlgHom = f.toIntAlgHom.comp g.toIntAlgHom :=
  AlgHom.ext fun _ ↦ rfl

/-- `RingHom.toIntAlgHom` is a left inverse of `AlgHom.toRingHom` on `ℤ`-algebra homomorphisms.
Kept private: it is a wrapper identity used only to transport Mathlib's ring homomorphism
equalities into `AlgHom`. -/
private lemma toIntAlgHom_toRingHom (φ : R →ₐ[ℤ] S) : φ.toRingHom.toIntAlgHom = φ :=
  AlgHom.ext fun _ ↦ rfl

end ToIntAlgHom

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
  rw [iterateFrobeniusPoints, iterateFrobenius_zero, toIntAlgHom_id, AlgHom.mapValue_id]

/-- Frobenius iterates add under composition on the monoid of points. -/
theorem iterateFrobeniusPoints_add (m : ℕ) :
    iterateFrobeniusPoints p (n + m) (H := H) (A := A) =
      (iterateFrobeniusPoints p n).comp (iterateFrobeniusPoints p m) := by
  rw [iterateFrobeniusPoints, iterateFrobeniusPoints, iterateFrobeniusPoints,
    iterateFrobenius_add, toIntAlgHom_comp, AlgHom.mapValue_comp]

variable {B : Type w} [CommRing B] [ExpChar B p]

/-- Naturality of Frobenius on points in the value algebra: Frobenius commutes with every
homomorphism `φ : A →ₐ[ℤ] B` into a value algebra of the same exponential characteristic `p`, so
post-composing a point by `φ` before or after applying the `n`-fold Frobenius gives the same
point. -/
theorem mapValue_comp_iterateFrobeniusPoints (φ : A →ₐ[ℤ] B) :
    (AlgHom.mapValue (H := H) φ).comp (iterateFrobeniusPoints p n (H := H) (A := A)) =
      (iterateFrobeniusPoints p n (H := H) (A := B)).comp (AlgHom.mapValue (H := H) φ) := by
  -- Mathlib's commuting square lives in `RingHom`; transport it along `RingHom.toIntAlgHom`.
  have hφ : φ.comp (iterateFrobenius A p n).toIntAlgHom =
      (iterateFrobenius B p n).toIntAlgHom.comp φ := by
    have h := congrArg RingHom.toIntAlgHom (φ.toRingHom.iterateFrobenius_comm p n)
    rwa [toIntAlgHom_comp, toIntAlgHom_comp, toIntAlgHom_toRingHom] at h
  rw [iterateFrobeniusPoints, iterateFrobeniusPoints, ← AlgHom.mapValue_comp,
    ← AlgHom.mapValue_comp, hφ]

end Bialgebra

end TauCeti
