/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient

/-!
# Homomorphisms from quotients by Lie ideals

Mathlib equips the quotient of a Lie algebra by a Lie ideal with its Lie algebra structure and
provides the quotient map as a morphism of Lie modules. This file records that map as a
homomorphism of Lie algebras and gives its universal property: a homomorphism killing the ideal
factors uniquely through the quotient.

These declarations live in the root `LieIdeal` namespace, extending Mathlib's API and supporting
receiver notation on the ideal.

## Main definitions

* `LieIdeal.mkQ`: the quotient map `L →ₗ⁅R⁆ L ⧸ I`.
* `LieIdeal.liftQ`: the homomorphism `L ⧸ I →ₗ⁅R⁆ L'` induced by a homomorphism
  `L →ₗ⁅R⁆ L'` whose kernel contains `I`.

## Main results

* `LieIdeal.mkQ_surjective`: every quotient class has a representative in the original Lie
  algebra.
* `LieIdeal.liftQ_mkQ`: the lifted homomorphism restricts to the original one along the quotient
  map.
* `LieIdeal.lieHom_qext`: two homomorphisms from the quotient are equal when they agree after the
  quotient map.
* `LieIdeal.eq_liftQ`: the lifted homomorphism is the unique such factorization.
-/

public section

namespace LieIdeal

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (I : LieIdeal R L)

/-- The quotient map `L → L ⧸ I` as a homomorphism of Lie algebras.

Its underlying function is Mathlib's `LieSubmodule.Quotient.mk`, sending each element to its
quotient class. -/
def mkQ : L →ₗ⁅R⁆ L ⧸ I where
  __ := I.toSubmodule.mkQ
  map_lie' := rfl

/-- The quotient homomorphism sends an element to its class. -/
@[simp]
theorem mkQ_apply (x : L) : I.mkQ x = LieSubmodule.Quotient.mk x := (rfl)

/-- Every element of the quotient has a representative in the original Lie algebra. -/
theorem mkQ_surjective : Function.Surjective I.mkQ := fun y => by
  obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' I y
  exact ⟨x, (I.mkQ_apply x).trans hx⟩

/-- The kernel of the quotient homomorphism is the ideal quotiented by. -/
@[simp]
theorem ker_mkQ : I.mkQ.ker = I := by
  ext x
  simp [LieHom.mem_ker]

/-- The homomorphism `L ⧸ I →ₗ⁅R⁆ L'` induced by a homomorphism `f : L →ₗ⁅R⁆ L'` whose kernel
contains the ideal `I`. -/
def liftQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) : L ⧸ I →ₗ⁅R⁆ L' where
  __ := LieSubmodule.toSubmodule I |>.liftQ (f : L →ₗ[R] L') h
  map_lie' {x y} := by
    induction x using Quotient.inductionOn' with | _ x
    induction y using Quotient.inductionOn' with | _ y
    exact f.map_lie x y

/-- The induced homomorphism on the quotient sends the class of `x` to `f x`. -/
@[simp]
theorem liftQ_apply (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) (x : L) :
    I.liftQ f h (LieSubmodule.Quotient.mk x) = f x := (rfl)

/-- The induced homomorphism on the quotient composed with the quotient map is the original
homomorphism. -/
@[simp]
theorem liftQ_mkQ (f : L →ₗ⁅R⁆ L') (h : I ≤ f.ker) : (I.liftQ f h).comp I.mkQ = f := by
  ext x
  simp

/-- Two homomorphisms out of `L ⧸ I` that agree after composition with the quotient map are
equal. -/
@[ext high]
theorem lieHom_qext {g₁ g₂ : L ⧸ I →ₗ⁅R⁆ L'} (h : ∀ x : L, g₁ (I.mkQ x) = g₂ (I.mkQ x)) :
    g₁ = g₂ := by
  apply LieHom.ext
  exact LinearMap.congr_fun <|
    Submodule.quot_hom_ext I.toSubmodule g₁.toLinearMap g₂.toLinearMap fun x => h x

/-- The factorization of `LieIdeal.liftQ` is the only one: a homomorphism out of `L ⧸ I`
restricting to `f` along the quotient map is `I.liftQ f h`. -/
theorem eq_liftQ {f : L →ₗ⁅R⁆ L'} {h : I ≤ f.ker} {g : L ⧸ I →ₗ⁅R⁆ L'}
    (hg : ∀ x : L, g (I.mkQ x) = f x) : g = I.liftQ f h :=
  I.lieHom_qext fun x => by rw [hg]; simp

end LieIdeal
