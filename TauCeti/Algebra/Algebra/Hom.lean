/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: `AlgHom`, `RingHom.toAlgebra` and `algebraMap` all occur in the statement below.
public import Mathlib.Algebra.Algebra.Hom

/-!
# The structure map of the algebra induced by an algebra homomorphism

An algebra homomorphism `f : A →ₐ[R] B` induces an `A`-algebra structure on `B`, namely
`f.toRingHom.toAlgebra`. Mathlib's `RingHom.algebraMap_toAlgebra` identifies the structure map of
that algebra with the homomorphism it was built from, but states it as an equality of *bundled ring
homomorphisms*. Every consumer that has to feed a hypothesis of the form `∀ z, algebraMap A B z =
f z` therefore applies it pointwise by hand, through `congrArg DFunLike.coe` and `congrFun`.

This file states the pointwise form once, for an `AlgHom`, which is the shape those consumers want:
the right-hand side is `f z` rather than `f.toRingHom z`.

## Main results

* `AlgHom.algebraMap_toAlgebra_apply`: `algebraMap A B z = f z` for the algebra structure
  `f.toRingHom.toAlgebra` induced by `f : A →ₐ[R] B`.

## Implementation notes

The codomain is a `CommSemiring`, not a `Semiring`. That is forced rather than chosen:
`RingHom.toAlgebra` is itself stated for `[CommSemiring R] [CommSemiring S]`
(`Mathlib/Algebra/Algebra/Defs.lean`), so the algebra instance this lemma is about does not exist
over a bare semiring codomain. The `Semiring` version of the construction is `RingHom.toAlgebra'`,
which takes a commutation hypothesis `∀ c x, i c * x = x * i c` and is a different instance; a
lemma about it would not apply to any of the call sites here, all of which build their algebra with
the unprimed `toAlgebra`.

This is original work, not ported: Mathlib carries the un-applied `RingHom.algebraMap_toAlgebra`
but no pointwise `AlgHom` form, though it does carry the analogous `_apply` lemmas for the other
`AlgHom` coercions (`AlgHom.toLinearMap_apply`, `AlgHom.toLieHom_apply`).
-/

public section

/-- **The structure map of `f.toRingHom.toAlgebra` is `f`**, pointwise. Mathlib's
`RingHom.algebraMap_toAlgebra` is the same fact as an equality of bundled ring homomorphisms; this
is the applied form, stated for an `AlgHom` so that the right-hand side is `f z`.

Consumers wanting a hypothesis `∀ z, algebraMap A B z = f z` can pass this lemma directly, since
`z` is explicit. -/
-- Proved from `RingHom.algebraMap_toAlgebra` and `AlgHom.coe_toRingHom` rather than by `rfl`:
-- both sides are definitionally equal, but `rfl` closes the goal only by reducing through
-- `toRingHom`, `toAlgebra`, `algebraMap` and two coercions -- exactly the fragile defeq this
-- lemma exists to spare its call sites.
theorem AlgHom.algebraMap_toAlgebra_apply {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (z : A) :
    @algebraMap A B _ _ f.toRingHom.toAlgebra z = f z := by
  rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
