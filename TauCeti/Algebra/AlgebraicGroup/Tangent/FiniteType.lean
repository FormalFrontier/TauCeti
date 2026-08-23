/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.RingTheory.Ideal.Cotangent.Basic

/-!
# Finiteness of the tangent space of a finite-type affine monoid

The counit of a commutative bialgebra of finite type over a noetherian base has finite cotangent
space at the identity. Over a field it is consequently finite-dimensional and projective, which
is the finiteness input for the scalar-extension description of the tangent space and the adjoint
representation in the ReductiveGroups roadmap, Layer 2.

## Main declarations

* `TauCeti.Bialgebra.instModuleFiniteCotangentSpace`: the specialization to the counit of a
  finite-type commutative bialgebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 14.
-/

public section

namespace TauCeti.Bialgebra

open _root_.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The cotangent space at the identity of a finite-type commutative bialgebra over a noetherian
base is finite over that base. -/
instance instModuleFiniteCotangentSpace [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Module.Finite R (CotangentSpace R A) := by
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact AlgHom.finite_cotangent_ker (counitAlgHom R A)

end TauCeti.Bialgebra
