/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The spectrum point defined by an augmentation

An algebra homomorphism from a commutative algebra to its ground field determines a rational point
of the algebra's prime spectrum. This file records that point and its underlying prime ideal.

## Main declarations

* `TauCeti.AlgHom.kernelPoint`: the point cut out by the kernel of an augmentation.
-/

public section

open AlgebraicGeometry IsLocalRing

namespace TauCeti.AlgHom

universe u v

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Algebra k H]
variable (f : H →ₐ[k] k)

/-- The point of `Spec H` defined by an augmentation `f : H →ₐ[k] k`. Its prime ideal is
`ker f`. -/
def kernelPoint : Spec (CommRingCat.of H) :=
  PrimeSpectrum.comap (f : H →+* k) (closedPoint k)

/-- The prime ideal of an augmentation point is the kernel of the augmentation. -/
@[simp]
theorem kernelPoint_asIdeal :
    (kernelPoint f).asIdeal = RingHom.ker (f : H →+* k) := by
  rw [kernelPoint, PrimeSpectrum.comap_asIdeal]
  dsimp only [closedPoint]
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

end TauCeti.AlgHom
