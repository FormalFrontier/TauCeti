/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.Bialgebra.Augmentation

/-!
# The augmentation point of a commutative Hopf algebra

The antipode fixes the augmentation point of a commutative Hopf algebra. This is the
prime-spectrum form of the identity saying that the counit composed with the antipode is the
counit.

## Main declarations

* `TauCeti.HopfAlgebra.comap_antipodeAlgHom_augmentationPoint_eq_self`: contraction along the
  antipode fixes the augmentation point.
-/

public section

open AlgebraicGeometry

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra k H]

/-- Contraction along the antipode fixes the prime defined by the counit. -/
theorem comap_antipodeAlgHom_augmentationPoint_eq_self :
    PrimeSpectrum.comap (_root_.HopfAlgebra.antipodeAlgHom k H)
        (Bialgebra.augmentationPoint k H) = Bialgebra.augmentationPoint k H := by
  rw [AlgHom.comap_kernelPoint, AlgHom.counitAlgHom_comp_antipodeAlgHom]

end TauCeti.HopfAlgebra
