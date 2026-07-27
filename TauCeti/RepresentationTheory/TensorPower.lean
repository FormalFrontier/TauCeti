/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RepresentationTheory.Character

/-!
# Tensor powers of representations

This file equips the tensor power of a representation with its diagonal action. The action on a
pure tensor applies the original action in every factor. This construction is used by the
classical-groups roadmap to form tensor powers of the standard representation.

## Main definitions

* `Representation.tensorPower` is the diagonal action on `⨂[R]^d M`.
* `Representation.tensorPowerFDRep` is the corresponding finite-dimensional representation.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md), Layer 1.
-/

public section

open scoped TensorProduct

namespace Representation

universe u v

variable {R : Type u} {G : Type v} {M : Type u}

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The diagonal action of `G` on the `d`-fold tensor power of a representation. -/
noncomputable def tensorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⨂[R]^d M) where
  toFun g := PiTensorProduct.map fun _ : Fin d => ρ g
  map_one' := by
    change PiTensorProduct.map (fun _ : Fin d => ρ 1) = 1
    simpa only [map_one] using (PiTensorProduct.map_one (R := R) (s := fun _ : Fin d => M))
  map_mul' g h := by
    change PiTensorProduct.map (fun _ : Fin d => ρ (g * h)) =
      PiTensorProduct.map (fun _ : Fin d => ρ g) * PiTensorProduct.map (fun _ : Fin d => ρ h)
    simpa only [map_mul] using
      (PiTensorProduct.map_mul (R := R) (s := fun _ : Fin d => M)
        (fun _ : Fin d => ρ g) (fun _ : Fin d => ρ h))

/-- The tensor-power action applies the original action in every tensor factor. -/
@[simp]
theorem tensorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.tensorPower d g = PiTensorProduct.map fun _ : Fin d => ρ g :=
  by unfold tensorPower; rfl

end CommSemiring

section CommRing

variable [CommRing R] [Group G] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The tensor power of a finite representation, bundled as an object of `FDRep`. -/
noncomputable abbrev tensorPowerFDRep (ρ : Representation R G M) (d : ℕ) : FDRep R G :=
  FDRep.of (ρ.tensorPower d)

end CommRing

end Representation
