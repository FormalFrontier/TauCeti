/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.TensorPower

/-!
# Tensor powers of the standard representation

This file specializes the diagonal tensor-power construction to the standard representation of
the general linear group. It supplies the tensor powers that underpin the Weyl construction for
polynomial representations.

## Main definitions

* `TauCeti.tensorPowerRep` is the `d`-fold tensor power of `stdRep`.
* `TauCeti.tensorPowerFDRep` is its bundled finite-dimensional form.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md), Layer 1, “The tensor power representation”.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The diagonal action of `GL n k` on the `d`-fold tensor power of its standard representation. -/
noncomputable abbrev tensorPowerRep :
    Representation k (GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (stdRep k n).tensorPower d

/-- The tensor-power standard action sends a pure tensor to the tensor of its matrix actions. -/
@[simp]
theorem tensorPowerRep_apply_tprod (g : GL (Fin n) k) (v : Fin d → Fin n → k) :
    tensorPowerRep k n d g (PiTensorProduct.tprod k v) =
      PiTensorProduct.tprod k (fun i => (g : Matrix (Fin n) (Fin n) k) *ᵥ v i) := by
  simp only [tensorPowerRep, Representation.tensorPower_apply_tprod, stdRep_apply_apply]

/-- The zero-fold tensor-power standard representation is trivial. -/
@[simp]
theorem tensorPowerRep_zero_apply (g : GL (Fin n) k) :
    tensorPowerRep k n 0 g = LinearMap.id :=
  Representation.tensorPower_zero_apply (stdRep k n) g

/-- The `d`-fold tensor power of the standard representation, bundled as an `FDRep`. -/
noncomputable abbrev tensorPowerFDRep : FDRep k (GL (Fin n) k) :=
  (stdRep k n).tensorPowerFDRep d

/-- The finite-dimensional tensor-power standard action agrees with the tensor-power action. -/
@[simp]
theorem tensorPowerFDRep_ρ :
    (tensorPowerFDRep k n d).ρ = tensorPowerRep k n d :=
  rfl

end CommRing

end TauCeti
