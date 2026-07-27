/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.TensorPower
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RepresentationTheory.Character

/-!
# Tensor powers of the standard representation

This file specializes the diagonal tensor-power construction to the standard representation of
the general linear group. It supplies the tensor powers that underpin the Weyl construction for
polynomial representations.

## Main definitions

* `TauCeti.tensorPowerRep` is the `d`-fold tensor power of `stdRep`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md), Layer 1, “The tensor power representation”.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

private theorem trace_map_tensorPower {M : Type u} [Field k] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] (f : M →ₗ[k] M) (d : ℕ) :
    LinearMap.trace k (⨂[k]^d M) (PiTensorProduct.map fun _ : Fin d => f) =
      (LinearMap.trace k M f) ^ d := by
  classical
  letI (d : ℕ) : FiniteDimensional k (⨂[k]^d M) :=
    (Basis.piTensorProduct fun _ : Fin d => Module.finBasis k M).finiteDimensional_of_finite
  induction d with
  | zero =>
    have hmap : PiTensorProduct.map (fun _ : Fin 0 => f) = LinearMap.id := by
      rw [← PiTensorProduct.map_id]
      congr
      funext i
      exact Fin.elim0 i
    rw [hmap]
    let e := PiTensorProduct.isEmptyEquiv (Fin 0) (R := k) (s := fun _ => M)
    rw [← LinearMap.trace_conj' (LinearMap.id : (⨂[k]^0 M) →ₗ[k] _) e]
    simp [e]
  | succ d ih =>
    let e : (⨂[k]^d M) ⊗[k] (⨂[k]^1 M) ≃ₗ[k] (⨂[k]^(d + 1) M) :=
      TensorPower.mulEquiv
    have he : e.conj
        (TensorProduct.map (PiTensorProduct.map fun _ : Fin d => f)
          (PiTensorProduct.map fun _ : Fin 1 => f)) =
        PiTensorProduct.map (fun _ : Fin (d + 1) => f) := by
      ext x
      apply e.symm.injective
      simp [LinearEquiv.conj_apply_apply, e, TensorPower.mulEquiv]
    rw [← he, LinearMap.trace_conj', LinearMap.trace_tensorProduct']
    have h_one : LinearMap.trace k (⨂[k]^1 M) (PiTensorProduct.map fun _ : Fin 1 => f) =
        LinearMap.trace k M f := by
      let e₁ := PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => M) 0
      rw [← LinearMap.trace_conj' (PiTensorProduct.map fun _ : Fin 1 => f) e₁]
      congr 1
      ext x
      simp [LinearEquiv.conj_apply_apply, e₁]
    rw [ih, h_one, pow_succ]

section CommRing

variable [CommRing k]

/-- The diagonal action of `GL n k` on the `d`-fold tensor power of its standard representation. -/
noncomputable abbrev tensorPowerRep :
    Representation k (GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (stdRep k n).tensorPower d

end CommRing

section Field

variable [Field k]

/- The finite-dimensionality instance for tensor powers is constructed locally in the proof below
from Mathlib's `Basis.piTensorProduct`, since Mathlib does not provide it globally. -/
/-- The character of the tensor power is the corresponding power of the standard character. -/
theorem char_tensorPowerRep (g : GL (Fin n) k) :
    (tensorPowerRep k n d).character g = ((stdRep k n).character g) ^ d := by
  simp only [Representation.character, tensorPowerRep, Representation.tensorPower_apply]
  exact trace_map_tensorPower k ((stdRep k n) g) d

end Field

end TauCeti
