/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Character

/-!
# Tensor powers of representations

This file equips the tensor power of a representation with its diagonal action. The action on a
pure tensor applies the original action in every factor. This construction is used by the
classical-groups roadmap to form tensor powers of the standard representation.

## Main definitions

* `Representation.tensorPower` is the diagonal action on `⨂[R]^d M`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md), Layer 1.
-/

public section

open scoped TensorProduct

namespace Representation

universe u v w

variable {R : Type u} {G : Type v} {M : Type w}

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The diagonal action of `G` on the `d`-fold tensor power of a representation. -/
noncomputable def tensorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⨂[R]^d M) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun _ : Fin d => ρ)

/-- The tensor-power action applies the original action in every tensor factor. -/
@[simp]
theorem tensorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.tensorPower d g = PiTensorProduct.map fun _ : Fin d => ρ g :=
  by unfold tensorPower; rfl

end CommSemiring

section Field

variable [Field R] [Monoid G] [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- The character of a tensor-power representation is the corresponding power of the character. -/
@[simp]
theorem char_tensorPower (ρ : Representation R G M) (d : ℕ) (g : G) :
    (ρ.tensorPower d).character g = (ρ.character g) ^ d := by
  classical
  simp only [Representation.character, tensorPower_apply]
  induction d with
  | zero =>
    have hmap : PiTensorProduct.map (fun _ : Fin 0 => ρ g) = LinearMap.id := by
      rw [← PiTensorProduct.map_id]
      congr
      funext i
      exact Fin.elim0 i
    rw [hmap]
    let e := PiTensorProduct.isEmptyEquiv (Fin 0) (R := R) (s := fun _ => M)
    rw [← LinearMap.trace_conj' (LinearMap.id : (⨂[R]^0 M) →ₗ[R] _) e]
    simp [e]
  | succ d ih =>
    let e : (⨂[R]^d M) ⊗[R] (⨂[R]^1 M) ≃ₗ[R] (⨂[R]^(d + 1) M) :=
      TensorPower.mulEquiv
    have he : e.conj
        (TensorProduct.map (PiTensorProduct.map fun _ : Fin d => ρ g)
          (PiTensorProduct.map fun _ : Fin 1 => ρ g)) =
        PiTensorProduct.map (fun _ : Fin (d + 1) => ρ g) := by
      ext x
      apply e.symm.injective
      simp [LinearEquiv.conj_apply_apply, e, TensorPower.mulEquiv]
    rw [← he, LinearMap.trace_conj', LinearMap.trace_tensorProduct']
    have h_one : LinearMap.trace R (⨂[R]^1 M) (PiTensorProduct.map fun _ : Fin 1 => ρ g) =
        LinearMap.trace R M (ρ g) := by
      let e₁ := PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => M) 0
      rw [← LinearMap.trace_conj' (PiTensorProduct.map fun _ : Fin 1 => ρ g) e₁]
      congr 1
      ext x
      simp [LinearEquiv.conj_apply_apply, e₁]
    rw [ih, h_one, pow_succ]

end Field

end Representation
