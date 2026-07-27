/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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

universe u v w

variable {R : Type u} {G : Type v} {M : Type w}

namespace TauCeti.TensorPower

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Splitting a tensor power intertwines the tensor product of diagonal maps with the
diagonal map on the combined tensor power. -/
theorem mulEquiv_conj_map (f : M →ₗ[R] M) (d e : ℕ) :
    (_root_.TensorPower.mulEquiv :
      (⨂[R]^d M) ⊗[R] (⨂[R]^e M) ≃ₗ[R] (⨂[R]^(d + e) M)).conj
        (TensorProduct.map (PiTensorProduct.map fun _ : Fin d => f)
          (PiTensorProduct.map fun _ : Fin e => f)) =
      PiTensorProduct.map (fun _ : Fin (d + e) => f) := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply]
  rw [LinearEquiv.conj_apply_apply]
  let a : Fin d → M := fun i => x (Fin.castAdd e i)
  let b : Fin e → M := fun i => x (Fin.natAdd d i)
  have hx : Fin.append a b = x := by
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [a, Fin.append_left]
    · intro j
      simp only [b, Fin.append_right]
  have hsplit : (_root_.TensorPower.mulEquiv :
      (⨂[R]^d M) ⊗[R] (⨂[R]^e M) ≃ₗ[R] (⨂[R]^(d + e) M)).symm (⨂ₜ[R] i, x i) =
      (⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i) := by
    apply (_root_.TensorPower.mulEquiv :
      (⨂[R]^d M) ⊗[R] (⨂[R]^e M) ≃ₗ[R] (⨂[R]^(d + e) M)).injective
    rw [LinearEquiv.apply_symm_apply]
    rw [← _root_.TensorPower.gMul_def, _root_.TensorPower.tprod_mul_tprod]
    rw [hx]
  rw [hsplit, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
    PiTensorProduct.map_tprod]
  rw [← _root_.TensorPower.gMul_def, _root_.TensorPower.tprod_mul_tprod]
  rw [PiTensorProduct.map_tprod]
  congr 1
  rw [← hx]
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left]
  · intro j
    simp only [Fin.append_right]

end CommSemiring

end TauCeti.TensorPower

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- The diagonal action of `G` on the `d`-fold tensor power of a representation. -/
noncomputable def tensorPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (⨂[R]^d M) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun _ : Fin d => ρ)

/-- The tensor-power action applies the original action in every tensor factor. -/
@[simp]
theorem tensorPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.tensorPower d g = PiTensorProduct.map fun _ : Fin d => ρ g := by
  simp only [tensorPower, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply]
  exact congrArg PiTensorProduct.map (funext fun i => MonoidHom.pi_apply _ g i)

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
    rw [LinearEquiv.conj_id, LinearMap.trace_id, Module.finrank_self, Nat.cast_one]
    simp only [pow_zero]
  | succ d ih =>
    -- Split `Fin (d + 1)` into `Fin d` and `Fin 1`, then use multiplicativity of trace.
    rw [← TauCeti.TensorPower.mulEquiv_conj_map, LinearMap.trace_conj',
      LinearMap.trace_tensorProduct']
    have h_one : LinearMap.trace R (⨂[R]^1 M) (PiTensorProduct.map fun _ : Fin 1 => ρ g) =
        LinearMap.trace R M (ρ g) := by
      let e₁ := PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => M) 0
      rw [← LinearMap.trace_conj' (PiTensorProduct.map fun _ : Fin 1 => ρ g) e₁]
      congr 1
      ext x
      rw [LinearEquiv.conj_apply_apply]
      have he₁ : e₁.symm x = ⨂ₜ[R] _ : Fin 1, x := by
        simpa only using
          (PiTensorProduct.subsingletonEquiv_symm_apply' (R := R) (ι := Fin 1) 0 x)
      rw [he₁, PiTensorProduct.map_tprod, PiTensorProduct.subsingletonEquiv_apply_tprod]
    rw [ih, h_one, pow_succ]

end Field

end Representation
