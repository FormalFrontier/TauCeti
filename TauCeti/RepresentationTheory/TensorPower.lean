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

/-- A family of linear maps indexed by `Fin 0` acts as the identity on the zero-fold tensor
power. -/
@[simp]
theorem map_fin_zero (f : Fin 0 → M →ₗ[R] M) :
    PiTensorProduct.map f = LinearMap.id := by
  rw [← PiTensorProduct.map_id]
  congr
  funext i
  exact Fin.elim0 i

private theorem append_const {α : Type*} {d e : ℕ} (x : α) :
    Fin.append (fun _ : Fin d => x) (fun _ : Fin e => x) = fun _ : Fin (d + e) => x := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> simp

private theorem mulEquiv_map {d e : ℕ} (f : Fin d → M →ₗ[R] M)
    (g : Fin e → M →ₗ[R] M) :
    (_root_.TensorPower.mulEquiv :
      (⨂[R]^d M) ⊗[R] (⨂[R]^e M) ≃ₗ[R] (⨂[R]^(d + e) M)).toLinearMap ∘ₗ
        TensorProduct.map (PiTensorProduct.map f) (PiTensorProduct.map g) =
      PiTensorProduct.map (Fin.append f g) ∘ₗ
        (_root_.TensorPower.mulEquiv :
          (⨂[R]^d M) ⊗[R] (⨂[R]^e M) ≃ₗ[R] (⨂[R]^(d + e) M)).toLinearMap := by
  ext x y
  simp only [LinearMap.compMultilinearMap_apply, TensorProduct.AlgebraTensorModule.curry_apply,
    LinearMap.restrictScalars_self, TensorProduct.curry_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul,
    PiTensorProduct.map_tprod]
  rw [← _root_.TensorPower.gMul_def, _root_.TensorPower.tprod_mul_tprod,
    ← _root_.TensorPower.gMul_def, _root_.TensorPower.tprod_mul_tprod,
    PiTensorProduct.map_tprod]
  congr 1 with i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Fin.append]

/-- Splitting a tensor power intertwines separate families of maps on the two factors with
their appended family on the combined tensor power. -/
theorem mulEquiv_conj_map {d e : ℕ} (f : Fin d → M →ₗ[R] M) (g : Fin e → M →ₗ[R] M) :
    (_root_.TensorPower.mulEquiv :
      (⨂[R]^d M) ⊗[R] (⨂[R]^e M) ≃ₗ[R] (⨂[R]^(d + e) M)).conj
        (TensorProduct.map (PiTensorProduct.map f) (PiTensorProduct.map g)) =
      PiTensorProduct.map (Fin.append f g) := by
  apply LinearMap.ext
  intro x
  rw [LinearEquiv.conj_apply_apply]
  have h := LinearMap.congr_fun (mulEquiv_map f g)
    ((_root_.TensorPower.mulEquiv :
      (⨂[R]^d M) ⊗[R] (⨂[R]^e M) ≃ₗ[R] (⨂[R]^(d + e) M)).symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.coe_coe] using h

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

/-- The action on the zero-fold tensor power is the identity.

This is intentionally not a simp lemma: `tensorPower_apply` followed by
`TauCeti.TensorPower.map_fin_zero` already performs this simplification. -/
theorem tensorPower_zero_apply (ρ : Representation R G M) (g : G) :
    ρ.tensorPower 0 g = LinearMap.id := by
  simp

/-- Splitting the factors gives an equivalence from the tensor product of two tensor-power
representations to the tensor power indexed by their sum. -/
noncomputable def tensorPowerAddEquiv (ρ : Representation R G M) (d e : ℕ) :
    ((ρ.tensorPower d).tprod (ρ.tensorPower e)).Equiv (ρ.tensorPower (d + e)) :=
  .mk (_root_.TensorPower.mulEquiv) fun g => by
    rw [tprod_apply, tensorPower_apply, tensorPower_apply, tensorPower_apply]
    simpa only [TauCeti.TensorPower.append_const] using
      TauCeti.TensorPower.mulEquiv_map (fun _ : Fin d => ρ g) (fun _ : Fin e => ρ g)

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
    rw [TauCeti.TensorPower.map_fin_zero]
    let e := PiTensorProduct.isEmptyEquiv (Fin 0) (R := R) (s := fun _ => M)
    rw [← LinearMap.trace_conj' (LinearMap.id : (⨂[R]^0 M) →ₗ[R] _) e]
    rw [LinearEquiv.conj_id, LinearMap.trace_id, Module.finrank_self, Nat.cast_one]
    simp only [pow_zero]
  | succ d ih =>
    -- Split `Fin (d + 1)` into `Fin d` and `Fin 1`, then use multiplicativity of trace.
    rw [← TauCeti.TensorPower.append_const (d := d) (e := 1) (ρ g),
      ← TauCeti.TensorPower.mulEquiv_conj_map (fun _ : Fin d => ρ g)
      (fun _ : Fin 1 => ρ g), LinearMap.trace_conj',
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
