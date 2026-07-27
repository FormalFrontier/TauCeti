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
  by
    simp only [tensorPower, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply]
    congr 1

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
    let e : (⨂[R]^d M) ⊗[R] (⨂[R]^1 M) ≃ₗ[R] (⨂[R]^(d + 1) M) :=
      TensorPower.mulEquiv
    have he : e.conj
        (TensorProduct.map (PiTensorProduct.map fun _ : Fin d => ρ g)
          (PiTensorProduct.map fun _ : Fin 1 => ρ g)) =
        PiTensorProduct.map (fun _ : Fin (d + 1) => ρ g) := by
      ext x
      simp only [LinearMap.compMultilinearMap_apply]
      -- `ext` leaves the pure tensor behind the defining multilinear map; expose it so the
      -- public apply lemmas below can rewrite the action without unfolding `TensorPower.mulEquiv`.
      change e.conj _ (⨂ₜ[R] i, x i) = _
      rw [LinearEquiv.conj_apply_apply]
      let a : Fin d → M := fun i => x (Fin.castAdd 1 i)
      let b : Fin 1 → M := fun i => x (Fin.natAdd d i)
      have hx : Fin.append a b = x := by
        ext i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simp only [a, Fin.append_left]
        · intro j
          simp only [b, Fin.append_right]
      have hsplit : e.symm (⨂ₜ[R] i, x i) =
          (⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i) := by
        apply e.injective
        rw [e.apply_symm_apply]
        -- Rewriting cannot match through the local name `e`; this conversion exposes exactly the
        -- public `tprod_mul_tprod` equation without unfolding the equivalence.
        rw [show e ((⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i)) =
          ⨂ₜ[R] i, Fin.append a b i from TensorPower.tprod_mul_tprod R a b]
        rw [hx]
      rw [hsplit, TensorProduct.map_tmul, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod]
      -- As above, make the let-bound equivalence transparent only through its public pure-tensor
      -- equation, which lets `rw` avoid the implementation of `TensorPower.mulEquiv`.
      rw [show e ((⨂ₜ[R] i, (ρ g) (a i)) ⊗ₜ[R] (⨂ₜ[R] i, (ρ g) (b i))) =
        ⨂ₜ[R] i, Fin.append (fun i => (ρ g) (a i)) (fun i => (ρ g) (b i)) i from
          TensorPower.tprod_mul_tprod R _ _]
      rw [PiTensorProduct.map_tprod]
      congr 1
      rw [← hx]
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Fin.append_left]
      · intro j
        simp only [Fin.append_right]
    rw [← he, LinearMap.trace_conj', LinearMap.trace_tensorProduct']
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
