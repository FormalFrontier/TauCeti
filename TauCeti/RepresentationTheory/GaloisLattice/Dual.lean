/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.GaloisLattice.Basic

/-!
# Duals of integral Galois lattices

The contragredient representation on the integral dual of a Galois lattice is again a Galois
lattice. Continuity is proved using a finite basis: the pointwise stabilizer of that basis is an
open subgroup, and it fixes every linear functional under the contragredient action.

## Main declaration

* `TauCeti.galoisLatticeProperty_dual`: the integral dual of a Galois lattice,
  with its contragredient action, is a Galois lattice.
* `TauCeti.galoisLatticeProperty_contragredient`: transport the contragredient action across a
  linear equivalence with an integral dual.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k V : Type u} [Field k] [AddCommGroup V]
variable [Module.Free ℤ V] [Module.Finite ℤ V]

/-- A representation identified equivariantly with the contragredient of a Galois lattice is
itself a Galois lattice. This form lets a construction retain its intrinsic carrier rather than
replacing it by an integral dual. -/
theorem galoisLatticeProperty_contragredient
    {W : Type u} [AddCommGroup W] [Module ℤ W]
    (ρ : Representation ℤ (Field.absoluteGaloisGroup k) V)
    (τ : Representation ℤ (Field.absoluteGaloisGroup k) W)
    (e : W ≃ₗ[ℤ] Module.Dual ℤ V)
    (he : ∀ (σ : Field.absoluteGaloisGroup k) (w : W) (x : V),
      e (τ σ w) x = e w (ρ σ⁻¹ x))
    (hopen : ∀ x : V, IsOpen {σ | ρ σ x = x}) :
    galoisLatticeProperty k (Rep.of τ) := by
  let _ : Module.Free ℤ W := Module.Free.of_equiv e.symm
  let _ : Module.Finite ℤ W := Module.Finite.equiv e.symm
  -- `MulAction.stabilizer` needs actions on the carriers, while the hypotheses deliberately
  -- retain the bundled representation form. These local actions expose exactly those maps.
  let _ : MulAction (Field.absoluteGaloisGroup k) V := {
    smul σ x := ρ σ x
    one_smul x := by
      change ρ 1 x = x
      rw [map_one, Module.End.one_apply]
    mul_smul σ τ x := by
      change ρ (σ * τ) x = ρ σ (ρ τ x)
      rw [map_mul, Module.End.mul_apply]
  }
  let _ : MulAction (Field.absoluteGaloisGroup k) W := {
    smul σ w := τ σ w
    one_smul w := by
      change τ 1 w = w
      rw [map_one, Module.End.one_apply]
    mul_smul σ τ' w := by
      change τ (σ * τ') w = τ σ (τ τ' w)
      rw [map_mul, Module.End.mul_apply]
  }
  rw [galoisLatticeProperty_iff]
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  intro w
  let B := Module.Free.chooseBasis ℤ V
  let U : Subgroup (Field.absoluteGaloisGroup k) :=
    ⨅ i : Module.Free.ChooseBasisIndex ℤ V,
      MulAction.stabilizer (Field.absoluteGaloisGroup k) (B i)
  -- Rewrite the continuity goal as openness of a subgroup so an open basis stabilizer can be
  -- enlarged with `Subgroup.isOpen_mono`.
  change IsOpen (↑(MulAction.stabilizer (Field.absoluteGaloisGroup k) w) :
    Set (Field.absoluteGaloisGroup k))
  apply Subgroup.isOpen_mono (H₁ := U)
  · intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    apply e.injective
    apply LinearMap.ext
    intro x
    -- Expose the local action above before applying the stated equivariance formula for `e`.
    change e (τ σ w) x = e w x
    rw [he]
    have hσinv : σ⁻¹ ∈ U := U.inv_mem hσ
    have hfix : ρ σ⁻¹ = LinearMap.id := by
      apply B.ext
      intro i
      rw [LinearMap.id_apply]
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_iInf.mp hσinv i)
    rw [hfix, LinearMap.id_apply]
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ hopen (B i)

/-- The contragredient representation on the integral dual of a Galois lattice is again a
Galois lattice. -/
theorem galoisLatticeProperty_dual
    (ρ : Representation ℤ (Field.absoluteGaloisGroup k) V)
    (hopen : ∀ x : V, IsOpen {σ | ρ σ x = x}) :
    galoisLatticeProperty k (Rep.of ρ.dual) := by
  apply galoisLatticeProperty_contragredient ρ ρ.dual (LinearEquiv.refl ℤ _)
  · intro σ f x
    rfl
  · exact hopen

end TauCeti
