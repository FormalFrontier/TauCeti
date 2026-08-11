/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.NoncommRing

/-!
# Endomorphisms of tensor products

This file establishes semisimplicity and nilpotence properties of tensor-product endomorphisms.
After choosing a basis of an unchanged factor, the tensor product is a direct sum of copies of the
original module, and the corresponding one-sided tensor endomorphism acts componentwise.

## Main declarations

* `TauCeti.Module.End.IsSemisimple.rTensor`: `f ⊗ 1` is semisimple when `f` is.
* `TauCeti.Module.End.IsSemisimple.lTensor`: `1 ⊗ f` is semisimple when `f` is.
* `TauCeti.Module.End.commute_rTensor_lTensor`: one-sided tensor endomorphisms on different factors
  commute.
* `TauCeti.Module.End.IsSemisimple.tensorProduct`: tensor products of semisimple endomorphisms are
  semisimple.
* `TauCeti.Module.End.isNilpotent_map_sub_one`: `TensorProduct.map f g - 1` is nilpotent when
  `f - 1` and `g - 1` are nilpotent.
-/

public section

namespace TauCeti

open Polynomial
open scoped TensorProduct

namespace Module.End

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}

section CommRing

variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

section Right

variable [Module.Free K W]

/-- Tensoring a semisimple endomorphism on the right with an identity endomorphism preserves
semisimplicity. -/
theorem IsSemisimple.rTensor {f : _root_.Module.End K V} (hf : f.IsSemisimple) :
    _root_.Module.End.IsSemisimple (f.rTensor W) := by
  classical
  rw [_root_.Module.End.IsSemisimple] at hf ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  let b := Module.Free.chooseBasis K W
  let E₀ : (V ⊗[K] W) ≃ₗ[K] (Module.Free.ChooseBasisIndex K W →₀ V) :=
    TensorProduct.equivFinsuppOfBasisRight b
  let E₀' : (V ⊗[K] W) ≃ₗ[K]
      (Module.Free.ChooseBasisIndex K W →₀ Module.AEval' f) :=
    E₀.trans (Finsupp.mapRange.linearEquiv (Module.AEval'.of f))
  let _ : IsScalarTower K K[X]
      (Module.Free.ChooseBasisIndex K W →₀ Module.AEval' f) := {
    smul_assoc := fun r p x ↦ by
        ext i
        exact smul_assoc r p (x i) }
  let E : Module.AEval' (f.rTensor W) ≃ₗ[K[X]]
      (Module.Free.ChooseBasisIndex K W →₀ Module.AEval' f) :=
    LinearEquiv.ofAEval _ E₀' fun x ↦ by
      ext i
      simp only [E₀', LinearEquiv.trans_apply, Finsupp.mapRange.linearEquiv_apply,
        Finsupp.mapRange_apply, Finsupp.smul_apply, Module.AEval'.X_smul_of]
      apply (Module.AEval'.of f).injective
      -- The basis equivalence computes right tensor actions coordinatewise by definition;
      -- expose that form so tensor induction applies.
      change E₀ (f.rTensor W x) i = f (E₀ x i)
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v w => simp [E₀]
      | add x y hx hy => simp [hx, hy]
  exact IsSemisimpleModule.congr E

end Right

section Left

variable [Module.Free K V]

/-- Tensoring a semisimple endomorphism on the left with an identity endomorphism preserves
semisimplicity. -/
theorem IsSemisimple.lTensor {f : _root_.Module.End K W} (hf : f.IsSemisimple) :
    _root_.Module.End.IsSemisimple (f.lTensor V) := by
  exact ((TensorProduct.comm K V W).isSemisimple_iff (f.lTensor V) (f.rTensor V)
    (LinearMap.rTensor_comp_comm f).symm).mpr
      (IsSemisimple.rTensor (W := V) hf)

end Left

/-- One-sided tensor endomorphisms acting on different factors commute. -/
theorem commute_rTensor_lTensor (f : _root_.Module.End K V) (g : _root_.Module.End K W) :
    Commute (f.rTensor W) (g.lTensor V) := by
  rw [commute_iff_eq, _root_.Module.End.mul_eq_comp, _root_.Module.End.mul_eq_comp]
  exact (LinearMap.rTensor_comp_lTensor V f g).trans
    (LinearMap.lTensor_comp_rTensor V f g).symm

/-- If `f - 1` and `g - 1` are nilpotent, then `TensorProduct.map f g - 1` is nilpotent. -/
theorem isNilpotent_map_sub_one {f : _root_.Module.End K V} {g : _root_.Module.End K W}
    (hf : IsNilpotent (f - 1)) (hg : IsNilpotent (g - 1)) :
    IsNilpotent (TensorProduct.map f g - 1) := by
  let n : _root_.Module.End K (V ⊗[K] W) := f.rTensor W - 1
  let m : _root_.Module.End K (V ⊗[K] W) := g.lTensor V - 1
  have hn : IsNilpotent n := by
    have hn' := hf.map (_root_.Module.End.rTensorAlgHom K V W)
    rw [map_sub, map_one] at hn'
    -- Expose the algebra homomorphism's action as right tensoring after applying the map laws.
    change IsNilpotent (f.rTensor W - 1) at hn'
    exact hn'
  have hm : IsNilpotent m := by
    have hm' := hg.map (_root_.Module.End.lTensorAlgHom K W V)
    rw [map_sub, map_one] at hm'
    -- Expose the algebra homomorphism's action as left tensoring after applying the map laws.
    change IsNilpotent (g.lTensor V - 1) at hm'
    exact hm'
  have hab := commute_rTensor_lTensor f g
  have hnm : Commute n m := by
    dsimp only [n, m]
    exact (hab.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have hmul : IsNilpotent (n * m) := hnm.isNilpotent_mul_left hm
  have hn_mul : Commute n (n * m) := (Commute.refl n).mul_right hnm
  have hm_mul : Commute m (n * m) := hnm.symm.mul_right (Commute.refl m)
  have hmap : TensorProduct.map f g - 1 = n + m + n * m := by
    rw [← LinearMap.lTensor_comp_rTensor, ← _root_.Module.End.mul_eq_comp]
    dsimp only [n, m]
    noncomm_ring [hab.eq]
  rw [hmap]
  exact Commute.isNilpotent_add (hn_mul.add_left hm_mul)
    (Commute.isNilpotent_add hnm hn hm) hmul

end CommRing

section PerfectField

variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- The tensor product of two semisimple endomorphisms is semisimple. -/
theorem IsSemisimple.tensorProduct {f : _root_.Module.End K V} {g : _root_.Module.End K W}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    _root_.Module.End.IsSemisimple (TensorProduct.map f g) := by
  rw [← LinearMap.lTensor_comp_rTensor, ← _root_.Module.End.mul_eq_comp]
  exact _root_.Module.End.IsSemisimple.mul_of_commute (commute_rTensor_lTensor f g).symm
    (IsSemisimple.lTensor hg) (IsSemisimple.rTensor hf)

end PerfectField

end Module.End

end TauCeti
