/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.LinearAlgebra.Semisimple
import Mathlib.Tactic.NoncommRing

/-!
# Endomorphisms of tensor products

This file establishes semisimplicity and nilpotence properties of tensor-product endomorphisms.
After embedding an unchanged projective factor as a direct summand of a free module, the tensor
product is a direct summand of a direct sum of copies of the original module, and the corresponding
one-sided tensor endomorphism acts componentwise.

## Main declarations

* `TauCeti.Module.End.IsSemisimple.rTensor`: `f ⊗ 1` is semisimple when `f` is.
* `TauCeti.Module.End.IsSemisimple.lTensor`: `1 ⊗ f` is semisimple when `f` is.
* `TauCeti.Module.End.commute_rTensor_lTensor`: one-sided tensor endomorphisms on different factors
  commute.
* `TauCeti.Module.End.IsSemisimple.tensorProduct`: tensor products of semisimple endomorphisms are
  semisimple.
* `IsNilpotent.tensorProduct_map_sub_one`: `TensorProduct.map f g - 1` is nilpotent when
  `f - 1` and `g - 1` are nilpotent.
-/

public section

namespace TauCeti

open Polynomial
open scoped TensorProduct

namespace Module.End

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}

/-- The right-tensor algebra homomorphism sends `f` to `f.rTensor W`. -/
theorem rTensorAlgHom_apply [CommSemiring K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] (f : _root_.Module.End K V) :
    (_root_.Module.End.rTensorAlgHom K V W) f = f.rTensor W := by
  apply LinearMap.ext
  exact _root_.Module.End.rTensorAlgHom_apply_apply K V W f

/-- The left-tensor algebra homomorphism sends `f` to `f.lTensor V`. -/
theorem lTensorAlgHom_apply [CommSemiring K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] (f : _root_.Module.End K W) :
    (_root_.Module.End.lTensorAlgHom K W V) f = f.lTensor V := by
  apply LinearMap.ext
  exact _root_.Module.End.lTensorAlgHom_apply_apply K W V f

/-- One-sided tensor endomorphisms acting on different factors commute. -/
theorem commute_rTensor_lTensor [CommSemiring K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] (f : _root_.Module.End K V)
    (g : _root_.Module.End K W) : Commute (f.rTensor W) (g.lTensor V) := by
  rw [commute_iff_eq, _root_.Module.End.mul_eq_comp, _root_.Module.End.mul_eq_comp]
  exact (LinearMap.rTensor_comp_lTensor V f g).trans
    (LinearMap.lTensor_comp_rTensor V f g).symm

section CommRing

variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

section Right

variable [Module.Projective K W]

/-- Tensoring a semisimple endomorphism on the right with the identity of a *free* module
preserves semisimplicity. -/
private theorem isSemisimple_rTensor_of_free {N : Type*} [AddCommGroup N] [Module K N]
    [Module.Free K N] {f : _root_.Module.End K V} (hf : f.IsSemisimple) :
    _root_.Module.End.IsSemisimple (f.rTensor N) := by
  classical
  rw [_root_.Module.End.IsSemisimple] at hf ⊢
  let _ : IsSemisimpleModule K[X] (Module.AEval' f) := hf
  -- A basis of `N` splits `V ⊗ N` as a direct sum of copies of `V`, on which `f.rTensor N` acts
  -- as `f` in each coordinate.
  let b := Module.Free.chooseBasis K N
  let E₀ : (V ⊗[K] N) ≃ₗ[K] (Module.Free.ChooseBasisIndex K N →₀ V) :=
    TensorProduct.equivFinsuppOfBasisRight b
  let E₀' : (V ⊗[K] N) ≃ₗ[K]
      (Module.Free.ChooseBasisIndex K N →₀ Module.AEval' f) :=
    E₀.trans (Finsupp.mapRange.linearEquiv (Module.AEval'.of f))
  let E : Module.AEval' (f.rTensor N) ≃ₗ[K[X]]
      (Module.Free.ChooseBasisIndex K N →₀ Module.AEval' f) :=
    LinearEquiv.ofAEval _ E₀' fun x ↦ by
      ext j
      simp only [E₀', LinearEquiv.trans_apply, Finsupp.mapRange.linearEquiv_apply,
        Finsupp.mapRange_apply, Finsupp.smul_apply, Module.AEval'.X_smul_of,
        _root_.Module.End.smul_def]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v m => simp [E₀]
      | add x y hx hy => simp [hx, hy]
  exact IsSemisimpleModule.congr E

/-- Tensoring a semisimple endomorphism on the right with an identity endomorphism preserves
semisimplicity. -/
theorem IsSemisimple.rTensor {f : _root_.Module.End K V} (hf : f.IsSemisimple) :
    _root_.Module.End.IsSemisimple (f.rTensor W) := by
  -- Split `W` off a free module `M`; the free case then transfers back along `i.lTensor V`.
  obtain ⟨M, _, _, _, i, s, his⟩ :=
    (Module.Projective.iff_split (R := K) (P := W)).mp inferInstance
  -- `iff_split` only supplies `AddCommMonoid M`; over a ring the module structure promotes it.
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  refine IsSemisimple.of_injective (isSemisimple_rTensor_of_free (N := M) hf)
    (i.lTensor V) ?_ ?_
  · apply LinearMap.injective_of_comp_eq_id (i.lTensor V) (s.lTensor V)
    rw [← LinearMap.lTensor_comp, his, LinearMap.lTensor_id]
  · exact (LinearMap.lTensor_comp_rTensor V f i).trans
      (LinearMap.rTensor_comp_lTensor V f i).symm

end Right

section Left

variable [Module.Projective K V]

/-- Tensoring a semisimple endomorphism on the left with an identity endomorphism preserves
semisimplicity. -/
theorem IsSemisimple.lTensor {f : _root_.Module.End K W} (hf : f.IsSemisimple) :
    _root_.Module.End.IsSemisimple (f.lTensor V) := by
  exact ((TensorProduct.comm K V W).isSemisimple_iff (f.lTensor V) (f.rTensor V)
    (LinearMap.rTensor_comp_comm f).symm).mpr
      (IsSemisimple.rTensor (W := V) hf)

end Left

end CommRing

section CommSemiring

variable [CommSemiring K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- If `f - 1` and `g - 1` are nilpotent, then `TensorProduct.map f g - 1` is nilpotent. -/
theorem _root_.IsNilpotent.tensorProduct_map_sub_one {f : _root_.Module.End K V}
    {g : _root_.Module.End K W} (hf : IsNilpotent (f - 1)) (hg : IsNilpotent (g - 1)) :
    IsNilpotent (TensorProduct.map f g - 1) := by
  let n : _root_.Module.End K (V ⊗[K] W) := f.rTensor W - 1
  let m : _root_.Module.End K (V ⊗[K] W) := g.lTensor V - 1
  have hn : IsNilpotent n := by
    have hn' := hf.map (_root_.Module.End.rTensorAlgHom K V W)
    rw [map_sub, map_one, rTensorAlgHom_apply] at hn'
    exact hn'
  have hm : IsNilpotent m := by
    have hm' := hg.map (_root_.Module.End.lTensorAlgHom K W V)
    rw [map_sub, map_one, lTensorAlgHom_apply] at hm'
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

end CommSemiring

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
