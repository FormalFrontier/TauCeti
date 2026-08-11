/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.End.TensorProduct
public import TauCeti.LinearAlgebra.GeneralLinearGroup.TensorProduct
public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.NoncommRing

/-!
# Tensor products of multiplicative Jordan decompositions

Over a perfect field, the multiplicative Jordan decomposition of a tensor product of linear
automorphisms is obtained by tensoring their semisimple factors and their unipotent factors.

This is the tensor-product compatibility needed to assemble the componentwise Jordan factors of
point actions on finite comodules into tensor automorphisms.  Together with the intertwining
results in `TauCeti.LinearAlgebra.JordanChevalley.Functoriality`, it is the linear-algebraic bridge
from Jordan decomposition in general linear groups to Jordan decomposition in an affine group via
Tannakian reconstruction.

## Main declarations

* `TauCeti.GeneralLinearGroup.IsSemisimple.tensorProduct`: tensor products of semisimple
  automorphisms are semisimple.
* `TauCeti.GeneralLinearGroup.IsUnipotent.tensorProduct`: tensor products of unipotent
  automorphisms are unipotent.
* `TauCeti.GeneralLinearGroup.jordanDecomposition_tensorProduct`: the canonical decomposition is
  factorwise on tensor products.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap
open scoped TensorProduct

namespace GeneralLinearGroup

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}

section Semisimple

variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- The tensor product of semisimple linear automorphisms is semisimple. -/
theorem IsSemisimple.tensorProduct {g : GeneralLinearGroup K V}
    {h : GeneralLinearGroup K W} (hg : IsSemisimple g) (hh : IsSemisimple h) :
    IsSemisimple (tensorProduct g h) := by
  rw [isSemisimple_def, coe_tensorProduct]
  rw [← LinearMap.lTensor_comp_rTensor]
  have hl : Module.End.IsSemisimple ((h : Module.End K W).lTensor V) :=
    Module.End.IsSemisimple.lTensor (K := K) (V := V) (W := W)
      ((isSemisimple_def h).mp hh)
  have hr : Module.End.IsSemisimple ((g : Module.End K V).rTensor W) :=
    Module.End.IsSemisimple.rTensor (K := K) (V := V) (W := W)
      ((isSemisimple_def g).mp hg)
  have hcomm : Commute ((h : Module.End K W).lTensor V)
      ((g : Module.End K V).rTensor W) := by
    rw [Commute]
    exact (LinearMap.lTensor_comp_rTensor V (g : Module.End K V)
      (h : Module.End K W)).trans
        (LinearMap.rTensor_comp_lTensor V (g : Module.End K V)
          (h : Module.End K W)).symm
  exact Module.End.IsSemisimple.mul_of_commute hcomm hl hr

end Semisimple

section CommRing

variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The tensor product of unipotent linear automorphisms is unipotent. -/
theorem IsUnipotent.tensorProduct {g : GeneralLinearGroup K V}
    {h : GeneralLinearGroup K W} (hg : IsUnipotent g) (hh : IsUnipotent h) :
    IsUnipotent (tensorProduct g h) := by
  rw [isUnipotent_def, coe_tensorProduct]
  let n : Module.End K (V ⊗[K] W) :=
    (g : Module.End K V).rTensor W - 1
  let m : Module.End K (V ⊗[K] W) :=
    (h : Module.End K W).lTensor V - 1
  have hn : _root_.IsNilpotent n := by
    have hn' := ((isUnipotent_def g).mp hg).map (Module.End.rTensorAlgHom K V W)
    -- Expose the algebra homomorphism as one-sided tensoring before normalizing subtraction.
    change _root_.IsNilpotent (((g : Module.End K V) - 1).rTensor W) at hn'
    rw [LinearMap.rTensor_sub] at hn'
    change _root_.IsNilpotent ((g : Module.End K V).rTensor W -
      (LinearMap.id : Module.End K V).rTensor W) at hn'
    rw [LinearMap.rTensor_id] at hn'
    exact hn'
  have hm : _root_.IsNilpotent m := by
    have hm' := ((isUnipotent_def h).mp hh).map (Module.End.lTensorAlgHom K W V)
    -- Expose the algebra homomorphism as one-sided tensoring before normalizing subtraction.
    change _root_.IsNilpotent (((h : Module.End K W) - 1).lTensor V) at hm'
    rw [LinearMap.lTensor_sub] at hm'
    change _root_.IsNilpotent ((h : Module.End K W).lTensor V -
      (LinearMap.id : Module.End K W).lTensor V) at hm'
    rw [LinearMap.lTensor_id] at hm'
    exact hm'
  have hab : Commute ((g : Module.End K V).rTensor W)
      ((h : Module.End K W).lTensor V) := by
    rw [Commute]
    exact (LinearMap.rTensor_comp_lTensor V (g : Module.End K V)
      (h : Module.End K W)).trans
        (LinearMap.lTensor_comp_rTensor V (g : Module.End K V)
          (h : Module.End K W)).symm
  have hnm : Commute n m := by
    dsimp only [n, m]
    exact (hab.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have hmul : _root_.IsNilpotent (n * m) := hnm.isNilpotent_mul_left hm
  have hn_mul : Commute n (n * m) := (Commute.refl n).mul_right hnm
  have hm_mul : Commute m (n * m) := hnm.symm.mul_right (Commute.refl m)
  have hmap : TensorProduct.map (g : Module.End K V) (h : Module.End K W) - 1 =
      n + m + n * m := by
    rw [← LinearMap.lTensor_comp_rTensor]
    -- Ring multiplication of endomorphisms is composition; expose it for `noncomm_ring`.
    change (h : Module.End K W).lTensor V * (g : Module.End K V).rTensor W - 1 = _
    dsimp only [n, m]
    noncomm_ring [hab.eq]
  rw [hmap]
  exact Commute.isNilpotent_add (hn_mul.add_left hm_mul)
    (Commute.isNilpotent_add hnm hn hm) hmul

end CommRing

section PerfectField

variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- The multiplicative Jordan decomposition of a tensor product is the tensor product of the
corresponding factors. -/
theorem jordanDecomposition_tensorProduct
    (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    jordanDecomposition (tensorProduct g h) =
      (tensorProduct (semisimplePart g) (semisimplePart h),
        tensorProduct (unipotentPart g) (unipotentPart h)) := by
  symm
  apply (eq_jordanDecomposition_iff (tensorProduct g h) _ _).2
  refine ⟨(isSemisimple_semisimplePart g).tensorProduct
      (isSemisimple_semisimplePart h),
    (isUnipotent_unipotentPart g).tensorProduct (isUnipotent_unipotentPart h), ?_, ?_⟩
  · rw [commute_iff_eq, ← tensorProduct_mul, ← tensorProduct_mul]
    rw [(commute_semisimplePart_unipotentPart g).eq,
      (commute_semisimplePart_unipotentPart h).eq]
  · rw [← tensorProduct_mul, semisimplePart_mul_unipotentPart,
      semisimplePart_mul_unipotentPart]

/-- The semisimple factor of a tensor product is the tensor product of the semisimple factors. -/
@[simp]
theorem semisimplePart_tensorProduct
    (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    semisimplePart (tensorProduct g h) =
      tensorProduct (semisimplePart g) (semisimplePart h) :=
  (semisimplePart_def (tensorProduct g h)).trans <|
    congrArg Prod.fst (jordanDecomposition_tensorProduct g h)

/-- The unipotent factor of a tensor product is the tensor product of the unipotent factors. -/
@[simp]
theorem unipotentPart_tensorProduct
    (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    unipotentPart (tensorProduct g h) =
      tensorProduct (unipotentPart g) (unipotentPart h) :=
  (unipotentPart_def (tensorProduct g h)).trans <|
    congrArg Prod.snd (jordanDecomposition_tensorProduct g h)

end PerfectField

end GeneralLinearGroup

end TauCeti
