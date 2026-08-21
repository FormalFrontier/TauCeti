/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.TensorProduct
public import TauCeti.LinearAlgebra.GeneralLinearGroup.TensorProduct
public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative
public import Mathlib.RingTheory.TensorProduct.Finite

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

* `LinearMap.GeneralLinearGroup.IsSemisimple.tensorProduct`: tensor products of semisimple
  automorphisms are semisimple.
* `LinearMap.GeneralLinearGroup.IsUnipotent.tensorProduct`: tensor products of unipotent
  automorphisms are unipotent.
* `LinearMap.GeneralLinearGroup.jordanDecomposition_tensorProduct`: the canonical decomposition is
  factorwise on tensor products.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace LinearMap.GeneralLinearGroup

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}

section Semisimple

variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- The tensor product of semisimple linear automorphisms is semisimple. -/
theorem IsSemisimple.tensorProduct {g : GeneralLinearGroup K V}
    {h : GeneralLinearGroup K W} (hg : IsSemisimple g) (hh : IsSemisimple h) :
    IsSemisimple (tensorProduct g h) := by
  rw [isSemisimple_def] at hg hh ⊢
  rw [coe_tensorProduct]
  exact TauCeti.Module.End.IsSemisimple.tensorProduct hg hh

end Semisimple

section CommRing

variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The tensor product of unipotent linear automorphisms is unipotent. -/
theorem IsUnipotent.tensorProduct {g : GeneralLinearGroup K V}
    {h : GeneralLinearGroup K W} (hg : IsUnipotent g) (hh : IsUnipotent h) :
    IsUnipotent (tensorProduct g h) := by
  rw [isUnipotent_def] at hg hh ⊢
  rw [coe_tensorProduct]
  exact hg.tensorProduct_map_sub_one hh

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
        tensorProduct (unipotentPart g) (unipotentPart h)) :=
  jordanDecomposition_map₂ tensorProduct tensorProduct_mul IsSemisimple.tensorProduct
    IsUnipotent.tensorProduct g h

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

end LinearMap.GeneralLinearGroup
