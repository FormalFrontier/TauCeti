/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Prod
public import TauCeti.LinearAlgebra.End.Prod

/-!
# Products of multiplicative Jordan decompositions

Semisimple and unipotent linear automorphisms are preserved by componentwise products.  On
finite-dimensional modules over a perfect field, the multiplicative Jordan decomposition of a
product automorphism is therefore computed componentwise.

This supplies product infrastructure for the linear-algebraic functoriality step in Layer 4 of the
ReductiveGroups roadmap.

## Main declarations

* `TauCeti.GeneralLinearGroup.jordanDecomposition_prodMap`: Jordan decomposition is componentwise
  on product modules.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

open LinearMap Polynomial

namespace GeneralLinearGroup

universe u v w

section CommRing

variable {K : Type u} {V : Type v} {W : Type w}
variable [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The product map of two semisimple automorphisms is semisimple. -/
theorem IsSemisimple.prodMap {g : GeneralLinearGroup K V} {h : GeneralLinearGroup K W}
    (hg : IsSemisimple g) (hh : IsSemisimple h) : IsSemisimple (prodMap g h) := by
  rw [isSemisimple_def] at hg hh ⊢
  rw [coe_prodMap]
  exact Module.End.IsSemisimple.prodMap hg hh

/-- The product map of two unipotent automorphisms is unipotent. -/
theorem IsUnipotent.prodMap {g : GeneralLinearGroup K V} {h : GeneralLinearGroup K W}
    (hg : IsUnipotent g) (hh : IsUnipotent h) : IsUnipotent (prodMap g h) := by
  rw [isUnipotent_def] at hg hh ⊢
  have hp := hg.prodMap hh
  -- Expose the component endomorphisms beneath the product-map and identity coercions.
  rw [show (GeneralLinearGroup.prodMap g h : Module.End K (V × W)) - 1 =
      ((g : Module.End K V) - 1).prodMap ((h : Module.End K W) - 1) by
    rw [coe_prodMap]
    ext x <;> simp]
  exact hp

end CommRing

section PerfectField

variable {K : Type u} {V : Type v} {W : Type w}
variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [PerfectField K] [FiniteDimensional K V] [FiniteDimensional K W]

/-- The multiplicative Jordan decomposition of a product-map automorphism is the product map of
the decompositions of its two factors. -/
theorem jordanDecomposition_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    jordanDecomposition (prodMap g h) =
      (prodMap (semisimplePart g) (semisimplePart h),
        prodMap (unipotentPart g) (unipotentPart h)) :=
  jordanDecomposition_map₂ prodMap prodMap_mul IsSemisimple.prodMap IsUnipotent.prodMap g h

/-- The semisimple factor of a product-map automorphism is computed componentwise. -/
@[simp]
theorem semisimplePart_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    semisimplePart (prodMap g h) = prodMap (semisimplePart g) (semisimplePart h) := by
  rw [semisimplePart_def]
  exact congrArg Prod.fst (jordanDecomposition_prodMap g h)

/-- The unipotent factor of a product-map automorphism is computed componentwise. -/
@[simp]
theorem unipotentPart_prodMap (g : GeneralLinearGroup K V) (h : GeneralLinearGroup K W) :
    unipotentPart (prodMap g h) = prodMap (unipotentPart g) (unipotentPart h) := by
  rw [unipotentPart_def]
  exact congrArg Prod.snd (jordanDecomposition_prodMap g h)

end PerfectField

end GeneralLinearGroup

end TauCeti
