/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Chevalley relations for the root subgroups of the special linear group

For distinct indices, `TauCeti.SpecialLinear.rootSubgroupPoints` identifies an additive-group
point of parameter `c` with the determinant-one elementary matrix

```text
xᵢⱼ(c) = 1 + c Eᵢⱼ.
```

This file transports the type-A Chevalley commutator relations from elementary matrices to the
functor of points of `SLₙ`. If two index pairs do not chain, their special-linear root-subgroup
values commute. For three distinct indices, the chaining relation is

```text
⁅xᵢⱼ(c), xⱼₗ(d)⁆ = xᵢₗ(cd).
```

The product `cd` is multiplication in the value algebra, not the convolution product on
`𝔾ₐ(A)`, which corresponds to addition. The additive-group operation
`TauCeti.AdditiveGroup.gaPointParamMul` packages this distinction and is natural in the value
algebra.

On scheme-valued points, composing with the special-linear root subgroup morphism satisfies the
corresponding commutation and commutator relations.

This file supplies the commutator-relations part of the pinned Chevalley–Demazure interface from
Layer 9 of the ReductiveGroups roadmap for the worked example `SLₙ` over an arbitrary commutative
base ring.

## Main declarations

* `TauCeti.SpecialLinear.commute_rootSubgroupPoints`: root subgroups at non-chaining index pairs
  commute in `SLₙ(A)`.
* `TauCeti.SpecialLinear.commutatorElement_rootSubgroupPoints`: the type-A Chevalley commutator
  relation on algebra-valued points of `SLₙ`.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_rootSubgroup_commute`: commutation on scheme-valued
  points of `SLₙ`.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_rootSubgroup_commutatorElement`: the type-A Chevalley
  commutator relation on scheme-valued points of `SLₙ`.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_rootSubgroup_mul`: multiplication on scheme-valued
  points of root subgroups.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_rootSubgroup_inv`: inversion on scheme-valued points
  of root subgroups.

## References

* The formal development in
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ChevalleyRelations`, adapted here from `GLₙ` to
  `SLₙ`.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
* J. S. Milne, *Algebraic Groups* (2017), §21.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj commutatorElement

namespace TauCeti.SpecialLinear

universe u w

variable {R : Type u} [CommRing R]
variable {A : Type w} [CommRing A] [Algebra R A]
variable {N : ℕ} {i j k l : Fin N}

/-- Coercing a determinant-one transvection in `SLₙ` to `GLₙ` via `toGL` yields
`transvectionUnit`. -/
@[simp]
theorem toGL_transvection (hij : i ≠ j) (c : A) :
    _root_.Matrix.SpecialLinearGroup.toGL
        (_root_.Matrix.SpecialLinearGroup.transvection hij c) =
      TauCeti.transvectionUnit hij c := by
  ext a b
  rw [TauCeti.coe_transvectionUnit, _root_.Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    _root_.Matrix.SpecialLinearGroup.transvection_coe, _root_.Matrix.transvection]

section Points

/-- Root-subgroup values at two non-chaining index pairs commute in `SLₙ(A)`.

The hypotheses `j ≠ k` and `l ≠ i` state that the sum of the roots `εᵢ - εⱼ` and `εₖ - εₗ` is
neither a root nor zero. -/
theorem commute_rootSubgroupPoints (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    Commute (rootSubgroupPoints (R := R) (A := A) hij f)
      (rootSubgroupPoints (R := R) (A := A) hkl g) := by
  rw [commute_iff_eq]
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [map_mul, map_mul, pointsMulEquiv_rootSubgroupPoints hij f,
    pointsMulEquiv_rootSubgroupPoints hkl g]
  exact (_root_.Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f))
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g))).eq

/-- **The type-A Chevalley commutator relation on algebra-valued points of `SLₙ`.** For three
distinct indices,

```text
⁅xᵢⱼ(c), xⱼₗ(d)⁆ = xᵢₗ(cd).
```

The point on the right has parameter `cd` in the value algebra, as recorded by
`AdditiveGroup.gaPointParamMul`. -/
@[simp]
theorem commutatorElement_rootSubgroupPoints (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ⁅rootSubgroupPoints (R := R) (A := A) hij f,
      rootSubgroupPoints (R := R) (A := A) hjl g⁆ =
      rootSubgroupPoints (R := R) (A := A) hil (AdditiveGroup.gaPointParamMul f g) := by
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [map_commutatorElement, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv f,
    AdditiveGroup.toAdd_gaPointsMulEquiv g,
    AdditiveGroup.toAdd_gaPointsMulEquiv (AdditiveGroup.gaPointParamMul f g),
    AdditiveGroup.gaPointParamMul_apply_ι]
  apply _root_.Matrix.SpecialLinearGroup.toGL_injective
  rw [map_commutatorElement]
  rw [toGL_transvection, toGL_transvection, toGL_transvection]
  exact TauCeti.commutatorElement_transvectionUnit hij hjl hil _ _

end Points

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

/-- On scheme-valued points of `SLₙ`, root subgroups at non-chaining index pairs commute. -/
theorem schemePointsMulEquiv_rootSubgroup_commute (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    Commute (schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom))
      (schemePointsMulEquiv N A (q ≫ (rootSubgroup hkl).hom.hom)) := by
  simp only [schemePointsMulEquiv_rootSubgroup]
  exact _root_.Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli _ _

/-- **The type-A Chevalley commutator relation on scheme-valued points of `SLₙ`.** -/
@[simp]
theorem schemePointsMulEquiv_rootSubgroup_commutatorElement (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    ⁅schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom),
      schemePointsMulEquiv N A (q ≫ (rootSubgroup hjl).hom.hom)⁆ =
      schemePointsMulEquiv N A
        (((AdditiveGroup.schemePointsMulEquiv (R := R) A).symm
          (Multiplicative.ofAdd
            (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv (R := R) A p) *
              Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv (R := R) A q)))) ≫
          (rootSubgroup hil).hom.hom) := by
  rw [schemePointsMulEquiv_rootSubgroup, schemePointsMulEquiv_rootSubgroup,
    schemePointsMulEquiv_rootSubgroup]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  apply _root_.Matrix.SpecialLinearGroup.toGL_injective
  rw [map_commutatorElement]
  rw [toGL_transvection, toGL_transvection, toGL_transvection]
  exact TauCeti.commutatorElement_transvectionUnit hij hjl hil _ _

/-- Multiplying two scheme-valued points of the same root subgroup multiplies along the group
law of `𝔾ₐ`. -/
@[simp]
theorem schemePointsMulEquiv_rootSubgroup_mul (hij : i ≠ j)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom) *
        schemePointsMulEquiv N A (q ≫ (rootSubgroup hij).hom.hom) =
      schemePointsMulEquiv N A ((p * q) ≫ (rootSubgroup hij).hom.hom) := by
  rw [schemePointsMulEquiv_rootSubgroup, schemePointsMulEquiv_rootSubgroup,
    schemePointsMulEquiv_rootSubgroup]
  simp only [map_mul, toAdd_mul, ← Matrix.SpecialLinearGroup.transvection_add]

/-- Inverting a scheme-valued point of a root subgroup inverts along the group law of `𝔾ₐ`. -/
@[simp]
theorem schemePointsMulEquiv_rootSubgroup_inv (hij : i ≠ j)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    (schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom))⁻¹ =
      schemePointsMulEquiv N A (p⁻¹ ≫ (rootSubgroup hij).hom.hom) := by
  rw [schemePointsMulEquiv_rootSubgroup, schemePointsMulEquiv_rootSubgroup]
  simp only [map_inv, toAdd_inv, Matrix.SpecialLinearGroup.transvection_inv]

end SchemePoints

end TauCeti.SpecialLinear
