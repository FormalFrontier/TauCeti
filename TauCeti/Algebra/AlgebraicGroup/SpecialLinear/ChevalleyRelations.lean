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
corresponding commutation and commutator relations. Furthermore, composing with the
determinant-one embedding recovers the general-linear root subgroup relations.

This file supplies the commutator-relations part of the pinned Chevalley–Demazure interface from
Layer 9 of the ReductiveGroups roadmap for the worked example `SLₙ` over an arbitrary commutative
base ring.

## Main declarations

* `TauCeti.SpecialLinear.commute_rootSubgroupPoints`: root subgroups at non-chaining index pairs
  commute in `SLₙ(A)`.
* `TauCeti.SpecialLinear.commutatorElement_rootSubgroupPoints`: the type-A Chevalley commutator
  relation on algebra-valued points of `SLₙ`.
* `TauCeti.SpecialLinear.rootSubgroupPoints_mul`: root subgroup point multiplication adds
  parameters.
* `TauCeti.SpecialLinear.rootSubgroupPoints_inv`: root subgroup point inversion negates the
  parameter.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_commute`: commutation on scheme-valued points of
  `SLₙ`.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_commutatorElement`: the type-A Chevalley commutator
  relation on scheme-valued points of `SLₙ`.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_mul`: multiplication on scheme-valued points
  corresponds to addition of additive parameters.
* `TauCeti.SpecialLinear.schemePointsMulEquiv_inv`: inversion on scheme-valued points corresponds
  to negation of the additive parameter.

## References

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
  exact _root_.Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil _ _

/-- Special-linear root subgroup multiplication of points corresponds to convolution multiplication
of the additive parameters. -/
theorem rootSubgroupPoints_mul (hij : i ≠ j)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    rootSubgroupPoints (R := R) (A := A) hij (f * g) =
      rootSubgroupPoints hij f * rootSubgroupPoints hij g :=
  map_mul (rootSubgroupPoints (R := R) (A := A) hij) f g

/-- Special-linear root subgroup inversion of points corresponds to convolution inversion of the
additive parameter. -/
theorem rootSubgroupPoints_inv (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    rootSubgroupPoints (R := R) (A := A) hij f⁻¹ =
      (rootSubgroupPoints (R := R) (A := A) hij f)⁻¹ :=
  map_inv (rootSubgroupPoints (R := R) (A := A) hij) f

/-- The trivial additive parameter yields the identity point in `SLₙ(A)`. -/
theorem rootSubgroupPoints_one (hij : i ≠ j) :
    rootSubgroupPoints (R := R) (A := A) (N := N) hij 1 = 1 :=
  map_one (rootSubgroupPoints (R := R) (A := A) hij)

end Points

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

/-- On scheme-valued points of `SLₙ`, root subgroups at non-chaining index pairs commute. -/
theorem schemePointsMulEquiv_commute (hij : i ≠ j) (hkl : k ≠ l)
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
theorem schemePointsMulEquiv_commutatorElement (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    ⁅schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom),
      schemePointsMulEquiv N A (q ≫ (rootSubgroup hjl).hom.hom)⁆ =
      Matrix.SpecialLinearGroup.transvection hil
        (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
          Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)) := by
  simp only [schemePointsMulEquiv_rootSubgroup]
  exact _root_.Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil _ _

/-- Multiplying two scheme-valued points of the same root subgroup adds their additive
parameters. -/
theorem schemePointsMulEquiv_mul (hij : i ≠ j)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom) *
        schemePointsMulEquiv N A (q ≫ (rootSubgroup hij).hom.hom) =
      Matrix.SpecialLinearGroup.transvection hij
        (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) +
          Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)) := by
  simp only [schemePointsMulEquiv_rootSubgroup, ← Matrix.SpecialLinearGroup.transvection_add]

/-- Inverting a scheme-valued point of a root subgroup negates its additive parameter. -/
theorem schemePointsMulEquiv_inv (hij : i ≠ j)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    (schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom))⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij
        (-Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p)) := by
  simp only [schemePointsMulEquiv_rootSubgroup, Matrix.SpecialLinearGroup.transvection_inv]

end SchemePoints

end TauCeti.SpecialLinear
