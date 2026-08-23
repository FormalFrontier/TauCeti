/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup

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
corresponding commutation and commutator relations. The scheme-level parameter product is
`TauCeti.AdditiveGroup.gaSchemePointParamMul`, the scheme-point counterpart of
`gaPointParamMul`.

This file supplies the commutator-relations part of the pinned Chevalley–Demazure interface from
Layer 9 of the ReductiveGroups roadmap for the worked example `SLₙ` over an arbitrary commutative
base ring.

## Main declarations

* `TauCeti.SpecialLinear.commute_rootSubgroupPoints`: root subgroups at non-chaining index pairs
  commute in `SLₙ(A)`.
* `TauCeti.SpecialLinear.commutatorElement_rootSubgroupPoints`: the type-A Chevalley commutator
  relation on algebra-valued points of `SLₙ`.
* `TauCeti.SpecialLinear.commute_schemePointsMulEquiv_rootSubgroup`: commutation on scheme-valued
  points of `SLₙ`.
* `TauCeti.SpecialLinear.commutatorElement_schemePointsMulEquiv_rootSubgroup`: the type-A Chevalley
  commutator relation on scheme-valued points of `SLₙ`.

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

section Points

/-- Root-subgroup values at two non-chaining index pairs commute in `SLₙ(A)`.

The hypotheses `j ≠ k` and `l ≠ i` state that the sum of the roots `εᵢ - εⱼ` and `εₖ - εₗ` is
neither a root nor zero. -/
theorem commute_rootSubgroupPoints (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    Commute (rootSubgroupPoints (R := R) (A := A) hij f)
      (rootSubgroupPoints (R := R) (A := A) hkl g) := by
  refine Commute.of_map (pointsMulEquiv (R := R) (A := A) N).injective ?_
  rw [pointsMulEquiv_rootSubgroupPoints hij f, pointsMulEquiv_rootSubgroupPoints hkl g]
  exact _root_.Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f))
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g))

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

end Points

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

/-- On scheme-valued points of `SLₙ`, root subgroups at non-chaining index pairs commute. -/
theorem commute_schemePointsMulEquiv_rootSubgroup (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    Commute (schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom))
      (schemePointsMulEquiv N A (q ≫ (rootSubgroup hkl).hom.hom)) := by
  simp only [schemePointsMulEquiv_rootSubgroup]
  exact _root_.Matrix.SpecialLinearGroup.commute_transvection hij hkl hjk hli _ _

/-- **The type-A Chevalley commutator relation on scheme-valued points of `SLₙ`.** The root-subgroup
point on the right has parameter `cd`, the product in the value algebra `A` of the parameters of
`p` and `q`; this is not their convolution product, which corresponds to addition. -/
theorem commutatorElement_schemePointsMulEquiv_rootSubgroup (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X)
    (q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (AdditiveGroup.groupScheme R).X) :
    ⁅schemePointsMulEquiv N A (p ≫ (rootSubgroup hij).hom.hom),
      schemePointsMulEquiv N A (q ≫ (rootSubgroup hjl).hom.hom)⁆ =
      schemePointsMulEquiv N A
        (AdditiveGroup.gaSchemePointParamMul A p q ≫
          (rootSubgroup hil).hom.hom) := by
  rw [schemePointsMulEquiv_rootSubgroup, schemePointsMulEquiv_rootSubgroup,
    schemePointsMulEquiv_rootSubgroup]
  simp only [AdditiveGroup.schemePointsMulEquiv_gaSchemePointParamMul, toAdd_ofAdd]
  exact _root_.Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjl hil _ _

end SchemePoints

end TauCeti.SpecialLinear
