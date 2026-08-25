/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.RootSubgroup

/-!
# Chevalley relations for the root subgroups of the general linear group

For distinct indices, `TauCeti.GeneralLinear.rootSubgroupPoints` identifies an additive-group
point of parameter `c` with the elementary matrix

```text
xᵢⱼ(c) = 1 + c Eᵢⱼ.
```

This file transports the type-A Chevalley commutator relations from elementary matrices to the
functor of points of `GLₙ`. If two index pairs do not chain, their root-subgroup values commute.
For three distinct indices, the chaining relation is

```text
⁅xᵢⱼ(c), xⱼₗ(d)⁆ = xᵢₗ(cd).
```

The product `cd` is multiplication in the value algebra, not the convolution product on
`𝔾ₐ(A)`, which corresponds to addition. The additive-group operation
`TauCeti.AdditiveGroup.gaPointParamMul` packages this distinction and is natural in the value
algebra.

This file supplies the commutator-relations part of the pinned Chevalley--Demazure interface from
Layer 9 of the ReductiveGroups roadmap for the worked example `GLₙ` over an arbitrary commutative
base ring. The pinning equations and the general Chevalley--Demazure construction are not covered
here.

## Main declarations

* `TauCeti.GeneralLinear.commute_rootSubgroupPoints`: root subgroups at non-chaining index pairs
  commute.
* `TauCeti.GeneralLinear.commutatorElement_rootSubgroupPoints`: the type-A Chevalley commutator
  relation on algebra-valued points.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.GeneralLinear

universe u w

variable {R : Type u} [CommRing R]
variable {A : Type w} [CommRing A] [Algebra R A]
variable {N : ℕ} {i j k l : Fin N}

/-- Root-subgroup values at two non-chaining index pairs commute.

The hypotheses `j ≠ k` and `l ≠ i` say that the sum of the corresponding roots is neither a root
nor zero; the remaining hypotheses ensure that both elementary matrices are root-subgroup
values. -/
theorem commute_rootSubgroupPoints (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    Commute (rootSubgroupPoints hij f) (rootSubgroupPoints hkl g) := by
  refine Commute.of_map (pointsMulEquiv (R := R) (A := A) N).injective ?_
  rw [pointsMulEquiv_rootSubgroupPoints hij f, pointsMulEquiv_rootSubgroupPoints hkl g]
  exact commute_transvectionUnit hij hkl hjk hli
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f))
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g))

/-- **The type-A Chevalley commutator relation on algebra-valued points.** For three distinct
indices,

```text
⁅xᵢⱼ(c), xⱼₗ(d)⁆ = xᵢₗ(cd).
```

The point on the right has parameter `cd` in the value algebra, as recorded by
`AdditiveGroup.gaPointParamMul`. -/
theorem commutatorElement_rootSubgroupPoints (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ⁅rootSubgroupPoints hij f, rootSubgroupPoints hjl g⁆ =
      rootSubgroupPoints hil (AdditiveGroup.gaPointParamMul f g) := by
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [map_commutatorElement, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv f,
    AdditiveGroup.toAdd_gaPointsMulEquiv g,
    AdditiveGroup.toAdd_gaPointsMulEquiv (AdditiveGroup.gaPointParamMul f g),
    AdditiveGroup.gaPointParamMul_apply_ι]
  exact commutatorElement_transvectionUnit hij hjl hil _ _

end TauCeti.GeneralLinear
