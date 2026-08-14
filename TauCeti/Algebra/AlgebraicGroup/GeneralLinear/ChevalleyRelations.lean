/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
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
`𝔾ₐ(A)`, which corresponds to addition. The auxiliary point
`TauCeti.GeneralLinear.rootParameterProduct` packages this distinction and is natural in the
value algebra.

These are the root-subgroup equations required by the pinned Chevalley--Demazure interface in
Layer 9 of the ReductiveGroups roadmap, here verified for the worked example `GLₙ` over an
arbitrary commutative base ring.

## Main declarations

* `TauCeti.GeneralLinear.rootParameterProduct`: the additive-group point whose parameter is the
  product of the parameters of two given points.
* `TauCeti.GeneralLinear.commute_rootSubgroupPoints`: root subgroups at non-chaining index pairs
  commute.
* `TauCeti.GeneralLinear.commutatorElement_rootSubgroupPoints`: the type-A Chevalley commutator
  relation on algebra-valued points.
* `TauCeti.GeneralLinear.commutatorElement_rootSubgroupPoints_reverse`: the reverse-chaining
  relation, with the inverse parameter encoding the structure constant `-1`.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.GeneralLinear

universe u w x

variable {R : Type u} [CommRing R]
variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type x} [CommRing B] [Algebra R B]
variable {N : ℕ} {i j k l : Fin N}

/-- The `A`-valued point of `𝔾ₐ` whose parameter is the product of the parameters of `f` and
`g`.

This is not the group multiplication of `𝔾ₐ(A)`: convolution corresponds to addition, whereas
`rootParameterProduct f g` records multiplication in the value algebra. It is the parameter on
the right-hand side of the type-A Chevalley commutator relation. -/
noncomputable def rootParameterProduct
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) :=
  (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
    Multiplicative.ofAdd
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g))

/-- The value of `rootParameterProduct f g` on the additive coordinate is the product of the two
original coordinate values. -/
@[simp]
theorem rootParameterProduct_apply_ι
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    (rootParameterProduct f g).ofConv (SymmetricAlgebra.ι R R 1) =
      f.ofConv (SymmetricAlgebra.ι R R 1) *
        g.ofConv (SymmetricAlgebra.ι R R 1) := by
  rw [← AdditiveGroup.toAdd_gaPointsMulEquiv, rootParameterProduct,
    MulEquiv.apply_symm_apply]
  rw [toAdd_ofAdd, AdditiveGroup.toAdd_gaPointsMulEquiv f,
    AdditiveGroup.toAdd_gaPointsMulEquiv g]

/-- Multiplication of root parameters is natural in the value algebra. -/
theorem mapValue_rootParameterProduct (phi : A →ₐ[R] B)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi
        (rootParameterProduct f g) =
      rootParameterProduct
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f)
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi g) := by
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := B)).injective
  have h :
      Multiplicative.toAdd
          (AdditiveGroup.gaPointsMulEquiv
            (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi
              (rootParameterProduct f g))) =
        Multiplicative.toAdd
          (AdditiveGroup.gaPointsMulEquiv
            (rootParameterProduct
              (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f)
              (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi g))) := by
    calc
      Multiplicative.toAdd
          (AdditiveGroup.gaPointsMulEquiv
            (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi
              (rootParameterProduct f g))) =
          phi (Multiplicative.toAdd
            (AdditiveGroup.gaPointsMulEquiv (rootParameterProduct f g))) :=
        AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue phi _
      _ = phi (f.ofConv (SymmetricAlgebra.ι R R 1) *
          g.ofConv (SymmetricAlgebra.ι R R 1)) := by
        rw [AdditiveGroup.toAdd_gaPointsMulEquiv, rootParameterProduct_apply_ι]
      _ = phi (f.ofConv (SymmetricAlgebra.ι R R 1)) *
          phi (g.ofConv (SymmetricAlgebra.ι R R 1)) := map_mul phi _ _
      _ = (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f).ofConv
            (SymmetricAlgebra.ι R R 1) *
          (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi g).ofConv
            (SymmetricAlgebra.ι R R 1) := rfl
      _ = Multiplicative.toAdd
          (AdditiveGroup.gaPointsMulEquiv
            (rootParameterProduct
              (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi f)
              (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) phi g))) := by
        rw [AdditiveGroup.toAdd_gaPointsMulEquiv, rootParameterProduct_apply_ι]
  simpa only [ofAdd_toAdd] using congrArg Multiplicative.ofAdd h

/-- Root-subgroup values at two non-chaining index pairs commute.

The hypotheses `j ≠ k` and `l ≠ i` say that the corresponding roots do not add to a root;
the remaining hypotheses ensure that both elementary matrices are root-subgroup values. -/
theorem commute_rootSubgroupPoints (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    Commute (rootSubgroupPoints hij f) (rootSubgroupPoints hkl g) := by
  rw [Commute]
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [map_mul, map_mul, pointsMulEquiv_rootSubgroupPoints hij f,
    pointsMulEquiv_rootSubgroupPoints hkl g]
  exact (commute_transvectionUnit hij hkl hjk hli
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f))
    (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g))).eq

/-- **The type-A Chevalley commutator relation on algebra-valued points.** For three distinct
indices,

```text
⁅xᵢⱼ(c), xⱼₗ(d)⁆ = xᵢₗ(cd).
```

The point on the right has parameter `cd` in the value algebra, as recorded by
`rootParameterProduct`. -/
theorem commutatorElement_rootSubgroupPoints (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ⁅rootSubgroupPoints hij f, rootSubgroupPoints hjl g⁆ =
      rootSubgroupPoints hil (rootParameterProduct f g) := by
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [map_commutatorElement, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv f,
    AdditiveGroup.toAdd_gaPointsMulEquiv g,
    AdditiveGroup.toAdd_gaPointsMulEquiv (rootParameterProduct f g),
    rootParameterProduct_apply_ι]
  exact commutatorElement_transvectionUnit hij hjl hil _ _

/-- **The reverse-chaining type-A Chevalley commutator relation.** For three distinct indices,

```text
⁅xᵢⱼ(c), xₖᵢ(d)⁆ = xₖⱼ(-dc).
```

The inverse on the right negates the parameter because inversion in `𝔾ₐ(A)` is negation. This is
the orientation of the type-A relation whose structure constant is `-1`. -/
theorem commutatorElement_rootSubgroupPoints_reverse (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ⁅rootSubgroupPoints hij f, rootSubgroupPoints hki g⁆ =
      rootSubgroupPoints hkj (rootParameterProduct g f)⁻¹ := by
  calc
    ⁅rootSubgroupPoints hij f, rootSubgroupPoints hki g⁆ =
        ⁅rootSubgroupPoints hki g, rootSubgroupPoints hij f⁆⁻¹ :=
      (commutatorElement_inv _ _).symm
    _ = (rootSubgroupPoints hkj (rootParameterProduct g f))⁻¹ := by
      rw [commutatorElement_rootSubgroupPoints hki hij hkj g f]
    _ = rootSubgroupPoints hkj (rootParameterProduct g f)⁻¹ :=
      (map_inv (rootSubgroupPoints (R := R) (A := A) hkj) _).symm

end TauCeti.GeneralLinear
