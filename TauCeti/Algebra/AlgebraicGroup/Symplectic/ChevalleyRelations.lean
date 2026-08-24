/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations

/-!
# Chevalley relations for symplectic root subgroups

This file lifts the two multiply-laced rank-two commutator relations from the standard
symplectic matrices to the functor of points of `Sp₂ₘ`. For distinct `i` and `j`, they are

```text
⁅x_{eᵢ-eⱼ}(a), x_{2eⱼ}(b)⁆
  = x_{eᵢ+eⱼ}(ab) x_{2eᵢ}(a²b),
⁅x_{eᵢ-eⱼ}(a), x_{eᵢ+eⱼ}(b)⁆
  = x_{2eᵢ}(2ab).
```

The parameters on the right are expressed using the algebra structure of the value ring. Thus
`TauCeti.AdditiveGroup.gaPointParamMul f g` has parameter `ab`; its product with itself in the
additive group has parameter `2ab`. These are not statements about convolution multiplication
being the multiplication of the value ring.

The relations supply the rank-two `C₂` check for the root-subgroup part of the pinned
Chevalley--Demazure interface. In characteristic two, the second relation becomes commutation,
while the first retains the quadratic term used by the `B₂/C₂` special isogeny.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2 and §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.Symplectic

universe u w

variable {R : Type u} [CommRing R]
variable {A : Type w} [CommRing A] [Algebra R A]
variable {m : ℕ} {i j : Fin m}

/-- **The multiply-laced Chevalley relation on algebra-valued points of `Sp₂ₘ`.** For
distinct `i` and `j`, the commutator of the roots `eᵢ-eⱼ` and `2eⱼ` is the product of the
root subgroups for `eᵢ+eⱼ` and `2eᵢ`, with parameters `ab` and `a²b`. -/
theorem commutatorElement_differenceShortRootSubgroupPoints_positiveLongRootSubgroupPoints
    (hij : i ≠ j)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ⁅shortRootSubgroupPoints .difference hij f, positiveLongRootSubgroupPoints j g⁆ =
      shortRootSubgroupPoints .positiveSum hij (AdditiveGroup.gaPointParamMul f g) *
        positiveLongRootSubgroupPoints i
          (AdditiveGroup.gaPointParamMul f (AdditiveGroup.gaPointParamMul f g)) := by
  apply (pointsMulEquiv (R := R) (A := A) m).injective
  rw [map_commutatorElement, map_mul, pointsMulEquiv_shortRootSubgroupPoints,
    pointsMulEquiv_positiveLongRootSubgroupPoints,
    pointsMulEquiv_shortRootSubgroupPoints,
    pointsMulEquiv_positiveLongRootSubgroupPoints]
  rw [GLSymplecticFin.ShortRootFamily.hom_difference,
    GLSymplecticFin.differenceShortRootHom_apply,
    GLSymplecticFin.ShortRootFamily.hom_positiveSum,
    GLSymplecticFin.positiveSumShortRootHom_apply]
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv f,
    AdditiveGroup.toAdd_gaPointsMulEquiv g,
    AdditiveGroup.toAdd_gaPointsMulEquiv (AdditiveGroup.gaPointParamMul f g),
    AdditiveGroup.toAdd_gaPointsMulEquiv
      (AdditiveGroup.gaPointParamMul f (AdditiveGroup.gaPointParamMul f g)),
    AdditiveGroup.gaPointParamMul_apply_ι,
    AdditiveGroup.gaPointParamMul_apply_ι,
    AdditiveGroup.gaPointParamMul_apply_ι]
  ring_nf
  exact
    GLSymplecticFin.commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit
      hij
      (f.ofConv (SymmetricAlgebra.ι R R 1))
      (g.ofConv (SymmetricAlgebra.ι R R 1))

/-- **The structure-constant-two Chevalley relation on algebra-valued points of `Sp₂ₘ`.**
For distinct `i` and `j`, the commutator of the roots `eᵢ-eⱼ` and `eᵢ+eⱼ` is the long-root
point `x_{2eᵢ}(2ab)`. The square on the right is convolution multiplication in `𝔾ₐ(A)`,
which adds its parameter to itself. -/
theorem commutatorElement_differenceShortRootSubgroupPoints_positiveSumShortRootSubgroupPoints
    (hij : i ≠ j)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ⁅shortRootSubgroupPoints .difference hij f, shortRootSubgroupPoints .positiveSum hij g⁆ =
      positiveLongRootSubgroupPoints i (AdditiveGroup.gaPointParamMul f g) ^ 2 := by
  apply (pointsMulEquiv (R := R) (A := A) m).injective
  rw [map_commutatorElement, map_pow, pointsMulEquiv_shortRootSubgroupPoints,
    pointsMulEquiv_shortRootSubgroupPoints,
    pointsMulEquiv_positiveLongRootSubgroupPoints]
  rw [GLSymplecticFin.ShortRootFamily.hom_difference,
    GLSymplecticFin.differenceShortRootHom_apply,
    GLSymplecticFin.ShortRootFamily.hom_positiveSum,
    GLSymplecticFin.positiveSumShortRootHom_apply]
  simp only [AdditiveGroup.toAdd_gaPointsMulEquiv,
    AdditiveGroup.gaPointParamMul_apply_ι]
  convert
    GLSymplecticFin.commutatorElement_differenceShortRootUnit_positiveSumShortRootUnit
        hij
        (f.ofConv (SymmetricAlgebra.ι R R 1))
        (g.ofConv (SymmetricAlgebra.ι R R 1)) using 1
  rw [pow_two]
  let c := f.ofConv (SymmetricAlgebra.ι R R 1) *
    g.ofConv (SymmetricAlgebra.ι R R 1)
  have hadd :
      GLSymplecticFin.positiveLongRootTransvectionUnit i c *
          GLSymplecticFin.positiveLongRootTransvectionUnit i c =
        GLSymplecticFin.positiveLongRootTransvectionUnit i (c + c) := by
    simpa only [GLSymplecticFin.positiveLongRootTransvectionHom_apply,
      toAdd_ofAdd, toAdd_mul] using
      ((GLSymplecticFin.positiveLongRootTransvectionHom (R := A) i).map_mul
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd c)).symm
  rw [hadd]
  congr 1
  dsimp only [c]
  ring

end TauCeti.Symplectic
