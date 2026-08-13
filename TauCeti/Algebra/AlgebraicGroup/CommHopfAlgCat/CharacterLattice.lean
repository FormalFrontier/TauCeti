/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.Galois

/-!
# Geometric character groups and their Galois action

For a commutative Hopf algebra `H` over a field `k`, its geometric characters are the group-like
elements of its coordinate algebra after extension to an algebraic closure:

```text
X*(H) = GroupLike k̄ (k̄ ⊗[k] H).
```

The generic scalar action from `TauCeti.Algebra.Bialgebra.GroupLike.Galois` specializes to the
absolute Galois group and acts by `σ • (a ⊗ h) = σ(a) ⊗ h`. Its actions on the scalar
extension, the group-like elements, and their additive form are available through the instances
`GaloisScalar.instScalarMulSemiringAction`, `GaloisScalar.instGroupLikeDistribMulAction`, and
`GaloisScalar.instAdditiveDistribMulAction`; this module supplies the instance bridges needed for
the opaque `Field.absoluteGaloisGroup` definition.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterGroup`: the geometric character group.
* `TauCeti.CommHopfAlgCat.additiveCharacterGroup`: its additive form.
* `TauCeti.CommHopfAlgCat.instGaloisScalarMulSemiringAction`: an instance bridge for the
  absolute-Galois action on the scalar extension.
* `TauCeti.CommHopfAlgCat.instGeometricCharacterGroupGaloisAction`: an instance bridge for the
  induced action on geometric characters.
* `TauCeti.CommHopfAlgCat.instAdditiveCharacterGroupGaloisAction`: an instance bridge for the
  transported additive action.

## References

For the torus character-module viewpoint motivating this construction, see J. S. Milne,
*Algebraic Groups* (2017), §§12.14--12.17. The scalar-action lemmas themselves are generic
bialgebra facts.
-/

public section

open TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{u} k)

/-- The geometric character group of a commutative Hopf algebra: the group-like elements of
its coordinate algebra after extension to an algebraic closure. For a represented affine group,
these are exactly its morphisms over `k̄` to the multiplicative group. -/
abbrev geometricCharacterGroup :=
  GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H)

/-- Bridge the generic scalar action across the opaque `Field.absoluteGaloisGroup` definition. -/
noncomputable instance instGaloisScalarMulSemiringAction :
    MulSemiringAction (Field.absoluteGaloisGroup k) (AlgebraicClosure k ⊗[k] H) := by
  unfold Field.absoluteGaloisGroup
  exact GaloisScalar.instScalarMulSemiringAction

/-- Bridge the generic group-like action across the opaque absolute-Galois-group definition. -/
noncomputable instance instGeometricCharacterGroupGaloisAction :
    MulDistribMulAction (Field.absoluteGaloisGroup k) (geometricCharacterGroup H) := by
  unfold Field.absoluteGaloisGroup
  exact GaloisScalar.instGroupLikeDistribMulAction

/-- The additive form of the geometric character group of a commutative Hopf algebra. For a
torus its underlying additive group is free of finite rank. -/
abbrev additiveCharacterGroup := Additive (geometricCharacterGroup H)

/-- Bridge the generic additive action across the opaque absolute-Galois-group definition. -/
noncomputable instance instAdditiveCharacterGroupGaloisAction :
    DistribMulAction (Field.absoluteGaloisGroup k) (additiveCharacterGroup H) := by
  unfold Field.absoluteGaloisGroup
  exact GaloisScalar.instAdditiveDistribMulAction

end CommHopfAlgCat

end TauCeti
