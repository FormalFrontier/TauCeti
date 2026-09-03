/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Properties
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced

/-!
# Smoothness of affine group images

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a field. Contravariantly,
`f` represents a homomorphism from the affine group with coordinate algebra `K` to the one with
coordinate algebra `H`. If the target ambient group is of finite type, its scheme-theoretic image
has coordinate algebra

```text
H / ker f.
```

When the source group is smooth, its coordinate algebra is geometrically reduced. The image
coordinate algebra embeds in the source coordinate algebra, so it is geometrically reduced as
well. Finite type of the ambient group passes to the quotient, and the equivalence between
geometric reducedness and smoothness for finite-type affine groups then proves that the image is
smooth.

This is the smoothness step in forming the product of two connected normal smooth unipotent
closed subgroups as the image of their multiplication map. Unipotence of that image requires the
separate quotient-closure argument; it is not asserted here.

## Main declaration

* `TauCeti.smoothCommHopfAlgProperty.image`: a finite-type affine group image of a smooth affine
  group is smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1 and 5.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 11 and 16.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap. The binary
product step uses the scheme-theoretic image of multiplication from a semidirect product; this
file supplies smoothness of that image once the source product is known to be smooth.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace smoothCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : CommHopfAlgCat.{u} k}

/-- **The scheme-theoretic image in a finite-type affine group of a smooth affine group is
smooth.**

Here `f : H ⟶ K` is contravariant: `K` is the coordinate algebra of the source group, while
`H` is the coordinate algebra of the ambient group. The finite-type hypothesis is therefore on
`H`; it passes to `CommHopfAlgCat.image f = H / ker f`. -/
theorem image [Algebra.FiniteType k H] (f : H ⟶ K)
    (hK : smoothCommHopfAlgProperty k K) :
    smoothCommHopfAlgProperty k (CommHopfAlgCat.image f) :=
  smoothCommHopfAlgProperty_of_geometricallyReduced k (CommHopfAlgCat.image f)
    ((geometricallyReducedCommHopfAlgProperty_of_smooth k K hK).image f)

end smoothCommHopfAlgProperty

end TauCeti
