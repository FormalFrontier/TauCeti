/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Extensions of geometrically solvable affine groups

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a field `k`. Contravariantly,
it represents a homomorphism from the affine group represented by `K` to the one represented by
`H`. This file proves that the source group of geometric points is solvable when the target and
the scheme-theoretic kernel are solvable.

On coordinate rings, the kernel has algebra

```text
K / K·f(H⁺),
```

implemented as `CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f)`. Its geometric
points map injectively into those of `K`, with image exactly the kernel of the map induced by
`f`. Mathlib's abstract extension theorem for solvable groups then applies directly. Conversely,
a closed subgroup of a geometrically solvable affine group has solvable geometric points, so the
kernel condition is also necessary once the source is solvable.

## Main declarations

* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_of_kernel`: geometric solvability is
  closed under extensions.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_iff_kernel`: when the target is
  geometrically solvable, the source is geometrically solvable exactly when its kernel is.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies extension closure for the "Lie--Kolchin; solvable groups" milestone in Layer 5 of
the ReductiveGroups roadmap. Together with closed-subgroup and product closure, it is part of the
subgroup calculus needed for the solvable radical in Layer 6.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

/-- Geometric-point solvability is closed under extensions.

For the group homomorphism represented by `f : H ⟶ K`, assume that the target `Spec H` and
the scheme-theoretic kernel `Spec (K / K·f(H⁺))` have solvable groups of geometric points.
Then the geometric point group of the source `Spec K` is solvable. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_of_kernel
    (k : Type u) [Field k] {H K : CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H)
    (hkernel : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f))) :
    geometricallySolvablePointsCommHopfAlgProperty k K := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hH hkernel ⊢
  let i : WithConv ((CommHopfAlgCat.quotient K
      (CommHopfAlgCat.kernelHopfIdeal f)) →ₐ[k] AlgebraicClosure k) →*
      WithConv (K →ₐ[k] AlgebraicClosure k) :=
    (CommHopfAlgCat.quotientPointsHom K (CommHopfAlgCat.kernelHopfIdeal f)
      (CommAlgCat.of k (AlgebraicClosure k))).hom
  let p : WithConv (K →ₐ[k] AlgebraicClosure k) →*
      WithConv (H →ₐ[k] AlgebraicClosure k) :=
    AlgHom.mapDomain (H₁ := H) (H₂ := K) (A := AlgebraicClosure k) f.hom
  refine @Group.isSolvable_of_ker_le_range
    (WithConv (K →ₐ[k] AlgebraicClosure k)) _
    (WithConv ((CommHopfAlgCat.quotient K
      (CommHopfAlgCat.kernelHopfIdeal f)) →ₐ[k] AlgebraicClosure k))
    (WithConv (H →ₐ[k] AlgebraicClosure k)) _ _ i p ?_ hkernel hH
  intro g hg
  have hp : p g = 1 := MonoidHom.mem_ker.mp hg
  have hp' : toConv (g.ofConv.comp (f.hom : H →ₐ[k] K)) = 1 := by
    simpa only [p, AlgHom.mapDomain_apply] using hp
  dsimp only [i]
  exact (CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff f
    (CommAlgCat.of k (AlgebraicClosure k)) g).mp hp'

/-- If the target of a homomorphism is geometrically solvable, then its source is geometrically
solvable exactly when its scheme-theoretic kernel is.

The forward implication is closed-subgroup stability, applied to the quotient coordinate map.
The reverse implication is extension closure. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_iff_kernel
    (k : Type u) [Field k] {H K : CommHopfAlgCat.{u} k} (f : H ⟶ K)
    (hH : geometricallySolvablePointsCommHopfAlgProperty k H) :
    geometricallySolvablePointsCommHopfAlgProperty k K ↔
      geometricallySolvablePointsCommHopfAlgProperty k
        (CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f)) := by
  constructor
  · intro hK
    exact geometricallySolvablePointsCommHopfAlgProperty_quotient k K
      (CommHopfAlgCat.kernelHopfIdeal f) hK
  · exact geometricallySolvablePointsCommHopfAlgProperty_of_kernel k f hH

end TauCeti
