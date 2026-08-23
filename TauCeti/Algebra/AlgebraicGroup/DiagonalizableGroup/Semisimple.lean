/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.GeometricSemisimplePoint
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Semisimple

/-!
# Points of diagonalizable groups are semisimple

A representation of a diagonalizable group `D(G) = Spec R[G]` decomposes into weight submodules
(the internal direct sum of character spaces). Consequently, every point of `D(G)` acts on each
representation by scalar multiplication on each weight space, making the underlying linear
endomorphism diagonalizable and therefore semisimple.

This file proves that **every point of a diagonalizable group is semisimple**: for any commutative
semiring `R`, any commutative group `G`, and any field `K` equipped with an `R`-algebra structure,
every point `g : WithConv (R[G] →ₐ[R] K)` acts on every finitely generated comodule by a semisimple
linear automorphism.

As a consequence, over a perfect field `K`, the multiplicative Jordan decomposition of every point
`g` of a diagonalizable group is trivial: `g_s = g` and `g_u = 1`.

The result applies immediately to split tori and the roots-of-unity groups `μ_n`. Using the generic
object property
`geometricallySemisimplePointsCommHopfAlgProperty`, this file also packages the geometric statement
for diagonalizable groups, which likewise applies directly to split tori.

## Main declarations

* `TauCeti.DiagonalizableGroup.isSemisimplePoint`: every point of a diagonalizable group is a
  semisimple point.
* `TauCeti.DiagonalizableGroup.semisimplePart_eq_self` and
  `TauCeti.DiagonalizableGroup.unipotentPart_eq_one`: the Jordan factors of a point of a
  diagonalizable group are the point itself and the identity.
* `TauCeti.DiagonalizableGroup.geometricallySemisimplePointsCommHopfAlgProperty`: diagonalizable
  groups have only semisimple geometric points.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.

This supplies the semisimple-points theorem for diagonalizable groups and tori in Layer 4 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v x

namespace DiagonalizableGroup

variable {R : Type u} {G : Type v} {K : Type x}
variable [CommSemiring R] [CommGroup G] [Field K] [Algebra R K]

/-- **Every point of the diagonalizable group `D(G)` is semisimple.** -/
theorem isSemisimplePoint (g : WithConv (MonoidAlgebra R G →ₐ[R] K)) :
    HopfAlgebra.IsSemisimplePoint g := by
  rw [HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_endOfPoint]
  intro M
  exact Comodule.isSemisimple_endOfPoint_monoidAlgebra g.ofConv

section JordanDecomposition

variable {k : Type u} {G : Type u} {K : Type u}
variable [Field k] [CommGroup G] [Field K] [Algebra k K] [PerfectField K]

/-- **The semisimple part of a point of a diagonalizable group is the point itself.** -/
@[simp]
theorem semisimplePart_eq_self (g : WithConv (MonoidAlgebra k G →ₐ[k] K)) :
    HopfAlgebra.Point.semisimplePart k (MonoidAlgebra k G) K g = g :=
  HopfAlgebra.Point.semisimplePart_eq_self k (MonoidAlgebra k G) K (fun M ↦ by
    have h := isSemisimplePoint (R := k) (G := G) (K := K) g
    exact (HopfAlgebra.isSemisimplePoint_def g).mp h M)

/-- **The unipotent part of a point of a diagonalizable group is trivial.** -/
@[simp]
theorem unipotentPart_eq_one (g : WithConv (MonoidAlgebra k G →ₐ[k] K)) :
    HopfAlgebra.Point.unipotentPart k (MonoidAlgebra k G) K g = 1 :=
  HopfAlgebra.Point.unipotentPart_eq_one_of_isSemisimple k (MonoidAlgebra k G) K (fun M ↦ by
    have h := isSemisimplePoint (R := k) (G := G) (K := K) g
    exact (HopfAlgebra.isSemisimplePoint_def g).mp h M)

end JordanDecomposition

end DiagonalizableGroup

section ObjectPropertyExamples

variable (k : Type u) [Field k]

namespace DiagonalizableGroup

/-- **Every diagonalizable group has only semisimple geometric points.** -/
theorem geometricallySemisimplePointsCommHopfAlgProperty (G : Type v) [CommGroup G] :
    TauCeti.geometricallySemisimplePointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (MonoidAlgebra k G)) := by
  rw [TauCeti.geometricallySemisimplePointsCommHopfAlgProperty_iff]
  intro g
  exact isSemisimplePoint g

end DiagonalizableGroup

end ObjectPropertyExamples

end TauCeti
