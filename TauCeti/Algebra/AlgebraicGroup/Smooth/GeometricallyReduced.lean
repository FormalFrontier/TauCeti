/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.GeometricallyReduced
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Smoothness of geometrically reduced affine groups

Mathlib proves that a geometrically reduced group scheme locally of finite type over a field is
smooth. Transporting that theorem through Tau Ceti's affine Hopf/group-scheme dictionary gives
the coordinate criterion

```text
finite type + geometrically reduced ⇒ smooth.
```

The finite-type hypothesis is kept separate throughout. In particular, neither geometric
reducedness nor smoothness is built into the category of commutative Hopf algebras.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty_of_geometricallyReduced`: a finite-type geometrically
  reduced commutative Hopf algebra over a field is smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.

This advances Layer 2, "Smoothness and dimension tools via `Lie(G)`", of the ReductiveGroups
roadmap. The scheme-theoretic input is Mathlib's `AlgebraicGeometry.smooth_of_grpObj`.
-/

public section

open CategoryTheory

namespace TauCeti

open AlgebraicGeometry

universe u

noncomputable section

/-- **A finite-type geometrically reduced commutative Hopf algebra over a field is smooth.**
-/
theorem smoothCommHopfAlgProperty_of_geometricallyReduced
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H]
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    smoothCommHopfAlgProperty k H := by
  let _ : LocallyOfFiniteType
      (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) :=
    (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance
  let _ : GeometricallyReduced
      (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) :=
    (geometricallyReducedCommHopfAlg_iff_geometricallyReduced_hopfSpec k H).mp hH
  -- `smooth_of_grpObj` asks for the `Over.mk X.hom` spelling of the Hopf spectrum object `X`.
  let _ : GrpObj
      (Over.mk (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom)) :=
    inferInstanceAs (GrpObj ((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X)
  apply (algebraSmooth_iff_smooth_hopfSpec k H).mpr
  rw [smoothAffineGroupSchemeProperty_iff]
  exact smooth_of_grpObj _

end

end TauCeti
