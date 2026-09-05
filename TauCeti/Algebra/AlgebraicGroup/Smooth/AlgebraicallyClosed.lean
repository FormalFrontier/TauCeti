/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import TauCeti.AlgebraicGeometry.Group.Smooth

/-!
# Smooth affine groups over algebraically closed fields

A reduced group scheme locally of finite type over an algebraically closed field is smooth.
For finite-type commutative Hopf algebras this gives the particularly useful coordinate
criterion

```text
smooth over an algebraically closed field ↔ reduced coordinate ring.
```

These criteria let downstream constructions establish the ring-theoretic condition of ordinary
reducedness instead of proving smoothness directly. The geometric-reducedness criterion also
supplies the resulting stability under field extension when affine groups and their subgroup
schemes are compared after base change.

## Main declarations

* `TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced`: the
  scheme-theoretic criterion.
* `TauCeti.smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced`: a reduced finite-type
  commutative Hopf algebra over an algebraically closed field is smooth.
* `TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed`: the coordinate smoothness
  criterion.
* `TauCeti.geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed`: over an
  algebraically closed field, ordinary and geometric reducedness agree for finite-type
  commutative Hopf algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.
-/

-- The group-scheme argument is adapted from the private algebraically-closed-field lemma underlying
-- `AlgebraicGeometry.smooth_of_grpObj` in Mathlib.

public section

open CategoryTheory

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

noncomputable section

/-- **A reduced finite-type commutative Hopf algebra over an algebraically closed field is
smooth.** -/
theorem smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced
    (k : Type u) [Field k] [IsAlgClosed k] (H : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] [IsReduced H] :
    smoothCommHopfAlgProperty k H := by
  let _ : LocallyOfFiniteType
      (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) :=
    (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance
  let _ : IsReduced ((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.left :=
    by
      rw [hopfSpec_obj_X_left]
      rw [affine_isReduced_iff]
      infer_instance
  let _ : GrpObj
      (Over.mk (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom)) :=
    inferInstanceAs (GrpObj ((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X)
  apply (algebraSmooth_iff_smooth_hopfSpec k H).mpr
  rw [smoothAffineGroupSchemeProperty_iff]
  exact AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced _

/-- For a finite-type commutative Hopf algebra over an algebraically closed field, smoothness is
equivalent to reducedness of its coordinate ring. -/
theorem smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (H : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] :
    smoothCommHopfAlgProperty k H ↔ IsReduced H := by
  constructor
  · intro hH
    let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff H).mp hH
    exact isReduced_of_smooth_of_field k H
  · intro hH
    let _ : IsReduced H := hH
    exact smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k H

/-- Over an algebraically closed field, a finite-type commutative Hopf algebra is geometrically
reduced exactly when its coordinate ring is reduced. -/
theorem geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (H : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] :
    geometricallyReducedCommHopfAlgProperty k H ↔ IsReduced H := by
  rw [← smoothCommHopfAlgProperty_iff_geometricallyReduced,
    smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed]

end

end TauCeti
