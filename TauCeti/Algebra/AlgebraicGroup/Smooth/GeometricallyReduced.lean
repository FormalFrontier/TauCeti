/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.GeometricallyReduced
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Smoothness and geometric reducedness of affine groups

Mathlib proves that a geometrically reduced group scheme locally of finite type over a field is
smooth. Conversely, a smooth algebra over a field remains smooth, and hence reduced, after every
field extension. Transporting both directions through Tau Ceti's affine Hopf/group-scheme
dictionary gives the coordinate criterion

```text
finite type + commutative Hopf algebra: geometrically reduced ⇔ smooth.
```

The finite-type hypothesis is kept separate throughout. In particular, neither geometric
reducedness nor smoothness is built into the category of commutative Hopf algebras.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty_of_geometricallyReduced`: a finite-type geometrically
  reduced commutative Hopf algebra over a field is smooth.
* `TauCeti.geometricallyReducedCommHopfAlgProperty_of_smooth`: a smooth commutative Hopf algebra
  over a field is geometrically reduced.
* `TauCeti.smoothCommHopfAlgProperty_iff_geometricallyReduced`: the finite-type equivalence.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.

This advances Layer 2, "Smoothness and dimension tools via `Lie(G)`", of the ReductiveGroups
roadmap. The forward implication uses Mathlib's `AlgebraicGeometry.smooth_of_grpObj`; the reverse
uses `TauCeti.isReduced_of_smooth_of_field` after arbitrary field extension.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u v

noncomputable section

/-- **A smooth commutative Hopf algebra over a field is geometrically reduced.**

Smoothness is preserved by extension of the ground field. The resulting tensor product is
reduced by `TauCeti.isReduced_of_smooth_of_field`; commuting the tensor factors puts the result
in the orientation used by `geometricallyReducedCommHopfAlgProperty`. -/
theorem geometricallyReducedCommHopfAlgProperty_of_smooth
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k)
    (hH : smoothCommHopfAlgProperty k H) :
    geometricallyReducedCommHopfAlgProperty k H := by
  rw [geometricallyReducedCommHopfAlgProperty_iff]
  intro K _ _
  let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff H).mp hH
  let _ : Algebra.Smooth K (K ⊗[k] H) := Algebra.Smooth.baseChange k H K
  let _ : IsReduced (K ⊗[k] H) := isReduced_of_smooth_of_field K (K ⊗[k] H)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k H K).toRingHom
    (Algebra.TensorProduct.comm k H K).injective

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

/-- For a finite-type commutative Hopf algebra over a field, smoothness is equivalent to geometric
reducedness. -/
theorem smoothCommHopfAlgProperty_iff_geometricallyReduced
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) [Algebra.FiniteType k H] :
    smoothCommHopfAlgProperty k H ↔ geometricallyReducedCommHopfAlgProperty k H :=
  ⟨geometricallyReducedCommHopfAlgProperty_of_smooth k H,
    smoothCommHopfAlgProperty_of_geometricallyReduced k H⟩

end

end TauCeti
