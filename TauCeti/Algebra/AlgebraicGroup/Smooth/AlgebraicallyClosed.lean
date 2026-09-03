/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced

/-!
# Smooth affine groups over algebraically closed fields

A reduced group scheme locally of finite type over an algebraically closed field is smooth.
For finite-type commutative Hopf algebras this gives the particularly useful coordinate
criterion

```text
smooth over an algebraically closed field ↔ reduced coordinate ring.
```

The reverse implication does not require the coordinate ring to be geometrically reduced in
advance. Smoothness is first proved directly on the group scheme by translating one smooth
closed point to every other closed point. The existing equivalence between smoothness and
geometric reducedness then shows that reducedness over an algebraically closed field already
persists after every field extension.

## Main declarations

* `TauCeti.smooth_of_grpObj_of_isAlgClosed_of_isReduced`: the scheme-theoretic criterion.
* `TauCeti.smoothCommHopfAlgProperty_of_isReduced_of_isAlgClosed`: a reduced finite-type
  commutative Hopf algebra over an algebraically closed field is smooth.
* `TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed`: the coordinate smoothness
  criterion.
* `TauCeti.geometricallyReducedCommHopfAlgProperty_iff_isReduced_of_isAlgClosed`: over an
  algebraically closed field, ordinary and geometric reducedness agree for finite-type
  commutative Hopf algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.

The group-scheme argument is adapted from the private algebraically-closed-field lemma underlying
`AlgebraicGeometry.smooth_of_grpObj` in Mathlib.

This supplies the smoothness input for the reduced-center step in Layer 6, "Reductive and
semisimple groups", of the ReductiveGroups roadmap. Once the nilradical of the center is packaged
as a Hopf ideal, this criterion makes the resulting reduced central subgroup smooth.
-/

public section

open CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory

namespace TauCeti

open AlgebraicGeometry

universe u

noncomputable section

/-- A reduced group scheme locally of finite type over an algebraically closed field is smooth.

Smoothness holds on a dense open subset because the field is perfect. If the nonsmooth locus
contained a point, its Jacobson property would provide a closed point there. Translation by
closed rational points carries that point to a closed point in the smooth locus, contradicting
invariance of the smooth locus under isomorphisms over the base. -/
theorem smooth_of_grpObj_of_isAlgClosed_of_isReduced
    {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [GrpObj (Over.mk f)] [IsReduced G] :
    Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty G := ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro h
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints h f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f :=
    Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f :=
    Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let e := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    GrpObj.mulRight (A := Over.mk f) y'
  let eLeft : G ≅ G := (Over.forget _).mapIso e
  have he : x' ≫ e.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, e]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have heLeft : pointOfClosedPoint f x hxc ≫ eLeft.hom =
      pointOfClosedPoint f y hyc := by
    simpa [x', y', eLeft, pointEquivClosedPoint] using congrArg Over.Hom.left he
  have he' : eLeft.hom x = y := by
    rw [← pointOfClosedPoint_apply f x hxc (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply f y hyc (IsLocalRing.closedPoint K)]
    exact congr(($heLeft) (IsLocalRing.closedPoint K))
  rw! [← he', ← eLeft.hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show eLeft.hom ≫ f = f from e.hom.w] at hy
  exact hx hy

/-- **A reduced finite-type commutative Hopf algebra over an algebraically closed field is
smooth.** -/
theorem smoothCommHopfAlgProperty_of_isReduced_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (H : CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] [IsReduced H] :
    smoothCommHopfAlgProperty k H := by
  let _ : LocallyOfFiniteType
      (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) :=
    (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance
  let _ : IsReduced ((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.left :=
    by
      change IsReduced (Spec (CommRingCat.of H))
      rw [affine_isReduced_iff]
      infer_instance
  let _ : GrpObj
      (Over.mk (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom)) :=
    inferInstanceAs (GrpObj ((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X)
  apply (algebraSmooth_iff_smooth_hopfSpec k H).mpr
  rw [smoothAffineGroupSchemeProperty_iff]
  exact smooth_of_grpObj_of_isAlgClosed_of_isReduced _

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
    exact smoothCommHopfAlgProperty_of_isReduced_of_isAlgClosed k H

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
