/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Smoothness of group schemes over algebraically closed fields

A reduced group scheme locally of finite type over an algebraically closed field is smooth.
This upgrades a ring-theoretic reducedness hypothesis to geometric smoothness at the level of
group schemes, and supplies the scheme-theoretic input for coordinate-ring consequences such as
the finite-type commutative Hopf algebra smoothness criterion.

## Main declarations

* `TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed_of_isReduced`: the
  reducedness criterion for smooth group schemes over algebraically closed fields.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26.
-/

-- The proof is adapted from the private algebraically-closed-field lemma underlying
-- `AlgebraicGeometry.smooth_of_grpObj` in Mathlib.

public section

open CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

/-- A reduced group scheme locally of finite type over an algebraically closed field is smooth. -/
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
  have hx' : x'.left = pointOfClosedPoint f x hxc := by
    simp only [x', Over.homMk_left, pointEquivClosedPoint_symm_apply_coe]
  have hy' : y'.left = pointOfClosedPoint f y hyc := by
    simp only [y', Over.homMk_left, pointEquivClosedPoint_symm_apply_coe]
  have eLeft_hom : eLeft.hom = e.hom.left := by
    simp only [eLeft, Functor.mapIso_hom, Over.forget_map]
  have heLeft : pointOfClosedPoint f x hxc ≫ eLeft.hom =
      pointOfClosedPoint f y hyc := by
    rw [eLeft_hom, ← hx', ← hy']
    simpa only [Over.comp_left] using congrArg Over.Hom.left he
  have he' : eLeft.hom x = y := by
    rw [← pointOfClosedPoint_apply f x hxc (IsLocalRing.closedPoint K),
      ← pointOfClosedPoint_apply f y hyc (IsLocalRing.closedPoint K)]
    exact congr(($heLeft) (IsLocalRing.closedPoint K))
  have eLeft_hom_comp : eLeft.hom ≫ f = f := by
    rw [eLeft_hom]
    exact e.hom.w
  rw! [← he', ← eLeft.hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    eLeft_hom_comp] at hy
  exact hx hy

end

end TauCeti.AlgebraicGeometry
