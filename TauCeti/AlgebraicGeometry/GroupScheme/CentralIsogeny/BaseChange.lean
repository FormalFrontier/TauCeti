/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic

/-!
# Base change of group-scheme isogenies

This file proves that isogenies of group schemes over a field remain isogenies after base change
along a morphism between spectra of fields. The point groups before and after base change are
identified through the pullback adjunction, which shows that central kernels remain central. For a
commutative source, the base-changed isogeny is central without any centrality hypothesis. The
group-scheme base change is the pullback functor on the over category, lifted to group objects.

## Main declarations

* `TauCeti.GroupScheme.IsIsogeny.baseChange`: isogenies remain isogenies after base change.
* `TauCeti.GroupScheme.IsCentralIsogeny.baseChange`: central isogenies remain central after base
  change.
* `TauCeti.GroupScheme.IsIsogeny.baseChange_isCentral_of_isCommMonObj`: the base change of an
  isogeny from a commutative source is a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.

The base-change argument follows
`TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny.baseChange`.

This is the base-change stability needed for the central-isogeny interface in Layer 6 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj
namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

section Field

variable {k L : Type u} [Field k] [Field L]
variable {G H : Grp (Over (Spec (CommRingCat.of k)))}

/-- Base change along a morphism between spectra of fields preserves group-scheme isogenies. -/
theorem IsIsogeny.baseChange
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) {f : G ⟶ H}
    (hf : IsIsogeny f) : IsIsogeny ((Over.pullback s).mapGrp.map f) := by
  rw [isIsogeny_iff, Functor.mapGrp_map_hom_hom]
  exact ⟨MorphismProperty.overPullbackMap _ _ hf.isFinite,
    MorphismProperty.overPullbackMap _ _ hf.flat,
    MorphismProperty.overPullbackMap _ _ hf.surjective⟩

/-- The adjunction between postcomposition and pullback identifies points of a base-changed group
scheme with points of the original group scheme over the same test scheme viewed over the old
base. This identification is multiplicative. -/
private noncomputable def baseChangePointMulEquiv
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k))
    (G : Grp (Over (Spec (CommRingCat.of k))))
    (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ ((Over.pullback s).mapGrp.obj G).X) ≃*
      ((Over.map s).obj T ⟶ G.X) where
  toFun p := ((Over.mapPullbackAdj s).homEquiv T G.X).symm p
  invFun p := (Over.mapPullbackAdj s).homEquiv T G.X p
  left_inv := (Over.mapPullbackAdj s).homEquiv T G.X |>.right_inv
  right_inv := (Over.mapPullbackAdj s).homEquiv T G.X |>.left_inv
  map_mul' p q := by
    let pLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s := p.left
    let qLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s := q.left
    have hpq :
        pLeft ≫ Limits.pullback.snd G.X.hom s =
          qLeft ≫ Limits.pullback.snd G.X.hom s :=
      p.w.trans q.w.symm
    have hleft (r : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
        Over.Hom.left (((Over.mapPullbackAdj s).homEquiv T G.X).symm r) =
          Over.Hom.left r ≫ Limits.pullback.fst G.X.hom s :=
      rfl
    have hmulPoint :
        Over.Hom.left (p * q) =
          (Limits.pullback.lift pLeft qLeft hpq ≫
              Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
            Over.Hom.left ((Over.pullback s).map μ[G.X]) := (rfl)
    ext
    rw [hleft (p * q), hmulPoint]
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left, hleft]
    have hfst :
        Limits.pullback.fst ((Over.pullback s).obj G.X).hom
            ((Over.pullback s).obj G.X).hom =
          Limits.pullback.fst (Limits.pullback.snd G.X.hom s)
            (Limits.pullback.snd G.X.hom s) := (rfl)
    have hsnd :
        Limits.pullback.snd ((Over.pullback s).obj G.X).hom
            ((Over.pullback s).obj G.X).hom =
          Limits.pullback.snd (Limits.pullback.snd G.X.hom s)
            (Limits.pullback.snd G.X.hom s) := (rfl)
    have hmap :
        Over.Hom.left ((Over.pullback s).map μ[G.X]) ≫
            (Limits.pullback.fst G.X.hom s :
              ((Over.pullback s).mapGrp.obj G).X.left ⟶ G.X.left) =
          Limits.pullback.fst (MonoidalCategoryStruct.tensorObj G.X G.X).hom s ≫
            Over.Hom.left μ[G.X] := by
      simp only [Over.pullback_map_left, Limits.pullback.lift_fst]
    have hmap_assoc :
        (((Limits.pullback.lift pLeft qLeft hpq ≫
              Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
            Over.Hom.left ((Over.pullback s).map μ[G.X])) ≫
          (Limits.pullback.fst G.X.hom s :
            ((Over.pullback s).mapGrp.obj G).X.left ⟶ G.X.left)) =
        (((Limits.pullback.lift pLeft qLeft hpq ≫
              Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
            Limits.pullback.fst (MonoidalCategoryStruct.tensorObj G.X G.X).hom s) ≫
          Over.Hom.left μ[G.X]) := by
      simp only [Category.assoc, hmap]
    have hpair :
        (Limits.pullback.lift pLeft qLeft hpq ≫
            Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
          Limits.pullback.fst _ s =
        Limits.pullback.lift
          (pLeft ≫ Limits.pullback.fst G.X.hom s)
          (qLeft ≫ Limits.pullback.fst G.X.hom s)
          (by
            simp only [Category.assoc, Limits.pullback.condition]
            simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ s) hpq) := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc,
          Over.μ_pullback_left_fst_fst G.X G.X, hfst]
        simp only [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_fst]
      · rw [Category.assoc, Category.assoc,
          Over.μ_pullback_left_fst_snd G.X G.X, hsnd]
        simp only [Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]
    exact (hmap_assoc.trans
      (congrArg (fun z ↦ z ≫ Over.Hom.left μ[G.X]) hpair))

/-- The point-group equivalence is the underlying pullback-adjunction equivalence. -/
private theorem baseChangePointMulEquiv_apply
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k))
    (G : Grp (Over (Spec (CommRingCat.of k))))
    (T : Over (Spec (CommRingCat.of L)))
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s G T p =
      ((Over.mapPullbackAdj s).homEquiv T G.X).symm p := (rfl)

/-- The point-group identification intertwines a base-changed morphism with the original
morphism. -/
private theorem baseChangePointMulEquiv_pointMap
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) (f : G ⟶ H)
    (T : Over (Spec (CommRingCat.of L)))
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s H T
        (pointMap ((Over.pullback s).mapGrp.map f) T p) =
      pointMap f ((Over.map s).obj T) (baseChangePointMulEquiv s G T p) := by
  simp only [baseChangePointMulEquiv_apply, pointMap_apply,
    Functor.mapGrp_map_hom_hom]
  exact ((Over.mapPullbackAdj s).homEquiv_naturality_right_symm p f.hom.hom)

/-- Base change along a morphism between spectra of fields preserves central isogenies. -/
theorem IsCentralIsogeny.baseChange
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) {f : G ⟶ H}
    (hf : IsCentralIsogeny f) :
    IsCentralIsogeny ((Over.pullback s).mapGrp.map f) := by
  rw [isCentralIsogeny_iff]
  have hi := hf.isIsogeny.baseChange s
  refine ⟨hi.isFinite, hi.flat, hi.surjective, ?_⟩
  rw [hasCentralKernel_iff_pointMap_ker_le_center]
  intro T p hp
  rw [Subgroup.mem_center_iff]
  intro q
  let eG := baseChangePointMulEquiv s G T
  have hp₀ : pointMap ((Over.pullback s).mapGrp.map f) T p = 1 :=
    (MonoidHom.mem_ker).mp hp
  have hp' : pointMap f ((Over.map s).obj T) (eG p) = 1 := by
    rw [← baseChangePointMulEquiv_pointMap, hp₀, map_one]
  have hf' := (hasCentralKernel_iff_pointMap_ker_le_center f).mp hf.hasCentralKernel
  have hc := Subgroup.mem_center_iff.mp
    (hf' ((Over.map s).obj T) ((MonoidHom.mem_ker).mpr hp')) (eG q)
  apply eG.injective
  simpa only [map_mul] using hc

/-- The base change of an isogeny from a commutative group scheme is a central isogeny. -/
theorem IsIsogeny.baseChange_isCentral_of_isCommMonObj
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) {f : G ⟶ H}
    (hf : IsIsogeny f) [IsCommMonObj G.X] :
    IsCentralIsogeny ((Over.pullback s).mapGrp.map f) := by
  let _ : IsCommMonObj ((Over.pullback s).mapGrp.obj G).X := by
    exact ((Over.pullback s).mapCommMon.obj (.mk G.X)).comm
  exact (hf.baseChange s).isCentral_of_isCommMonObj

end Field

end TauCeti.GroupScheme
