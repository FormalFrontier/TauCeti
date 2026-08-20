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

set_option backward.isDefEq.respectTransparency false in
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
    ext
    have hleft (r : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
        Over.Hom.left (((Over.mapPullbackAdj s).homEquiv T G.X).symm r) =
          Over.Hom.left r ≫ Limits.pullback.fst G.X.hom s :=
      rfl
    rw [hleft (p * q)]
    simp only [Hom.mul_def]
    simp only [Over.comp_left, Over.lift_left]
    simp only [hleft]
    change T ⟶ (Over.pullback s).obj G.X at p q
    have hmul :
        Over.Hom.left μ[((Over.pullback s).mapGrp.obj G).X] =
          Over.Hom.left
            (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X ≫
              (Over.pullback s).map μ[G.X]) :=
      rfl
    rw [hmul]
    simp only [Over.comp_left]
    simp only [Category.assoc, Over.pullback_map_left, Limits.pullback.lift_fst]
    have hpq :
        Over.Hom.left p ≫ Limits.pullback.snd G.X.hom s =
          Over.Hom.left q ≫ Limits.pullback.snd G.X.hom s :=
      p.w.trans q.w.symm
    have hpair :
        (Limits.pullback.lift (Over.Hom.left p) (Over.Hom.left q) hpq ≫
            Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
          Limits.pullback.fst _ s =
        Limits.pullback.lift
          (Over.Hom.left p ≫ Limits.pullback.fst G.X.hom s)
          (Over.Hom.left q ≫ Limits.pullback.fst G.X.hom s)
          (by
            simp only [Category.assoc, Limits.pullback.condition]
            simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ s) hpq) := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc,
          Over.μ_pullback_left_fst_fst G.X G.X]
        simp
      · rw [Category.assoc, Category.assoc,
          Over.μ_pullback_left_fst_snd G.X G.X]
        simp
    exact congrArg (fun z ↦ z ≫ Over.Hom.left μ[G.X]) hpair

set_option backward.isDefEq.respectTransparency false in
/-- The point-group identification intertwines a base-changed morphism with the original
morphism. -/
private theorem baseChangePointMulEquiv_pointMap
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) (f : G ⟶ H)
    (T : Over (Spec (CommRingCat.of L)))
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s H T
        (pointMap ((Over.pullback s).mapGrp.map f) T p) =
      pointMap f ((Over.map s).obj T) (baseChangePointMulEquiv s G T p) := by
  ext
  have hleftG :
      Over.Hom.left (baseChangePointMulEquiv s G T p) =
        Over.Hom.left p ≫ Limits.pullback.fst G.X.hom s :=
    rfl
  have hleftH
      (q : T ⟶ ((Over.pullback s).mapGrp.obj H).X) :
      Over.Hom.left (baseChangePointMulEquiv s H T q) =
        Over.Hom.left q ≫ Limits.pullback.fst H.X.hom s :=
    rfl
  rw [hleftH, pointMap_apply, Over.comp_left, Functor.mapGrp_map_hom_hom]
  simp only [Category.assoc, Over.pullback_map_left, Limits.pullback.lift_fst]
  rw [pointMap_apply, Over.comp_left, hleftG]
  simp only [Category.assoc]

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
