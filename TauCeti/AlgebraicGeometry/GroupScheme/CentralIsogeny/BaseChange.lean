/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic

/-!
# Base change of group-scheme isogenies

This file proves that central kernels of group-scheme morphisms remain central after arbitrary
base change, by identifying the point groups before and after base change through the pullback
adjunction. Consequently, isogenies and central isogenies over a field remain so after base change
along a morphism between spectra of fields. For a commutative source, the base-changed isogeny is
central without any centrality hypothesis. The group-scheme base change is the pullback functor on
the over category, lifted to group objects.

## Main declarations

* `TauCeti.GroupScheme.baseChangePointMulEquiv`: the multiplicative point-group identification
  furnished by the pullback adjunction.
* `TauCeti.GroupScheme.HasCentralKernel.baseChange`: central kernels remain central after arbitrary
  base change.
* `TauCeti.GroupScheme.IsIsogeny.baseChange`: isogenies remain isogenies after base change.
* `TauCeti.GroupScheme.IsCentralIsogeny.baseChange`: central isogenies remain central after base
  change.
* `TauCeti.GroupScheme.IsIsogeny.baseChange_isCentral_of_isCommMonObj`: the base change of an
  isogeny from a commutative source is a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.
* Mathlib's `Over.mapPullbackAdj` and the cartesian-monoidal structure on `Over.pullback` provide
  the point identification and its compatibility with multiplication.

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

end Field

section BaseChange

variable {X Y : Scheme.{u}} {G H : Grp (Over X)}

/-- The underlying map of the inverse pullback-adjunction equivalence is postcomposition with the
first pullback projection. -/
private theorem mapPullbackAdj_homEquiv_symm_left
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    Over.Hom.left (((Over.mapPullbackAdj s).homEquiv T G.X).symm p) =
      Over.Hom.left p ≫ Limits.pullback.fst G.X.hom s := by
  -- `mapPullbackAdj` has no projection lemma for its hom-equivalence; this is exactly the
  -- computation rule in its public definition.
  rfl

/-- After the pullback functor's lax-monoidal map and the pulled-back multiplication, the first
projection agrees with multiplication after projecting the pair. -/
private theorem pullback_laxMonoidal_map_mul_fst
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (pLeft qLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s)
    (hpq : pLeft ≫ Limits.pullback.snd G.X.hom s =
      qLeft ≫ Limits.pullback.snd G.X.hom s) :
    (((Limits.pullback.lift pLeft qLeft hpq ≫
          Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
        Over.Hom.left ((Over.pullback s).map μ[G.X])) ≫
      (Limits.pullback.fst G.X.hom s :
        ((Over.pullback s).mapGrp.obj G).X.left ⟶ G.X.left)) =
    (((Limits.pullback.lift pLeft qLeft hpq ≫
          Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
        Limits.pullback.fst (MonoidalCategoryStruct.tensorObj G.X G.X).hom s) ≫
      Over.Hom.left μ[G.X]) := by
  have hmap :
      Over.Hom.left ((Over.pullback s).map μ[G.X]) ≫
          (Limits.pullback.fst G.X.hom s :
            ((Over.pullback s).mapGrp.obj G).X.left ⟶ G.X.left) =
        Limits.pullback.fst (MonoidalCategoryStruct.tensorObj G.X G.X).hom s ≫
          Over.Hom.left μ[G.X] := by
    simp only [Over.pullback_map_left, Limits.pullback.lift_fst]
  simp only [Category.assoc, hmap]

/-- Pairing two points, applying the pullback functor's lax-monoidal map, and then projecting to
the original tensor product pairs the two projected points. -/
private theorem pullback_laxMonoidal_pair_fst
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (pLeft qLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s)
    (hpq : pLeft ≫ Limits.pullback.snd G.X.hom s =
      qLeft ≫ Limits.pullback.snd G.X.hom s) :
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
      Over.μ_pullback_left_fst_fst G.X G.X]
    simp only [Over.pullback_obj_hom, Limits.pullback.lift_fst_assoc,
      Limits.pullback.lift_fst]
  · rw [Category.assoc, Category.assoc,
      Over.μ_pullback_left_fst_snd G.X G.X]
    simp only [Over.pullback_obj_hom, Limits.pullback.lift_snd_assoc,
      Limits.pullback.lift_snd]

/-- The adjunction between postcomposition and pullback identifies points of a base-changed group
scheme with points of the original group scheme over the same test scheme viewed over the old
base. This identification is multiplicative. -/
noncomputable def baseChangePointMulEquiv
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y) :
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
    ext
    rw [mapPullbackAdj_homEquiv_symm_left]
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left,
      mapPullbackAdj_homEquiv_symm_left]
    rw [Functor.mapGrp_obj_X] at p q
    erw [congrArg Over.Hom.left (Functor.obj.μ_def (F := Over.pullback s) G.X), Over.comp_left]
    exact (pullback_laxMonoidal_map_mul_fst s G T pLeft qLeft hpq).trans
      (congrArg (fun z ↦ z ≫ Over.Hom.left μ[G.X])
        (pullback_laxMonoidal_pair_fst s G T pLeft qLeft hpq))

/-- The point-group equivalence is the underlying pullback-adjunction equivalence. -/
@[simp]
theorem baseChangePointMulEquiv_apply
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s G T p =
      ((Over.mapPullbackAdj s).homEquiv T G.X).symm p := (rfl)

/-- The inverse point-group equivalence is the forward pullback-adjunction equivalence. -/
@[simp]
theorem baseChangePointMulEquiv_symm_apply
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : (Over.map s).obj T ⟶ G.X) :
    (baseChangePointMulEquiv s G T).symm p =
      (Over.mapPullbackAdj s).homEquiv T G.X p := (rfl)

/-- The point-group identification intertwines a base-changed morphism with the original
morphism. -/
theorem baseChangePointMulEquiv_pointMap
    (s : Y ⟶ X) (f : G ⟶ H) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s H T
        (pointMap ((Over.pullback s).mapGrp.map f) T p) =
      pointMap f ((Over.map s).obj T) (baseChangePointMulEquiv s G T p) := by
  simp only [baseChangePointMulEquiv_apply, pointMap_apply,
    Functor.mapGrp_map_hom_hom]
  exact ((Over.mapPullbackAdj s).homEquiv_naturality_right_symm p f.hom.hom)

/-- Arbitrary base change preserves central kernels of group-scheme morphisms. -/
theorem HasCentralKernel.baseChange
    (s : Y ⟶ X) {f : G ⟶ H} (hf : HasCentralKernel f) :
    HasCentralKernel ((Over.pullback s).mapGrp.map f) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center]
  intro T p hp
  rw [Subgroup.mem_center_iff]
  intro q
  let eG := baseChangePointMulEquiv s G T
  have hp₀ : pointMap ((Over.pullback s).mapGrp.map f) T p = 1 :=
    (MonoidHom.mem_ker).mp hp
  have hp' : pointMap f ((Over.map s).obj T) (eG p) = 1 := by
    rw [← baseChangePointMulEquiv_pointMap, hp₀, map_one]
  have hf' := (hasCentralKernel_iff_pointMap_ker_le_center f).mp hf
  have hc := Subgroup.mem_center_iff.mp
    (hf' ((Over.map s).obj T) ((MonoidHom.mem_ker).mpr hp')) (eG q)
  apply eG.injective
  simpa only [map_mul] using hc

end BaseChange

section Field

variable {k L : Type u} [Field k] [Field L]
variable {G H : Grp (Over (Spec (CommRingCat.of k)))}

/-- Base change along a morphism between spectra of fields preserves central isogenies. -/
theorem IsCentralIsogeny.baseChange
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) {f : G ⟶ H}
    (hf : IsCentralIsogeny f) :
    IsCentralIsogeny ((Over.pullback s).mapGrp.map f) := by
  rw [isCentralIsogeny_iff]
  have hi := hf.isIsogeny.baseChange s
  exact ⟨hi.isFinite, hi.flat, hi.surjective, hf.hasCentralKernel.baseChange s⟩

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
