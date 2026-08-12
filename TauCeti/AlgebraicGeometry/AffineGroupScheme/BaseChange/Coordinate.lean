/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Basic

/-!
# Coordinate compatibility of affine-group-scheme base change

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `S` be a
commutative `R`-algebra. There are two constructions of the base-changed affine group scheme:
pull back `Spec H` from `Spec R` to `Spec S`, or first extend scalars on coordinates to
`S ⊗[R] H` and then take its Hopf spectrum. This file identifies the two constructions.

The underlying scheme isomorphism is Mathlib's `AlgebraicGeometry.pullbackSpecIso'`, preceded
by pullback symmetry so that the new base ring is the left tensor factor. Mathlib also proves
that this isomorphism preserves the monoid-object structure. Here it is bundled as an
isomorphism of affine group schemes and composed with the established Hopf-spectrum
anti-equivalence.

## Main declarations

* `TauCeti.AffineGroupSchemeCat.hopfSpecBaseChangeIso`: pullback of a Hopf spectrum is the
  Hopf spectrum of the scalar-extended coordinate Hopf algebra.
* `TauCeti.AffineGroupSchemeCat.hopfSpecBaseChangeNatIso`: the comparison is natural in the
  coordinate Hopf algebra.

## References

This is the base-change compatibility in the Hopf-algebra/affine-group-scheme dictionary; see
J. S. Milne, *Algebraic Groups* (2017), Section 1.f.

## Roadmap

This synchronizes the coordinate and scheme models in the base-change part of Layer 0 of the
ReductiveGroups roadmap. In particular, it lets later scheme-side constructions, including the
Layer 4 dictionary for groups of multiplicative type, reuse coordinate scalar extension.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace TauCeti

universe u

namespace AffineGroupSchemeCat

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Pullback symmetry followed by the affine pullback comparison identifies the base-changed
spectrum with the spectrum of the scalar extension. -/
private noncomputable def pullbackSpecBaseChangeIso (H : CommHopfAlgCat.{u} R) :
    Limits.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R H)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      Spec (CommRingCat.of (S ⊗[R] H)) :=
  Limits.pullbackSymmetry
      (Spec.map (CommRingCat.ofHom (algebraMap R H)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≪≫
    pullbackSpecIso R S H

@[reassoc (attr := simp)]
private theorem pullbackSpecBaseChangeIso_inv_fst (H : CommHopfAlgCat.{u} R) :
    (pullbackSpecBaseChangeIso (R := R) (S := S) H).inv ≫
        Limits.pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := H)).toRingHom) := by
  simp [pullbackSpecBaseChangeIso]

@[reassoc (attr := simp)]
private theorem pullbackSpecBaseChangeIso_inv_snd (H : CommHopfAlgCat.{u} R) :
    (pullbackSpecBaseChangeIso (R := R) (S := S) H).inv ≫
        Limits.pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R H)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] H)) := by
  simp [pullbackSpecBaseChangeIso]

private theorem hopfSpec_map_left {T : Type u} [CommRing T]
    {H K : CommHopfAlgCat.{u} T} (f : H ⟶ K) :
    ((hopfSpec (CommRingCat.of T)).map f.op).hom.hom.left =
      Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) := by
  -- `hopfSpec.map` is built by lifting this `Spec.map`; no separate projection lemma is exposed.
  rfl

private theorem pullbackSpecIso'_natural {H K : CommHopfAlgCat.{u} R}
    (f : H ⟶ K) :
    (pullbackSpecBaseChangeIso (R := R) (S := S) K).inv ≫
        Limits.pullback.lift
          (Limits.pullback.fst
              (Spec.map (CommRingCat.ofHom (algebraMap R K)))
              (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
            Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))
          (Limits.pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
            (Spec.map (CommRingCat.ofHom (algebraMap R S))))
          (by
            have hf :
                Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap R H)) =
                  Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
              rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
              congr 1
              ext r
              exact f.hom.toAlgHom.commutes r
            rw [Category.assoc, hf]
            exact Limits.pullback.condition) ≫
      (pullbackSpecBaseChangeIso (R := R) (S := S) H).hom =
        Spec.map (CommRingCat.ofHom
          ((CommHopfAlgCat.baseChangeMap (K := S) f).hom).toAlgHom.toRingHom) := by
  rw [← Category.assoc]
  apply (pullbackSpecBaseChangeIso (R := R) (S := S) H).eq_comp_inv.mp
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst]
    rw [← Category.assoc, pullbackSpecBaseChangeIso_inv_fst,
      pullbackSpecBaseChangeIso_inv_fst]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
  · simp only [Category.assoc, Limits.pullback.lift_snd]
    rw [pullbackSpecBaseChangeIso_inv_snd]
    rw [pullbackSpecBaseChangeIso_inv_snd]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    simp

private theorem hopfSpecPullbackIso_natural {H K : CommHopfAlgCat.{u} R}
    (f : H ⟶ K) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          ((hopfSpec (CommRingCat.of R)).map f.op) ≫
        (hopfSpecBaseChangeGrpIso (R := R) (S := S) H).hom =
        (hopfSpecBaseChangeGrpIso (R := R) (S := S) K).hom ≫
        (hopfSpec (CommRingCat.of S)).map
          (CommHopfAlgCat.baseChangeMap (K := S) f).op := by
  rw [← cancel_epi (hopfSpecBaseChangeGrpIso (R := R) (S := S) K).inv]
  simp only [Iso.inv_hom_id_assoc]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, Over.comp_left, Over.comp_left,
    hopfSpecBaseChangeGrpIso_inv_hom_hom_left, hopfSpecBaseChangeGrpIso_hom_hom_hom_left]
  rw [Functor.mapGrp_map_hom_hom]
  exact pullbackSpecIso'_natural (R := R) (S := S) f

/-- The group-object comparison between pullback of Hopf spectra and Hopf spectra of scalar
extensions, natural in the coordinate Hopf algebra. -/
private noncomputable def hopfSpecPullbackNatIso :
    hopfSpec (CommRingCat.of R) ⋙
          (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp ≅
      (CommHopfAlgCat.baseChangeFunctor (K := S)).op ⋙
        hopfSpec (CommRingCat.of S) :=
  NatIso.ofComponents
    (fun H ↦ hopfSpecBaseChangeGrpIso (R := R) (S := S) H.unop)
    (fun f ↦ hopfSpecPullbackIso_natural (R := R) (S := S) f.unop)

/-- The base-change comparison after including affine group schemes into all group objects. -/
private noncomputable def hopfSpecBaseChangeιNatIso :
    ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor ⋙
          baseChangeFunctor (CommRingCat.ofHom (algebraMap R S))) ⋙
        (affineGroupSchemeProperty (CommRingCat.of S)).ι ≅
      ((CommHopfAlgCat.baseChangeFunctor (K := S)).op ⋙
          (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of S)).functor) ⋙
        (affineGroupSchemeProperty (CommRingCat.of S)).ι := by
  -- The equivalence functor followed by the subtype inclusion is definitionally its `hopfSpec`
  -- model; `functorCompιIso` below supplies the explicit comparison once the goal has that shape.
  change
    (((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor ⋙
          (affineGroupSchemeProperty (CommRingCat.of R)).ι) ⋙
        (Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp) ≅ _
  exact
    Functor.isoWhiskerRight
        (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of R)) _ ≪≫
      hopfSpecPullbackNatIso (R := R) (S := S) ≪≫
      Functor.isoWhiskerLeft (CommHopfAlgCat.baseChangeFunctor (K := S)).op
        (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of S)).symm ≪≫
      (Functor.associator _ _ _).symm

private theorem hopfSpecBaseChangeιNatIso_hom_app (H : (CommHopfAlgCat.{u} R)ᵒᵖ) :
    (hopfSpecBaseChangeιNatIso (R := R) (S := S)).hom.app H =
      (hopfSpecBaseChangeIso (R := R) (S := S) H.unop).hom.hom := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  -- No projection lemma exposes the component of this private composite natural isomorphism;
  -- unfold that composite definitionally so its constituent component lemmas can simplify it.
  change
    (((Functor.isoWhiskerRight
          (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
            (CommRingCat.of R))
          (Over.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp ≪≫
        hopfSpecPullbackNatIso (R := R) (S := S) ≪≫
        Functor.isoWhiskerLeft (CommHopfAlgCat.baseChangeFunctor (K := S)).op
          (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
            (CommRingCat.of S)).symm ≪≫
        (Functor.associator _ _ _).symm).hom.app H).hom.hom.left = _)
  rw [hopfSpecBaseChangeIso_hom_hom]
  simp [hopfSpecPullbackNatIso]

/-- Scheme-theoretic pullback of affine group schemes corresponds naturally, under the
Hopf-spectrum anti-equivalence, to scalar extension of their coordinate Hopf algebras. -/
noncomputable def hopfSpecBaseChangeNatIso :
    (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor ⋙
        baseChangeFunctor (CommRingCat.ofHom (algebraMap R S)) ≅
      (CommHopfAlgCat.baseChangeFunctor (K := S)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of S)).functor :=
  NatIso.ofComponents (fun H ↦ hopfSpecBaseChangeIso (R := R) (S := S) H.unop) (fun f ↦ by
    apply (affineGroupSchemeProperty (CommRingCat.of S)).ι.map_injective
    simpa only [Functor.comp_map, Functor.map_comp, ObjectProperty.ι_map,
      ObjectProperty.FullSubcategory.comp_hom,
      hopfSpecBaseChangeιNatIso_hom_app] using
      (hopfSpecBaseChangeιNatIso (R := R) (S := S)).hom.naturality f)

/-- The forward component of `hopfSpecBaseChangeNatIso` is
`hopfSpecBaseChangeIso`. -/
@[simp]
theorem hopfSpecBaseChangeNatIso_hom_app (H : (CommHopfAlgCat.{u} R)ᵒᵖ) :
    (hopfSpecBaseChangeNatIso (R := R) (S := S)).hom.app H =
      (hopfSpecBaseChangeIso (R := R) (S := S) H.unop).hom :=
  (rfl)

/-- The inverse component of `hopfSpecBaseChangeNatIso` is the inverse of
`hopfSpecBaseChangeIso`. -/
@[simp]
theorem hopfSpecBaseChangeNatIso_inv_app (H : (CommHopfAlgCat.{u} R)ᵒᵖ) :
    (hopfSpecBaseChangeNatIso (R := R) (S := S)).inv.app H =
      (hopfSpecBaseChangeIso (R := R) (S := S) H.unop).inv :=
  (rfl)

end AffineGroupSchemeCat

end TauCeti
