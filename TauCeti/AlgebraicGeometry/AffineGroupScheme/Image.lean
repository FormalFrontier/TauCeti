/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Scheme-theoretic images of affine group morphisms

For a morphism `f : H ⟶ K` of commutative Hopf algebras over a field, the represented affine
group morphism runs from `Spec K` to `Spec H`. Its coordinate image is the quotient

```text
H ⟶ H / ker(f) ⟶ K.
```

This file identifies `Spec (H / ker(f))` with Mathlib's scheme-theoretic image of
`Spec K ⟶ Spec H`. The isomorphism carries both maps in the Hopf image factorization to the
canonical closed immersion and source factor of the scheme-theoretic image. Thus the existing
coordinate construction can be used as an actual closed subgroup scheme, rather than merely as
an analogous quotient.

## Main declarations

* `TauCeti.CommHopfAlgCat.specTargetImageIdeal_hopfSpec_map`: the scheme-theoretic image ideal is
  the kernel Hopf ideal's underlying ideal.
* `TauCeti.CommHopfAlgCat.specTargetImageIsoImage`: the scheme-theoretic image coordinate ring is
  the quotient-by-kernel Hopf image.
* `TauCeti.CommHopfAlgCat.hopfSpecImageSchemeIso`: the corresponding isomorphism of schemes.
* `TauCeti.CommHopfAlgCat.hopfSpecImageSchemeIso_hom_comp_specTargetImageRingHom` and
  `TauCeti.CommHopfAlgCat.hopfSpec_imageι_comp_hopfSpecImageSchemeIso_hom`: compatibility with
  the two image factorizations.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15--16.
* `Mathlib.AlgebraicGeometry.AffineScheme`: `specTargetImageIdeal`, `specTargetImage`, and their
  canonical factorization.

This is the scheme-side image compatibility required by Layer 3, "Subgroups, quotients,
components", of the ReductiveGroups roadmap. It is also the image infrastructure used when
constructing generated normal subgroups such as the unipotent radical and derived subgroup.
-/

public section

open CategoryTheory Opposite

namespace TauCeti

open AlgebraicGeometry

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{u} k}

/-- After identifying the source and target Hopf spectra with ordinary spectra, the underlying
scheme map of `hopfSpec.map f.op` is `Spec.map f`. -/
theorem hopfSpec_map_left_comp_eqToHom (f : H ⟶ K) :
    ((hopfSpec (CommRingCat.of k)).map f.op).hom.hom.left ≫
        eqToHom (hopfSpec_obj_X_left k H) =
      eqToHom (hopfSpec_obj_X_left k K) ≫
        Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) :=
  rfl

/-- The ideal defining the scheme-theoretic image of the spectrum map of a Hopf-algebra morphism
is the ordinary ring kernel of that morphism. -/
theorem specTargetImageIdeal_specMap (f : H ⟶ K) :
    specTargetImageIdeal (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) =
      (HopfIdeal.ker f.hom).toIdeal := by
  rw [HopfIdeal.ker_toIdeal]
  rw [specTargetImageIdeal]
  rw [Adjunction.homEquiv_symm_apply]
  -- The image ideal is phrased through the `Γ ⊣ Spec` adjunction. Normalize its recovered
  -- coordinate map to the explicit global-sections map before using naturality of `ΓSpecIso`.
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of H)).inv ≫
    (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)).appTop).hom) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (f.hom x) = 0 ↔ f.hom x = 0
  constructor
  · intro hx
    calc
      f.hom x = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (f.hom x)) :=
        (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) (f.hom x)).symm
      _ = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom 0 := congrArg _ hx
      _ = 0 := map_zero _
  · intro hx
    rw [hx, map_zero]

/-- The ideal defining the scheme-theoretic image of a morphism of Hopf spectra is the kernel
Hopf ideal's underlying ideal. -/
theorem specTargetImageIdeal_hopfSpec_map (f : H ⟶ K) :
    specTargetImageIdeal ((hopfSpec (CommRingCat.of k)).map f.op).hom.hom.left =
      (HopfIdeal.ker f.hom).toIdeal := by
  change specTargetImageIdeal (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) = _
  exact specTargetImageIdeal_specMap f

/-- The coordinate ring of the scheme-theoretic image is canonically isomorphic to the Hopf
image, the quotient by the kernel Hopf ideal. -/
noncomputable def specTargetImageIsoImage (f : H ⟶ K) :
    specTargetImage (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ≅
      CommRingCat.of (image f) :=
  (Ideal.quotientEquivAlgOfEq ℤ (specTargetImageIdeal_specMap f)).toRingEquiv
    |>.toCommRingCatIso

/-- The coordinate-ring isomorphism sends the class of an element to the same class in the Hopf
image quotient. -/
@[simp]
theorem specTargetImageIsoImage_hom_mk (f : H ⟶ K) (x : H) :
    (specTargetImageIsoImage f).hom
        (Ideal.Quotient.mk (specTargetImageIdeal
          (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) x) =
      Ideal.Quotient.mk (HopfIdeal.ker f.hom).toIdeal x := by
  exact Ideal.quotientEquivAlgOfEq_mk ℤ (specTargetImageIdeal_specMap f) x

/-- The inverse coordinate-ring isomorphism also sends the class of an element to the same
class, now regarded in the scheme-theoretic image quotient. -/
@[simp]
theorem specTargetImageIsoImage_inv_mk (f : H ⟶ K) (x : H) :
    (specTargetImageIsoImage f).inv
        (Ideal.Quotient.mk (HopfIdeal.ker f.hom).toIdeal x) =
      Ideal.Quotient.mk (specTargetImageIdeal
        (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) x := by
  rw [specTargetImageIsoImage]
  change (Ideal.quotientEquivAlgOfEq ℤ
      (specTargetImageIdeal_specMap f)).symm
        (Ideal.Quotient.mk (HopfIdeal.ker f.hom).toIdeal x) = _
  rw [Ideal.quotientEquivAlgOfEq_symm,
    Ideal.quotientEquivAlgOfEq_mk]

/-- The Hopf spectrum of the quotient-by-kernel image is canonically the scheme-theoretic image
of the represented affine-group morphism. -/
noncomputable def hopfSpecImageSchemeIso (f : H ⟶ K) :
    ((hopfSpec (CommRingCat.of k)).obj (op (image f))).X.left ≅
      Spec (specTargetImage
        (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) :=
  eqToIso (hopfSpec_obj_X_left k (image f)) ≪≫
    Scheme.Spec.mapIso (specTargetImageIsoImage f).op

/-- Under the image isomorphism, the Hopf-spectrum map induced by the quotient morphism is the
closed immersion of the scheme-theoretic image into the target. -/
theorem hopfSpecImageSchemeIso_hom_comp_specTargetImageRingHom (f : H ⟶ K) :
    (hopfSpecImageSchemeIso f).hom ≫
        Spec.map (specTargetImageRingHom
          (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) =
      ((hopfSpec (CommRingCat.of k)).map (mkImage f).op).hom.hom.left ≫
        eqToHom (hopfSpec_obj_X_left k H) := by
  rw [hopfSpecImageSchemeIso]
  -- `hopfSpec` and ordinary `Spec` have propositionally identified underlying schemes. Move once
  -- across that boundary so the remainder is a calculation with explicit spectrum maps.
  change (eqToHom (hopfSpec_obj_X_left k (image f)) ≫
      (Scheme.Spec.mapIso (specTargetImageIsoImage f).op).hom) ≫
        Spec.map (specTargetImageRingHom
          (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) =
      eqToHom (hopfSpec_obj_X_left k (image f)) ≫
        Spec.map (CommRingCat.ofHom (mkImage f).hom.toAlgHom.toRingHom)
  have hcoord : specTargetImageRingHom
        (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ≫
      (specTargetImageIsoImage f).hom =
        CommRingCat.ofHom (mkImage f).hom.toAlgHom.toRingHom := by
    ext x
    rw [CommRingCat.comp_apply]
    exact (specTargetImageIsoImage_hom_mk f x).trans (mkImage_apply f x).symm
  have h : (Scheme.Spec.mapIso (specTargetImageIsoImage f).op).hom ≫
        Spec.map (specTargetImageRingHom
          (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) =
      Spec.map (CommRingCat.ofHom (mkImage f).hom.toAlgHom.toRingHom) := by
    calc
      (Scheme.Spec.mapIso (specTargetImageIsoImage f).op).hom ≫
          Spec.map (specTargetImageRingHom
            (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) =
        Spec.map ((specTargetImageIsoImage f).hom) ≫
          Spec.map (specTargetImageRingHom
            (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) := rfl
      _ = Spec.map (specTargetImageRingHom
            (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ≫
          (specTargetImageIsoImage f).hom) := (Spec.map_comp _ _).symm
      _ = Spec.map (CommRingCat.ofHom (mkImage f).hom.toAlgHom.toRingHom) :=
        congrArg Spec.map hcoord
  simpa only [Category.assoc] using
    congrArg (fun g ↦ eqToHom (hopfSpec_obj_X_left k (image f)) ≫ g) h

/-- Under the image isomorphism, the injective Hopf-algebra factor represents Mathlib's canonical
factor from the source to its scheme-theoretic image. -/
theorem hopfSpec_imageι_comp_hopfSpecImageSchemeIso_hom (f : H ⟶ K) :
    ((hopfSpec (CommRingCat.of k)).map (imageι f).op).hom.hom.left ≫
        (hopfSpecImageSchemeIso f).hom =
      eqToHom (hopfSpec_obj_X_left k K) ≫
        specTargetImageFactorization
          (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) := by
  let j := Spec.map (specTargetImageRingHom
    (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)))
  let _ : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _
    (specTargetImageRingHom_surjective
      (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)))
  have hgroup :
      (hopfSpec (CommRingCat.of k)).map (imageι f).op ≫
          (hopfSpec (CommRingCat.of k)).map (mkImage f).op =
        (hopfSpec (CommRingCat.of k)).map f.op := by
    rw [← Functor.map_comp]
    rw [← op_comp, mkImage_comp_imageι]
  have hscheme := congrArg
    (fun g ↦ g.hom.hom.left) hgroup
  have hscheme' :
      ((hopfSpec (CommRingCat.of k)).map (imageι f).op).hom.hom.left ≫
          ((hopfSpec (CommRingCat.of k)).map (mkImage f).op).hom.hom.left =
        ((hopfSpec (CommRingCat.of k)).map f.op).hom.hom.left := by
    simpa only [Grp.comp', Mon.comp_hom', Over.comp_left] using hscheme
  rw [← cancel_mono j]
  rw [Category.assoc, hopfSpecImageSchemeIso_hom_comp_specTargetImageRingHom]
  calc
    ((hopfSpec (CommRingCat.of k)).map (imageι f).op).hom.hom.left ≫
          (((hopfSpec (CommRingCat.of k)).map (mkImage f).op).hom.hom.left ≫
            eqToHom (hopfSpec_obj_X_left k H)) =
        (((hopfSpec (CommRingCat.of k)).map (imageι f).op).hom.hom.left ≫
          ((hopfSpec (CommRingCat.of k)).map (mkImage f).op).hom.hom.left) ≫
            eqToHom (hopfSpec_obj_X_left k H) := Category.assoc _ _ _ |>.symm
    _ = ((hopfSpec (CommRingCat.of k)).map f.op).hom.hom.left ≫
          eqToHom (hopfSpec_obj_X_left k H) := congrArg (· ≫
            eqToHom (hopfSpec_obj_X_left k H)) hscheme'
    _ = eqToHom (hopfSpec_obj_X_left k K) ≫
          Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) :=
      hopfSpec_map_left_comp_eqToHom f
    _ = eqToHom (hopfSpec_obj_X_left k K) ≫
          (specTargetImageFactorization
            (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ≫ j) := by
      rw [specTargetImageFactorization_comp]
    _ = (eqToHom (hopfSpec_obj_X_left k K) ≫
          specTargetImageFactorization
            (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) ≫ j :=
      Category.assoc _ _ _ |>.symm

end CommHopfAlgCat

end TauCeti
