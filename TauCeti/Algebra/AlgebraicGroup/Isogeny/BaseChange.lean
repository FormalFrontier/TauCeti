/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate
import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.BaseChange
import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Isomorphism

/-!
# Base change of isogenies in Hopf coordinates

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a commutative ring `k`.
Scalar extension along `k → L` gives a coordinate morphism
`L ⊗[k] H ⟶ L ⊗[k] K`. This file proves that isogenies and central isogenies remain so after
this scalar extension.

The proof keeps the coordinate and scheme models synchronized. Hopf spectrum turns `f`
contravariantly into a morphism of affine group schemes; scheme-theoretic pullback preserves
(central) isogenies, and the natural Hopf-spectrum base-change comparison identifies that
pullback with the spectrum of the scalar-extended coordinate morphism.

## Main declarations

* `TauCeti.CommHopfAlgCat.IsIsogeny.baseChange`: scalar extension preserves isogenies.
* `TauCeti.CommHopfAlgCat.IsCentralIsogeny.baseChange`: scalar extension preserves central
  isogenies.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 4 and 16.
* J. S. Milne, *Algebraic Groups* (2017), Sections 1.f and 18.a.
* The coordinate proof structure, including its use of `MorphismProperty.overPullbackMap`, is
  adapted from `TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.BaseChange`.

This supplies scalar-extension stability for the central-isogeny interface in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap. It is used when comparing
simply connected and adjoint forms after passage to an algebraic closure.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.CommHopfAlgCat

universe u

variable {k L : Type u} [CommRing k] [CommRing L] [Algebra k L]
variable {H K : _root_.CommHopfAlgCat.{u} k}

/-- The conjunction of scheme-morphism properties underlying a coordinate isogeny. -/
private def isogenyProperty : MorphismProperty (Grp (Over (Spec (CommRingCat.of L)))) :=
  ((@IsFinite ⊓ (@Flat ⊓ @Surjective)) : MorphismProperty Scheme).inverseImage
    (Grp.forget _ ⋙ Over.forget _)

private instance : isogenyProperty (L := L).RespectsIso := by
  unfold isogenyProperty
  let _ : MorphismProperty.RespectsIso
      (@Flat ⊓ @Surjective : MorphismProperty Scheme) :=
    MorphismProperty.RespectsIso.inf @Flat @Surjective
  let _ : MorphismProperty.RespectsIso
      (@IsFinite ⊓ (@Flat ⊓ @Surjective) : MorphismProperty Scheme) :=
    MorphismProperty.RespectsIso.inf @IsFinite (@Flat ⊓ @Surjective)
  infer_instance

private theorem isogenyProperty_iff_schemeMap
    {G K : Grp (Over (Spec (CommRingCat.of L)))} (f : G ⟶ K) :
    isogenyProperty (L := L) f ↔
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left :=
  Iff.rfl

private theorem isogenyProperty_iff (f : H ⟶ K) :
    isogenyProperty (L := k) ((hopfSpec (CommRingCat.of k)).map f.op) ↔ IsIsogeny f :=
  (isIsogeny_iff_isFinite_and_flat_and_surjective_hopfSpec_map f).symm

private theorem isogenyProperty_pullback
    (f : H ⟶ K) (h : isogenyProperty (L := k) ((hopfSpec (CommRingCat.of k)).map f.op)) :
    isogenyProperty (L := L)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp.map
        ((hopfSpec (CommRingCat.of k)).map f.op)) := by
  rw [isogenyProperty_iff_schemeMap, Functor.mapGrp_map_hom_hom]
  exact ⟨MorphismProperty.overPullbackMap _ _ h.1,
    MorphismProperty.overPullbackMap _ _ h.2.1,
    MorphismProperty.overPullbackMap _ _ h.2.2⟩

private theorem groupSchemeProperty_hopfSpec_baseChange
    (P : MorphismProperty (Grp (Over (Spec (CommRingCat.of L))))) [P.RespectsIso]
    (f : H ⟶ K)
    (h : P
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp.map
        ((hopfSpec (CommRingCat.of k)).map f.op))) :
    P
      ((hopfSpec (CommRingCat.of L)).map (baseChangeMap (K := L) f).op) := by
  have hnat := AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso_natural
    (R := k) (S := L) f
  have hcomp := MorphismProperty.RespectsIso.postcomp P
    (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (R := k) (S := L) H).hom _ h
  rw [hnat] at hcomp
  have hresult := MorphismProperty.RespectsIso.precomp P
    (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (R := k) (S := L) K).inv _ hcomp
  simpa using hresult

/-- Scalar extension of a coordinate morphism preserves isogenies of affine group schemes. -/
theorem IsIsogeny.baseChange {f : H ⟶ K} (hf : IsIsogeny f) :
    IsIsogeny (baseChangeMap (K := L) f) := by
  rw [← isogenyProperty_iff]
  exact groupSchemeProperty_hopfSpec_baseChange isogenyProperty f <|
    isogenyProperty_pullback f (isogenyProperty_iff f |>.2 hf)

/-- Scalar extension of a coordinate morphism preserves central isogenies of affine group
schemes. -/
theorem IsCentralIsogeny.baseChange {f : H ⟶ K} (hf : IsCentralIsogeny f) :
    IsCentralIsogeny (baseChangeMap (K := L) f) := by
  apply (isCentralIsogeny_iff _).2
  have hiso := hf.isIsogeny.baseChange (L := L)
  refine ⟨hiso.finite, hiso.faithfullyFlat, ?_⟩
  rw [← GroupScheme.hasCentralKernel_hopfSpec_map_iff]
  apply groupSchemeProperty_hopfSpec_baseChange
    (GroupScheme.hasCentralKernel (Spec (CommRingCat.of L))) f
  exact GroupScheme.HasCentralKernel.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    ((GroupScheme.hasCentralKernel_hopfSpec_map_iff f).2
      hf.isCentral_kernelHopfIdeal)

end TauCeti.CommHopfAlgCat
