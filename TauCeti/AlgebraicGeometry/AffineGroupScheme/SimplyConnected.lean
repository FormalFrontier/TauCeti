/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SimplyConnected.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Semisimple.Reductive
public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Isomorphism

/-!
# Simply connected semisimple affine group schemes

A semisimple affine group scheme `G` over a field is **simply connected** when every central
isogeny `G' ⟶ G` from another semisimple affine group scheme is an isomorphism. Restricting the
source to semisimple affine group schemes is essential: the ambient category of all group schemes
also contains nonsmooth finite group schemes, whose structural morphisms to the trivial group are
central isogenies without being isomorphisms.

The definition is phrased in `SemisimpleAffineGroupSchemeCat`, so smoothness, geometric
connectedness, affineness, and finite type remain separate structural properties rather than
being repeated as hypotheses on every source. It is invariant under isomorphism and therefore
cuts out the full subcategory `SimplyConnectedSemisimpleAffineGroupSchemeCat`.

For a central isogeny, being an isomorphism is equivalent to its underlying scheme morphism being
monic. Indeed, an isogeny is finite, flat, and surjective; a flat, quasi-compact, surjective
monomorphism of schemes is an isomorphism. This gives the kernel-free characterization
`simplyConnectedSemisimpleAffineGroupSchemeProperty_iff_forall_mono`.

## Main declarations

* `TauCeti.simplyConnectedSemisimpleAffineGroupSchemeProperty`: simple connectivity for
  semisimple affine group schemes over a field.
* `TauCeti.SimplyConnectedSemisimpleAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.simplyConnectedSemisimpleAffineGroupSchemeProperty_iff_forall_mono`: a semisimple
  affine group scheme is simply connected exactly when every central isogeny onto it has monic
  underlying scheme morphism.
* `TauCeti.simplyConnectedSemisimpleAffineGroupSchemeProperty_inverseImage`: pulling the scheme
  property back along `Spec` recovers the coordinate-Hopf property.
* The restricted anti-equivalence between the coordinate and scheme models is
  `simplyConnectedSemisimpleCommHopfAlgCatOpEquivSimplyConnectedSemisimpleAffineGroupSchemeCat`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.4.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.

This is the simply-connected-form target in Layer 6, "Reductive and semisimple groups", of the
ReductiveGroups roadmap. Central isogenies and semisimple affine group schemes are already
available; construction and classification of simply connected covers remain downstream.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

variable {k : Type u} [Field k]

/-- The forgetful functor from semisimple affine group schemes to group schemes. -/
noncomputable abbrev semisimpleAffineGroupSchemeForget (k : Type u) [Field k] :
    SemisimpleAffineGroupSchemeCat k ⥤ Grp (Over (Spec (CommRingCat.of k))) :=
  semisimpleToReductiveAffineGroupSchemeFunctor k ⋙
    (reductiveAffineGroupSchemeProperty k).ι ⋙
    (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
      (affineGroupSchemeProperty (CommRingCat.of k)).ι

/-- The object property selecting simply connected semisimple affine group schemes over a field.

A semisimple affine group scheme `G` is simply connected when every central isogeny `H ⟶ G`
in the category of semisimple affine group schemes is an isomorphism. The source is required to
be semisimple; allowing arbitrary group schemes would incorrectly include nonsmooth finite
central covers among the maps tested by the definition. -/
def simplyConnectedSemisimpleAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (SemisimpleAffineGroupSchemeCat k) :=
  fun G ↦ ∀ (H : SemisimpleAffineGroupSchemeCat k) (f : H ⟶ G),
    GroupScheme.IsCentralIsogeny ((semisimpleAffineGroupSchemeForget k).map f) → IsIso f

/-- Membership in the simply connected semisimple affine-group-scheme property means that every
central isogeny from a semisimple affine group scheme is an isomorphism. -/
@[simp]
theorem simplyConnectedSemisimpleAffineGroupSchemeProperty_iff
    (G : SemisimpleAffineGroupSchemeCat k) :
    simplyConnectedSemisimpleAffineGroupSchemeProperty k G ↔
      ∀ (H : SemisimpleAffineGroupSchemeCat k) (f : H ⟶ G),
        GroupScheme.IsCentralIsogeny
          ((semisimpleAffineGroupSchemeForget k).map f) → IsIso f :=
  Iff.rfl

namespace simplyConnectedSemisimpleAffineGroupSchemeProperty

variable {G : SemisimpleAffineGroupSchemeCat k}

/-- Every central isogeny from a semisimple affine group scheme to a simply connected one is an
isomorphism. -/
theorem isIso (hG : simplyConnectedSemisimpleAffineGroupSchemeProperty k G)
    {H : SemisimpleAffineGroupSchemeCat k} (f : H ⟶ G)
    (hf : GroupScheme.IsCentralIsogeny ((semisimpleAffineGroupSchemeForget k).map f)) : IsIso f :=
  hG H f hf

/-- Establish simple connectivity by proving that every central isogeny onto the group is an
isomorphism. -/
theorem mk
    (hG : ∀ (H : SemisimpleAffineGroupSchemeCat k) (f : H ⟶ G),
      GroupScheme.IsCentralIsogeny ((semisimpleAffineGroupSchemeForget k).map f) → IsIso f) :
    simplyConnectedSemisimpleAffineGroupSchemeProperty k G :=
  hG

end simplyConnectedSemisimpleAffineGroupSchemeProperty

/-- Simple connectivity of semisimple affine group schemes is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (simplyConnectedSemisimpleAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms where
  of_iso {G K} e hG H f hf := by
    have hcomp : GroupScheme.IsCentralIsogeny
        ((semisimpleAffineGroupSchemeForget k).map (f ≫ e.inv)) := by
      rw [Functor.map_comp]
      exact ((GroupScheme.centralIsogenies k).cancel_right_of_respectsIso
        ((semisimpleAffineGroupSchemeForget k).map f)
        ((semisimpleAffineGroupSchemeForget k).map e.inv)).mpr hf
    let _ : IsIso (f ≫ e.inv) := hG H (f ≫ e.inv) hcomp
    exact IsIso.of_isIso_comp_right f e.inv

/-- The category of simply connected semisimple affine group schemes over a field. -/
abbrev SimplyConnectedSemisimpleAffineGroupSchemeCat (k : Type u) [Field k] :=
  (simplyConnectedSemisimpleAffineGroupSchemeProperty k).FullSubcategory

/-- A semisimple affine group scheme is simply connected exactly when the underlying scheme map
of every central isogeny onto it is a monomorphism. -/
theorem simplyConnectedSemisimpleAffineGroupSchemeProperty_iff_forall_mono
    (G : SemisimpleAffineGroupSchemeCat k) :
    simplyConnectedSemisimpleAffineGroupSchemeProperty k G ↔
      ∀ (H : SemisimpleAffineGroupSchemeCat k) (f : H ⟶ G),
        GroupScheme.IsCentralIsogeny
            ((semisimpleAffineGroupSchemeForget k).map f) →
          Mono
            ((semisimpleAffineGroupSchemeForget k).map f).hom.hom.left := by
  constructor
  · intro hG H f hf
    let _ : IsIso f := hG H f hf
    infer_instance
  · intro hG H f hf
    let _ : Mono ((semisimpleAffineGroupSchemeForget k).map f).hom.hom.left := hG H f hf
    let _ : IsIso ((semisimpleAffineGroupSchemeForget k).map f) := hf.isIsogeny.isIso_of_mono
    exact isIso_of_reflects_iso f (semisimpleAffineGroupSchemeForget k)

/-- Under the semisimple Hopf/group-scheme anti-equivalence, a morphism is a coordinate central
isogeny exactly when its image is a group-scheme central isogeny. -/
theorem
    semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat.isCentralIsogeny_map_iff
    {H K : (SemisimpleCommHopfAlgCat.{u} k)ᵒᵖ} (f : H ⟶ K) :
    GroupScheme.IsCentralIsogeny
        ((semisimpleAffineGroupSchemeForget k).map
          ((semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).functor.map f)) ↔
      CommHopfAlgCat.IsCentralIsogeny f.unop.hom.hom := by
  rw [CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map]
  let α :=
    semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat.functorCompιIso k
  exact (GroupScheme.centralIsogenies k).arrow_mk_iso_iff
    (Arrow.isoMk (α.app H) (α.app K) (α.hom.naturality f).symm)

/-- Pulling simple connectivity on semisimple affine group schemes back along `Spec` recovers
simple connectivity of semisimple commutative Hopf algebras. -/
theorem simplyConnectedSemisimpleAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (simplyConnectedSemisimpleAffineGroupSchemeProperty k).inverseImage
        (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).functor =
      (simplyConnectedSemisimpleCommHopfAlgProperty k).op := by
  ext H
  rw [ObjectProperty.prop_inverseImage_iff, ObjectProperty.op_iff]
  let E := semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k
  constructor
  · intro hG
    apply simplyConnectedSemisimpleCommHopfAlgProperty.mk
    intro K f hf
    let g : op K ⟶ H := f.op
    have hg : GroupScheme.IsCentralIsogeny
        ((semisimpleAffineGroupSchemeForget k).map (E.functor.map g)) :=
      (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat.isCentralIsogeny_map_iff
        g).2 hf
    let _ : IsIso (E.functor.map g) := hG (E.functor.obj (op K)) (E.functor.map g) hg
    let _ : IsIso g := isIso_of_reflects_iso g E.functor
    exact (isIso_op_iff f).1 (inferInstance : IsIso f.op)
  · intro hH
    apply simplyConnectedSemisimpleAffineGroupSchemeProperty.mk
    intro G f hf
    let e := E.counitIso.app G
    let g : E.functor.obj (E.inverse.obj G) ⟶ E.functor.obj H := e.hom ≫ f
    let g' : E.inverse.obj G ⟶ H := E.functor.preimage g
    have hmap : E.functor.map g' = g := by
      simp only [g', Functor.map_preimage]
    have hg : GroupScheme.IsCentralIsogeny
        ((semisimpleAffineGroupSchemeForget k).map g) := by
      rw [Functor.map_comp]
      exact ((GroupScheme.centralIsogenies k).cancel_left_of_respectsIso _ _).2 hf
    have hg' : CommHopfAlgCat.IsCentralIsogeny g'.unop.hom.hom := by
      apply
        (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat.isCentralIsogeny_map_iff
          g').1
      rw [hmap]
      exact hg
    let _ : IsIso g'.unop := hH.isIso g'.unop hg'
    let _ : IsIso g' := (isIso_unop_iff g').1 (inferInstance : IsIso g'.unop)
    let _ : IsIso g := hmap ▸ (inferInstance : IsIso (E.functor.map g'))
    exact IsIso.of_isIso_comp_left e.hom f

/-- `Spec` restricts to an anti-equivalence from simply connected semisimple finite-type
commutative Hopf algebras to simply connected semisimple affine group schemes. -/
noncomputable def
    simplyConnectedSemisimpleCommHopfAlgCatOpEquivSimplyConnectedSemisimpleAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (SimplyConnectedSemisimpleCommHopfAlgCat.{u} k)ᵒᵖ ≌
      SimplyConnectedSemisimpleAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence (simplyConnectedSemisimpleCommHopfAlgProperty k)).symm.trans <|
    (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).congrFullSubcategory
      (simplyConnectedSemisimpleAffineGroupSchemeProperty_inverseImage k)

namespace
  simplyConnectedSemisimpleCommHopfAlgCatOpEquivSimplyConnectedSemisimpleAffineGroupSchemeCat

/-- After forgetting simple connectivity, the restricted anti-equivalence is the existing
semisimple Hopf/group-scheme anti-equivalence. -/
noncomputable def functorCompιIso
    (k : Type u) [Field k] :
    (simplyConnectedSemisimpleCommHopfAlgCatOpEquivSimplyConnectedSemisimpleAffineGroupSchemeCat
          k).functor ⋙
        (simplyConnectedSemisimpleAffineGroupSchemeProperty k).ι ≅
      (forget₂ (SimplyConnectedSemisimpleCommHopfAlgCat.{u} k)
          (SemisimpleCommHopfAlgCat.{u} k)).op ⋙
        (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).functor := by
  let P := simplyConnectedSemisimpleCommHopfAlgProperty k
  let Q := simplyConnectedSemisimpleAffineGroupSchemeProperty k
  let e := semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k
  let h := simplyConnectedSemisimpleAffineGroupSchemeProperty_inverseImage k
  exact
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (ObjectProperty.opEquivalence P).symm.functor
        (Q.liftCompιIso (P.op.ι ⋙ e.functor) (fun X ↦
          (congrFun h X.obj).symm.mp X.property)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (P.op.liftCompιIso P.ι.op (fun X ↦ X.unop.property)) e.functor

end simplyConnectedSemisimpleCommHopfAlgCatOpEquivSimplyConnectedSemisimpleAffineGroupSchemeCat

end TauCeti
