/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

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

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.4.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.

This is the simply-connected-form target in Layer 6, "Reductive and semisimple groups", of the
ReductiveGroups roadmap. Central isogenies and semisimple affine group schemes are already
available; construction and classification of simply connected covers remain downstream.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry

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

end TauCeti
