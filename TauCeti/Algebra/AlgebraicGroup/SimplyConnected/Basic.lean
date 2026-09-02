/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Isomorphism

/-!
# Simply connected semisimple affine groups in Hopf coordinates

A semisimple affine group over a field is **simply connected** when every central isogeny onto
it is an isomorphism. In coordinate Hopf algebras the arrows reverse: a central isogeny onto the
group represented by `H` is a finite faithfully flat morphism `H ⟶ K`, and simple connectivity
says that every such morphism to a semisimple coordinate algebra `K` is an isomorphism.

The source and target of the isogenies are required to be semisimple. Allowing arbitrary affine
group schemes would make the definition test central isogenies from nonsmooth finite group
schemes, which is not the standard notion for semisimple algebraic groups.

This coordinate-Hopf interface is adapted from the scheme-side formalization in
`TauCeti.AlgebraicGeometry.AffineGroupScheme.SimplyConnected`.

Because a faithfully flat coordinate morphism is injective, the only missing half of bijectivity
is surjectivity. Thus `simplyConnectedSemisimpleCommHopfAlgProperty_iff_forall_surjective` gives
the characteristic coordinate criterion: a semisimple group is simply connected exactly when
every central-isogeny coordinate map out of it is surjective.

## Main declarations

* `TauCeti.simplyConnectedSemisimpleCommHopfAlgProperty`: simple connectivity for semisimple
  finite-type commutative Hopf algebras.
* `TauCeti.SimplyConnectedSemisimpleCommHopfAlgCat`: the corresponding full subcategory.
* `TauCeti.simplyConnectedSemisimpleCommHopfAlgProperty_iff_forall_surjective`: the coordinate
  surjectivity criterion.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.4.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.

This supplies the coordinate-Hopf form of the simply-connected-form target in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap. Construction of simply
connected covers and their relation to root data remain downstream.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} [Field k]

/-- The object property selecting simply connected semisimple affine groups in Hopf coordinates.

For a semisimple coordinate Hopf algebra `H`, arrows reverse under `Spec`, so the central
isogenies onto the represented group are precisely the coordinate morphisms `H ⟶ K` tested
here. Requiring `K` to be semisimple is part of the standard definition. -/
def simplyConnectedSemisimpleCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (SemisimpleCommHopfAlgCat.{u} k) :=
  fun H ↦ ∀ (K : SemisimpleCommHopfAlgCat.{u} k) (f : H ⟶ K),
    CommHopfAlgCat.IsCentralIsogeny f.hom.hom → IsIso f

/-- Membership in the simply connected property means that every coordinate central isogeny
out of the Hopf algebra and into another semisimple coordinate Hopf algebra is an isomorphism. -/
@[simp]
theorem simplyConnectedSemisimpleCommHopfAlgProperty_iff
    (H : SemisimpleCommHopfAlgCat.{u} k) :
    simplyConnectedSemisimpleCommHopfAlgProperty k H ↔
      ∀ (K : SemisimpleCommHopfAlgCat.{u} k) (f : H ⟶ K),
        CommHopfAlgCat.IsCentralIsogeny f.hom.hom → IsIso f :=
  Iff.rfl

namespace simplyConnectedSemisimpleCommHopfAlgProperty

variable {H : SemisimpleCommHopfAlgCat.{u} k}

/-- Every coordinate central isogeny out of a simply connected semisimple group is an
isomorphism. -/
theorem isIso (hH : simplyConnectedSemisimpleCommHopfAlgProperty k H)
    {K : SemisimpleCommHopfAlgCat.{u} k} (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsCentralIsogeny f.hom.hom) : IsIso f :=
  hH K f hf

/-- Establish simple connectivity by proving that every coordinate central isogeny out of the
group is an isomorphism. -/
theorem mk
    (hH : ∀ (K : SemisimpleCommHopfAlgCat.{u} k) (f : H ⟶ K),
      CommHopfAlgCat.IsCentralIsogeny f.hom.hom → IsIso f) :
    simplyConnectedSemisimpleCommHopfAlgProperty k H :=
  hH

/-- The coordinate map of every central isogeny out of a simply connected semisimple group is
surjective. -/
theorem surjective (hH : simplyConnectedSemisimpleCommHopfAlgProperty k H)
    {K : SemisimpleCommHopfAlgCat.{u} k} (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsCentralIsogeny f.hom.hom) :
    Function.Surjective f.hom.hom := by
  let _ : IsIso f := hH.isIso f hf
  let _ : IsIso f.hom.hom := inferInstance
  exact hf.isIsogeny.isIso_iff_surjective.mp inferInstance

end simplyConnectedSemisimpleCommHopfAlgProperty

/-- A semisimple affine group is simply connected exactly when every coordinate central
isogeny out of its Hopf algebra is surjective.

Injectivity is automatic from faithful flatness, so surjectivity makes the coordinate morphism
bijective and hence an isomorphism. -/
theorem simplyConnectedSemisimpleCommHopfAlgProperty_iff_forall_surjective
    (H : SemisimpleCommHopfAlgCat.{u} k) :
    simplyConnectedSemisimpleCommHopfAlgProperty k H ↔
      ∀ (K : SemisimpleCommHopfAlgCat.{u} k) (f : H ⟶ K),
        CommHopfAlgCat.IsCentralIsogeny f.hom.hom → Function.Surjective f.hom.hom := by
  constructor
  · exact fun hH K f hf ↦ hH.surjective f hf
  · intro hH K f hf
    have hIso : IsIso f.hom.hom :=
      hf.isIsogeny.isIso_iff_surjective.mpr (hH K f hf)
    exact (ObjectProperty.isIso_hom_iff f).mp <|
      (ObjectProperty.isIso_hom_iff f.hom).mp hIso

/-- Simple connectivity in Hopf coordinates is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (simplyConnectedSemisimpleCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso {H K} e hH L f hf := by
    have hcomp : CommHopfAlgCat.IsCentralIsogeny (e.hom.hom.hom ≫ f.hom.hom) := by
      rw [CommHopfAlgCat.isCentralIsogeny_iff_isCentralIsogeny_hopfSpec_map] at hf ⊢
      simpa only [op_comp, Functor.map_comp] using
        ((GroupScheme.centralIsogenies k).cancel_right_of_respectsIso
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map f.hom.hom.op)
          ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).map e.hom.hom.hom.op)).mpr hf
    let _ : IsIso (e.hom ≫ f) := hH L (e.hom ≫ f) hcomp
    exact IsIso.of_isIso_comp_left e.hom f

/-- The category of simply connected semisimple finite-type commutative Hopf algebras over a
field. -/
abbrev SimplyConnectedSemisimpleCommHopfAlgCat (k : Type u) [Field k] :=
  (simplyConnectedSemisimpleCommHopfAlgProperty k).FullSubcategory

end

end TauCeti
