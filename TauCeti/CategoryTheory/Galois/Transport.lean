/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Basic

/-!
# Transporting the Galois-category axioms along an equivalence

Being a Galois category is a property of a category, not of a presentation of it, so it should
transfer along an equivalence. Mathlib states the axioms (SGA1's (G1)–(G3), and (G4)–(G6) for a
fibre functor) in terms of limits, colimits and monomorphisms, all of which are preserved and
reflected by an equivalence, but it does not record the transfer. This file does.

The point of the transfer is that a category one wants to *recognise* as Galois is usually not
presented as one. The finite covering spaces of a nice base, for instance, are only known to
satisfy the axioms because they are equivalent to the finite `π₁`-sets, which Mathlib proves are
a `GaloisCategory` in `Mathlib/CategoryTheory/Galois/Examples.lean`; transporting is much cheaper
than building finite coproducts, pullbacks and quotients by finite groups of covering spaces by
hand.

Only axiom (G3) needs an argument. Given a monomorphism `i : A ⟶ B` in `C`, its image under the
equivalence is a monomorphism, so it is the inclusion of a direct summand `u : Z ⟶ e.functor.obj B`
in `D`. The complementary summand is transported back as `e.inverse.obj Z`, with structure map the
preimage under `e.functor` of `e.counit.app Z ≫ u`; taking the preimage rather than
`e.inverse.map u` composed with the unit is what makes the colimit check a single rewrite, since
`e.functor` then maps the transported cofan to the original one reindexed by an isomorphism.

## Main declarations

* `TauCeti.preGaloisCategory_of_equivalence`: (G1)–(G3) transfer along an equivalence.
* `TauCeti.fiberFunctor_comp_of_equivalence`: (G4)–(G6) transfer, so that a fibre functor on `D`
  composes with an equivalence `C ≌ D` to a fibre functor on `C`.
* `TauCeti.galoisCategory_of_equivalence`: a category equivalent to a Galois category is a
  Galois category.

## References

* [lenstraGSchemes]: H. W. Lenstra, *Galois theory for schemes*, Definition 3.1.
-/

public section

universe v₁ v₂ u₁ u₂ w

namespace TauCeti

open CategoryTheory Limits Functor PreGaloisCategory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A category equivalent to a pre-Galois category is a pre-Galois category.**

The finite limits and colimits required by (G1) and (G2) transport along the equivalence, and a
monomorphism is a direct summand in `C` exactly when its image is one in `D`, which is (G3). -/
theorem preGaloisCategory_of_equivalence (e : C ≌ D) [PreGaloisCategory D] :
    PreGaloisCategory C where
  hasTerminal := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasPullbacks := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasFiniteCoproducts := ⟨fun _ => Adjunction.hasColimitsOfShape_of_equivalence e.functor⟩
  hasQuotientsByFiniteGroups _ _ _ := Adjunction.hasColimitsOfShape_of_equivalence e.functor
  monoInducesIsoOnDirectSummand {A B} i _ := by
    obtain ⟨Z, u, ⟨hZ⟩⟩ :=
      PreGaloisCategory.monoInducesIsoOnDirectSummand (e.functor.map i)
    refine ⟨e.inverse.obj Z, e.functor.preimage (e.counitIso.hom.app Z ≫ u), ⟨?_⟩⟩
    refine isColimitOfReflects e.functor
      ((isColimitMapCoconeBinaryCofanEquiv e.functor i _).symm ?_)
    rw [e.functor.map_preimage]
    exact BinaryCofan.isColimitCompRightIso (BinaryCofan.mk (e.functor.map i) u)
      (e.counitIso.hom.app Z) hZ

/-- **A fibre functor stays a fibre functor after composing with an equivalence.**

An equivalence preserves all limits and colimits and reflects isomorphisms, so each of (G4)–(G6)
for `F` gives the same axiom for `e.functor ⋙ F`. -/
theorem fiberFunctor_comp_of_equivalence (e : C ≌ D) [PreGaloisCategory C] [PreGaloisCategory D]
    (F : D ⥤ FintypeCat.{w}) [FiberFunctor F] : FiberFunctor (e.functor ⋙ F) where
  preservesFiniteCoproducts := ⟨fun _ => inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance

/-- **A category equivalent to a Galois category is a Galois category.**

Unlike `preGaloisCategory_of_equivalence` and `fiberFunctor_comp_of_equivalence`, this fixes the
morphism universe of `D` to that of `C`. Mathlib's `GaloisCategory D` asks for a fibre functor
into `FintypeCat.{v₂}`, while `GaloisCategory C` asks for one into `FintypeCat.{v₁}`, and there
is no universe-lowering functor between the two to bridge the gap. -/
theorem galoisCategory_of_equivalence {D : Type u₂} [Category.{v₁} D] (e : C ≌ D)
    [GaloisCategory D] : GaloisCategory C where
  toPreGaloisCategory := preGaloisCategory_of_equivalence e
  hasFiberFunctor := by
    have := preGaloisCategory_of_equivalence e
    obtain ⟨F, hF⟩ := GaloisCategory.hasFiberFunctor D
    exact ⟨e.functor ⋙ F, fiberFunctor_comp_of_equivalence e F⟩

end TauCeti
