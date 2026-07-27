module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.RepresentationTheory.Induced

/-!
# Transitivity of induction

This file records induction in stages for representations along composable group homomorphisms.
It obtains the natural isomorphism from the functoriality of restriction and Mathlib's induction--
restriction adjunction.  This is the categorical core used by the subgroup form of induction in
the induction and Mackey-theory roadmap.
-/

@[expose] public section

namespace TauCeti

open CategoryTheory

universe u v w

variable {k : Type u} [CommRing k]
  {G : Type v} {H : Type v} {K : Type v} [Group G] [Group H] [Group K]

/-- Restricting a representation along two composable group homomorphisms is naturally
isomorphic to restriction along their composite. -/
noncomputable def resFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.resFunctor (k := k) ψ ⋙ _root_.Rep.resFunctor φ ≅
      _root_.Rep.resFunctor (ψ.comp φ) :=
  Iso.refl _

/-- Induction in stages: induction along a composite is naturally isomorphic to successive
inductions along the two group homomorphisms. -/
noncomputable def indFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.indFunctor k φ ⋙ _root_.Rep.indFunctor k ψ ≅
      _root_.Rep.indFunctor k (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (_root_.Rep.indResAdjunction k φ)
    (_root_.Rep.indResAdjunction k ψ) (_root_.Rep.indResAdjunction k (ψ.comp φ))
    (resFunctorCompIso φ ψ)

end TauCeti
