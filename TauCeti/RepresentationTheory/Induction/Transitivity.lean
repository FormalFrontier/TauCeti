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

universe u v w x

variable {k : Type u} [CommRing k]
  {G : Type v} {H : Type w} {K : Type x} [Group G] [Group H] [Group K]

/-- Induction in stages: induction along a composite is naturally isomorphic to successive
inductions along the two group homomorphisms. -/
noncomputable def indFunctorCompIso (φ : G →* H) (ψ : H →* K) :
    _root_.Rep.indFunctor.{max u v w x} k φ ⋙
      _root_.Rep.indFunctor.{max u v w x} k ψ ≅
        _root_.Rep.indFunctor.{max u v w x} k (ψ.comp φ) :=
  Adjunction.leftAdjointCompIso (_root_.Rep.indResAdjunction.{max u v w x} k φ)
    (_root_.Rep.indResAdjunction.{max u v w x} k ψ)
    (_root_.Rep.indResAdjunction.{max u v w x} k (ψ.comp φ))
    (Iso.refl _)

end TauCeti
