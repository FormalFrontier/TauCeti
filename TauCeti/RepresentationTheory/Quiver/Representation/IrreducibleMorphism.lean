/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.CategoryTheory.IrreducibleMorphism
public import TauCeti.RepresentationTheory.Quiver.Representation.Basic
-- Non-public: these supply the abelian structure of `ModuleCat k` and of a functor category into
-- it, together with the pointwise criteria for monomorphisms and epimorphisms. All of that is
-- used inside the proofs below; the statements mention only injectivity and surjectivity of the
-- component maps, so an importer of this file does not pay for the abelian machinery.
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Irreducible morphisms of quiver representations

`TauCeti/CategoryTheory/IrreducibleMorphism.lean` defines an irreducible morphism in an arbitrary
category — one that is neither a split mono nor a split epi and factors only trivially. This file
reads that notion off vertex by vertex for representations of a quiver, where a morphism is a
natural transformation between functors into `ModuleCat k` and every categorical condition is
pointwise.

The category `TauCeti.QuiverRep k Q` of representations is abelian, being a functor category into
the abelian category of `k`-modules, so the general dichotomy applies: an irreducible morphism of
quiver representations is a monomorphism or an epimorphism, hence **injective at every vertex or
surjective at every vertex**. That is the concrete form in which the arrows of the
Auslander-Reiten quiver of a quiver algebra are recognized.

## Main results

* `TauCeti.QuiverRep.injective_or_surjective_of_isIrreducibleMorphism`: an irreducible morphism of
  quiver representations is injective at every vertex, or surjective at every vertex.
* `TauCeti.QuiverRep.not_forall_bijective_of_isIrreducibleMorphism`: it is never bijective at
  every vertex, a pointwise isomorphism of quiver representations being an isomorphism.

## Implementation notes

The two clauses of the first result are not exclusive as stated — being injective everywhere and
surjective everywhere would make the morphism an isomorphism, which
`not_forall_bijective_of_isIrreducibleMorphism` rules out, so together they say that exactly one
of the two alternatives holds.

Both proofs pass through Mathlib's pointwise criteria for monomorphisms and epimorphisms in a
functor category (`CategoryTheory.NatTrans.mono_iff_mono_app`,
`CategoryTheory.NatTrans.epi_iff_epi_app`), which need pullbacks resp. pushouts in the target
category; `ModuleCat k` has both. Vertices are quantified as objects of `CategoryTheory.Paths Q`
rather than of `Q`, because that is the index a natural transformation between representations is
applied at; the two agree along `CategoryTheory.Paths.of`.

## References

This is the quiver-representation reading of the `IsIrreducibleMorphism` target of Layer 6
(Auslander-Reiten theory) of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

namespace QuiverRep

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] {M N : QuiverRep k Q} {f : M ⟶ N}

/-- **An irreducible morphism of quiver representations is injective at every vertex or
surjective at every vertex.** The category of representations is abelian, so an irreducible
morphism is a monomorphism or an epimorphism; in a functor category into `ModuleCat k` those are
detected vertex by vertex, and there they are injectivity and surjectivity. -/
theorem injective_or_surjective_of_isIrreducibleMorphism (hf : IsIrreducibleMorphism f) :
    (∀ a : Paths Q, Function.Injective (f.app a)) ∨
      (∀ a : Paths Q, Function.Surjective (f.app a)) := by
  rcases hf.mono_or_epi with h | h
  · exact Or.inl fun a => (ModuleCat.mono_iff_injective _).1 inferInstance
  · exact Or.inr fun a => (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- **An irreducible morphism of quiver representations is not bijective at every vertex.** A
morphism of representations that is an isomorphism at each vertex is an isomorphism, and an
irreducible morphism is not one. -/
theorem not_forall_bijective_of_isIrreducibleMorphism (hf : IsIrreducibleMorphism f) :
    ¬ ∀ a : Paths Q, Function.Bijective (f.app a) := by
  intro hbij
  refine hf.not_isIso ?_
  have hiso : ∀ a : Paths Q, IsIso (f.app a) := fun a => by
    have hmono : Mono (f.app a) := (ModuleCat.mono_iff_injective _).2 (hbij a).1
    have hepi : Epi (f.app a) := (ModuleCat.epi_iff_surjective _).2 (hbij a).2
    exact isIso_of_mono_of_epi _
  exact NatIso.isIso_of_isIso_app f

/-- The two alternatives of
`TauCeti.QuiverRep.injective_or_surjective_of_isIrreducibleMorphism` cannot both hold: an
irreducible morphism that is injective at every vertex fails to be surjective at some vertex. -/
theorem not_surjective_of_isIrreducibleMorphism_of_injective (hf : IsIrreducibleMorphism f)
    (hinj : ∀ a : Paths Q, Function.Injective (f.app a)) :
    ¬ ∀ a : Paths Q, Function.Surjective (f.app a) :=
  fun hsurj => not_forall_bijective_of_isIrreducibleMorphism hf
    fun a => ⟨hinj a, hsurj a⟩

end QuiverRep

end TauCeti
