/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Mathlib.RingTheory.FiniteLength` is imported for the instance chain that makes a semisimple
-- ring Noetherian over itself, which is what supplies `Finite (isotypicComponents R R)` in
-- `TauCeti.finite_of_pairwise_not_linearEquiv`.
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Isotypic components of the regular module as an invariant of abstract simple modules

Mathlib's `isotypicComponent R N S` is the sum of all submodules of `N` isomorphic to `S`, and
`isotypicComponents R N` is the set of its nontrivial values as `S` ranges over the simple
*submodules* of `N`. For `N = R` the latter is a set of left ideals, and it is what indexes the
Artin-Wedderburn decomposition of a semisimple ring. Calling those indices the isomorphism classes
of simple `R`-modules is a theorem, not a rename: an abstract simple module carries no relation to
`R` beyond its action.

Mathlib supplies the input, `IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`: every
simple module over a semisimple ring is isomorphic to a left ideal, necessarily a minimal one. This
file turns that realization into the statement that `M ↦ isotypicComponent R R M`, which Mathlib
already defines for an abstract `M`, is a complete isomorphism invariant of simple modules whose
values are exactly `isotypicComponents R R`.

## Main results

* `TauCeti.le_isotypicComponent_iff`: a simple submodule lies in the `S`-isotypic component exactly
  when it is a copy of the simple module `S`. The isotypic component therefore sees no simple
  module other than `S`; this holds in any ambient module, with no hypothesis on the ring.
* `TauCeti.isotypicComponent_eq_iff`: **the block ⇆ simple-module dictionary.** Two simple modules
  over a semisimple ring cut out the same isotypic component of `R` if and only if they are
  isomorphic — the injectivity half.
* `TauCeti.isotypicComponent_mem_isotypicComponents`: the isotypic component cut out by an abstract
  simple module is one of the isotypic components of the regular module, so the map above is
  well defined into `isotypicComponents R R`. Surjectivity needs no lemma: by definition every
  element of `isotypicComponents R R` is `isotypicComponent R R I` for a simple left ideal `I`.
* `TauCeti.finite_of_pairwise_not_linearEquiv`: a semisimple ring has only finitely many
  isomorphism classes of simple modules.

## Implementation notes

Isomorphism classes are handled without a quotient type: "the map is injective" is
`TauCeti.isotypicComponent_eq_iff`, and "the map is well defined" is
`LinearEquiv.isotypicComponent_eq` together with
`TauCeti.isotypicComponent_mem_isotypicComponents`.

Each proof over a semisimple ring realizes the abstract module as a left ideal and transports along
that realization; nothing here redoes the isotypic theory.

This implements the isomorphism-class bijection of Layer 1.5 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3, and C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R]

section IsotypicComponent

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A simple submodule lies in the `S`-isotypic component of `M` exactly when it is a copy of the
simple module `S`. Unlike Mathlib's `Submodule.le_isotypicComponent`, the module `S` cutting out
the component is an arbitrary simple `R`-module rather than a submodule of `M`. -/
theorem le_isotypicComponent_iff {S : Type w} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (N : Submodule R M) [IsSimpleModule R N] :
    N ≤ isotypicComponent R M S ↔ Nonempty (S ≃ₗ[R] N) :=
  ⟨fun h ↦ ⟨(isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S) N h).some.symm⟩,
    fun ⟨e⟩ ↦ le_sSup ⟨e.symm⟩⟩

variable (R M)

/-- Over a semisimple ring, the isotypic component of the regular module cut out by an abstract
simple module really is one of the isotypic components of `R`, which are indexed by the simple
*left ideals*. -/
theorem isotypicComponent_mem_isotypicComponents [IsSemisimpleRing R] [IsSimpleModule R M] :
    isotypicComponent R R M ∈ isotypicComponents R R := by
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  exact ⟨I, .congr e.symm, e.isotypicComponent_eq⟩

variable {R M}

/-- **The isotypic component of the regular module is a complete isomorphism invariant of a simple
module.** Over a semisimple ring, two simple modules cut out the same isotypic component of `R` if
and only if they are isomorphic.

Together with `TauCeti.isotypicComponent_mem_isotypicComponents` and the fact that every element of
`isotypicComponents R R` is by definition an isotypic component of a simple left ideal, this is the
bijection between isomorphism classes of simple `R`-modules and the isotypic components of `R`; the
latter index the blocks of an Artin-Wedderburn decomposition. -/
theorem isotypicComponent_eq_iff [IsSemisimpleRing R] {N : Type w} [AddCommGroup N] [Module R N]
    [IsSimpleModule R M] [IsSimpleModule R N] :
    isotypicComponent R R M = isotypicComponent R R N ↔ Nonempty (M ≃ₗ[R] N) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.isotypicComponent_eq⟩
  obtain ⟨I, ⟨f⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  have : IsSimpleModule R I := .congr f.symm
  have hle : (I : Submodule R R) ≤ isotypicComponent R R M :=
    h ▸ (le_isotypicComponent_iff I).mpr ⟨f⟩
  exact ⟨((le_isotypicComponent_iff I).mp hle).some.trans f.symm⟩

/-- A semisimple ring has only finitely many isomorphism classes of simple modules: a family of
pairwise non-isomorphic simple `R`-modules is indexed by a finite type, because
`isotypicComponent R R` embeds it into the finite set `isotypicComponents R R`. -/
theorem finite_of_pairwise_not_linearEquiv [IsSemisimpleRing R] {ι : Type*} (S : ι → Type v)
    [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, IsSimpleModule R (S i)]
    (h : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) : Finite ι :=
  Finite.of_injective
    (fun i ↦ (⟨isotypicComponent R R (S i),
      isotypicComponent_mem_isotypicComponents R (S i)⟩ : isotypicComponents R R))
    fun i j hij ↦ h i j (isotypicComponent_eq_iff.mp (Subtype.ext_iff.mp hij))

end IsotypicComponent

end TauCeti
