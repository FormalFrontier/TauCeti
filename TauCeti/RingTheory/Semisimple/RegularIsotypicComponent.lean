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

Mathlib's isotypic decomposition (`isotypicComponent`, `isotypicComponents`) organizes the
**submodules** of a module: `isotypicComponents R R` is a set of left ideals of `R`, indexed by
the isomorphism classes of *simple submodules* of the regular module. The Artin-Wedderburn
decomposition of a semisimple ring is indexed by that same set. Calling those indices the
isomorphism classes of simple `R`-modules is a theorem, not a rename: an abstract simple module
carries no relation to `R` beyond its action.

Mathlib supplies the input, `IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`: every
simple module over a semisimple ring is isomorphic to a left ideal, necessarily a minimal one. This
file turns that realization into a complete isomorphism invariant of simple modules, which is what
lets `isotypicComponents R R` be indexed by isomorphism classes of abstract simple `R`-modules.

## Main results

* `TauCeti.regularIsotypicComponent`: the isotypic component of the regular module attached to an
  abstract `R`-module `M`, namely the sum of all left ideals isomorphic to `M`. It agrees with
  Mathlib's `isotypicComponent R R I` whenever `M` is realized as a left ideal `I`
  (`TauCeti.regularIsotypicComponent_eq_isotypicComponent`).
* `TauCeti.regularIsotypicComponent_eq_iff`: **the block ⇆ simple-module dictionary.** Two simple
  modules over a semisimple ring cut out the same isotypic component of `R` if and only if they are
  isomorphic. With `TauCeti.regularIsotypicComponent_mem_isotypicComponents` and
  `TauCeti.exists_regularIsotypicComponent_eq` this is the announced bijection: the assignment
  `M ↦ regularIsotypicComponent R M` is a well-defined, injective and surjective map from the
  isomorphism classes of simple `R`-modules onto `isotypicComponents R R`.
* `TauCeti.le_regularIsotypicComponent_iff`: the sharper local statement that a simple left ideal
  lies in the `M`-isotypic component exactly when it is a copy of `M`.
* `TauCeti.finite_of_pairwise_not_linearEquiv`: a semisimple ring has only finitely many
  isomorphism classes of simple modules.

## Implementation notes

`TauCeti.regularIsotypicComponent R M` is defined directly as `sSup {I | Nonempty (M ≃ₗ[R] I)}`,
with no choice of a realization of `M` as a left ideal, so it is manifestly an isomorphism
invariant of `M`. Mathlib's `isotypicComponent R N S` is the same construction for `S` a submodule
of the ambient module `N`; the extra generality here is exactly that `M` may be an abstract module,
which is what a statement about isomorphism classes of simple modules needs. The two agree once a
realization is available, and every lemma below is proved by transporting to Mathlib's version
along such a realization rather than by redoing the isotypic theory.

The definition does not assume `M` simple, nor `R` semisimple: those hypotheses are what make the
invariant *complete* and *surjective*, not what makes it well defined.

Isomorphism classes are handled without a quotient type: "the map is injective" is
`regularIsotypicComponent_eq_iff`, and "the map is surjective" is
`exists_regularIsotypicComponent_eq`.

This implements the isomorphism-class bijection of Layer 1.5 of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3, and C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R]

section RegularIsotypicComponent

variable (R) (M : Type v) [AddCommGroup M] [Module R M]

/-- The isotypic component of the regular module `R` attached to an `R`-module `M`: the sum of all
left ideals of `R` isomorphic to `M`.

For `M` a submodule of `R` this is Mathlib's `isotypicComponent R R M`
(`TauCeti.regularIsotypicComponent_eq_isotypicComponent`); allowing `M` to be an abstract module is
what lets the isotypic components of `R` be indexed by isomorphism classes of simple `R`-modules
rather than by simple submodules of `R`. No hypotheses are needed for the definition; over a
semisimple ring and for `M` simple it is a complete isomorphism invariant of `M`
(`TauCeti.regularIsotypicComponent_eq_iff`). -/
def regularIsotypicComponent : Submodule R R := sSup {I : Submodule R R | Nonempty (M ≃ₗ[R] I)}

variable {R M}

/-- A left ideal isomorphic to `M` is contained in the `M`-isotypic component of `R`. -/
theorem le_regularIsotypicComponent {I : Submodule R R} (e : M ≃ₗ[R] I) :
    I ≤ regularIsotypicComponent R M :=
  le_sSup ⟨e⟩

/-- Realizing `M` as a left ideal `I` identifies `TauCeti.regularIsotypicComponent R M` with
Mathlib's isotypic component `isotypicComponent R R I`. -/
theorem regularIsotypicComponent_eq_isotypicComponent {I : Submodule R R} (e : M ≃ₗ[R] I) :
    regularIsotypicComponent R M = isotypicComponent R R I :=
  congr_arg sSup <| Set.ext fun _ ↦
    Nonempty.congr (fun f ↦ f.symm.trans e) fun g ↦ e.trans g.symm

/-- The isotypic component cut out by `M` depends only on the isomorphism class of `M`. -/
theorem regularIsotypicComponent_congr {N : Type w} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : regularIsotypicComponent R M = regularIsotypicComponent R N :=
  congr_arg sSup <| Set.ext fun _ ↦ Nonempty.congr (fun f ↦ e.symm.trans f) fun g ↦ e.trans g

variable (R M)

/-- Over a semisimple ring, the isotypic component cut out by a simple module really is one of the
isotypic components of the regular module. -/
theorem regularIsotypicComponent_mem_isotypicComponents [IsSemisimpleRing R] [IsSimpleModule R M] :
    regularIsotypicComponent R M ∈ isotypicComponents R R := by
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  exact ⟨I, .congr e.symm, regularIsotypicComponent_eq_isotypicComponent e⟩

/-- A nonzero isotypic component: over a semisimple ring a simple module does occur in the regular
module. -/
theorem bot_lt_regularIsotypicComponent [IsSemisimpleRing R] [IsSimpleModule R M] :
    ⊥ < regularIsotypicComponent R M := by
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  have : IsSimpleModule R I := .congr e.symm
  rw [regularIsotypicComponent_eq_isotypicComponent e]
  exact bot_lt_isotypicComponent I

variable {R M}

/-- A simple left ideal lies in the `M`-isotypic component of `R` exactly when it is a copy of the
simple module `M`. The isotypic component therefore sees no simple module other than `M`. -/
theorem le_regularIsotypicComponent_iff [IsSimpleModule R M] (I : Submodule R R)
    [IsSimpleModule R I] : I ≤ regularIsotypicComponent R M ↔ Nonempty (M ≃ₗ[R] I) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ le_regularIsotypicComponent e⟩
  haveI (J : {J : Submodule R R | Nonempty (M ≃ₗ[R] J)}) : IsSimpleModule R J :=
    .congr J.2.some.symm
  have h' : I ≤ sSup {J : Submodule R R | Nonempty (M ≃ₗ[R] J)} := h
  obtain ⟨J, hJ, ⟨f⟩⟩ := I.linearEquiv_of_le_sSup _ h'
  exact ⟨hJ.some.trans f.symm⟩

/-- **The isotypic component is a complete isomorphism invariant of a simple module.** Over a
semisimple ring, two simple modules cut out the same isotypic component of the regular module if
and only if they are isomorphic.

Together with `TauCeti.regularIsotypicComponent_mem_isotypicComponents` and
`TauCeti.exists_regularIsotypicComponent_eq`, this is the bijection between isomorphism classes of
simple `R`-modules and the isotypic components of `R`; the latter index the blocks of an
Artin-Wedderburn decomposition. -/
theorem regularIsotypicComponent_eq_iff [IsSemisimpleRing R] {N : Type w} [AddCommGroup N]
    [Module R N] [IsSimpleModule R M] [IsSimpleModule R N] :
    regularIsotypicComponent R M = regularIsotypicComponent R N ↔ Nonempty (M ≃ₗ[R] N) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ regularIsotypicComponent_congr e⟩
  obtain ⟨I, ⟨f⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  have : IsSimpleModule R I := .congr f.symm
  have hle : (I : Submodule R R) ≤ regularIsotypicComponent R M := by
    rw [h]; exact le_regularIsotypicComponent f
  exact ⟨((le_regularIsotypicComponent_iff I).mp hle).some.trans f.symm⟩

/-- Every isotypic component of the regular module is cut out by a simple module, namely by any of
the simple left ideals it contains. This is the surjectivity half of the bijection between
isomorphism classes of simple modules and isotypic components. -/
theorem exists_regularIsotypicComponent_eq {c : Submodule R R} (hc : c ∈ isotypicComponents R R) :
    ∃ I : Submodule R R, IsSimpleModule R I ∧ regularIsotypicComponent R I = c := by
  obtain ⟨I, hI, rfl⟩ := hc
  exact ⟨I, hI, regularIsotypicComponent_eq_isotypicComponent (.refl R I)⟩

/-- A semisimple ring has only finitely many isomorphism classes of simple modules: a family of
pairwise non-isomorphic simple `R`-modules is indexed by a finite type, because
`TauCeti.regularIsotypicComponent` embeds it into the finite set `isotypicComponents R R`. -/
theorem finite_of_pairwise_not_linearEquiv [IsSemisimpleRing R] {ι : Type*} (S : ι → Type v)
    [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, IsSimpleModule R (S i)]
    (h : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) : Finite ι :=
  Finite.of_injective
    (fun i ↦ (⟨regularIsotypicComponent R (S i),
      regularIsotypicComponent_mem_isotypicComponents R (S i)⟩ : isotypicComponents R R))
    fun i j hij ↦ h i j (regularIsotypicComponent_eq_iff.mp (Subtype.ext_iff.mp hij))

end RegularIsotypicComponent

end TauCeti
