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
* `TauCeti.simpleSubmoduleClassesEquiv`: **the bijection.** The isomorphism classes of simple
  submodules of `M`, as the quotient type `TauCeti.SimpleSubmoduleClasses R M`, correspond to the
  isotypic components of `M`, the class of `N` going to the `N`-isotypic component. This needs no
  hypothesis on the ring; for `M = R` it is the bijection with the Artin-Wedderburn blocks.
* `TauCeti.simpleModuleClass`: over a semisimple ring, the class in `SimpleSubmoduleClasses R R`
  of the simple left ideals realizing an abstract simple module. Its fibres are the isomorphism
  classes (`TauCeti.simpleModuleClass_eq_iff`) and it hits every class
  (`TauCeti.simpleModuleClass_coe`), so `SimpleSubmoduleClasses R R` is a universe-safe type of
  isomorphism classes of simple `R`-modules.
* `TauCeti.finite_of_pairwise_not_linearEquiv`: a semisimple ring has only finitely many
  isomorphism classes of simple modules.

## Implementation notes

Isomorphism classes of *abstract* simple modules cannot be a type: they range over every universe.
They are therefore handled in two ways here. The relational lemmas
`TauCeti.isotypicComponent_eq_iff` and `TauCeti.isotypicComponent_mem_isotypicComponents` state
injectivity and well-definedness of `M ↦ isotypicComponent R R M` without naming a type of classes
at all. The bundled bijection instead uses `TauCeti.SimpleSubmoduleClasses R R`, the classes of
simple *left ideals*, which is a type in `Type u`; over a semisimple ring
`TauCeti.simpleModuleClass` identifies it with the classes of abstract simple modules. It is used
through `TauCeti.SimpleSubmoduleClasses.mk`, `TauCeti.SimpleSubmoduleClasses.mk_eq_mk_iff` and the
eliminators `TauCeti.SimpleSubmoduleClasses.lift` (into `Sort`, with its defining equation
`TauCeti.SimpleSubmoduleClasses.lift_mk`) and `TauCeti.SimpleSubmoduleClasses.ind` (into `Prop`),
which is a complete API: nothing downstream has to know it is a quotient.

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

variable (R M) in
/-- The isomorphism classes of simple submodules of `M`. Unlike the isomorphism classes of abstract
simple modules, which range over every universe, this is a type; over a semisimple ring the two
agree for `M = R`, by `TauCeti.simpleModuleClass`.

That this is a quotient of the simple submodules by linear isomorphism is an implementation
detail: build a class with `TauCeti.SimpleSubmoduleClasses.mk`, compare classes with
`TauCeti.SimpleSubmoduleClasses.mk_eq_mk_iff`, and eliminate with
`TauCeti.SimpleSubmoduleClasses.lift` into `Sort` or `TauCeti.SimpleSubmoduleClasses.ind` into
`Prop`. The `@[expose]` annotations here and on those declarations are forced by the module
system, which refuses the defining equations `TauCeti.SimpleSubmoduleClasses.lift_mk` and
`TauCeti.coe_simpleSubmoduleClassesEquiv_mk` over a definition it cannot unfold; Mathlib exposes
its own quotient constructions wholesale for the same reason. -/
@[expose]
def SimpleSubmoduleClasses :=
  Quot fun N N' : {N : Submodule R M // IsSimpleModule R N} ↦ Nonempty (N.1 ≃ₗ[R] N'.1)

namespace SimpleSubmoduleClasses

/-- The isomorphism class of a simple submodule of `M`. -/
@[expose]
def mk (N : Submodule R M) [IsSimpleModule R N] : SimpleSubmoduleClasses R M := Quot.mk _ ⟨N, ‹_›⟩

theorem mk_eq_mk_iff {N N' : Submodule R M} [IsSimpleModule R N] [IsSimpleModule R N'] :
    mk N = mk N' ↔ Nonempty (N ≃ₗ[R] N') :=
  Quot.eq.trans <| Equivalence.eqvGen_iff
    ⟨fun _ ↦ ⟨.refl R _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

/-- Every isomorphism class is the class of a simple submodule: the eliminator into `Prop`. -/
@[elab_as_elim]
theorem ind {motive : SimpleSubmoduleClasses R M → Prop}
    (mk : ∀ (N : Submodule R M) (_ : IsSimpleModule R N), motive (.mk N))
    (c : SimpleSubmoduleClasses R M) : motive c :=
  Quot.ind (fun N ↦ mk N.1 N.2) c

/-- **The eliminator into `Sort`.** To define data on the isomorphism classes of simple submodules
of `M` it suffices to give a value on each simple submodule and to check that isomorphic simple
submodules get the same value; the value on a class is then read off by
`TauCeti.SimpleSubmoduleClasses.lift_mk`. -/
@[expose]
def lift {α : Sort*} (f : ∀ (N : Submodule R M) [IsSimpleModule R N], α)
    (hf : ∀ (N N' : Submodule R M) [IsSimpleModule R N] [IsSimpleModule R N'],
      Nonempty (N ≃ₗ[R] N') → f N = f N')
    (c : SimpleSubmoduleClasses R M) : α :=
  Quot.lift (fun N ↦ @f N.1 N.2) (fun N N' h ↦ @hf N.1 N'.1 N.2 N'.2 h) c

/-- The defining equation of `TauCeti.SimpleSubmoduleClasses.lift`. -/
@[simp]
theorem lift_mk {α : Sort*} {f : ∀ (N : Submodule R M) [IsSimpleModule R N], α} {hf}
    (N : Submodule R M) [IsSimpleModule R N] : lift f hf (mk N) = f N := rfl

end SimpleSubmoduleClasses

variable (R M) in
/-- **Isomorphism classes of simple submodules biject with isotypic components.** The class of a
simple submodule `N` of `M` corresponds to the `N`-isotypic component of `M`.

Injectivity is `TauCeti.le_isotypicComponent_iff`: a simple submodule of an isotypic component is a
copy of the module cutting it out. Surjectivity is the definition of `isotypicComponents`. -/
@[expose]
noncomputable def simpleSubmoduleClassesEquiv :
    SimpleSubmoduleClasses R M ≃ isotypicComponents R M :=
  Equiv.ofBijective
    (SimpleSubmoduleClasses.lift
      (fun N hN ↦ (⟨isotypicComponent R M N, N, hN, rfl⟩ : isotypicComponents R M))
      fun _ _ _ _ ⟨e⟩ ↦ Subtype.ext e.isotypicComponent_eq)
    ⟨by
      refine SimpleSubmoduleClasses.ind fun N _ ↦ SimpleSubmoduleClasses.ind fun N' _ ↦ fun h ↦ ?_
      rw [SimpleSubmoduleClasses.mk_eq_mk_iff]
      have h' : isotypicComponent R M N = isotypicComponent R M N' := congrArg Subtype.val h
      exact ⟨((le_isotypicComponent_iff N).mp (h' ▸ N.le_isotypicComponent)).some.symm⟩,
     by rintro ⟨_, N, _, rfl⟩; exact ⟨.mk N, rfl⟩⟩

@[simp]
theorem coe_simpleSubmoduleClassesEquiv_mk (N : Submodule R M) [IsSimpleModule R N] :
    (simpleSubmoduleClassesEquiv R M (.mk N) : Submodule R M) = isotypicComponent R M N := rfl

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

variable (R M) in
/-- Over a semisimple ring, the isomorphism class of the simple left ideals realizing an abstract
simple module `M`; see `TauCeti.simpleModuleClass_eq_mk_iff`. -/
noncomputable def simpleModuleClass [IsSemisimpleRing R] [IsSimpleModule R M] :
    SimpleSubmoduleClasses R R :=
  (simpleSubmoduleClassesEquiv R R).symm
    ⟨isotypicComponent R R M, isotypicComponent_mem_isotypicComponents R M⟩

@[simp]
theorem coe_simpleSubmoduleClassesEquiv_simpleModuleClass [IsSemisimpleRing R]
    [IsSimpleModule R M] :
    (simpleSubmoduleClassesEquiv R R (simpleModuleClass R M) : Submodule R R) =
      isotypicComponent R R M :=
  congrArg Subtype.val ((simpleSubmoduleClassesEquiv R R).apply_symm_apply _)

/-- The class of an abstract simple module is the class of a simple left ideal exactly when the two
are isomorphic, which is what makes `TauCeti.simpleModuleClass` a realization of `M`. -/
theorem simpleModuleClass_eq_mk_iff [IsSemisimpleRing R] [IsSimpleModule R M]
    (I : Submodule R R) [IsSimpleModule R I] :
    simpleModuleClass R M = .mk I ↔ Nonempty (M ≃ₗ[R] I) := by
  rw [← (simpleSubmoduleClassesEquiv R R).apply_eq_iff_eq, ← Subtype.coe_inj,
    coe_simpleSubmoduleClassesEquiv_simpleModuleClass, coe_simpleSubmoduleClassesEquiv_mk]
  exact isotypicComponent_eq_iff

/-- Every isomorphism class of simple left ideals is the class of an abstract simple module, namely
of the ideal itself: `TauCeti.simpleModuleClass` is surjective. -/
theorem simpleModuleClass_coe [IsSemisimpleRing R] (I : Submodule R R) [IsSimpleModule R I] :
    simpleModuleClass R I = .mk I :=
  (simpleModuleClass_eq_mk_iff I).mpr ⟨.refl R I⟩

/-- **The dictionary as a map to a type of classes.** Over a semisimple ring, two simple modules
have the same class of realizing left ideals if and only if they are isomorphic.

With `TauCeti.simpleModuleClass_coe` this says that `SimpleSubmoduleClasses R R`, which
`TauCeti.simpleSubmoduleClassesEquiv` identifies with the isotypic components of `R`, is a type of
isomorphism classes of simple `R`-modules. -/
theorem simpleModuleClass_eq_iff [IsSemisimpleRing R] {N : Type w} [AddCommGroup N] [Module R N]
    [IsSimpleModule R M] [IsSimpleModule R N] :
    simpleModuleClass R M = simpleModuleClass R N ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← (simpleSubmoduleClassesEquiv R R).apply_eq_iff_eq, ← Subtype.coe_inj,
    coe_simpleSubmoduleClassesEquiv_simpleModuleClass,
    coe_simpleSubmoduleClassesEquiv_simpleModuleClass]
  exact isotypicComponent_eq_iff

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
