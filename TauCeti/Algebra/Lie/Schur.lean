/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.Weights.Central

public section

/-!
# The space of morphisms between irreducible Lie modules

Let `M` and `N` be irreducible Lie modules over a Lie algebra `L`. A nonzero morphism `M → N` has
kernel and range that are Lie submodules, so both are trivial or everything; being nonzero forces
the kernel to be `⊥` and the range to be `⊤`, and the morphism is an equivalence
(`TauCeti.LieModule.bijective_of_ne_zero`). So the morphism space is zero unless `M` and `N` are
equivalent.

Over an algebraically closed field the other case is just as rigid. Schur's lemma
(`TauCeti.exists_forall_apply_eq_smul`) makes every self-morphism of a finite-dimensional
irreducible module a scalar, so the endomorphism space is the line spanned by the identity, and
transporting along an equivalence gives the same for `M → N`. Together:

`dim_K (M →ₗ⁅K,L⁆ N) = 1` if `M ≃ₗ⁅K,L⁆ N`, and `0` otherwise.

That dichotomy is the input a *multiplicity* count needs: in a decomposition of `M` into
irreducibles, each summand contributes `1` to `dim_K (S →ₗ⁅K,L⁆ M)` when it is equivalent to `S`
and `0` when it is not. Reading the multiplicity off `dim_K (S →ₗ⁅K,L⁆ M)` needs one further
ingredient, additivity of the morphism space over a direct sum; that is
`TauCeti.LieModule.lieModuleHomDirectSumEquiv` of `TauCeti/Algebra/Lie/DirectSum.lean`, and this
file goes no further than the two-irreducible dimension count.

## Main results

* `TauCeti.LieModule.bijective_of_ne_zero`: **a nonzero morphism between irreducible Lie modules
  is bijective**, over an arbitrary commutative ring.
* `TauCeti.LieModule.eq_zero_of_isEmpty_lieModuleEquiv` and
  `TauCeti.LieModule.subsingleton_lieModuleHom_of_isEmpty_lieModuleEquiv`: inequivalent irreducible
  Lie modules admit only the zero morphism.
* `TauCeti.LieModule.nonempty_lieModuleEquiv_iff_exists_ne_zero`: two irreducible Lie modules are
  equivalent exactly when some morphism between them is nonzero.
* `TauCeti.LieModule.finrank_lieModuleHom_self`: **the endomorphisms of a finite-dimensional
  irreducible Lie module over an algebraically closed field are the scalars**, so the
  endomorphism space is a line.
* `TauCeti.LieModule.finiteDimensional_lieModuleHom_of_isIrreducible`: the morphism space from a
  finite-dimensional irreducible to any irreducible is finite-dimensional.
* `TauCeti.LieModule.finrank_lieModuleHom_eq_one_iff`,
  `TauCeti.LieModule.finrank_lieModuleHom_eq_zero_iff` and
  `TauCeti.LieModule.finrank_lieModuleHom_le_one`: the dimension of the morphism space is `1` when
  the two irreducible modules are equivalent and `0` when they are not, packaged as
  `TauCeti.LieModule.finrank_lieModuleHom`.

## Implementation notes

Schur's lemma itself, `TauCeti.exists_forall_apply_eq_smul`, stays in
`TauCeti/Algebra/Lie/Weights/Central.lean`, where it is proved and where the central weight of an
irreducible module consumes it. This file is its consequence for whole morphism *spaces*, which
needs the morphism-space linear structure and nothing about weights.

## Roadmap

This is the uniqueness input for the multiplicity `m_λ = dim Hom_L(L(λ), M)` of the decomposition
toolkit in Layer 6 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`
(the `isotypicMultiplicity` target of its `Suggested.lean`, whose "`Hom` definition is the one that
makes uniqueness automatic"): the morphism space between irreducibles has dimension `1` or `0`
according as they are equivalent. The multiplicity theorem itself is
`LieModule.isotypicMultiplicity_eq_ncard_of_isInternal` of
`TauCeti/Algebra/Lie/Multiplicity.lean`, which adds to this file the additivity of the morphism
space over a direct-sum decomposition; the `L(λ)`-indexed form additionally needs the irreducible
quotient `L(λ)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.1.
* The statements mirror the categorical
  `CategoryTheory.finrank_hom_simple_simple` of `Mathlib/CategoryTheory/Preadditive/Schur.lean`,
  which is unavailable here: Mathlib has no category of Lie modules over a fixed Lie algebra.
-/

namespace TauCeti.LieModule

open Module (finrank)

universe u v w w₁

/-! ### Over an arbitrary commutative ring -/

section CommRing

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [_root_.LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [_root_.LieModule R L N]
variable [_root_.LieModule.IsIrreducible R L M] [_root_.LieModule.IsIrreducible R L N]

-- The `LieAlgebra` and `LieModule` instances above are needed only to state the irreducibility
-- hypotheses; the results themselves are about the underlying `LieRingModule` structure.
omit [LieAlgebra R L] [_root_.LieModule R L M] [_root_.LieModule R L N]

/-- **Schur's lemma for Lie modules, in its bijectivity form**: a nonzero morphism between
irreducible Lie modules is bijective. Its kernel is a Lie submodule of `M` other than `⊤` and its
range is a Lie submodule of `N` other than `⊥`, and irreducibility leaves no other option. -/
theorem bijective_of_ne_zero {f : M →ₗ⁅R,L⁆ N} (hf : f ≠ 0) : Function.Bijective f := by
  constructor
  · rw [← LieModuleHom.ker_eq_bot]
    refine (IsSimpleOrder.eq_bot_or_eq_top f.ker).resolve_right fun h ↦ hf ?_
    ext m
    simpa using LieModuleHom.mem_ker.1 (h ▸ LieSubmodule.mem_top m)
  · rw [← LieModuleHom.range_eq_top]
    refine (IsSimpleOrder.eq_bot_or_eq_top f.range).resolve_left fun h ↦ hf ?_
    ext m
    have hmem : f m ∈ f.range := (LieModuleHom.mem_range f _).2 ⟨m, rfl⟩
    rw [h, LieSubmodule.mem_bot] at hmem
    simpa using hmem

/-- A nonzero morphism between irreducible Lie modules makes them equivalent. -/
theorem nonempty_lieModuleEquiv_of_ne_zero {f : M →ₗ⁅R,L⁆ N} (hf : f ≠ 0) :
    Nonempty (M ≃ₗ⁅R,L⁆ N) :=
  ⟨LieModuleEquiv.ofBijective f (bijective_of_ne_zero hf)⟩

/-- **Inequivalent irreducible Lie modules admit only the zero morphism.** -/
theorem eq_zero_of_isEmpty_lieModuleEquiv (h : IsEmpty (M ≃ₗ⁅R,L⁆ N)) (f : M →ₗ⁅R,L⁆ N) : f = 0 :=
  by_contra fun hf ↦ (nonempty_lieModuleEquiv_of_ne_zero hf).elim h.elim

/-- The morphism space between inequivalent irreducible Lie modules is trivial. -/
theorem subsingleton_lieModuleHom_of_isEmpty_lieModuleEquiv (h : IsEmpty (M ≃ₗ⁅R,L⁆ N)) :
    Subsingleton (M →ₗ⁅R,L⁆ N) :=
  ⟨fun f g ↦ by
    rw [eq_zero_of_isEmpty_lieModuleEquiv h f, eq_zero_of_isEmpty_lieModuleEquiv h g]⟩

/-- **Two irreducible Lie modules are equivalent exactly when they admit a nonzero morphism.** -/
theorem nonempty_lieModuleEquiv_iff_exists_ne_zero :
    Nonempty (M ≃ₗ⁅R,L⁆ N) ↔ ∃ f : M →ₗ⁅R,L⁆ N, f ≠ 0 := by
  refine ⟨fun ⟨e⟩ ↦ ⟨(e : M →ₗ⁅R,L⁆ N), fun h ↦ ?_⟩, fun ⟨_, hf⟩ ↦
    nonempty_lieModuleEquiv_of_ne_zero hf⟩
  have _i : Nontrivial M := _root_.LieModule.nontrivial_of_isIrreducible R L M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  exact hm (e.injective (by simpa using congrArg (fun g : M →ₗ⁅R,L⁆ N ↦ g m) h))

end CommRing

/-! ### Over an algebraically closed field -/

section IsAlgClosed

variable (K : Type u) (L : Type v) (M : Type w) {N : Type w₁}
variable [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable [AddCommGroup N] [Module K N] [LieRingModule L N] [_root_.LieModule K L N]
variable [FiniteDimensional K M] [_root_.LieModule.IsIrreducible K L M]

/-- **The endomorphism space of a finite-dimensional irreducible Lie module is a line.** Over an
algebraically closed field Schur's lemma makes every endomorphism a scalar multiple of the
identity, and the identity is nonzero because an irreducible module is nontrivial. -/
theorem finrank_lieModuleHom_self : finrank K (M →ₗ⁅K,L⁆ M) = 1 := by
  have _i : Nontrivial M := _root_.LieModule.nontrivial_of_isIrreducible K L M
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hid : (LieModuleHom.id : M →ₗ⁅K,L⁆ M) ≠ 0 := fun h ↦
    hm₀ (by simpa using congrArg (fun g : M →ₗ⁅K,L⁆ M ↦ g m₀) h)
  rw [finrank_eq_one_iff_of_nonzero' _ hid]
  intro f
  obtain ⟨c, hc⟩ := exists_forall_apply_eq_smul K L M f
  exact ⟨c, by ext m; simpa using (hc m).symm⟩

variable {M}

/-- Equivalent finite-dimensional irreducible Lie modules have a one-dimensional morphism space:
postcomposing with the equivalence identifies it with the endomorphism space. -/
theorem finrank_lieModuleHom_eq_one_of_nonempty_lieModuleEquiv (h : Nonempty (M ≃ₗ⁅K,L⁆ N)) :
    finrank K (M →ₗ⁅K,L⁆ N) = 1 := by
  rw [← (LieModuleEquiv.congrRight (M := M) h.some).finrank_eq]
  exact finrank_lieModuleHom_self K L M

variable [_root_.LieModule.IsIrreducible K L N]

omit [IsAlgClosed K] [_root_.LieModule K L M] [FiniteDimensional K M] in
/-- Inequivalent irreducible Lie modules have a zero-dimensional morphism space. -/
theorem finrank_lieModuleHom_eq_zero_of_isEmpty_lieModuleEquiv (h : IsEmpty (M ≃ₗ⁅K,L⁆ N)) :
    finrank K (M →ₗ⁅K,L⁆ N) = 0 :=
  have := subsingleton_lieModuleHom_of_isEmpty_lieModuleEquiv h
  Module.finrank_zero_of_subsingleton

omit [IsAlgClosed K] in
/-- The morphism space from a finite-dimensional irreducible Lie module to any irreducible Lie
module is finite-dimensional: it is either trivial, when the two modules are inequivalent, or,
transported along an equivalence, the endomorphism space of the finite-dimensional `M`. -/
theorem finiteDimensional_lieModuleHom_of_isIrreducible :
    FiniteDimensional K (M →ₗ⁅K,L⁆ N) := by
  by_cases h : Nonempty (M ≃ₗ⁅K,L⁆ N)
  · have hend : FiniteDimensional K (M →ₗ⁅K,L⁆ M) := inferInstance
    exact Module.Finite.equiv (LieModuleEquiv.congrRight (M := M) h.some)
  · have : Subsingleton (M →ₗ⁅K,L⁆ N) :=
      subsingleton_lieModuleHom_of_isEmpty_lieModuleEquiv (not_nonempty_iff.mp h)
    exact Module.Finite.of_surjective (0 : K →ₗ[K] (M →ₗ⁅K,L⁆ N))
      fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- **The morphism space of two finite-dimensional irreducible Lie modules is one-dimensional
exactly when they are equivalent.** -/
theorem finrank_lieModuleHom_eq_one_iff :
    finrank K (M →ₗ⁅K,L⁆ N) = 1 ↔ Nonempty (M ≃ₗ⁅K,L⁆ N) := by
  refine ⟨fun h ↦ ?_, finrank_lieModuleHom_eq_one_of_nonempty_lieModuleEquiv K L⟩
  rw [← not_isEmpty_iff]
  intro hempty
  rw [finrank_lieModuleHom_eq_zero_of_isEmpty_lieModuleEquiv K L hempty] at h
  exact zero_ne_one h

/-- **The morphism space of two finite-dimensional irreducible Lie modules vanishes exactly when
they are inequivalent.** -/
theorem finrank_lieModuleHom_eq_zero_iff :
    finrank K (M →ₗ⁅K,L⁆ N) = 0 ↔ IsEmpty (M ≃ₗ⁅K,L⁆ N) := by
  refine ⟨fun h ↦ ?_, finrank_lieModuleHom_eq_zero_of_isEmpty_lieModuleEquiv K L⟩
  rw [← not_nonempty_iff]
  intro hne
  rw [finrank_lieModuleHom_eq_one_of_nonempty_lieModuleEquiv K L hne] at h
  exact one_ne_zero h

/-- **The morphism space of two finite-dimensional irreducible Lie modules is at most a line.** -/
theorem finrank_lieModuleHom_le_one : finrank K (M →ₗ⁅K,L⁆ N) ≤ 1 := by
  rcases isEmpty_or_nonempty (M ≃ₗ⁅K,L⁆ N) with h | h
  · exact le_of_eq_of_le (finrank_lieModuleHom_eq_zero_of_isEmpty_lieModuleEquiv K L h) zero_le_one
  · exact le_of_eq (finrank_lieModuleHom_eq_one_of_nonempty_lieModuleEquiv K L h)

open scoped Classical in
/-- **Schur's lemma for finite-dimensional irreducible Lie modules over an algebraically closed
field, in its dimension form**: the morphism space is a line for equivalent modules and zero for
inequivalent ones. This is the per-summand contribution that a multiplicity count of `S` in `M`
reads off `dim_K (S →ₗ⁅K,L⁆ M)`, which additivity of the morphism space over a decomposition of `M`
supplies: `TauCeti.LieModule.finrank_lieModuleHom_eq_sum_of_isInternal` of
`TauCeti/Algebra/Lie/Submodule/DirectSum.lean`. -/
theorem finrank_lieModuleHom :
    finrank K (M →ₗ⁅K,L⁆ N) = if Nonempty (M ≃ₗ⁅K,L⁆ N) then 1 else 0 := by
  split
  · exact finrank_lieModuleHom_eq_one_of_nonempty_lieModuleEquiv K L ‹_›
  · exact finrank_lieModuleHom_eq_zero_of_isEmpty_lieModuleEquiv K L (not_nonempty_iff.1 ‹_›)

end IsAlgClosed

end TauCeti.LieModule
