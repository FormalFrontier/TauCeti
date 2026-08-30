/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Algebra.Module.Injective.Envelope

/-!
# Minimal injective copresentations

A **minimal injective copresentation** of a module `M` is an exact sequence

`0 → M → Q₀ → Q₁`

in which `Q₀` and `Q₁` are injective and both successive extensions are minimal. The first
structure map is an injective envelope of `M`. Exactness makes the second map descend to an
embedding
`Q₀ / range(i₀) → Q₁`, and minimality says that this induced embedding is an injective envelope as
well. Equivalently, the ranges of both displayed maps are essential submodules of their targets.

This file records both directions of that equivalence and proves uniqueness: two minimal injective
copresentations of the same module are related by linear equivalences of both injective terms,
commuting with both maps. Thus the first two terms of a minimal injective resolution are
independent of the choices.
The construction is dual to minimal projective presentations, and is the injective half of the
presentation theory used to define the Auslander--Reiten translate and its inverse.

## Main definitions and results

* `TauCeti.IsMinimalInjectiveCopresentation`: exactness, an injective envelope in degree zero,
  an injective module in degree one, and essential image in degree one.
* `TauCeti.IsMinimalInjectiveCopresentation.cokernelMap`: the induced map
  `Q₀ / range(i₀) → Q₁`.
* `TauCeti.IsMinimalInjectiveCopresentation.isInjectiveEnvelope_cokernelMap`: the induced map is
  the second injective envelope.
* `TauCeti.IsInjectiveEnvelope.isMinimalInjectiveCopresentation`: the converse constructor from
  two successive injective envelopes.
* `TauCeti.IsMinimalInjectiveCopresentation.exists_linearEquiv`: uniqueness as an isomorphism of
  the two copresentation diagrams.

## References

This supplies the injective half of sublayer 6B, "minimal projective/injective presentations", of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. That sublayer is an explicit
prerequisite for the transpose, the Auslander--Reiten translate, and almost-split sequences.

See M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995),
Chapter IV, and I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of
Associative Algebras, Vol. 1*, CUP (2006), Section IV.2.
-/

public section

namespace TauCeti

universe u v w₀ w₁ w₀' w₁'

variable {R : Type u} {M : Type v} {Q₀ : Type w₀} {Q₁ : Type w₁}
  [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]

/-- A **minimal injective copresentation** `0 → M → Q₀ → Q₁` consists of an injective envelope
`i₀ : M →ₗ[R] Q₀`, an exact pair `i₀, i₁`, and an injective `Q₁` in which the range of `i₁` is
essential. Exactness identifies `Q₀ / range(i₀)` with the source of the second embedding, so the
last two fields say precisely that this induced embedding is another injective envelope. -/
structure IsMinimalInjectiveCopresentation (i₀ : M →ₗ[R] Q₀) (i₁ : Q₀ →ₗ[R] Q₁) : Prop where
  /-- The first map exhibits `Q₀` as the injective envelope of `M`. -/
  isInjectiveEnvelope : IsInjectiveEnvelope i₀
  /-- The image of `i₀` is the kernel of `i₁`. -/
  exact : Function.Exact i₀ i₁
  /-- The second ambient module is injective. -/
  moduleInjective : Module.Injective R Q₁
  /-- The image of `i₁`, equivalently of the induced cokernel embedding, is essential in `Q₁`. -/
  isEssential_range : IsEssential (LinearMap.range i₁)

namespace IsMinimalInjectiveCopresentation

variable {i₀ : M →ₗ[R] Q₀} {i₁ : Q₀ →ₗ[R] Q₁}

/-- The map `Q₀ / range(i₀) → Q₁` induced by the second map of an injective copresentation. -/
def cokernelMap (h : IsMinimalInjectiveCopresentation i₀ i₁) :
    Q₀ ⧸ LinearMap.range i₀ →ₗ[R] Q₁ :=
  (LinearMap.range i₀).liftQ i₁ (LinearMap.exact_iff.mp h.exact).ge

/-- The induced cokernel map agrees with `i₁` on representatives. -/
@[simp]
theorem cokernelMap_mk (h : IsMinimalInjectiveCopresentation i₀ i₁) (x : Q₀) :
    h.cokernelMap (Submodule.Quotient.mk x) = i₁ x :=
  Submodule.liftQ_apply _ _ _

/-- The induced cokernel map has the same range as the displayed second map. -/
@[simp]
theorem range_cokernelMap (h : IsMinimalInjectiveCopresentation i₀ i₁) :
    LinearMap.range h.cokernelMap = LinearMap.range i₁ :=
  Submodule.range_liftQ _ _ _

/-- The induced map `Q₀ / range(i₀) → Q₁` is the second injective envelope in a minimal
injective copresentation. -/
theorem isInjectiveEnvelope_cokernelMap (h : IsMinimalInjectiveCopresentation i₀ i₁) :
    IsInjectiveEnvelope h.cokernelMap where
  moduleInjective := h.moduleInjective
  injective := LinearMap.injective_range_liftQ_of_exact h.exact
  isEssential_range := h.range_cokernelMap.symm ▸ h.isEssential_range

/-- Construct a minimal injective copresentation from an injective envelope of `M`, an exact
continuation, and an injective envelope of the resulting cokernel. -/
theorem _root_.TauCeti.IsInjectiveEnvelope.isMinimalInjectiveCopresentation
    (h₀ : IsInjectiveEnvelope i₀) (hexact : Function.Exact i₀ i₁)
    (h₁ : IsInjectiveEnvelope
      ((LinearMap.range i₀).liftQ i₁ (LinearMap.exact_iff.mp hexact).ge)) :
    IsMinimalInjectiveCopresentation i₀ i₁ where
  isInjectiveEnvelope := h₀
  exact := hexact
  moduleInjective := h₁.moduleInjective
  isEssential_range := by
    rw [← Submodule.range_liftQ (LinearMap.range i₀) i₁]
    exact h₁.isEssential_range

/-- If the module being copresented is already injective, then the first structure map is an
isomorphism. -/
theorem i₀_bijective_of_moduleInjective [Small.{w₀} R] [Small.{v} R]
    [Module.Injective R M] (h : IsMinimalInjectiveCopresentation i₀ i₁) :
    Function.Bijective i₀ := by
  obtain ⟨e, he⟩ := h.isInjectiveEnvelope.exists_linearEquiv
    (isInjectiveEnvelope_id (R := R) (M := M))
  constructor
  · exact h.isInjectiveEnvelope.injective
  · intro y
    refine ⟨e y, e.injective ?_⟩
    simpa using LinearMap.congr_fun he (e y)

/-- A minimal injective copresentation of an injective module has zero second map. -/
theorem i₁_eq_zero_of_moduleInjective [Small.{w₀} R] [Small.{v} R]
    [Module.Injective R M] (h : IsMinimalInjectiveCopresentation i₀ i₁) : i₁ = 0 :=
  (LinearMap.surjective_iff_eq_zero_of_exact h.exact).mp
    h.i₀_bijective_of_moduleInjective.surjective

/-- The second injective term of a minimal copresentation of an injective module is a zero
module. -/
theorem subsingleton_Q₁_of_moduleInjective [Small.{w₀} R] [Small.{v} R]
    [Module.Injective R M] (h : IsMinimalInjectiveCopresentation i₀ i₁) : Subsingleton Q₁ := by
  apply (isEssential_bot_iff (R := R) (M := Q₁)).mp
  simpa [h.i₁_eq_zero_of_moduleInjective] using h.isEssential_range

section Uniqueness

variable {Q₀' : Type w₀'} {Q₁' : Type w₁'}
  [AddCommGroup Q₀'] [Module R Q₀'] [AddCommGroup Q₁'] [Module R Q₁']
  {i₀' : M →ₗ[R] Q₀'} {i₁' : Q₀' →ₗ[R] Q₁'}

/-- **Uniqueness of minimal injective copresentations.** Two copresentations of the same module
are isomorphic in both injective degrees, by equivalences commuting with both structure maps. -/
theorem exists_linearEquiv [Small.{w₀} R] [Small.{w₀'} R]
    [Small.{w₁} R] [Small.{w₁'} R]
    (h : IsMinimalInjectiveCopresentation i₀ i₁)
    (h' : IsMinimalInjectiveCopresentation i₀' i₁') :
    ∃ (e₀ : Q₀ ≃ₗ[R] Q₀') (e₁ : Q₁ ≃ₗ[R] Q₁'),
      (e₀ : Q₀ →ₗ[R] Q₀') ∘ₗ i₀ = i₀' ∧
        (e₁ : Q₁ →ₗ[R] Q₁') ∘ₗ i₁ = i₁' ∘ₗ (e₀ : Q₀ →ₗ[R] Q₀') := by
  obtain ⟨e₀, he₀⟩ := h.isInjectiveEnvelope.exists_linearEquiv h'.isInjectiveEnvelope
  have hrange : (LinearMap.range i₀).map (e₀ : Q₀ →ₗ[R] Q₀') = LinearMap.range i₀' := by
    rw [← LinearMap.range_comp, he₀]
  let eCoker : (Q₀ ⧸ LinearMap.range i₀) ≃ₗ[R] (Q₀' ⧸ LinearMap.range i₀') :=
    Submodule.Quotient.equiv _ _ e₀ hrange
  have heCoker_range : IsEssential (LinearMap.range (eCoker :
      (Q₀ ⧸ LinearMap.range i₀) →ₗ[R] (Q₀' ⧸ LinearMap.range i₀'))) := by
    rw [LinearEquiv.range]
    exact isEssential_top
  have htarget : IsInjectiveEnvelope
      (h'.cokernelMap ∘ₗ (eCoker :
        (Q₀ ⧸ LinearMap.range i₀) →ₗ[R] (Q₀' ⧸ LinearMap.range i₀'))) :=
    h'.isInjectiveEnvelope_cokernelMap.comp eCoker.injective heCoker_range
  obtain ⟨e₁, he₁⟩ := h.isInjectiveEnvelope_cokernelMap.exists_linearEquiv htarget
  refine ⟨e₀, e₁, he₀, ?_⟩
  ext x
  have heCoker_mk : eCoker (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (e₀ x) : Q₀' ⧸ LinearMap.range i₀') := by
    simp [eCoker, Submodule.Quotient.equiv_apply]
  calc
    e₁ (i₁ x) = e₁ (h.cokernelMap (Submodule.Quotient.mk x)) :=
      congrArg e₁ (h.cokernelMap_mk x).symm
    _ = h'.cokernelMap (eCoker (Submodule.Quotient.mk x)) :=
      LinearMap.congr_fun he₁ _
    _ = h'.cokernelMap (Submodule.Quotient.mk (e₀ x)) := by rw [heCoker_mk]
    _ = i₁' (e₀ x) := h'.cokernelMap_mk (e₀ x)

end Uniqueness

end IsMinimalInjectiveCopresentation

end TauCeti
