/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import TauCeti.Algebra.Module.Submodule.Essential

/-!
# Injective envelopes

An **injective envelope** of a module `M` is an embedding `f : M →ₗ[R] Q` into an injective module
whose image is essential in `Q` (`TauCeti.IsEssential`). This is the notion dual to the projective
cover of `TauCeti/Algebra/Module/ProjectiveCover.lean`; Mathlib has injective objects but no
injective envelopes, and this file supplies the predicate together with the two facts everything
downstream rests on.

Both rest on the minimality packaged in `TauCeti.IsEssential.injective_of_injective_comp`: a map
out of the target of an envelope whose composite with the envelope is injective is itself
injective, the image of an envelope being too large for the kernel of such a map to avoid it. This
is the sense in which the essential-image condition makes an envelope *minimal*, and read backwards
it is `TauCeti.isInjectiveEnvelope_iff_forall_injective`: the envelopes of `M` are exactly the
essential monomorphisms from `M` into an injective module.

The first fact is that an essential extension maps into every embedding into an injective module:
if `Q'` is injective and `g : M →ₗ[R] Q'` is injective, then `g` factors as `h ∘ₗ f` with
`h : Q →ₗ[R] Q'` **injective** (`TauCeti.IsEssential.exists_injective`, stated at the
essential-monomorphism level its proof uses and specialized to an envelope through
`TauCeti.IsInjectiveEnvelope.isEssential_range`). The second is that an injective envelope is
unique: any two injective envelopes of `M` differ by a linear equivalence commuting with the
structure maps (`TauCeti.IsInjectiveEnvelope.exists_linearEquiv`). Uniqueness is what makes "the"
injective envelope a well-defined object.

*Existence* of injective envelopes is a separate matter, and is not proved here; nothing below
assumes it, every statement being conditional on an envelope being given. Over a finite-dimensional
algebra the indecomposable injectives arise as the envelopes of the simple modules.

## Universes

Mathlib's `Module.Injective` states its extension property only for source and target in the
universe of the injective module, and the universe-polymorphic form
`Module.Injective.extension_property` costs a `Small.{·} R` hypothesis on the ring. That hypothesis
is carried here on exactly the results that extend a map along an embedding, once per module used
as an extension target; it is automatic whenever `R` and that module live in the same universe.

## Main definitions

* `TauCeti.IsInjectiveEnvelope`: `f : M →ₗ[R] Q` is injective, `Q` is an injective module, and the
  range of `f` is essential.

## Main results

* `TauCeti.isInjectiveEnvelope_id`: an injective module is its own injective envelope.
* `TauCeti.isInjectiveEnvelope_iff_forall_injective`: an embedding into an injective module is an
  injective envelope exactly when it is an essential monomorphism.
* `TauCeti.IsEssential.exists_injective`: every embedding of `M` into an injective module receives
  an essential extension of `M`, in particular an injective envelope, by an embedding.
* `TauCeti.IsInjectiveEnvelope.bijective_of_comp_eq` and
  `TauCeti.IsInjectiveEnvelope.exists_linearEquiv`: **uniqueness**, first as bijectivity of any
  comparison map between two envelopes and then as the existence of an isomorphism under `M`.
* `TauCeti.IsInjectiveEnvelope.comp`: precomposing an injective envelope with an embedding that
  itself has essential range again gives an injective envelope.
* `TauCeti.isInjectiveEnvelope_subtype_iff`: the concrete family of envelopes, `N ↪ Q` is an
  injective envelope of a submodule `N` of an injective `Q` exactly when `N` is essential; over an
  atomic submodule lattice `TauCeti.isEssential_iff_forall_atom_le` reads this off the simple
  submodules.

## References

This implements the injective-envelope half of the "projective covers and injective envelopes"
bullet of Layer 3 of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`
("dually `injectiveEnvelope M`"), whose projective half is
`TauCeti/Algebra/Module/ProjectiveCover.lean`. As on the projective side, the bullet is not
discharged by this file: existence of envelopes, and hence a canonical `injectiveEnvelope M`
chosen by it, remains.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.5, and T. Y. Lam, *Lectures on Modules and Rings*, §3.
-/

public section

namespace TauCeti

universe u v w w'

section Basic

variable {R : Type u} {M : Type v} {Q : Type w}
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]

/-- An **injective envelope** of `M`: an embedding into an injective module whose range is
essential. The essential range is the minimality of the envelope: it says exactly that no proper
submodule of `Q` containing the image can be split off, equivalently that every map out of `Q`
whose composite with `f` is injective is injective already
(`TauCeti.isInjectiveEnvelope_iff_forall_injective`). -/
structure IsInjectiveEnvelope (f : M →ₗ[R] Q) : Prop where
  /-- The ambient module is injective. -/
  moduleInjective : Module.Injective R Q
  /-- The structure map is an embedding. -/
  injective : Function.Injective f
  /-- Minimality: the range is essential, so the envelope cannot be shrunk. -/
  isEssential_range : IsEssential (LinearMap.range f)

/-- An injective module is its own injective envelope, along the identity. -/
theorem isInjectiveEnvelope_id [Module.Injective R M] :
    IsInjectiveEnvelope (LinearMap.id : M →ₗ[R] M) where
  moduleInjective := ‹_›
  injective := Function.injective_id
  isEssential_range := by
    rw [LinearMap.range_id]
    exact isEssential_top

/-- **Injective envelopes are the essential monomorphisms into an injective module.** An embedding
`f : M →ₗ[R] Q` into an injective module is an injective envelope exactly when every map out of `Q`
whose composite with `f` is injective is itself injective. -/
theorem isInjectiveEnvelope_iff_forall_injective [Module.Injective R Q] {f : M →ₗ[R] Q}
    (hf : Function.Injective f) :
    IsInjectiveEnvelope f ↔
      ∀ {Q' : Type w} [AddCommGroup Q'] [Module R Q'] (h : Q →ₗ[R] Q'),
        Function.Injective (h ∘ₗ f) → Function.Injective h := by
  rw [← isEssential_range_iff_forall_injective hf]
  exact ⟨fun henv => henv.isEssential_range, fun hess => ⟨‹_›, hf, hess⟩⟩

/-- **An essential embedding maps into every embedding into an injective module.** An embedding
`f : M →ₗ[R] Q` with essential range receives every embedding of `M` into an injective module, by
an embedding. Injectivity of `Q` plays no part, so this holds of any essential extension of `M`;
applied through `TauCeti.IsInjectiveEnvelope.isEssential_range` it is the universal property of the
injective envelope. -/
theorem IsEssential.exists_injective [Small.{w'} R] {Q' : Type w'} [AddCommGroup Q']
    [Module R Q'] [Module.Injective R Q'] {f : M →ₗ[R] Q}
    (hrange : IsEssential (LinearMap.range f)) (hf : Function.Injective f)
    {g : M →ₗ[R] Q'} (hg : Function.Injective g) :
    ∃ h : Q →ₗ[R] Q', h ∘ₗ f = g ∧ Function.Injective h := by
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R Q' M Q f hf g
  exact ⟨h, hh, hrange.injective_of_injective_comp (by rw [hh]; exact hg)⟩

/-- **Uniqueness of the injective envelope, in comparison-map form.** A map from the target of an
injective envelope of `M` to an essential extension of `M` that commutes with the structure maps is
automatically an isomorphism; the target need only be an essential extension, not itself an
envelope. -/
theorem IsInjectiveEnvelope.bijective_of_comp_eq [Small.{w} R] {Q' : Type*} [AddCommGroup Q']
    [Module R Q'] {f : M →ₗ[R] Q} {f' : M →ₗ[R] Q'} (hf : IsInjectiveEnvelope f)
    (hf'inj : Function.Injective f') (hf'range : IsEssential (LinearMap.range f'))
    {h : Q →ₗ[R] Q'} (hcomp : h ∘ₗ f = f') :
    Function.Bijective h := by
  -- Injectivity is minimality of the source envelope.
  have hinj : Function.Injective h :=
    hf.isEssential_range.injective_of_injective_comp (by rw [hcomp]; exact hf'inj)
  refine ⟨hinj, ?_⟩
  -- For surjectivity, retract `h` using injectivity of its source.
  have hQ : Module.Injective R Q := hf.moduleInjective
  obtain ⟨σ, hσ⟩ := Module.Injective.extension_property R Q Q Q' h hinj LinearMap.id
  -- The range of `h` contains the essential range of `f'`, so the same minimality makes the
  -- retraction injective, and an injective retraction of an embedding is a two-sided inverse.
  have hrange : IsEssential (LinearMap.range h) :=
    hf'range.mono (by
      rw [← hcomp, LinearMap.range_comp]
      exact LinearMap.map_le_range)
  have hσinj : Function.Injective σ :=
    hrange.injective_of_injective_comp (f := h) (by rw [hσ]; exact fun _ _ hab => hab)
  intro y
  exact ⟨σ y, hσinj (by simpa using LinearMap.congr_fun hσ (σ y))⟩

/-- **Uniqueness of the injective envelope.** Two injective envelopes of the same module are
related by a linear equivalence commuting with the structure maps; in particular the ambient module
of an injective envelope is well defined up to isomorphism. -/
theorem IsInjectiveEnvelope.exists_linearEquiv [Small.{w} R] [Small.{w'} R] {Q' : Type w'}
    [AddCommGroup Q'] [Module R Q'] {f : M →ₗ[R] Q} {f' : M →ₗ[R] Q'}
    (hf : IsInjectiveEnvelope f) (hf' : IsInjectiveEnvelope f') :
    ∃ e : Q ≃ₗ[R] Q', (e : Q →ₗ[R] Q') ∘ₗ f = f' := by
  have hQ' : Module.Injective R Q' := hf'.moduleInjective
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R Q' M Q f hf.injective f'
  refine ⟨LinearEquiv.ofBijective h
    (hf.bijective_of_comp_eq hf'.injective hf'.isEssential_range hh), ?_⟩
  ext m
  simpa using LinearMap.congr_fun hh m

/-- Precomposing an injective envelope with an embedding whose range is essential again gives an
injective envelope. -/
theorem IsInjectiveEnvelope.comp {N : Type*} [AddCommGroup N] [Module R N] {f : M →ₗ[R] Q}
    (hf : IsInjectiveEnvelope f) {g : N →ₗ[R] M} (hg : Function.Injective g)
    (hgrange : IsEssential (LinearMap.range g)) : IsInjectiveEnvelope (f ∘ₗ g) where
  moduleInjective := hf.moduleInjective
  injective := hf.injective.comp hg
  isEssential_range := by
    -- The composite range is the image of `range g`, and images of essential submodules along an
    -- embedding with essential range are essential.
    rw [LinearMap.range_comp]
    exact hgrange.map hf.injective hf.isEssential_range

/-! ### Submodules

The inclusions of an injective module are the source of concrete injective envelopes: a submodule
of an injective module is enveloped by it exactly when it is essential. -/

/-- **When the inclusion of a submodule of an injective module is an injective envelope.** The
inclusion `N →ₗ[R] Q` of a submodule of an injective module is an injective envelope precisely when
`N` is essential. -/
@[simp]
theorem isInjectiveEnvelope_subtype_iff [Module.Injective R Q] {N : Submodule R Q} :
    IsInjectiveEnvelope N.subtype ↔ IsEssential N := by
  refine ⟨fun h => Submodule.range_subtype N ▸ h.isEssential_range, fun hN => ?_⟩
  exact
    { moduleInjective := ‹_›
      injective := N.injective_subtype
      isEssential_range := by rwa [Submodule.range_subtype] }

end Basic

end TauCeti
