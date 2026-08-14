/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.Algebra.Module.Submodule.Superfluous

/-!
# Projective covers

A **projective cover** of a module `M` is a surjection `f : P →ₗ[R] M` from a projective module
whose kernel is superfluous in `P` (`TauCeti.IsSuperfluous`). Mathlib has projective objects but no
projective covers; this file supplies the predicate and the two facts everything downstream rests
on.

Both rest on the minimality packaged in `TauCeti.IsSuperfluous.surjective_of_surjective_comp`: over
a ring, a map into the source of a cover whose composite with the cover is onto is itself onto, the
kernel of a cover being too small for the image of such a map to miss it. This is the sense in
which the superfluous-kernel condition makes a cover *minimal*, and it is why everything but the
definition and `TauCeti.isProjectiveCover_id` below is stated over a ring.

The first is that a projective cover receives every projective presentation: if `Q` is projective
and `g : Q →ₗ[R] M` is surjective, then `g` factors as `f ∘ₗ h` with `h : Q →ₗ[R] P` **surjective**
(`TauCeti.IsProjectiveCover.exists_surjective`). The second is that a projective cover is unique:
any two projective covers of `M` differ by a linear equivalence commuting with the covering maps
(`TauCeti.IsProjectiveCover.exists_linearEquiv`). Uniqueness is what makes "the" projective cover
a well-defined object, and hence what makes the Cartan matrix `Cᵢⱼ = [Pᵢ : Sⱼ]` of a
finite-dimensional algebra well defined.

*Existence* of projective covers is a separate matter: it holds over a semiperfect (in particular
a finite-dimensional) algebra and is not proved here. Nothing below assumes it; every statement is
conditional on a cover being given.

## Main definitions

* `TauCeti.IsProjectiveCover`: `f : P →ₗ[R] M` is surjective, `P` is projective, and `ker f` is
  superfluous.

## Main results

* `TauCeti.isProjectiveCover_id`: a projective module is its own projective cover.
* `TauCeti.IsProjectiveCover.exists_surjective`: every surjection onto `M` from a projective module
  factors through a projective cover by a surjection.
* `TauCeti.IsProjectiveCover.bijective_of_comp_eq` and
  `TauCeti.IsProjectiveCover.exists_linearEquiv`: **uniqueness**, first as bijectivity of any
  comparison map between two covers and then as the existence of an isomorphism over `M`.
* `TauCeti.IsProjectiveCover.comp`: composing a projective cover with a surjection that itself has
  superfluous kernel again gives a projective cover.
* `TauCeti.IsProjectiveCover.ker_le_jacobson`: the kernel of a projective cover lies in the radical
  of the covering module.
* `TauCeti.isProjectiveCover_mkQ_iff`: the concrete family of covers, `R ↠ R ⧸ I` is a projective
  cover exactly when `I` lies in the Jacobson radical of `R`.

## References

This implements the projective-cover half of the "projective covers and injective envelopes"
bullet of Layer 3 of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`
("`projectiveCover M`: a projective `P` with an essential epimorphism `P ↠ M` (superfluous
kernel), unique up to isomorphism"). Existence over a semiperfect algebra, and the dual injective
envelope, are the remaining halves.

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.5.
-/

public section

namespace TauCeti

universe u v w w'

section Semiring

variable {R : Type u} {M : Type v} {P : Type w}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]

/-- A **projective cover** of `M`: a surjection from a projective module whose kernel is
superfluous. Over a ring the superfluous kernel says exactly that no proper submodule of the source
still surjects onto `M`; see `TauCeti.IsSuperfluous.surjective_of_surjective_comp`. -/
structure IsProjectiveCover (f : P →ₗ[R] M) : Prop where
  /-- The covering module is projective. -/
  projective : Module.Projective R P
  /-- The covering map is onto. -/
  surjective : Function.Surjective f
  /-- Minimality: the kernel is superfluous, so the cover cannot be shrunk. -/
  isSuperfluous_ker : IsSuperfluous (LinearMap.ker f)

/-- A projective module is its own projective cover, along the identity. -/
theorem isProjectiveCover_id [Module.Projective R M] :
    IsProjectiveCover (LinearMap.id : M →ₗ[R] M) where
  projective := ‹_›
  surjective := Function.surjective_id
  isSuperfluous_ker := by
    rw [LinearMap.ker_id]
    exact isSuperfluous_bot

end Semiring

section Ring

variable {R : Type u} {M : Type v} {P : Type w} {Q : Type w'}
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q]

/-- The kernel of a projective cover lies in the radical of the covering module, being
superfluous. -/
theorem IsProjectiveCover.ker_le_jacobson {f : P →ₗ[R] M} (hf : IsProjectiveCover f) :
    LinearMap.ker f ≤ Module.jacobson R P :=
  hf.isSuperfluous_ker.le_jacobson

/-- **A projective cover receives every projective presentation.** A surjection onto `M` from a
projective module factors through a projective cover of `M`, by a surjection. -/
theorem IsProjectiveCover.exists_surjective [Module.Projective R Q] {f : P →ₗ[R] M}
    (hf : IsProjectiveCover f) {g : Q →ₗ[R] M} (hg : Function.Surjective g) :
    ∃ h : Q →ₗ[R] P, f ∘ₗ h = g ∧ Function.Surjective h := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf.surjective
  exact ⟨h, hh, hf.isSuperfluous_ker.surjective_of_surjective_comp (by rw [hh]; exact hg)⟩

/-- **Uniqueness of the projective cover, in comparison-map form.** A map between the sources of
two projective covers of `M` that commutes with the covering maps is automatically an isomorphism.

It is onto by minimality of the target cover. For injectivity, split it using projectivity of the
target: the splitting has range complementing `ker h`, and `ker h ≤ ker f` is superfluous, so that
range is everything; a splitting whose range is everything has trivial intersection with `ker h`,
which therefore vanishes. -/
theorem IsProjectiveCover.bijective_of_comp_eq {P' : Type*} [AddCommGroup P'] [Module R P']
    {f : P →ₗ[R] M} {f' : P' →ₗ[R] M} (hf : IsProjectiveCover f) (hf' : IsProjectiveCover f')
    {h : P →ₗ[R] P'} (hcomp : f' ∘ₗ h = f) : Function.Bijective h := by
  have hsurj : Function.Surjective h :=
    hf'.isSuperfluous_ker.surjective_of_surjective_comp (by rw [hcomp]; exact hf.surjective)
  refine ⟨?_, hsurj⟩
  have hkerle : LinearMap.ker h ≤ LinearMap.ker f := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [← hcomp]
    simp [hx]
  have hproj : Module.Projective R P' := hf'.projective
  obtain ⟨σ, hσ⟩ := h.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hsplit : ∀ y : P', h (σ y) = y := fun y => by simpa using LinearMap.congr_fun hσ y
  have hsup : LinearMap.ker h ⊔ LinearMap.range σ = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun p => ?_
    have hmem : p - σ (h p) ∈ LinearMap.ker h := by
      simp [LinearMap.mem_ker, map_sub, hsplit]
    simpa using Submodule.add_mem_sup hmem (LinearMap.mem_range_self σ (h p))
  have hrange : LinearMap.range σ = ⊤ := (hf.isSuperfluous_ker.mono hkerle).eq_top hsup
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro x hx
  have hxrange : x ∈ LinearMap.range σ := by rw [hrange]; exact Submodule.mem_top
  obtain ⟨y, rfl⟩ := hxrange
  have hy : y = 0 := by rw [← hsplit y]; exact hx
  rw [hy, map_zero]

/-- **Uniqueness of the projective cover.** Two projective covers of the same module are related by
a linear equivalence commuting with the covering maps; in particular the covering module of a
projective cover is well defined up to isomorphism. -/
theorem IsProjectiveCover.exists_linearEquiv {P' : Type*} [AddCommGroup P'] [Module R P']
    {f : P →ₗ[R] M} {f' : P' →ₗ[R] M} (hf : IsProjectiveCover f) (hf' : IsProjectiveCover f') :
    ∃ e : P ≃ₗ[R] P', f' ∘ₗ (e : P →ₗ[R] P') = f := by
  have hproj : Module.Projective R P := hf.projective
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f' f hf'.surjective
  refine ⟨LinearEquiv.ofBijective h (hf.bijective_of_comp_eq hf' hh), ?_⟩
  ext p
  simpa using LinearMap.congr_fun hh p

/-- Composing a projective cover with a surjection whose kernel is superfluous again gives a
projective cover: the composite kernel is the preimage of the second kernel, and
`TauCeti.IsSuperfluous.comap` says that is superfluous. -/
theorem IsProjectiveCover.comp {N : Type*} [AddCommGroup N] [Module R N] {f : P →ₗ[R] M}
    (hf : IsProjectiveCover f) {g : M →ₗ[R] N} (hg : Function.Surjective g)
    (hgker : IsSuperfluous (LinearMap.ker g)) : IsProjectiveCover (g ∘ₗ f) where
  projective := hf.projective
  surjective := hg.comp hf.surjective
  isSuperfluous_ker := by
    rw [LinearMap.ker_comp]
    exact hgker.comap hf.surjective hf.isSuperfluous_ker

/-! ### Cyclic modules

The quotient maps of the regular module are the source of concrete projective covers: `R` is free,
hence projective, so `R ⧸ I` is covered by `R` exactly when `I` is small in `R`, that is contained
in the Jacobson radical. Over a local ring this covers the residue field by `R`. -/

/-- **The projective cover of a cyclic module.** The quotient map `R →ₗ[R] R ⧸ I` is a projective
cover precisely when `I` lies in the Jacobson radical of `R`. -/
@[simp]
theorem isProjectiveCover_mkQ_iff {I : Submodule R R} :
    IsProjectiveCover I.mkQ ↔ I ≤ Ring.jacobson R := by
  constructor
  · intro h
    have := h.isSuperfluous_ker
    rw [Submodule.ker_mkQ] at this
    exact this.le_jacobson
  · intro hI
    exact
      { projective := inferInstance
        surjective := I.mkQ_surjective
        isSuperfluous_ker := by
          rw [Submodule.ker_mkQ]
          exact isSuperfluous_of_le_jacobson hI }

end Ring

end TauCeti
