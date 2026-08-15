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

Both rest on the minimality packaged in `TauCeti.IsSuperfluous.surjective_of_surjective_comp`: a
map into the source of a cover whose composite with the cover is onto is itself onto, the kernel of
a cover being too small for the image of such a map to miss it. This is the sense in which the
superfluous-kernel condition makes a cover *minimal*; the same statement read backwards is
`TauCeti.isProjectiveCover_iff_forall_surjective`, which says that the covers of `M` are exactly
the essential epimorphisms onto `M` from a projective module.

The first fact is that a projective cover receives every projective presentation: if `Q` is
projective and `g : Q →ₗ[R] M` is surjective, then `g` factors as `f ∘ₗ h` with `h : Q →ₗ[R] P`
**surjective** (`TauCeti.IsProjectiveCover.exists_surjective`). The second is that a projective
cover is unique: any two projective covers of `M` differ by a linear equivalence commuting with the
covering maps (`TauCeti.IsProjectiveCover.exists_linearEquiv`). Uniqueness is what makes "the"
projective cover a well-defined object, and hence what makes the Cartan matrix `Cᵢⱼ = [Pᵢ : Sⱼ]` of
a finite-dimensional algebra well defined.

*Existence* of projective covers is a separate matter: it holds over a semiperfect (in particular
a finite-dimensional) algebra and is not proved here. Nothing below assumes it; every statement is
conditional on a cover being given.

## Main definitions

* `TauCeti.IsProjectiveCover`: `f : P →ₗ[R] M` is surjective, `P` is projective, and `ker f` is
  superfluous.

## Main results

* `TauCeti.isProjectiveCover_id`: a projective module is its own projective cover.
* `TauCeti.isProjectiveCover_iff_forall_surjective`: a surjection from a projective module is a
  projective cover exactly when it is an essential epimorphism.
* `TauCeti.IsProjectiveCover.exists_surjective`: every surjection onto `M` from a projective module
  factors through a projective cover by a surjection.
* `TauCeti.IsProjectiveCover.bijective_of_comp_eq` and
  `TauCeti.IsProjectiveCover.exists_linearEquiv`: **uniqueness**, first as bijectivity of any
  comparison map between two covers and then as the existence of an isomorphism over `M`.
* `TauCeti.IsProjectiveCover.postcomp`: composing a projective cover with a surjection that itself
  has superfluous kernel again gives a projective cover.
* `TauCeti.IsProjectiveCover.ker_le_jacobson`: the kernel of a projective cover lies in the radical
  of the covering module.
* `TauCeti.isProjectiveCover_mkQ_iff`: the concrete family of covers, `P ↠ P ⧸ N` is a projective
  cover of a projective `P` exactly when `N` is superfluous; over a coatomic submodule lattice
  `TauCeti.isProjectiveCover_mkQ_iff_le_jacobson` reads this off the radical, so that `R ↠ R ⧸ I`
  is a projective cover exactly when `I ≤ Ring.jacobson R`.

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
superfluous. The superfluous kernel says exactly that no proper submodule of the source still
surjects onto `M`; see `TauCeti.isProjectiveCover_iff_forall_surjective`. -/
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

section AddCommGroup

variable {R : Type u} {M : Type v} {P : Type w} {Q : Type w'}
  [Semiring R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q]

/-- **Projective covers are the essential epimorphisms from a projective module.** A surjection
`f : P →ₗ[R] M` from a projective module is a projective cover exactly when every map into `P`
whose composite with `f` is onto is itself onto. -/
theorem isProjectiveCover_iff_forall_surjective [Module.Projective R P] {f : P →ₗ[R] M}
    (hf : Function.Surjective f) :
    IsProjectiveCover f ↔
      ∀ {P' : Type w} [AddCommMonoid P'] [Module R P'] (h : P' →ₗ[R] P),
        Function.Surjective (f ∘ₗ h) → Function.Surjective h := by
  rw [← isSuperfluous_ker_iff_forall_surjective hf]
  exact ⟨fun hcov => hcov.isSuperfluous_ker, fun hker => ⟨‹_›, hf, hker⟩⟩

/-- **A projective cover receives every projective presentation.** A surjection onto `M` from a
projective module factors through a projective cover of `M`, by a surjection. -/
theorem IsProjectiveCover.exists_surjective [Module.Projective R Q] {f : P →ₗ[R] M}
    (hf : IsProjectiveCover f) {g : Q →ₗ[R] M} (hg : Function.Surjective g) :
    ∃ h : Q →ₗ[R] P, f ∘ₗ h = g ∧ Function.Surjective h := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf.surjective
  exact ⟨h, hh, hf.isSuperfluous_ker.surjective_of_surjective_comp (by rw [hh]; exact hg)⟩

/-- **Uniqueness of the projective cover, in comparison-map form.** A map between the sources of
two projective covers of `M` that commutes with the covering maps is automatically an
isomorphism. -/
theorem IsProjectiveCover.bijective_of_comp_eq {P' : Type*} [AddCommGroup P'] [Module R P']
    {f : P →ₗ[R] M} {f' : P' →ₗ[R] M} (hf : IsProjectiveCover f) (hf' : IsProjectiveCover f')
    {h : P →ₗ[R] P'} (hcomp : f' ∘ₗ h = f) : Function.Bijective h := by
  -- Surjectivity is minimality of the target cover.
  have hsurj : Function.Surjective h :=
    hf'.isSuperfluous_ker.surjective_of_surjective_comp (by rw [hcomp]; exact hf.surjective)
  refine ⟨?_, hsurj⟩
  -- For injectivity, split `h` using projectivity of the target.
  have hkerle : LinearMap.ker h ≤ LinearMap.ker f := hcomp ▸ LinearMap.ker_le_ker_comp h f'
  have hproj : Module.Projective R P' := hf'.projective
  obtain ⟨σ, hσ⟩ := h.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hsplit : Function.LeftInverse h σ := fun y => by simpa using LinearMap.congr_fun hσ y
  -- The range of the splitting complements `ker h ≤ ker f`, which is superfluous, so it is
  -- everything; a splitting that is itself onto is a two-sided inverse.
  have hsup : LinearMap.ker h ⊔ LinearMap.range σ = ⊤ := by
    rw [sup_comm, ← Submodule.comap_map_eq, ← LinearMap.range_comp, hσ, LinearMap.range_id,
      Submodule.comap_top]
  have hσsurj : Function.Surjective σ :=
    LinearMap.range_eq_top.mp ((hf.isSuperfluous_ker.mono hkerle).eq_top_of_sup_eq_top hsup)
  exact (hsplit.rightInverse_of_surjective hσsurj).injective

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
projective cover. -/
theorem IsProjectiveCover.postcomp {N : Type*} [AddCommGroup N] [Module R N] {f : P →ₗ[R] M}
    (hf : IsProjectiveCover f) {g : M →ₗ[R] N} (hg : Function.Surjective g)
    (hgker : IsSuperfluous (LinearMap.ker g)) : IsProjectiveCover (g ∘ₗ f) where
  projective := hf.projective
  surjective := hg.comp hf.surjective
  isSuperfluous_ker := by
    -- The composite kernel is the preimage of `ker g`, and preimages of superfluous submodules
    -- along a surjection with superfluous kernel are superfluous.
    rw [LinearMap.ker_comp]
    exact hgker.comap hf.surjective hf.isSuperfluous_ker

end AddCommGroup

section Ring

variable {R : Type u} {M : Type v} {P : Type w}
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

/-- The kernel of a projective cover lies in the radical of the covering module, being
superfluous. -/
theorem IsProjectiveCover.ker_le_jacobson {f : P →ₗ[R] M} (hf : IsProjectiveCover f) :
    LinearMap.ker f ≤ Module.jacobson R P :=
  hf.isSuperfluous_ker.le_jacobson

/-! ### Quotients

The quotient maps of a projective module are the source of concrete projective covers. Since `R` is
free, hence projective, `R ⧸ I` is covered by `R` exactly when the left ideal `I` is small in `R`,
that is contained in the Jacobson radical; over a local ring this covers the residue field by
`R`. -/

/-- **When the quotient map of a projective module is a projective cover.** The quotient map
`P →ₗ[R] P ⧸ N` of a projective module is a projective cover precisely when `N` is superfluous. -/
@[simp]
theorem isProjectiveCover_mkQ_iff [Module.Projective R P] {N : Submodule R P} :
    IsProjectiveCover N.mkQ ↔ IsSuperfluous N := by
  refine ⟨fun h => Submodule.ker_mkQ N ▸ h.isSuperfluous_ker, fun hN => ?_⟩
  exact
    { projective := ‹_›
      surjective := N.mkQ_surjective
      isSuperfluous_ker := by rwa [Submodule.ker_mkQ] }

/-- Over a module with coatomic submodule lattice the quotient map of a projective module is a
projective cover precisely when the submodule divided out lies in the radical. For the regular
module this says that `R →ₗ[R] R ⧸ I` is a projective cover precisely when `I ≤ Ring.jacobson R`. -/
theorem isProjectiveCover_mkQ_iff_le_jacobson [Module.Projective R P]
    [IsCoatomic (Submodule R P)] {N : Submodule R P} :
    IsProjectiveCover N.mkQ ↔ N ≤ Module.jacobson R P :=
  isProjectiveCover_mkQ_iff.trans isSuperfluous_iff_le_jacobson

end Ring

end TauCeti
