/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Algebra.Module.ProjectiveCover

/-!
# Minimal projective presentations

A **projective presentation** of a module `M` is an exact sequence `P₁ → P₀ → M → 0` with `P₀` and
`P₁` projective. It is **minimal** when both of its maps are as small as they can be: `P₀ → M` is a
projective cover (`TauCeti.IsProjectiveCover`) and `P₁` covers the syzygy `ker (P₀ → M)`, again as
a projective cover. This file supplies the predicate `TauCeti.IsMinimalProjectivePresentation` and
the comparison theorem that makes it useful.

The minimality is packaged as two superfluous kernels rather than as a nested
`TauCeti.IsProjectiveCover`, because the second cover is a map into the submodule `ker p₀` and
carrying its corestriction around in the definition would make every consumer corestrict as well.
`TauCeti.IsMinimalProjectivePresentation.isProjectiveCover_codRestrict` reads the definition back
in the corestricted form, and `TauCeti.IsProjectiveCover.isMinimalProjectivePresentation` builds a
minimal presentation from a pair of covers, so the two readings are interchangeable.

The theorem the notion exists for is that a minimal projective presentation is a *quotient* of every
projective presentation: given any projective presentation of the same module there are
**surjections** from it onto the minimal one commuting with both maps
(`TauCeti.IsMinimalProjectivePresentation.exists_surjective`). Applying that to a second minimal
presentation and reading the surjections back through the uniqueness of projective covers makes
them isomorphisms, so a minimal projective presentation is unique up to isomorphism of the whole
diagram (`TauCeti.IsMinimalProjectivePresentation.exists_linearEquiv`). That uniqueness is what
lets a construction be made *from* a minimal presentation: the Auslander-Reiten transpose `Tr M`,
the cokernel of `Hom(−, A)` applied to a minimal projective presentation of `M`, is well defined
because of it.

*Existence* is a separate matter, exactly as for projective covers: it is a condition on the ring
(over a semiperfect ring every finitely generated module has a projective cover, and over an Artin
algebra, where finitely generated modules are noetherian and so the syzygy is again finitely
generated, iterating that gives a minimal presentation). Nothing here assumes it; every statement
is conditional on a presentation being given, and
`TauCeti.IsProjectiveCover.isMinimalProjectivePresentation` is the step that turns two covers into
one presentation.

The file is layered by the coefficients each part needs, as
`TauCeti/Algebra/Module/ProjectiveCover.lean` is. The predicate itself and the two cover-form
readings of it need only a semiring and additive monoids. The degeneration over a projective
module needs the presented module to be an additive group, that being what uniqueness of covers
needs. The comparison and uniqueness theorems need a ring, which the syzygy forces rather than the
proofs choosing it: they apply the cover statements of `TauCeti/Algebra/Module/ProjectiveCover.lean`
to the syzygy `ker p₀` as the *covered* module, and those are stated for a covered module that is
an additive group. A submodule of an additive group is itself an additive group only once the
scalars form a ring — `Submodule.addCommGroup` is a `[Ring R]` instance, and over a semiring a
submodule need not be closed under negation, as `ℕ ⊆ ℤ` shows — so over a semiring
`↥(LinearMap.ker p₀)` carries no `AddCommGroup` structure at all.

## Main definitions

* `TauCeti.IsMinimalProjectivePresentation p₁ p₀`: `p₀` is a projective cover of `M`, the source of
  `p₁` is projective, `range p₁ = ker p₀`, and `ker p₁` is superfluous.

## Main results

* `TauCeti.IsMinimalProjectivePresentation.exact`: the two maps do form a presentation.
* `TauCeti.IsMinimalProjectivePresentation.isProjectiveCover_codRestrict` and
  `TauCeti.IsProjectiveCover.isMinimalProjectivePresentation`: minimality read as `p₁` being a
  projective cover of the syzygy, in both directions.
* `TauCeti.IsMinimalProjectivePresentation.exists_surjective`: **a minimal projective presentation
  is a quotient of every projective presentation**, by a pair of surjections commuting with the
  maps.
* `TauCeti.IsMinimalProjectivePresentation.bijective_of_comp_eq` and
  `TauCeti.IsMinimalProjectivePresentation.exists_linearEquiv`: **uniqueness**, first as
  bijectivity of any pair of comparison maps between two minimal presentations and then as an
  isomorphism of the whole diagram. The accompanying isomorphism of syzygies needs neither
  left-hand map and so is stated one layer down, as
  `TauCeti.IsProjectiveCover.nonempty_linearEquiv_ker` for the two right-hand covers.
* `TauCeti.IsMinimalProjectivePresentation.bijective_of_projective`,
  `TauCeti.IsMinimalProjectivePresentation.eq_zero_of_projective` and
  `TauCeti.IsMinimalProjectivePresentation.subsingleton_of_projective`: over a projective module
  the presentation degenerates, `P₀ ≅ M` and `P₁ = 0`.
* `TauCeti.IsMinimalProjectivePresentation.range_le_jacobson` and
  `TauCeti.IsMinimalProjectivePresentation.ker_le_jacobson`: both kernels sit inside the radical,
  the standard quantitative form of minimality.

## References

This implements the projective half of sublayer 6B, "minimal projective/injective presentations",
of Layer 6 of
[the quiver-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md),
the prerequisite it names for the transpose `Tr` and the Auslander-Reiten translate `τ = D Tr`
("it is well-defined only up to projectives, through minimal presentations and duality on
finite-dimensional modules"). The injective co-presentation is the remaining half, as the injective
envelope is the remaining half of `TauCeti/Algebra/Module/ProjectiveCover.lean`.

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section I.2 and Section IV.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Section I.5 and Section IV.2.
-/

public section

namespace TauCeti

universe u v w w' x x'

section Semiring

variable {R : Type u} {M : Type v} {P₀ : Type w} {P₁ : Type w'}
  [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid P₀] [Module R P₀]
  [AddCommMonoid P₁] [Module R P₁]

/-- A **minimal projective presentation** `P₁ → P₀ → M → 0` of `M`: the sequence is exact at `P₀`
and at `M`, both sources are projective, and both maps are minimal — `p₀` is a projective cover of
`M`, and `p₁` has superfluous kernel, so that it is a projective cover of the syzygy `ker p₀`
(`TauCeti.IsMinimalProjectivePresentation.isProjectiveCover_codRestrict`).

Only the exactness at `P₀`, `range p₁ = ker p₀`, is recorded: exactness at `M` is the surjectivity
of `p₀`, which the projective cover already carries. -/
structure IsMinimalProjectivePresentation (p₁ : P₁ →ₗ[R] P₀) (p₀ : P₀ →ₗ[R] M) : Prop where
  /-- The right-hand map is a projective cover of the presented module. -/
  isProjectiveCover : IsProjectiveCover p₀
  /-- The left-hand source is projective. -/
  projective : Module.Projective R P₁
  /-- Exactness at `P₀`. -/
  range_eq_ker : LinearMap.range p₁ = LinearMap.ker p₀
  /-- Minimality of the left-hand map: it covers the syzygy without slack. -/
  isSuperfluous_ker : IsSuperfluous (LinearMap.ker p₁)

namespace IsMinimalProjectivePresentation

variable {p₁ : P₁ →ₗ[R] P₀} {p₀ : P₀ →ₗ[R] M}

/-- The presenting map of a minimal projective presentation is onto. -/
theorem surjective (h : IsMinimalProjectivePresentation p₁ p₀) : Function.Surjective p₀ :=
  h.isProjectiveCover.surjective

/-- **A minimal projective presentation is a presentation**: the sequence `P₁ → P₀ → M` is exact at
`P₀`. -/
theorem exact (h : IsMinimalProjectivePresentation p₁ p₀) : Function.Exact p₁ p₀ :=
  LinearMap.exact_iff.mpr h.range_eq_ker.symm

/-- The left-hand map of a presentation lands in the syzygy. -/
theorem apply_mem_ker (h : IsMinimalProjectivePresentation p₁ p₀) (x : P₁) :
    p₁ x ∈ LinearMap.ker p₀ := by
  simpa using LinearMap.congr_fun h.exact.linearMap_comp_eq_zero x

/-- **Minimality of the left-hand map, in cover form**: corestricted to the syzygy `ker p₀`, the
map `p₁` is a projective cover of it. This is the reading of the definition that
`TauCeti.IsProjectiveCover.isMinimalProjectivePresentation` inverts. -/
theorem isProjectiveCover_codRestrict (h : IsMinimalProjectivePresentation p₁ p₀) :
    IsProjectiveCover (LinearMap.codRestrict (LinearMap.ker p₀) p₁ h.apply_mem_ker) where
  projective := h.projective
  surjective := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, h.range_eq_ker,
      Submodule.comap_subtype_self]
  isSuperfluous_ker := by
    rw [LinearMap.ker_codRestrict]
    exact h.isSuperfluous_ker

end IsMinimalProjectivePresentation

/-- **Two projective covers make a minimal projective presentation.** Given a projective cover `p₀`
of `M` and a projective cover `c` of its syzygy `ker p₀`, following `c` by the inclusion of the
syzygy presents `M` minimally. This is the only way a minimal presentation is ever built, so
existence of minimal presentations is exactly existence of the two covers. -/
theorem IsProjectiveCover.isMinimalProjectivePresentation {p₀ : P₀ →ₗ[R] M}
    (h₀ : IsProjectiveCover p₀) {c : P₁ →ₗ[R] LinearMap.ker p₀} (h₁ : IsProjectiveCover c) :
    IsMinimalProjectivePresentation ((LinearMap.ker p₀).subtype ∘ₗ c) p₀ where
  isProjectiveCover := h₀
  projective := h₁.projective
  range_eq_ker := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr h₁.surjective, Submodule.map_top,
      Submodule.range_subtype]
  isSuperfluous_ker := by
    have hker : LinearMap.ker ((LinearMap.ker p₀).subtype ∘ₗ c) = LinearMap.ker c := by
      ext x
      simp
    rw [hker]
    exact h₁.isSuperfluous_ker

/-- **A comparison of presentations descends to the syzygies.** If `f` is a surjection between the
middle terms of two presentations of `M` commuting with the two presenting maps `a₀` and `b₀`, then
the induced map `A₁ → ker b₀` on syzygies is again onto: a syzygy of the target is hit in the middle
term, and exactness of the source sequence lifts it back along `a₁`.

This is the step both comparison theorems below rest on, once for the presentation being compared
and once for the second minimal presentation. -/
private theorem surjective_codRestrict_comp {A : Type*} {A₁ : Type*} {B : Type*}
    [AddCommMonoid A] [Module R A] [AddCommMonoid A₁] [Module R A₁] [AddCommMonoid B] [Module R B]
    {a₀ : A →ₗ[R] M} {a₁ : A₁ →ₗ[R] A} {b₀ : B →ₗ[R] M} {f : A →ₗ[R] B}
    (hf : Function.Surjective f) (ha : LinearMap.range a₁ = LinearMap.ker a₀)
    (hcomp : b₀ ∘ₗ f = a₀) (hmem : ∀ z, (f ∘ₗ a₁) z ∈ LinearMap.ker b₀) :
    Function.Surjective (LinearMap.codRestrict (LinearMap.ker b₀) (f ∘ₗ a₁) hmem) := by
  have hbf : ∀ x, b₀ (f x) = a₀ x := fun x => LinearMap.congr_fun hcomp x
  intro y
  obtain ⟨u, hu⟩ := hf (y : B)
  have hu' : u ∈ LinearMap.range a₁ := by
    rw [ha]
    have hzero : b₀ (f u) = 0 := by rw [hu]; exact y.2
    simpa [hbf] using hzero
  obtain ⟨z, hz⟩ := hu'
  exact ⟨z, Subtype.ext (by simp [hz, hu])⟩

end Semiring

section Projective

variable {R : Type u} {M : Type v} {P₀ : Type w} {P₁ : Type w'}
  [Semiring R] [AddCommGroup M] [Module R M] [AddCommGroup P₀] [Module R P₀]
  [AddCommMonoid P₁] [Module R P₁]

namespace IsMinimalProjectivePresentation

variable {p₁ : P₁ →ₗ[R] P₀} {p₀ : P₀ →ₗ[R] M} [Module.Projective R M]

/-- **A projective module presents itself.** In a minimal projective presentation of a projective
module the presenting map is already an isomorphism, being a projective cover of a module that
covers itself. -/
theorem bijective_of_projective (h : IsMinimalProjectivePresentation p₁ p₀) :
    Function.Bijective p₀ :=
  h.isProjectiveCover.bijective_of_comp_eq isProjectiveCover_id (LinearMap.id_comp p₀)

/-- The syzygy of a projective module vanishes, so the left-hand map of a minimal projective
presentation of it is zero. -/
theorem eq_zero_of_projective (h : IsMinimalProjectivePresentation p₁ p₀) : p₁ = 0 := by
  have hker : LinearMap.ker p₀ = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun m hm => h.bijective_of_projective.injective (by simpa using hm)
  have hrange : LinearMap.range p₁ = ⊥ := by rw [h.range_eq_ker, hker]
  exact LinearMap.range_eq_bot.mp hrange

/-- Minimality forces the left-hand source of a minimal projective presentation of a projective
module to vanish as well, not merely the map out of it. -/
theorem subsingleton_of_projective (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton P₁ := by
  have hker : LinearMap.ker p₁ = ⊤ := by
    rw [h.eq_zero_of_projective]
    exact LinearMap.ker_zero
  have hsup := h.isSuperfluous_ker
  rw [hker] at hsup
  exact isSuperfluous_top_iff.mp hsup

end IsMinimalProjectivePresentation

end Projective

section Ring

variable {R : Type u} {M : Type v} {P₀ : Type w} {P₁ : Type w'}
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P₀] [Module R P₀]
  [AddCommGroup P₁] [Module R P₁]

namespace IsMinimalProjectivePresentation

variable {p₁ : P₁ →ₗ[R] P₀} {p₀ : P₀ →ₗ[R] M}

section Comparison

variable {Q₀ : Type x} {Q₁ : Type x'}

/-- **A minimal projective presentation is a quotient of every projective presentation.** If
`Q₁ →ₗ Q₀ ↠ M` is any projective presentation of `M` — projective sources, exact at `Q₀`, onto `M`
— then it maps onto a minimal projective presentation of `M` by a pair of **surjections**
commuting with both maps.

Both surjectivities are the minimality of the target: the first is that a projective cover receives
every projective presentation by a surjection, and the second is the same statement for the induced
map on syzygies, which is onto because the first one is. -/
theorem exists_surjective [AddCommMonoid Q₀] [Module R Q₀] [Module.Projective R Q₀]
    [AddCommMonoid Q₁] [Module R Q₁] [Module.Projective R Q₁]
    (h : IsMinimalProjectivePresentation p₁ p₀) {q₁ : Q₁ →ₗ[R] Q₀} {q₀ : Q₀ →ₗ[R] M}
    (hq₀ : Function.Surjective q₀) (hq : LinearMap.range q₁ = LinearMap.ker q₀) :
    ∃ (f₀ : Q₀ →ₗ[R] P₀) (f₁ : Q₁ →ₗ[R] P₁),
      p₀ ∘ₗ f₀ = q₀ ∧ f₀ ∘ₗ q₁ = p₁ ∘ₗ f₁ ∧
        Function.Surjective f₀ ∧ Function.Surjective f₁ := by
  obtain ⟨f₀, hf₀, hf₀surj⟩ := h.isProjectiveCover.exists_surjective hq₀
  have hpf : ∀ y, p₀ (f₀ y) = q₀ y := fun y => LinearMap.congr_fun hf₀ y
  -- The induced map on the two syzygies, corestricted to `ker p₀`.
  have hmem : ∀ z : Q₁, (f₀ ∘ₗ q₁) z ∈ LinearMap.ker p₀ := by
    intro z
    have hz : q₁ z ∈ LinearMap.ker q₀ := by rw [← hq]; exact LinearMap.mem_range_self q₁ z
    simpa [hpf] using hz
  obtain ⟨f₁, hf₁, hf₁surj⟩ := h.isProjectiveCover_codRestrict.exists_surjective
    (surjective_codRestrict_comp hf₀surj hq hf₀ hmem)
  refine ⟨f₀, f₁, hf₀, LinearMap.ext fun z => ?_, hf₀surj, hf₁surj⟩
  have hval := congrArg Subtype.val (LinearMap.congr_fun hf₁ z)
  simpa using hval.symm

variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]

/-- **Uniqueness of the minimal projective presentation, in comparison-map form.** A pair of maps
between the sources of two minimal projective presentations of `M` that commutes with the presenting
maps and with the two left-hand maps consists of two isomorphisms; no further hypothesis on the pair
is needed.

Each is bijective because it compares two projective covers of the same module — of `M` on the
right, and of the syzygy on the left, the two syzygies being identified by the right-hand map. -/
theorem bijective_of_comp_eq {q₁ : Q₁ →ₗ[R] Q₀} {q₀ : Q₀ →ₗ[R] M}
    (h : IsMinimalProjectivePresentation p₁ p₀)
    (h' : IsMinimalProjectivePresentation q₁ q₀) {f₀ : P₀ →ₗ[R] Q₀} {f₁ : P₁ →ₗ[R] Q₁}
    (hcomp : q₀ ∘ₗ f₀ = p₀) (hsquare : f₀ ∘ₗ p₁ = q₁ ∘ₗ f₁) :
    Function.Bijective f₀ ∧ Function.Bijective f₁ := by
  have hbij₀ : Function.Bijective f₀ :=
    h.isProjectiveCover.bijective_of_comp_eq h'.isProjectiveCover hcomp
  have hqf : ∀ y, q₀ (f₀ y) = p₀ y := fun y => LinearMap.congr_fun hcomp y
  -- The left-hand comparison, read as a map into the syzygy of the second presentation.
  have hmem : ∀ z : P₁, (f₀ ∘ₗ p₁) z ∈ LinearMap.ker q₀ := by
    intro z
    have hz : p₁ z ∈ LinearMap.ker p₀ := h.apply_mem_ker z
    simpa [hqf] using hz
  have hkerf₀ : LinearMap.ker f₀ = ⊥ := LinearMap.ker_eq_bot.mpr hbij₀.injective
  have hcover : IsProjectiveCover (LinearMap.codRestrict (LinearMap.ker q₀) (f₀ ∘ₗ p₁) hmem) := by
    refine ⟨h.projective,
      surjective_codRestrict_comp hbij₀.surjective h.range_eq_ker hcomp hmem, ?_⟩
    rw [LinearMap.ker_codRestrict, LinearMap.ker_comp, hkerf₀, Submodule.comap_bot]
    exact h.isSuperfluous_ker
  refine ⟨hbij₀, hcover.bijective_of_comp_eq h'.isProjectiveCover_codRestrict ?_⟩
  refine LinearMap.ext fun z => Subtype.ext ?_
  simpa using (LinearMap.congr_fun hsquare z).symm

/-- **Uniqueness of the minimal projective presentation.** Two minimal projective presentations of
the same module are isomorphic as diagrams: there are linear equivalences of both sources
commuting with the presenting map and with the two syzygy maps.

The comparison surjections come from
`TauCeti.IsMinimalProjectivePresentation.exists_surjective`, and
`TauCeti.IsMinimalProjectivePresentation.bijective_of_comp_eq` turns them into isomorphisms. -/
theorem exists_linearEquiv {q₁ : Q₁ →ₗ[R] Q₀} {q₀ : Q₀ →ₗ[R] M}
    (h : IsMinimalProjectivePresentation p₁ p₀)
    (h' : IsMinimalProjectivePresentation q₁ q₀) :
    ∃ (e₀ : P₀ ≃ₗ[R] Q₀) (e₁ : P₁ ≃ₗ[R] Q₁),
      q₀ ∘ₗ (e₀ : P₀ →ₗ[R] Q₀) = p₀ ∧
        (e₀ : P₀ →ₗ[R] Q₀) ∘ₗ p₁ = q₁ ∘ₗ (e₁ : P₁ →ₗ[R] Q₁) := by
  have hP₀ : Module.Projective R P₀ := h.isProjectiveCover.projective
  have hP₁ : Module.Projective R P₁ := h.projective
  obtain ⟨f₀, f₁, hcomp, hsquare, -, -⟩ := h'.exists_surjective h.surjective h.range_eq_ker
  obtain ⟨hbij₀, hbij₁⟩ := h.bijective_of_comp_eq h' hcomp hsquare
  exact ⟨LinearEquiv.ofBijective f₀ hbij₀, LinearEquiv.ofBijective f₁ hbij₁, hcomp, hsquare⟩

end Comparison

section Radical

/-- **Minimality, quantitatively, on the right**: the image of the left-hand map — equivalently the
syzygy — lies in the radical of `P₀`. A presentation whose image escaped the radical could be
shrunk. -/
theorem range_le_jacobson (h : IsMinimalProjectivePresentation p₁ p₀) :
    LinearMap.range p₁ ≤ Module.jacobson R P₀ :=
  h.range_eq_ker ▸ h.isProjectiveCover.ker_le_jacobson

/-- **Minimality, quantitatively, on the left**: the kernel of the left-hand map lies in the
radical of `P₁`. -/
theorem ker_le_jacobson (h : IsMinimalProjectivePresentation p₁ p₀) :
    LinearMap.ker p₁ ≤ Module.jacobson R P₁ :=
  h.isSuperfluous_ker.le_jacobson

end Radical

end IsMinimalProjectivePresentation

end Ring

end TauCeti
