/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.UniversalProperty
public import TauCeti.RingTheory.Huber.Completion
public import TauCeti.RingTheory.Localization.Completion

/-!
# The completion `A⟨T/s⟩`

The separated completion of `Aₛ` under `locTopology` is Wedhorn's `A⟨T/s⟩`. It is a Huber ring,
and the universal property of `LocalizationTopology.UniversalProperty` extends across it for
complete Hausdorff targets.

## Main definitions

* `locUniformSpace P T s S` : the uniformity `locTopology` determines, packaged so that
  `UniformSpace.Completion S` can be written down.
* `toCompletionLoc P T s S` : the structure map `A → A⟨T/s⟩`.
* `localizationUniform P T s S` : the pair `localization`, transported to the topology
  `locUniformSpace` induces, so that no statement about `A⟨T/s⟩` carries the transport.
* `completionLocalization P T s S` : the pair of definition `A⟨T/s⟩` carries.

## Main results

* `locUniformSpace_toTopologicalSpace`: the topology `locUniformSpace` induces is `locTopology`.
  This is what a proof rewrites against, so no body in this file needs exposing.
* `isUniformAddGroup_locUniformSpace` and `isTopologicalRing_locUniformSpace`: the two companions
  of `locUniformSpace`. Since `locTopology` is not an instance, a statement about `A⟨T/s⟩` has to
  name its structures; these three declarations are what it names.
* `localizationUniform_ringOfDefinition` and `mem_localizationUniform_idealOfDefinition`, with
  `completionLocalization_ringOfDefinition` and `mem_completionLocalization_idealOfDefinition`:
  the completed pair's API, reducing to the concrete `D` and `J`.
* `continuous_toCompletionLoc`: the structure map `A → A⟨T/s⟩` is continuous.
* `isHuberRing_completion_locTopology`: `A⟨T/s⟩` is a Huber ring — the completed pair above is a
  pair of definition for it.
* `isTateRing_completion_locTopology_of_isTopologicallyNilpotent`: a topologically nilpotent
  denominator becomes a pseudouniformiser, so the completed localization is Tate.
* `existsUnique_continuous_ringHom_completion_locTopology`: the universal property, for complete
  Hausdorff targets.
* `completion_locTopology_ringHom_ext_of_continuous`: two continuous ring homomorphisms out of
  `A⟨T/s⟩` agreeing on `A` are equal, so a map out of `A⟨T/s⟩` is determined by its restriction to
  `A`. Unlike the universal property this needs no hypothesis on `s` or the fractions — those
  govern which maps exist, not when two agree — and its target need only be a semiring carrying a
  Hausdorff topology.
* `eq_id_of_comp_toCompletionLoc_eq_self` and `eq_comp_of_comp_toCompletionLoc_eq`: two
  corollaries of the previous item, saying that a continuous map compatible with the structure
  maps is forced to be the identity, respectively the composite. These are **not** roadmap Layer
  3.1's identity and composition laws for restriction maps: no restriction map is constructed
  here, and these are conditional uniqueness statements about whatever compatible maps happen to
  exist. They are what those laws will be proved *from* once the restriction maps themselves are
  built.

## Provenance

`A⟨T/s⟩` and its universal property are this repository's own, built on the localisation topology
of `LocalizationTopology.Basic`, which is the AINTLIB port — see that module's Provenance section
for the source file and commit.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51, §5.6
* `Mathlib.Topology.Algebra.Valued.ValuationTopology`, `Valued.mk'` — the model for the instance
  setup here. It layers `IsTopologicalAddGroup.rightUniformSpace` and
  `isUniformAddGroup_of_addCommGroup` on a topology built from a `RingSubgroupsBasis`, passing
  that topology positionally because it is not an instance; `locTopology` is in the same position.
-/

open Pointwise Topology

namespace TauCeti.Huber

open TauCeti.Localization

public section

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-! ### The completion `A⟨T/s⟩` -/

/-- **The canonical uniformity on `Aₛ`**, the one its topology determines.

`locTopology` is not an instance, so a consumer of the completion has to name the uniform structure
explicitly. This packages the construction, and it takes **three** declarations to state anything
about `A⟨T/s⟩`: `locUniformSpace` makes `UniformSpace.Completion S` well-formed,
`isUniformAddGroup_locUniformSpace` makes the completion an additive group, and
`isTopologicalRing_locUniformSpace` is what its ring structure is inferred from. The first two
alone do not suffice.

`locUniformSpace_toTopologicalSpace` is the characteristic property — the topology it induces is
`locTopology` — so the body is not exposed and a proof rewrites against that lemma instead.

It is *the* uniformity, not merely one compatible with the topology:
`IsUniformAddGroup.rightUniformSpace_eq` identifies it with any uniformity making `Aₛ` a uniform
additive group, so a consumer arriving with its own such structure rewrites rather than
transports. -/
@[instance_reducible]
noncomputable def locUniformSpace (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    [IsTopologicalRing A] : UniformSpace S :=
  letI tS := locTopology P T s S hden
  letI := isTopologicalRing_locTopology P T s S hden
  @IsTopologicalAddGroup.rightUniformSpace S _ tS _

/-- The topology `locUniformSpace` induces is `locTopology`. This is the characteristic property
of the packaged uniformity: it lets a statement made at one be rewritten to the other. -/
@[simp]
theorem locUniformSpace_toTopologicalSpace [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    (locUniformSpace P T s S hden).toTopologicalSpace = locTopology P T s S hden := (rfl)

/-- `Aₛ` is a uniform additive group for `locUniformSpace`. The companion of `locUniformSpace`:
the two together are what `UniformSpace.Completion S` needs. -/
theorem isUniformAddGroup_locUniformSpace [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    @IsUniformAddGroup S (locUniformSpace P T s S hden) _ :=
  letI := isTopologicalRing_locTopology P T s S hden
  @isUniformAddGroup_of_addCommGroup _ _ (locTopology P T s S hden) _

/-- `Aₛ` is a topological ring for the topology `locUniformSpace` induces. Stated at that
topology rather than at `locTopology`, so that it applies where the packaged uniformity is in
scope. -/
theorem isTopologicalRing_locUniformSpace [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    IsTopologicalRing S :=
  isTopologicalRing_locTopology P T s S hden

/-- `Aₛ` is a Huber ring for the topology `locUniformSpace` induces. The third companion of
`locUniformSpace`, alongside the two above. A consumer working at the uniformity can reach the
`locTopology`-stated form by transporting along `locUniformSpace_toTopologicalSpace`; this
restates it so that it does not have to, which is what makes `powerBoundedSubring S` convenient to
name there. -/
theorem isHuberRing_locUniformSpace [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsHuberRing S :=
  isHuberRing_locTopology P T s S hden

/-- The image of a power-bounded element of `A` is power-bounded in `Aₛ`, at the uniformity's
topology. `isPowerBounded_algebraMap_of_isPowerBounded` states this at `locTopology`; this is the
same fact restated so that a consumer holding the uniformity need not transport along
`locUniformSpace_toTopologicalSpace` itself. -/
theorem isPowerBounded_algebraMap_of_isPowerBounded_locUniformSpace [IsTopologicalRing A]
    (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {a : A} (ha : IsPowerBounded a) :
    letI := locUniformSpace P T s S hden
    IsPowerBounded (algebraMap A S a) :=
  isPowerBounded_algebraMap_of_isPowerBounded P T s S hden ha

/-- Each distinguished fraction `t/s` is power-bounded in `Aₛ`, at the uniformity's topology.
The `locUniformSpace` companion of `isPowerBounded_divBy`. -/
theorem isPowerBounded_divBy_locUniformSpace [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {t : A} (ht : t ∈ T) :
    letI := locUniformSpace P T s S hden
    IsPowerBounded (divBy t s : S) :=
  isPowerBounded_divBy P T s S hden ht

/-- **The structure map `A → A⟨T/s⟩`**, the localisation map followed by the completion map. This
is the canonical ring homomorphism the universal property extends. -/
noncomputable def toCompletionLoc [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    A →+* UniformSpace.Completion S :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  (UniformSpace.Completion.coeRingHom).comp (algebraMap A S)

/-- The structure map is the localisation map followed by the completion map. The body of
`toCompletionLoc` is not exported, so this is how a consumer computes with it. -/
@[simp]
theorem toCompletionLoc_apply [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (a : A) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    toCompletionLoc P T s S hden a = (algebraMap A S a : UniformSpace.Completion S) := (rfl)


/-- The localisation pair `localization`, transported along `locUniformSpace_toTopologicalSpace`
to the topology the packaged uniformity induces.

`localization` is stated at `locTopology` and the completion is taken at `locUniformSpace`. The
two topologies are equal, but not syntactically, so the transport has to be named: naming it here
keeps the cast out of every statement about `A⟨T/s⟩` below. -/
noncomputable def localizationUniform [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    PairOfDefinition S :=
  (locUniformSpace_toTopologicalSpace P T s S hden).symm ▸ localization P T s S hden

/-- The ring of definition of `localizationUniform` is `D`, as for `localization`: the transport
is along an equality of topologies and `ringOfDefinition` is a `Subring S`, which does not depend
on one. This is what makes the completed pair's API reduce to the concrete data. -/
@[simp]
theorem localizationUniform_ringOfDefinition [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    (localizationUniform P T s S hden).ringOfDefinition = locSubring P T s S :=
  localization_ringOfDefinition P T s S hden

/-- Membership in the ideal of definition of `localizationUniform` is membership in `J`, as for
`localization`. With `localizationUniform_ringOfDefinition` this reduces the completed pair's
characteristic lemmas to the concrete `D` and `J`. -/
@[simp]
theorem mem_localizationUniform_idealOfDefinition [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    {x : letI := locUniformSpace P T s S hden;
      (localizationUniform P T s S hden).ringOfDefinition} :
    letI := locUniformSpace P T s S hden
    x ∈ (localizationUniform P T s S hden).idealOfDefinition ↔
      (⟨x, by rw [← localizationUniform_ringOfDefinition P T s S hden]; exact x.2⟩ :
        locSubring P T s S) ∈ locIdeal P T s S :=
  mem_localization_idealOfDefinition P T s S hden

/-- **The pair of definition on `A⟨T/s⟩`**, the completion of the pair `localization` carries on
`Aₛ`. This is the completed counterpart of `localization`, and it is what makes `A⟨T/s⟩` Huber.

Its ring of definition and ideal of definition are characterised by
`completionLocalization_ringOfDefinition` and `mem_completionLocalization_idealOfDefinition`,
which are how a consumer computes with it — the body is not exposed. -/
noncomputable def completionLocalization [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    PairOfDefinition (UniformSpace.Completion S) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  (localizationUniform P T s S hden).completion

/-- The ring of definition of `completionLocalization` is the one `PairOfDefinition.completion`
supplies for the localisation pair: the closure of the image of `D`. -/
@[simp]
theorem completionLocalization_ringOfDefinition [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completionLocalization P T s S hden).ringOfDefinition =
      (localizationUniform P T s S hden).completionRingOfDefinition := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  exact PairOfDefinition.completion_ringOfDefinition _

/-- Membership in the ideal of definition of `A⟨T/s⟩` is membership in `J · D̂`.

Stated as a membership characterisation rather than an equation because the type of
`idealOfDefinition` depends on `ringOfDefinition`, which the opaque body of `completionLocalization`
does not expose — the same shape as `PairOfDefinition.mem_completion_idealOfDefinition`, which
this delegates to. -/
@[simp]
theorem mem_completionLocalization_idealOfDefinition [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ {x : (completionLocalization P T s S hden).ringOfDefinition},
      x ∈ (completionLocalization P T s S hden).idealOfDefinition ↔
        (⟨x, by
            rw [← completionLocalization_ringOfDefinition P T s S hden]; exact x.2⟩ :
          (localizationUniform P T s S hden).completionRingOfDefinition)
            ∈ (localizationUniform P T s S hden).completionIdeal := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro x
  exact PairOfDefinition.mem_completion_idealOfDefinition (localizationUniform P T s S hden)

/-- **The structure map `A → A⟨T/s⟩` is continuous**: it is the continuous localisation map
followed by the completion map. -/
theorem continuous_toCompletionLoc [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (toCompletionLoc P T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have h : Continuous fun a : A ↦ ((algebraMap A S a : S) : UniformSpace.Completion S) :=
    (UniformSpace.Completion.continuous_coe (α := S)).comp
      (continuous_algebraMap_locTopology P T s S hden)
  exact h.congr fun a ↦ (toCompletionLoc_apply P T s S hden a).symm

/-- **`A⟨T/s⟩` is a Huber ring**: the separated completion of `Aₛ` under `locTopology` —
Wedhorn's `A⟨T/s⟩` — carries a pair of definition.

The statement introduces `locUniformSpace`, `isUniformAddGroup_locUniformSpace` and
`isTopologicalRing_locUniformSpace`, because `locTopology` is not an instance and
`UniformSpace.Completion S` is not well-formed without them. -/
theorem isHuberRing_completion_locTopology [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsHuberRing (UniformSpace.Completion S) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  ⟨⟨completionLocalization P T s S hden⟩⟩

/-- A topologically nilpotent denominator becomes a pseudouniformiser in the completed
localization: it is inverted by localization and remains topologically nilpotent under the
continuous structure map. -/
theorem isPseudoUniformizer_toCompletionLoc [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (hs : IsTopologicallyNilpotent s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsPseudoUniformizer (toCompletionLoc P T s S hden s) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [isPseudoUniformizer_iff]
  refine ⟨?_, hs.map (continuous_toCompletionLoc P T s S hden)⟩
  rw [toCompletionLoc_apply]
  exact (IsLocalization.Away.algebraMap_isUnit s).map UniformSpace.Completion.coeRingHom

/-- The completed localization at a topologically nilpotent denominator is a Tate ring. -/
theorem isTateRing_completion_locTopology_of_isTopologicallyNilpotent [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (hs : IsTopologicallyNilpotent s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsTateRing (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := isHuberRing_completion_locTopology P T s S hden
  exact ⟨⟨toCompletionLoc P T s S hden s,
    isPseudoUniformizer_toCompletionLoc P T s S hden hs⟩⟩

/-- **Maps out of `A⟨T/s⟩` are determined on `A`.** Two continuous ring homomorphisms into a
semiring carrying a Hausdorff topology that agree after composing with the structure map
from `A` are equal.

This is `TauCeti.completion_localization_ringHom_ext_of_continuous` at `Submonoid.powers s`. The
bridge it crosses is the unexported body of `toCompletionLoc`, namely
`UniformSpace.Completion.coeRingHom.comp (algebraMap A S)`: reassociating that composition turns
`g.comp (toCompletionLoc …)` into `(g.comp coeRingHom).comp (algebraMap A S)`, which is the
hypothesis that lemma takes. Nothing is unfolded at the level of coercions — the argument stays
with bundled `RingHom`s throughout. Crossing the unexported body once here keeps it out of every
consumer. -/
theorem completion_locTopology_ringHom_ext_of_continuous [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    {B : Type*} [Semiring B] [TopologicalSpace B] [T2Space B] :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (g h : UniformSpace.Completion S →+* B), Continuous g → Continuous h →
      g.comp (toCompletionLoc P T s S hden) = h.comp (toCompletionLoc P T s S hden) → g = h := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro g h hg hh hcomp
  refine TauCeti.completion_localization_ringHom_ext_of_continuous (Submonoid.powers s) hg hh
    (RingHom.ext fun a ↦ ?_)
  exact congrArg (fun k : A →+* B ↦ k a) hcomp

/-- **The universal property of `A⟨T/s⟩`**, for complete Hausdorff targets: a ring homomorphism
`φ : A →+* B` continuous at zero, with `φ s` a unit and each fraction `φ t / φ s` power-bounded,
extends to the completion in exactly one continuous way.

The hypotheses are those of `existsUnique_continuous_ringHom_locTopology` together with `B`
complete and separated, which is what an extension across the completion requires. As there, the
condition on the fractions is sufficient and is not claimed to be necessary. -/
theorem existsUnique_continuous_ringHom_completion_locTopology {B : Type*} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) {φ : A →+* B}
    (hφ : ContinuousAt φ 0) (hs : IsUnit (φ s))
    (hpow : ∀ t ∈ T, IsPowerBounded (φ t * ↑hs.unit⁻¹)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* B,
      Continuous g ∧ g.comp (toCompletionLoc P T s S hden) = φ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  obtain ⟨f, ⟨hfc, hfe⟩, huniq⟩ :=
    existsUnique_continuous_ringHom_locTopology P T s S hden hφ hs hpow
  have hext : (UniformSpace.Completion.extensionHom f hfc).comp
      (toCompletionLoc P T s S hden) = φ := by
    ext a
    simpa [UniformSpace.Completion.extensionHom_coe, UniformSpace.Completion.coeRingHom] using
      congrArg (fun h => h a) hfe
  refine ⟨UniformSpace.Completion.extensionHom f hfc,
    ⟨UniformSpace.Completion.continuous_extension, hext⟩, fun g ⟨hgc, hge⟩ ↦ ?_⟩
  -- uniqueness is extensionality: both maps are continuous and agree after `toCompletionLoc`
  exact completion_locTopology_ringHom_ext_of_continuous P T s S hden g _ hgc
    UniformSpace.Completion.continuous_extension (hge.trans hext.symm)


/-- **The identity law.** A continuous ring endomorphism of `A⟨T/s⟩` fixing the structure map from
`A` is the identity, since the identity fixes it too.

As with the composition law below, this constructs no restriction map: it says that at most one
continuous endomorphism is compatible with the structure map, and names it. -/
theorem eq_id_of_comp_toCompletionLoc_eq_self [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S), Continuous g →
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T s S hden →
      g = RingHom.id (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro g hg hcomp
  refine completion_locTopology_ringHom_ext_of_continuous P T s S hden g (RingHom.id _) hg
    continuous_id ?_
  rw [RingHom.id_comp]
  exact hcomp

/-- **The composition law.** If `g` carries the structure map of `A⟨T/s⟩` to a map `φ'`, and `h`
carries `φ'` on to `φ''`, then any continuous `k` carrying the structure map to `φ''` is `h.comp g`.

Only the *source* is a completed localisation — that is where extensionality is applied — so the
middle and target objects are arbitrary topological semirings, with `φ'` and `φ''` the ring
homomorphisms out of `A` they are equipped with. At the roadmap's intended instance these are the
completed localisations of two further presentations and their structure maps, but nothing here
requires that, and no restriction map is constructed: this is a uniqueness statement about maps
compatible with the structure maps, not Layer 3.1's composition law for restriction maps. -/
theorem eq_comp_of_comp_toCompletionLoc_eq [IsTopologicalRing A] (P : PairOfDefinition A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    {B C : Type*} [Semiring B] [TopologicalSpace B] [Semiring C] [TopologicalSpace C] [T2Space C]
    (phi' : A →+* B) (phi'' : A →+* C) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (g : UniformSpace.Completion S →+* B), Continuous g →
      g.comp (toCompletionLoc P T s S hden) = phi' →
      ∀ (h : B →+* C), Continuous h → h.comp phi' = phi'' →
      ∀ (k : UniformSpace.Completion S →+* C), Continuous k →
      k.comp (toCompletionLoc P T s S hden) = phi'' →
      k = h.comp g := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro g hg hgc h hh hhc k hk hkc
  refine completion_locTopology_ringHom_ext_of_continuous P T s S hden k (h.comp g) hk
    (hh.comp hg) ?_
  rw [RingHom.comp_assoc, hgc, hhc]
  exact hkc

end PairOfDefinition

end

end TauCeti.Huber
