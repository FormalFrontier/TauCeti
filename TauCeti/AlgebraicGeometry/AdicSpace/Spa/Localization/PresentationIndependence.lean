/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty
public import TauCeti.RingTheory.Huber.LocalizationTopology.Presentation

/-!
# Comparison maps from a containment of rational subsets

`TauCeti.Huber.existsUnique_continuous_ringHom_of_refines` compares two coordinate rings when the
second presentation *refines* the first syntactically — `s'' = s * r` with every `t * r` a
numerator. Wedhorn's Proposition 8.2(1) asks for the comparison under the weaker, geometric
hypothesis that the rational subsets are *contained* in one another, and this file instantiates
Lemma 8.1 at a coordinate ring to get it.

**Neither result is yet Wedhorn's in the generality he states it.** Instantiating Lemma 8.1 at a
coordinate ring inherits what Lemma 8.1 asks of a target pair, and below that is two hypotheses
carried rather than derived: invertibility of the containing presentation's denominator `s` in
`A⟨T'/s'⟩`, and openness of the plus subring `A_U⁺`. Until both are discharged neither result may
be cited as the statement Wedhorn gives. See *The hypotheses both results carry*.

> (1) If `U' ⊆ U`, then there exists a unique continuous homomorphism `σ : A⟨T/s⟩ → A⟨T'/s'⟩`
> such that `σ ∘ ρ = ρ'`.

Wedhorn's entire proof is "follows immediately from Lemma 8.1", and so is the one here: the point
of `Spa` is that `Spa ρ'` already factors through `R(T'/s')`
(`spaComapLoc_mem_rationalSubset`), so a containment `R(T'/s') ⊆ R(T/s)` hands the geometric
hypothesis of Lemma 8.1 over directly.

Applying that in both directions to two presentations of the *same* rational subset gives
presentation independence under the same hypothesis: each composite fixes the structure map
from `A`, hence is the identity, so the two coordinate rings are canonically isomorphic. That
is the shape `TauCeti.Huber.presentationRingEquiv` has been waiting for — it produces the
isomorphism *given* comparison maps both ways, and nothing supplies them from an equality of
rational subsets. This file supplies them, assuming that each denominator is invertible in the
other presentation's coordinate ring and that the plus subrings are open.

## Main results

* `TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_rationalSubset_subset` :
  Wedhorn's Proposition 8.2(1) **for a target in which `s` is invertible and whose plus subring is
  open** — under those two hypotheses a containment of rational subsets induces a unique
  continuous comparison map. Wedhorn asks for neither, so this is not yet his statement.
* `TauCeti.ValuationSpectrum.presentationRingEquivOfEq` : presentation independence **under the
  same two hypotheses in each direction** — two presentations of the same rational subset then
  have canonically isomorphic coordinate rings.

`presentationRingEquivOfEq` is a `def`, so it comes with the lemmas that pin down what it is
without unfolding the proof term: `continuous_presentationRingEquivOfEq` and
`continuous_presentationRingEquivOfEq_symm`, which make it an isomorphism of *topological*
rings, and `presentationRingEquivOfEq_coe_comp_toCompletionLoc` together with its `symm`
counterpart, which say the isomorphism and its inverse commute with the structure maps from `A`.
That compatibility is what determines it, so a consumer needs nothing else.

## The hypotheses both results carry

Wedhorn's Proposition 7.52(1) is no longer among them. It landed in #4552 as
`TauCeti.ValuationSpectrum.mem_of_forall_vle_one` and is consumed inside Lemma 8.1, so
instantiating Lemma 8.1 at a coordinate ring no longer inherits it. What each instantiation does
inherit is what 7.52(1) asks of that coordinate ring as a *pair*:

* invertibility of `s`, the containing presentation's denominator, in the contained
  presentation's coordinate ring — carried rather than derived. This is step 1 of Lemma 8.1, and
  it is the *satisfiable* form of that step: an earlier revision of this file instead carried
  `hmax`, openness of the target's maximal ideals, which by `IsTateRing.isOpen_iff_eq_top` no
  nonzero Tate ring has — so it made both results vacuous on exactly the coordinate rings §8 is
  about. The Lemma 8.1 variant used here,
  `existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset`, takes the unit
  instead of `hmax`;
* openness of the plus subring `A_U⁺`, which is **not** proved anywhere on main and is the one
  remaining obligation of this file. It is a strictly smaller one than the `hmem` it replaces:
  `hmem` was "prove Wedhorn 7.52(1) at this coordinate ring", whereas this is a single concrete
  topological fact about a subring the repository already constructs. Integral closedness needs
  no hypothesis at all — `isIntegrallyClosedIn_completedPlusSubring` is an instance, because
  `completedPlusSubring` is *defined* as an integral closure.

The gap that remains is exactly the one
`TauCeti.RingTheory.Huber.LocalizationTopology.Restriction` already names: it records that the
refinement route "removes that dependency" precisely because a refining presentation makes the
fraction distinguished, so that `isPowerBounded_divBy` covers it — which a bare containment does
not. Everything else Lemma 8.1 asks of the target *is* discharged here from what is on main:
power-boundedness of the plus ring by `completedPlusSubring_le_powerBoundedSubring`, the Huber
structure by `isHuberRing_completion_locTopology`, and continuity by
`continuous_toCompletionLoc`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(1) and
  Lemma 8.1.

## Provenance

Developed here; nothing is ported. AINTLIB reaches presentation independence through a
height-one reduction resting on unproved bodies, which is not followed.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn's Proposition 8.2(1), for a target in which `s` is invertible and whose plus
subring is open**: under those two hypotheses, if the rational subset presented by `T'` over `s'`
is contained in the one presented by `T` over `s`, then exactly one continuous ring homomorphism
`A⟨T/s⟩ → A⟨T'/s'⟩` is compatible with the structure maps from `A`.

Wedhorn imposes neither hypothesis, so **this is not yet Proposition 8.2(1) in the generality he
states it**, and it should not be cited as that. The two are inherited from Lemma 8.1 and are
discussed in the module docstring.

This is the containment form of `TauCeti.Huber.existsUnique_continuous_ringHom_of_refines`, which
asks instead that the second presentation refine the first syntactically. The proof is Wedhorn's:
`Spa ρ'` factors through `R(T'/s')` by `spaComapLoc_mem_rationalSubset`, so the containment makes
it factor through `R(T/s)`, which is the hypothesis of Lemma 8.1.

The two hypotheses on the target are Lemma 8.1's, and neither is Proposition 7.52(1) — that is
now consumed inside Lemma 8.1 itself. The first is invertibility of `s` in `A⟨T'/s'⟩`, which is
Lemma 8.1's step 1 taken as a hypothesis rather than derived from openness of the maximal ideals;
the second is openness of the target's plus subring `A_U⁺`, which 7.52(1) asks of the pair and
which is not proved anywhere on main. Integral closedness of `A_U⁺` needs no hypothesis:
`isIntegrallyClosedIn_completedPlusSubring` is an instance. -/
theorem existsUnique_continuous_ringHom_of_rationalSubset_subset (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    IsUnit (toCompletionLoc P T' s' S' hden' s) →
    IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
      Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')) →
    ∃! σ : UniformSpace.Completion S →+* UniformSpace.Completion S',
      Continuous σ ∧
        σ.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := isHuberRing_completion_locTopology P T' s' S' hden'
  intro hs hopen'
  refine existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset
    P Aplus T s S hden (completedPlusSubring P Aplus T' s' S' hden')
    ⟨hopen', inferInstance,
      completedPlusSubring_le_powerBoundedSubring P Aplus hAplus T' s' S' hden'⟩
    (continuous_toCompletionLoc P T' s' S' hden').continuousAt hs fun w hw ↦ hsub ?_
  -- `Spa ρ'` lands in `R(T'/s')`; the containment carries it into `R(T/s)`
  simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P Aplus T' s' S' hden' ⟨w, hw⟩

/-- **Presentation independence, when each denominator is invertible in the other coordinate ring
and both plus subrings are open**: under those hypotheses, two presentations of the *same*
rational subset have canonically isomorphic coordinate rings.

As with Proposition 8.2(1) above, the unconditional statement is not proved here: the hypotheses
are inherited from Lemma 8.1 and Wedhorn asks for neither.

Wedhorn's Proposition 8.2(1) applies in both directions, and
`TauCeti.Huber.presentationRingEquiv` turns the two comparison maps into an isomorphism — each
composite is compatible with the structure map from `A`, hence is the identity. Supplying those
two maps from an equality of rational subsets is the step that `presentationRingEquiv`'s own
docstring calls "a separate step"; this takes that step.

Each direction carries the target-side hypotheses of Lemma 8.1, so there are two of each: the
primed pair for `A⟨T'/s'⟩` and the unprimed pair for `A⟨T/s⟩`. -/
noncomputable def presentationRingEquivOfEq (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    IsUnit (toCompletionLoc P T' s' S' hden' s) →
    IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
      Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')) →
    IsUnit (toCompletionLoc P T s S hden s') →
    IsOpen ((completedPlusSubring P Aplus T s S hden :
      Subring (UniformSpace.Completion S)) : Set (UniformSpace.Completion S)) →
    UniformSpace.Completion S ≃+* UniformSpace.Completion S' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := isHuberRing_completion_locTopology P T s S hden
  let _ := isHuberRing_completion_locTopology P T' s' S' hden'
  intro hs' hopen' hs hopen
  -- the comparison maps are *data*, so they are extracted with `Exists.choose`; `obtain` would
  -- be eliminating an `ExistsUnique` (a `Prop`) into `Type`
  have hg := existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T s S hden
    T' s' S' hden' heq.ge hs' hopen'
  have hh := existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T' s' S'
    hden' T s S hden heq.le hs hopen
  exact presentationRingEquiv P T s S hden T' s' S' hden' hg.choose hh.choose
    hg.choose_spec.1.1 hh.choose_spec.1.1 hg.choose_spec.1.2 hh.choose_spec.1.2

/-- The presentation-independence isomorphism is continuous. This is
`TauCeti.Huber.continuous_presentationRingEquiv` at the two comparison maps this file supplies. -/
theorem continuous_presentationRingEquivOfEq (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (hs' : IsUnit (toCompletionLoc P T' s' S' hden' s))
      (hopen' : IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
        Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')))
      (hs : IsUnit (toCompletionLoc P T s S hden s'))
      (hopen : IsOpen ((completedPlusSubring P Aplus T s S hden :
        Subring (UniformSpace.Completion S)) : Set (UniformSpace.Completion S))),
      Continuous (presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq
        hs' hopen' hs hopen) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro hs' hopen' hs hopen
  exact continuous_presentationRingEquiv P T s S hden T' s' S' hden' _ _ _ _ _ _

/-- The isomorphism is compatible with the structure maps from `A`, which is the property that
determines it. -/
theorem presentationRingEquivOfEq_coe_comp_toCompletionLoc
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (hs' : IsUnit (toCompletionLoc P T' s' S' hden' s))
      (hopen' : IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
        Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')))
      (hs : IsUnit (toCompletionLoc P T s S hden s'))
      (hopen : IsOpen ((completedPlusSubring P Aplus T s S hden :
        Subring (UniformSpace.Completion S)) : Set (UniformSpace.Completion S))),
      (((presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq
          hs' hopen' hs hopen : UniformSpace.Completion S ≃+* UniformSpace.Completion S') :
        UniformSpace.Completion S →+* UniformSpace.Completion S')).comp
          (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro hs' hopen' hs hopen
  exact presentationRingEquiv_coe_comp_toCompletionLoc P T s S hden T' s' S' hden' _ _ _ _ _ _

/-- The inverse is compatible with the structure maps the other way. -/
theorem presentationRingEquivOfEq_symm_coe_comp_toCompletionLoc
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (hs' : IsUnit (toCompletionLoc P T' s' S' hden' s))
      (hopen' : IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
        Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')))
      (hs : IsUnit (toCompletionLoc P T s S hden s'))
      (hopen : IsOpen ((completedPlusSubring P Aplus T s S hden :
        Subring (UniformSpace.Completion S)) : Set (UniformSpace.Completion S))),
      (((presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq
          hs' hopen' hs hopen).symm :
        UniformSpace.Completion S' ≃+* UniformSpace.Completion S) :
          UniformSpace.Completion S' →+* UniformSpace.Completion S).comp
          (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro hs' hopen' hs hopen
  refine RingHom.ext fun a ↦ ?_
  have hfwd := RingHom.congr_fun (presentationRingEquivOfEq_coe_comp_toCompletionLoc
    P Aplus hAplus T s S hden T' s' S' hden' heq hs' hopen' hs hopen) a
  simp only [RingHom.coe_comp, Function.comp_apply] at hfwd ⊢
  rw [← hfwd]
  exact RingEquiv.symm_apply_apply _ _

/-- The inverse of the presentation-independence isomorphism is continuous. Together with
`continuous_presentationRingEquivOfEq` this says the isomorphism is one of topological rings, so
a consumer never has to unfold it to move continuously in either direction. -/
theorem continuous_presentationRingEquivOfEq_symm
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*)
    [CommRing S] [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A) (S' : Type*) [CommRing S'] [Algebra A S']
    [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (hs' : IsUnit (toCompletionLoc P T' s' S' hden' s))
      (hopen' : IsOpen ((completedPlusSubring P Aplus T' s' S' hden' :
        Subring (UniformSpace.Completion S')) : Set (UniformSpace.Completion S')))
      (hs : IsUnit (toCompletionLoc P T s S hden s'))
      (hopen : IsOpen ((completedPlusSubring P Aplus T s S hden :
        Subring (UniformSpace.Completion S)) : Set (UniformSpace.Completion S))),
      Continuous (presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq
        hs' hopen' hs hopen).symm := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro hs' hopen' hs hopen
  exact continuous_presentationRingEquiv_symm P T s S hden T' s' S' hden' _ _ _ _ _ _

end TauCeti.ValuationSpectrum
