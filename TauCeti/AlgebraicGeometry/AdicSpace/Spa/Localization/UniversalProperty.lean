/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Points
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Integral

/-!
# The geometric universal property of a rational localisation

The coordinate ring `A⟨T/s⟩` of a rational subset has an *algebraic* universal property: a
continuous `φ : A → B` into a complete `B` extends across `ρ : A → A⟨T/s⟩` as soon as `φ s` is a
unit and every fraction `φ t / φ s` is power-bounded
(`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`).
Wedhorn's Lemma 8.1 replaces those two algebraic conditions by a single *geometric* one — that
`Spa(φ)` factors
through the rational subset `U = R(T/s)`. This file carries that replacement out with the unit
`φ s` kept as a hypothesis, which asks nothing of the target's maximal ideals; Wedhorn's own
shape, where the unit is *derived* from the geometric condition, follows as a corollary for
targets whose maximal ideals are open — see *The hypothesis that is not yet Wedhorn's* below.

Wedhorn's proof has three steps, and all three are discharged here:

> As `Spa(φ)` factors through `U`, we have `|φ(t)|_w ≤ |φ(s)|_w ≠ 0` for all `w ∈ Spa B` and for
> all `t ∈ T`. This implies `φ(s) ∈ B^×` by Proposition 7.52. Moreover, for all `w ∈ Spa B` we
> have `|φ(t)/φ(s)|_w ≤ 1`. This implies `φ(t)/φ(s) ∈ B⁺` by Proposition 7.52. Thus the claim
> follows from the universal property of `A → A⟨T/s⟩`.

The step `φ s ∈ B^×` is Wedhorn's Proposition 7.52(2), which is on hand as
`TauCeti.ValuationSpectrum.isUnit_of_forall_not_vle_zero`; the step `|φ(t)/φ(s)|_w ≤ 1` is a
division by that unit. The step from there to `φ(t)/φ(s) ∈ B⁺` is Proposition 7.52(1), available
as `TauCeti.ValuationSpectrum.mem_of_forall_vle_one`, which the assembly consumes at its one use
site. All three steps are therefore proved. Only step 1 asks anything of maximal ideals, so the
assembly takes the unit as a hypothesis and steps 2 and 3 carry the rest; Wedhorn's own statement,
which derives the unit, is the corollary obtained by discharging step 1 under `hmax`. See *The
hypothesis that is not yet Wedhorn's* below for what that costs and what it does not cost.

The other half of Lemma 8.1, that `Spa ρ : Spa A⟨T/s⟩ → Spa A` factors through `U`, is already
`TauCeti.ValuationSpectrum.spaComapLoc_mem_rationalSubset`; it is not repeated here.

## Main results

All four are in the `TauCeti.ValuationSpectrum` namespace.

* `isUnit_of_forall_comap_mem_rationalSubset` : if every point of `Spa (B, B⁺)` pulls back into
  `R(T/s)`, the denominator becomes a unit in `B`.
* `vle_one_of_comap_mem_rationalSubset` : at a point whose pullback lies in `R(T/s)`, the
  fraction `φ t / φ s` is sub-unit.
* `existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset` : the geometric
  universal property — a continuous `φ : A → B` whose `Spa(φ)` factors through `R(T/s)` and whose
  `φ s` is a unit extends across `A → A⟨T/s⟩` in exactly one continuous way. Nothing is asked of
  the maximal ideals of `B`.
* `existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset` : the same, with the unit
  obtained from the geometric condition by step 1, for a target whose maximal ideals are open.

## The hypothesis that is not yet Wedhorn's

`hmax`, openness of the target's maximal ideals, is **not** a hypothesis Wedhorn imposes, and it
is not harmless: by `TauCeti.Huber.IsTateRing.isOpen_iff_eq_top` an ideal of a Tate ring is open
exactly when it is `⊤`, so a nonzero Tate ring has no open maximal ideal at all. Wedhorn states
Lemma 8.1 for a complete *affinoid* target, and the affinoid rings §8 works with are Tate in its
principal case. **So the `hmax` corollary below is vacuous for Tate targets, the principal case
of §8, and must not be cited as Lemma 8.1 without that restriction.**

The restriction is confined to that corollary. The theorem it comes from takes `φ s` being a unit
as a hypothesis and asks nothing of maximal ideals, so it applies to Tate targets the moment a
unit criterion for them exists; what is missing is a form of Wedhorn's Proposition 7.52(2) for
complete Tate rings, which belongs to `Spa/Points.lean` and not to this file.

It is non-vacuous for *complete* adic Huber targets — `ℤ_p` and its kin — and that is the
generality in which it is stated. Completeness is doing work in that sentence, not decoration: in
a complete adic ring the ideal of definition lies in the Jacobson radical, so every maximal ideal
contains it and is therefore open. Drop completeness and the conclusion fails — `ℤ` with the
`p`-adic topology is adic Huber, and its maximal ideal `(q)` for a prime `q ≠ p` contains no power
of `p`, so it is not open. Only this prose was ever at stake: the theorem assumes
`[CompleteSpace B]`.

The obstruction is inherited, not introduced here. `hmax` is carried by
`TauCeti.ValuationSpectrum.isUnit_of_forall_not_vle_zero`, this repository's only unit-detection
lemma over `spa`, which in turn gets it from `exists_mem_spa_supp_eq` — main's Proposition 7.51,
whose docstring records that it is "weakened from maximal to" open prime. Removing `hmax` needs a
form of Wedhorn's Proposition 7.52(2) for complete Tate rings that does not route through open
maximal ideals; that is a change to `Spa/Points.lean` and is tracked separately. Note that 7.52(1)
already avoids the problem — `mem_of_forall_vle_one` goes through
`isIntegral_of_forall_continuous_valuation_le_one` and asks nothing of maximal ideals — so the
asymmetry between the two halves of 7.52 on main is where a fix should start.

## What this file consumes

Wedhorn's Proposition 7.52(1) — that `f ∈ B⁺` as soon as `|f(x)| ≤ 1` for all `x ∈ Spa B` — is
what turns the sub-unit bound on `φ t / φ s` into membership in `B⁺`. It is supplied by
`TauCeti.ValuationSpectrum.mem_of_forall_vle_one`, landed in #4552. It asks three things of the
target:

* `IsOpen (Bplus : Set B)`,
* `[IsIntegrallyClosedIn Bplus B]`,
* `[IsHuberRing B]`.

The first two, together with `B⁺ ⊆ B°`, are the three fields of
`TauCeti.Huber.IsRingOfIntegralElements Bplus`, so the assembly below asks for that one bundled
hypothesis rather than spelling them out; with `[IsHuberRing B]` they are exactly a Huber pair on
`B`, and a consumer holding a `TauCeti.Huber.Pair B` passes its `isRingOfIntegralElements`
field. `[IsHuberRing B]` is not a restriction added to make the proof go
through: Wedhorn states Lemma 8.1 for a
continuous homomorphism into a *complete affinoid ring*, and an affinoid ring is a Huber pair.

Openness of the maximal ideals of `B` is carried separately, as `hmax`, and **is not** derivable
from `[IsHuberRing B]`. The route through
`Ideal.isOpen_of_isMaximal_of_isOpen_isTopologicallyNilpotent` needs
`[IsLinearTopology B B]` — a basis of zero-neighbourhoods by *ideals* — which no Huber instance
supplies and which would defeat the purpose: by `TauCeti.Huber.IsTateRing.isOpen_iff_eq_top` an
ideal of a Tate ring is open exactly when it is `⊤`, so a nonzero Tate ring has neither a proper
open ideal nor a linear topology, and Tate targets are the ones Wedhorn's §8 is about. `hmax`
therefore stays a hypothesis on `(B, B⁺)`, exactly as it is on
`TauCeti.ValuationSpectrum.isUnit_of_forall_not_vle_zero`, which is where it is spent.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.1, whose statement and
  three-step proof are quoted above, together with Propositions 7.18 and 7.52.

## Provenance

Developed here; nothing is ported. AINTLIB reaches the corresponding statement by a different
route — a height-one reduction pairing Wedhorn's Propositions 7.18 and 7.41 — which is not
followed.
-/

public section

open TauCeti.Localization

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

section Steps

variable {B : Type*} [CommRing B] [TopologicalSpace B]

/-- **The denominator becomes a unit.** If every point of `Spa (B, B⁺)` pulls back into the
rational subset `R(T/s)`, then no point of `Spa (B, B⁺)` vanishes on `φ s`, so `φ s` is a unit
by Wedhorn's Proposition 7.52(2).

This is the first step of Wedhorn's Lemma 8.1. Openness of the maximal ideals of `B` is the
hypothesis that 7.52(2) carries; `Ideal.isOpen_of_isMaximal_of_isOpen_isTopologicallyNilpotent`
supplies it for a complete Hausdorff linearly topologized ring whose topologically nilpotent
locus is open, as it is for a Huber ring. -/
theorem isUnit_of_forall_comap_mem_rationalSubset {φ : A →+* B} {Aplus : Subring A}
    {Bplus : Subring B} (T : Finset A) {s : A}
    (hmax : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → IsOpen (𝔪 : Set B))
    (hfac : ∀ w ∈ spa Bplus, comap φ w ∈ rationalSubset Aplus T s) :
    IsUnit (φ s) := by
  refine isUnit_of_forall_not_vle_zero Bplus hmax fun w hw hw0 ↦ ?_
  refine ((mem_rationalSubset_iff Aplus T s _).mp (hfac w hw)).2.2 ?_
  rw [comap_vle, map_zero]
  exact hw0

omit [TopologicalSpace B] in
/-- **The fractions are sub-unit.** At a point of `Spv B` whose pullback lies in `R(T/s)`, the
fraction `φ t / φ s` has value at most `1`.

This is the second step of Wedhorn's Lemma 8.1: the pullback condition gives `|φ t|_w ≤ |φ s|_w`,
and dividing by the unit `φ s` — which `isUnit_of_forall_comap_mem_rationalSubset` supplies —
turns that into `|φ t / φ s|_w ≤ 1`. Nothing beyond the pullback condition is used, so the unit
enters as an argument rather than being re-derived.

The pullback condition is taken at the single point `w` where it is spent, not as a hypothesis
quantified over `spa B⁺`: the proof looks at no other point, and `Bplus` then plays no part in
the statement at all, so no topology on `B` is needed either. The assembly holds the quantified
form and passes `hfac w hw`. -/
theorem vle_one_of_comap_mem_rationalSubset {φ : A →+* B} {Aplus : Subring A}
    {T : Finset A} {s : A} (hs : IsUnit (φ s)) {w : Spv B}
    (hmem : comap φ w ∈ rationalSubset Aplus T s) {t : A} (ht : t ∈ T) :
    w.toValuativeRel.vle (φ t * ↑hs.unit⁻¹) 1 := by
  have hvle : w.toValuativeRel.vle (φ t) (φ s) := by
    have h := ((mem_rationalSubset_iff Aplus T s _).mp hmem).2.1 t ht
    rwa [comap_vle] at h
  have h := w.toValuativeRel.mul_vle_mul_left hvle (↑hs.unit⁻¹ : B)
  rwa [hs.mul_val_inv] at h

end Steps

/-! ### Lemma 8.1: the geometric universal property

The assembly. `S` is an algebraic localisation of `A` away from `s` carrying the localisation
topology, so that `A⟨T/s⟩` is its separated completion, and the three `letI`s naming the
uniformity and its two companions are the ones every statement about `A⟨T/s⟩` carries. -/

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

/-- **The geometric universal property of `A⟨T/s⟩`, with `φ s` a unit**: a continuous
`φ : A → B` into a complete `(B, B⁺)` whose `Spa(φ)` factors through the rational subset
`R(T/s)`, and for which `φ s` is a unit, extends across the structure map `ρ : A → A⟨T/s⟩` in
exactly one continuous way.

Of the two algebraic conditions of
`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_completion_locTopology`, the
first is the hypothesis `hs`; the second is discharged from the geometric one: each fraction
`φ t / φ s` is sub-unit at every point of `Spa (B, B⁺)` by
`vle_one_of_comap_mem_rationalSubset`, hence lies in `B⁺` and so is power-bounded.

The passage from "sub-unit at every point of `Spa (B, B⁺)`" to "in `B⁺`" is Wedhorn's
Proposition 7.52(1), applied through `mem_of_forall_vle_one`; its hypotheses on the target are
openness of `B⁺`, `[IsIntegrallyClosedIn Bplus B]` and `[IsHuberRing B]`. The proof also uses
`B⁺ ⊆ B°`. Those three conditions on `B⁺` are exactly the fields of `IsRingOfIntegralElements`,
so they are carried by the single hypothesis `hB` rather than spelled out one by one.

Asking `B` to be Huber is not a restriction added here: Wedhorn states Lemma 8.1 for a continuous
homomorphism into a *complete affinoid ring*, and an affinoid ring is a Huber pair.

The unit `φ s` is a hypothesis rather than something derived: deriving it is step 1, which is the
only step that asks anything of the maximal ideals of `B`. Keeping it here leaves this statement
usable for Tate targets, for which no maximal ideal is open; the derived form is the corollary
below.

These are properties of the pair `(B, B⁺)` alone: they mention neither `φ` nor `T` nor `s`. The
per-morphism algebraic conditions of the universal property are replaced by the single geometric
condition `hfac`, at the cost of hypotheses on the target that are checked once. -/
theorem existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
    [IsHuberRing B] [CompleteSpace B] [T0Space B] (Bplus : Subring B)
    (hB : IsRingOfIntegralElements Bplus) {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hs : IsUnit (φ s))
    (hfac : ∀ w ∈ spa Bplus, comap φ w ∈ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* B,
      Continuous g ∧ g.comp (toCompletionLoc P T s S hden) = φ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  refine existsUnique_continuous_ringHom_completion_locTopology P T s S hden hφ hs fun t ht ↦ ?_
  have := hB.isIntegrallyClosedIn
  exact mem_powerBoundedSubring.mp
    (hB.le_powerBoundedSubring (mem_of_forall_vle_one hB.isOpen fun w hw ↦
      vle_one_of_comap_mem_rationalSubset hs (hfac w hw) ht))

/-- **Wedhorn's Lemma 8.1, for a target with open maximal ideals.** The geometric universal
property in the shape Wedhorn states it: the unit `φ s` is not assumed but derived from the
factorisation, which is step 1 and is what `hmax` pays for.

`hmax` is vacuous for every nonzero Tate ring, so this corollary is the restricted form; the
theorem above is the one to reach for otherwise. See the module docstring. -/
theorem existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset [IsTopologicalRing A]
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
    [IsHuberRing B] [CompleteSpace B] [T0Space B] (Bplus : Subring B)
    (hmax : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → IsOpen (𝔪 : Set B))
    (hB : IsRingOfIntegralElements Bplus) {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hfac : ∀ w ∈ spa Bplus, comap φ w ∈ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∃! g : UniformSpace.Completion S →+* B,
      Continuous g ∧ g.comp (toCompletionLoc P T s S hden) = φ :=
  existsUnique_continuous_ringHom_of_isUnit_of_forall_comap_mem_rationalSubset P Aplus T s S hden
    Bplus hB hφ (isUnit_of_forall_comap_mem_rationalSubset T hmax hfac) hfac

end TauCeti.ValuationSpectrum
