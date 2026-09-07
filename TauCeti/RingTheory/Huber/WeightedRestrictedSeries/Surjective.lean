/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

/-!
# Restricted series lift along an open surjection

A continuous **open** surjection `φ : A → B` of nonarchimedean rings whose source has countably
generated `𝓝 0` induces a surjection of restricted power-series *rings* — the trivial-weight
`TauCeti.Huber.weightedRestrictedSubring`, before completion — coefficientwise.

Openness is the hypothesis that matters. Surjectivity of `φ` alone lifts each coefficient of a
restricted series separately, but the preimages so chosen need not tend to zero, and then the lift
is a power series and not a restricted one. Openness is what lets the preimages be drawn from a
shrinking family of neighbourhoods; `TauCeti.exists_lift_tendsto_cofinite_nhds` is where that
choice is made, and this file is its transcription into the weighted language, at the trivial
weight family where restrictedness *is* convergence to zero
(`TauCeti.Huber.isWeightedRestricted_one_weight_iff`).

**Countable generation of `𝓝 (0 : A)` is a hypothesis of both results here**, not a background
assumption: it is what supplies the shrinking family the lifted coefficients are drawn from, and a
general `NonarchimedeanRing` need not have it. It is not restrictive in the intended application —
a Huber ring satisfies it, by `TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero`.

## Main results

* `TauCeti.Huber.weightedMap_one_weight_surjective`, with
  `IsOpenQuotientMap.weightedMap_one_weight_surjective` the form taking the bundled structure —
  in that namespace so `hq.weightedMap_one_weight_surjective` works.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §5.6 and
  Proposition & Definition 6.36.

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`,
`projects/AdicSpaces/Adic spaces/RestrictedModule.lean`, has the corresponding statement for
modules in one variable, `restrictedModule_map_surjective`, with both sides assumed Hausdorff.
Nothing was copied.
-/

public section

open Filter
open scoped Topology

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]

/-- **A continuous surjection carrying neighbourhoods of zero onto neighbourhoods of zero stays
surjective on restricted series**, provided `𝓝 (0 : A)` is countably generated. Every restricted
series over `B` is then the image of one over `A`.

The hypothesis is stated as the filter inequality the proof consumes. Alongside the surjectivity
assumed here it is the filter-level formulation of `IsOpenMap φ`, not a weakening of it — for a
surjective continuous additive map the two say the same thing, since openness of a group
homomorphism is decided at zero. `IsOpenQuotientMap.weightedMap_one_weight_surjective` is the form
for a caller holding the bundled open-quotient structure.

This is a step towards what Wedhorn's Proposition & Definition 6.36(ii) needs, not the whole of
it. `TauCeti.Huber.IsStrictlyTopologicallyFiniteType` asks for an open quotient map whose domain
is `TauCeti.Huber.restrictedMvPowerSeriesCompletion k A` — the *completion* `A⟨X₁,…,Xₖ⟩` at the
trivial weight — whereas the surjection here is one level below, between the restricted subrings
themselves. Passing from this to an open quotient out of the completion is a separate step.

`TauCeti.Huber.IsTopologicallyFiniteType` is the weaker notion, and what weakens it is the
*weight family*, not completion: it allows an arbitrary finite family `T` in place of the trivial
one. Both notions take their quotient out of a completion. -/
theorem weightedMap_one_weight_surjective [(𝓝 (0 : A)).IsCountablyGenerated] {φ : A →+* B}
    (hφ : Continuous φ) (hsurj : Function.Surjective φ)
    (hnhds : 𝓝 (0 : B) ≤ Filter.map φ (𝓝 (0 : A))) :
    Function.Surjective (weightedMap (k := k) hφ isWeightFamily_one_weight
      isWeightFamily_one_weight fun _ ↦ by simp) := by
  intro g
  obtain ⟨f, hf⟩ := restrictedMvPowerSeriesSubmoduleMap_surjective (k := k)
    φ.toAddMonoidHom.toIntLinearMap hφ.continuousAt hsurj hnhds
    ⟨(g : MvPowerSeries (Fin k) B), mem_restrictedMvPowerSeriesSubmodule.mpr
      (isRestricted_iff_coeff.mpr
        (isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp g.2)))⟩
  refine ⟨⟨(f : MvPowerSeries (Fin k) A),
      mem_weightedRestrictedSubring.mpr (isWeightedRestricted_one_weight_iff.mpr
        (isRestricted_iff_coeff.mp (mem_restrictedMvPowerSeriesSubmodule.mp f.2)))⟩,
    Subtype.ext (MvPowerSeries.ext fun ν ↦ ?_)⟩
  have h := congrArg (fun x : restrictedMvPowerSeriesSubmodule k ℤ B ↦
    ((x : MvPowerSeries (Fin k) B) : (Fin k →₀ ℕ) → B) ν) hf
  have key := coeff_restrictedMvPowerSeriesSubmoduleMap φ.toAddMonoidHom.toIntLinearMap
    hφ.continuousAt f ν
  rw [coe_weightedMap, MvPowerSeries.coeff_map]
  exact key.symm.trans h

/-- **The open-quotient form of `TauCeti.Huber.weightedMap_one_weight_surjective`**, for a caller
holding the bundled `IsOpenQuotientMap φ`.

That is the interface finite-type presentations come in — `TauCeti.Huber`
`.IsStrictlyTopologicallyFiniteType` produces one — so it is the form a consumer actually has,
and it bundles exactly the continuity, surjectivity and openness the filter-level theorem needs. -/
theorem _root_.IsOpenQuotientMap.weightedMap_one_weight_surjective
    [(𝓝 (0 : A)).IsCountablyGenerated] {φ : A →+* B} (hq : IsOpenQuotientMap φ) :
    Function.Surjective (weightedMap (k := k) hq.continuous isWeightFamily_one_weight
      isWeightFamily_one_weight fun _ ↦ by simp) :=
  TauCeti.Huber.weightedMap_one_weight_surjective hq.continuous hq.surjective
    (map_zero φ ▸ hq.isOpenMap.nhds_le 0)

end TauCeti.Huber

end
