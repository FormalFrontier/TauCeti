/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic

import Mathlib.Data.Finsupp.Encodable
import TauCeti.Topology.LiftTendstoCofinite

/-!
# `A⟨X₁,…,Xₖ⟩ → B⟨X₁,…,Xₖ⟩` is surjective along an open surjection

A continuous **open** surjection `φ : A → B` of nonarchimedean rings induces a surjection
`A⟨X₁,…,Xₖ⟩ → B⟨X₁,…,Xₖ⟩` of restricted power-series rings.

Openness is the hypothesis that matters. Surjectivity of `φ` alone lifts each coefficient of a
restricted series separately, but the preimages so chosen need not tend to zero, and then the lift
is a power series and not a restricted one. Openness is what lets the preimages be drawn from a
shrinking family of neighbourhoods; `TauCeti.exists_lift_tendsto_cofinite_nhds` is where that
choice is made, and this file is its transcription into the weighted language, at the trivial
weight family where restrictedness *is* convergence to zero
(`TauCeti.Huber.isWeightedRestricted_one_weight_iff`).

Countable generation of `𝓝 (0 : A)` is what supplies the family to draw from. It is not
restrictive here: a Huber ring satisfies it, by
`TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero`.

## Main results

* `TauCeti.Huber.surjective_weightedMap_one_weight`.

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

/-- **A continuous open surjection stays surjective on restricted series.** Every element of
`B⟨X₁,…,Xₖ⟩` is the image of one of `A⟨X₁,…,Xₖ⟩`.

This is the step Wedhorn's Proposition & Definition 6.36(ii) needs: a ring topologically of finite
type over `A` is an open quotient of some `A⟨X₁,…,Xₖ⟩`, and adjoining further variables to that
quotient has to stay a quotient for noetherianity to descend to it. -/
theorem surjective_weightedMap_one_weight [(𝓝 (0 : A)).IsCountablyGenerated] {φ : A →+* B}
    (hφ : Continuous φ) (hsurj : Function.Surjective φ) (hopen : IsOpenMap φ)
    (hTS : ∀ _ : Fin k, φ '' ({1} : Set A) ⊆ ({1} : Set B)) :
    Function.Surjective (weightedMap (k := k) hφ isWeightFamily_one_weight
      isWeightFamily_one_weight hTS) := by
  intro g
  obtain ⟨c, hcg, hc⟩ := TauCeti.exists_lift_tendsto_cofinite_nhds (φ : A → B) hsurj
    (map_zero φ ▸ hopen.nhds_le 0)
    (fun ν ↦ MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B))
    (isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp g.2))
  obtain ⟨f, hf⟩ : ∃ f : MvPowerSeries (Fin k) A, ∀ ν, MvPowerSeries.coeff ν f = c ν :=
    ⟨c, fun ν ↦ MvPowerSeries.coeff_apply c ν⟩
  refine ⟨⟨f, mem_weightedRestrictedSubring.mpr (isWeightedRestricted_one_weight_iff.mpr ?_)⟩,
    Subtype.ext (MvPowerSeries.ext fun ν ↦ ?_)⟩
  · simpa only [hf] using hc
  · rw [coe_weightedMap, MvPowerSeries.coeff_map, hf]
    exact hcg ν

end TauCeti.Huber

end
