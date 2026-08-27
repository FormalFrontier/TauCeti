/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Valuation

/-!
# The adic spectrum of a rational localisation covers the rational subset

Roadmap Layer 3.1 asks, for a rational subset `U = R(T/s)` of `X = Spa(A, A⁺)`, for a natural
homeomorphism between `U` and the adic spectrum of the rational localisation. `Localization.Basic`
supplies the map and shows it lands in `U`, and closes by saying that the map back — extending a
point of `U` to the coordinate ring — is "the remaining half of the roadmap's homeomorphism".
This file supplies that half **before completion**: it shows that the continuous map

```text
Spa (Aₛ, Aₛ⁺) → Spa (A, A⁺)
```

induced by the structure map `A → Aₛ` has image exactly `R(T/s)`, where `Aₛ` carries Wedhorn's
localisation topology `A(T/s)` and `Aₛ⁺` is the integral closure of `A⁺[t₁/s, …, tₙ/s]` in it —
the plus ring that
`TauCeti.Huber.PairOfDefinition.isRingOfIntegralElements_integralClosure_adjoin_plus` makes a ring
of integral elements of `Aₛ`.

The content is the inclusion `⊇`: a point of `R(T/s)` inverts `s` and makes each `t/s` sub-unit,
so its canonical valuation extends to `Aₛ`, and `Localization.Valuation` shows the extension is
continuous and sub-unit on `Aₛ⁺`. The inclusion `⊆` is `comap_mem_rationalSubset` applied to the
structure map.

## Main results

* `TauCeti.ValuationSpectrum.exists_mem_spa_comap_algebraMap_eq`: **every point of `R(T/s)` is
  the pullback of a point of `Spa (Aₛ, Aₛ⁺)`.**
* `TauCeti.ValuationSpectrum.image_comap_algebraMap_spa_eq_rationalSubset`: the image of
  `Spa (Aₛ, Aₛ⁺)` in `Spa (A, A⁺)` **is** `R(T/s)`.

## What remains for the roadmap's homeomorphism

Three things, none of them claimed here.

* **Injectivity**, and then that the resulting continuous bijection onto `R(T/s)` is a
  homeomorphism.
* **The passage to the completion.** The roadmap's `A_U` is the *completed* localisation
  `A⟨T/s⟩`, and every statement below is about `Aₛ` with `locTopology`. Identifying the two adic
  spectra is a separate theorem about extending continuous valuations along a completion, and it
  is neither used nor assumed here.
* **Identification of the rational subsets** on the two sides.

## The hypothesis `P.ringOfDefinition ≤ A⁺`

Both results fix a pair of definition `P = (A₀, I)` of `A` with `A₀ ⊆ A⁺`. The choice of pair of
definition is free — `locTopology` takes it as an argument — and such a `P` always exists, because
a ring of integral elements is open and
`TauCeti.Huber.PairOfDefinition.exists_pairOfDefinition_ringOfDefinition_le` produces a ring of
definition inside any open subring. The module docstring of
`TauCeti.RingTheory.Huber.LocalizationTopology.Valuation` explains why the hypothesis cannot be
dropped: without it the extension need not be `≤ 1` on `A₀[T/s]`, and the neighbourhoods of zero
in `Aₛ` are modules over that ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.29 for rational
  subsets, Proposition and Definition 5.51 for the localisation topology, and §8.1 for the
  coordinate ring of a rational subset.

## Provenance

Assembled from this repository's `LocalizationTopology` API and the valuation-extension results of
`TauCeti.RingTheory.Huber.LocalizationTopology.Valuation`; nothing is ported. As in
`Localization.Basic`, AINTLIB was **not** consulted — no checkout of it was available in the
authoring environment.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **At a point of a rational subset the denominator is off the support**, read on the canonical
valuation rather than on the valuative relation. This is the third conjunct of
`mem_rationalSubset_iff` in the form the extension results consume, `Valuation.extendToLocalization`
being stated for valuations. -/
theorem valuation_ne_zero_of_mem_rationalSubset {Aplus : Subring A} {T : Finset A} {s : A}
    {v : Spv A} (hv : v ∈ rationalSubset Aplus T s) : v.valuation s ≠ 0 := by
  have h := ((mem_rationalSubset_iff Aplus T s v).mp hv).2.2
  rwa [← valuation_le_iff, map_zero, le_zero_iff] at h

variable [IsTopologicalRing A]

/-- **Every point of `R(T/s)` is the pullback of a point of the adic spectrum of the rational
localisation.** The canonical valuation of the point is continuous, dominates every numerator by
the denominator, and is `≤ 1` on `A⁺`; extending it along `A → Aₛ` therefore gives a continuous
valuation on `Aₛ` that is `≤ 1` on the integral closure of `A⁺[T/s]`, and restricting it back
along the structure map returns the point.

Here `Aₛ` carries `locTopology`, not the topology of the completion; see the module docstring for
what that leaves open. -/
theorem exists_mem_spa_comap_algebraMap_eq (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) {v : Spv A} (hv : v ∈ rationalSubset Aplus T s) :
    letI := locTopology P T s S hden
    ∃ w ∈ spa (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring,
      comap (algebraMap A S) w = v := by
  let _ := locTopology P T s S hden
  have hs : v.valuation s ≠ 0 := valuation_ne_zero_of_mem_rationalSubset hv
  have hspa := rationalSubset_subset_spa Aplus T s hv
  have hplus : ∀ a ∈ Aplus, v.valuation a ≤ 1 := fun a ha ↦ by
    rw [← map_one v.valuation, valuation_le_iff]
    exact ((mem_spa_iff Aplus v).mp hspa).2 a ha
  have hT : ∀ t ∈ T, v.valuation t ≤ v.valuation s := fun t ht ↦
    (valuation_le_iff v t s).mpr (((mem_rationalSubset_iff Aplus T s v).mp hv).2.1 t ht)
  refine ⟨ofValuation
    (v.valuation.extendToLocalization (Valuation.powers_le_supp_primeCompl hs) S), ?_, ?_⟩
  · rw [mem_spa_iff]
    refine ⟨(isContinuous_ofValuation_iff _).mpr ?_, fun x hx ↦ ?_⟩
    · exact isContinuous_extendToLocalization S P T s hden
        ((isContinuous_def v).mp ((mem_spa_iff Aplus v).mp hspa).1) hs
        (fun a ha ↦ hplus a (hP ha)) hT
    · rw [vle_ofValuation, map_one]
      exact extendToLocalization_le_one_of_mem_integralClosure_adjoin_plus S T s Aplus hs
        hplus hT hx
  · rw [comap_ofValuation]
    refine Eq.trans (congrArg ofValuation (Valuation.ext fun a ↦ ?_)) (ofValuation_valuation v)
    exact Valuation.extendToLocalization_apply_map_apply _
      (Valuation.powers_le_supp_primeCompl hs) S a

/-- **The image of the adic spectrum of the rational localisation is exactly `R(T/s)`.** The
inclusion `⊆` holds because the structure map inverts `s` and sends each `t/s` into the plus ring
of `Aₛ`; the inclusion `⊇` is `exists_mem_spa_comap_algebraMap_eq`.

This is the roadmap's homeomorphism `Spa (A_U, A_U⁺) ≃ U` at the level of underlying sets and
before completion; injectivity, the topological comparison and the passage from `Aₛ` to `A⟨T/s⟩`
are not part of the statement. -/
theorem image_comap_algebraMap_spa_eq_rationalSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    comap (algebraMap A S) '' spa (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring =
      rationalSubset Aplus T s := by
  let _ := locTopology P T s S hden
  -- Every element of the generating subalgebra is integral over it, hence in the plus ring.
  have hmem : ∀ x ∈ Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)),
      x ∈ (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring := fun x hx ↦
    isIntegral_algebraMap (x := (⟨x, hx⟩ :
      ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))))
  refine Set.Subset.antisymm ?_ fun v hv ↦ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact comap_mem_rationalSubset (continuous_algebraMap_locTopology P T s S hden)
      (fun a ha ↦ hmem _ (Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : Aplus))) T s
      (IsLocalization.Away.mul_invSelf s)
      (fun t ht ↦ by
        rw [algebraMap_mul_invSelf]
        exact hmem _ (Algebra.subset_adjoin ⟨⟨t, ht⟩, rfl⟩)) hw
  · obtain ⟨w, hw, rfl⟩ := exists_mem_spa_comap_algebraMap_eq P Aplus hP T s S hden hv
    exact ⟨w, hw, rfl⟩

end TauCeti.ValuationSpectrum

end
