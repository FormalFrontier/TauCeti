/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Surjective

/-!
# The adic spectrum of a topological localization

For a rational subset `R(T/s)` of `Spa(A, A⁺)`, Wedhorn first equips the algebraic localization
`Aₛ` with a topology for which the fractions `t/s` are power-bounded. Its plus ring is the
integral closure of `A⁺[T/s]` in `Aₛ`. This file identifies the adic spectrum of that topological
localization with the rational subset:

```text
Spa(A(T/s), A(T/s)⁺) ≃ₜ R(T/s).
```

Pullback along `A → Aₛ` is an embedding because pullback embeds the whole valuation spectrum of a
localization. Surjectivity is the extension theorem from `Localization.Surjective`. The completed
coordinate ring `A⟨T/s⟩` requires a further extension of continuous valuations along the dense
completion map and is intentionally not identified here.

## Main definitions

* `TauCeti.ValuationSpectrum.spaLocalizationToRationalSubset`: pullback from the adic spectrum of
  `A(T/s)` to `R(T/s)`.
* `TauCeti.ValuationSpectrum.spaLocalizationHomeomorph`: the resulting canonical homeomorphism.

## Main results

* `TauCeti.ValuationSpectrum.spaLocalizationHomeomorph_apply_val`: the forward map is pullback
  along `A → A(T/s)`.
* `TauCeti.ValuationSpectrum.comap_spaLocalizationHomeomorph_symm_apply`: the inverse extends a
  point of the rational subset.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], arXiv:1910.05934v1, Proposition and Definition 5.51
  and §8.1.

## Provenance

The construction combines this repository's localization embedding and valuation-extension
results. It follows no external formalization.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

open scoped Classical in
/-- Pullback along `A → A(T/s)`, corestricted from the adic spectrum of the topological
localization to the rational subset `R(T/s)`. -/
noncomputable def spaLocalizationToRationalSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    spa (integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦
        (divBy (t : A) s : S))) S).toSubring →
      (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  let Bplus := (integralClosure ↥(Algebra.adjoin Aplus
    (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring
  have hplus : ∀ a ∈ Aplus, algebraMap A S a ∈ Bplus := fun a ha ↦
    Subalgebra.algebraMap_mem (integralClosure _ S)
      (⟨_, Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : Aplus)⟩ :
        ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))))
  let f : spa Bplus → spa Aplus :=
    spaComap (algebraMap A S) (continuous_algebraMap_locTopology P T s S hden)
      Aplus Bplus hplus
  exact Set.codRestrict f _ fun v ↦ by
    have hv := image_comap_algebraMap_spa_subset_rationalSubset P Aplus T s S hden
      ⟨v.1, v.2, rfl⟩
    simpa only [Set.mem_preimage, f, spaComap_val] using hv

/-- The map to the rational subset is pullback along `A → A(T/s)` on underlying valuations. -/
@[simp]
theorem spaLocalizationToRationalSubset_apply_val (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    ∀ v : spa (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring,
      ((spaLocalizationToRationalSubset P Aplus T s S hden v).1 : spa Aplus).1 =
        comap (algebraMap A S) v.1 := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  intro v
  unfold spaLocalizationToRationalSubset
  apply spaComap_val

/-- The canonical map from the localization spectrum to the rational subset is a topological
embedding. -/
theorem isEmbedding_spaLocalizationToRationalSubset (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    Topology.IsEmbedding (spaLocalizationToRationalSubset P Aplus T s S hden) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  unfold spaLocalizationToRationalSubset
  apply (isEmbedding_spaComap _ _ _ _ _
    (localization_comap_isEmbedding (Submonoid.powers s) S)).codRestrict

/-- Every point of `R(T/s)` is extended by the canonical map from the localization spectrum. -/
theorem surjective_spaLocalizationToRationalSubset (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    Function.Surjective (spaLocalizationToRationalSubset P Aplus T s S hden) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  intro v
  have himage := Set.ext_iff.mp
    (image_comap_algebraMap_spa_eq_rationalSubset P Aplus hP T s S hden) v.1.1
  obtain ⟨w, hwspa, hcomp⟩ := himage.mpr v.2
  refine ⟨⟨w, hwspa⟩, Subtype.ext ?_⟩
  exact Subtype.ext (by rw [spaLocalizationToRationalSubset_apply_val]; exact hcomp)

/-- The adic spectrum of the topological localization `A(T/s)`, with plus ring the integral
closure of `A⁺[T/s]`, is canonically homeomorphic to the rational subset `R(T/s)`.

The hypothesis `A₀ ≤ A⁺` ensures that extending a continuous valuation to the localization is
continuous; a pair of definition satisfying it exists for every ring of integral elements. -/
noncomputable def spaLocalizationHomeomorph (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    spa (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring ≃ₜ
      (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  exact (isEmbedding_spaLocalizationToRationalSubset P Aplus T s S hden).toHomeomorphOfSurjective
    (surjective_spaLocalizationToRationalSubset P Aplus hP T s S hden)

/-- The forward map of `spaLocalizationHomeomorph` is pullback along `A → A(T/s)`. -/
@[simp]
theorem spaLocalizationHomeomorph_apply_val (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    ∀ v : spa (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring,
      ((spaLocalizationHomeomorph P Aplus hP T s S hden v).1 : spa Aplus).1 =
        comap (algebraMap A S) v.1 := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  intro v
  rw [spaLocalizationHomeomorph, Topology.IsEmbedding.toHomeomorphOfSurjective_apply]
  exact spaLocalizationToRationalSubset_apply_val P Aplus T s S hden v

/-- Pulling the valuation supplied by the inverse homeomorphism back to `A` recovers the
original point of `R(T/s)`. -/
@[simp]
theorem comap_spaLocalizationHomeomorph_symm_apply (P : PairOfDefinition A)
    (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locTopology P T s S hden
    ∀ v : (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)),
      comap (algebraMap A S) ((spaLocalizationHomeomorph P Aplus hP T s S hden).symm v).1 =
        v.1.1 := by
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  intro v
  rw [← spaLocalizationHomeomorph_apply_val P Aplus hP T s S hden]
  exact congrArg (fun w : (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) ↦
    w.1.1) ((spaLocalizationHomeomorph P Aplus hP T s S hden).apply_symm_apply v)

end TauCeti.ValuationSpectrum

end
