/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Pullbacks and quotient embeddings of sub-unit valuation loci

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.23, Remark 7.30, and
Proposition 7.38.**

This file constructs the contravariant continuous map on sub-unit valuation loci induced by a
continuous ring homomorphism preserving the chosen subrings:

```text
spaComap φ : spa Bplus → spa Aplus
```

No Huber-ring hypotheses are needed. The bundled version for morphisms of Huber pairs is in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair`.

## Main definitions

* `TauCeti.ValuationSpectrum.spaComap`: the pullback map `spa Bplus → spa Aplus`.

## Main results

* `TauCeti.ValuationSpectrum.comap_mem_spa`: pullback preserves the sub-unit locus.
* `TauCeti.ValuationSpectrum.continuous_spaComap`: `spaComap` is continuous.
* `TauCeti.ValuationSpectrum.spaComap_id`, `spaComap_comp`: contravariant functoriality.
* `TauCeti.ValuationSpectrum.comap_preimage_rationalSubset_inter_spa`,
  `spaComap_preimage_rationalSubset`: preimages of rational subsets.
* `TauCeti.ValuationSpectrum.comap_mem_rationalSubset`,
  `rationalSubset_image_eq_spa`: elementwise criteria for rational subsets under pullback.
* `TauCeti.ValuationSpectrum.isEmbedding_spaComap`: an embedding of valuation spectra restricts
  to an embedding of sub-unit loci.
* `TauCeti.ValuationSpectrum.isEmbedding_spaComap_quotientMk`,
  `range_spaComap_quotientMk`, `isClosedEmbedding_spaComap_quotientMk`: the quotient map for the
  image plus ring is a closed embedding with support locus as its range.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23, Remark 7.30, Proposition 7.38.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch `dev/adic-spaces` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, files `AffinoidRings.lean` and
`AdicSpectrum.lean`, was consulted rather than copied for the induced map and quotient embedding.
It bundles the plus ring into its affinoid ring and phrases those results at that level. Here the
plus subrings are explicit, the generic results require no Huber hypotheses, and the bundled
Huber-pair interface is provided separately. The rational-subset criteria are direct proofs;
AINTLIB was not consulted for them.
-/

public section

namespace TauCeti.ValuationSpectrum

open Valuation

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [CommRing C] [TopologicalSpace C]

/-- A continuous ring homomorphism mapping `A⁺` into `B⁺` pulls points of `spa (B, B⁺)` back
to points of `spa (A, A⁺)`. -/
theorem comap_mem_spa {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {v : Spv B} (hv : v ∈ spa Bplus) :
    comap φ v ∈ spa Aplus := by
  rw [mem_spa_iff] at hv ⊢
  refine ⟨hv.1.comap hφ, fun a ha ↦ ?_⟩
  rw [comap_vle, map_one]
  exact hv.2 (φ a) (hplus a ha)

/-- The contravariant map on sub-unit valuation loci induced by a continuous ring homomorphism
`φ : A →+* B` carrying `Aplus` into `Bplus`. -/
def spaComap (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A) (Bplus : Subring B)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (v : spa Bplus) : spa Aplus :=
  ⟨comap φ v.1, comap_mem_spa hφ hplus v.2⟩

@[simp]
theorem spaComap_val (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (v : spa Bplus) :
    (spaComap φ hφ Aplus Bplus hplus v).1 = comap φ v.1 := (rfl)

/-- `spaComap` is continuous for the subspace topologies. -/
theorem continuous_spaComap (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) :
    Continuous (spaComap φ hφ Aplus Bplus hplus) := by
  rw [continuous_induced_rng]
  exact (continuous_comap φ).comp continuous_subtype_val

/-- `spaComap` of the identity homomorphism is the identity map on `spa Aplus`. -/
@[simp]
theorem spaComap_id {A : Type*} [CommRing A] [TopologicalSpace A] (Aplus : Subring A) :
    spaComap (RingHom.id A) continuous_id Aplus Aplus (fun _ ha ↦ ha) = _root_.id :=
  funext fun ⟨v, _⟩ ↦ Subtype.ext (congr_fun comap_id v)

/-- `spaComap` is contravariantly functorial: `spaComap (ψ ∘ φ) = spaComap φ ∘ spaComap ψ`. -/
@[simp]
theorem spaComap_comp {φ : A →+* B} (hφ : Continuous φ) {ψ : B →+* C} (hψ : Continuous ψ)
    (Aplus : Subring A) (Bplus : Subring B) (Cplus : Subring C)
    (hφ_plus : ∀ a ∈ Aplus, φ a ∈ Bplus) (hψ_plus : ∀ b ∈ Bplus, ψ b ∈ Cplus) :
    spaComap (ψ.comp φ) (hψ.comp hφ) Aplus Cplus
        (fun a ha ↦ hψ_plus (φ a) (hφ_plus a ha)) =
      spaComap φ hφ Aplus Bplus hφ_plus ∘ spaComap ψ hψ Bplus Cplus hψ_plus :=
  funext fun ⟨v, _⟩ ↦ Subtype.ext (congr_fun (comap_comp φ ψ) v)

open scoped Classical in
/-- Preimage of a rational subset under `comap φ`, after intersecting with `spa Bplus`:
`(comap φ) ⁻¹' R(T/s) ∩ spa Bplus = R(φ(T)/φ(s))`. -/
theorem comap_preimage_rationalSubset_inter_spa (φ : A →+* B) (hφ : Continuous φ)
    {Aplus : Subring A} {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (T : Finset A) (s : A) :
    comap φ ⁻¹' rationalSubset Aplus T s ∩ spa Bplus =
      rationalSubset Bplus (T.image φ) (φ s) := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_rationalSubset_iff, mem_spa_iff,
    comap_vle, map_one, map_zero]
  constructor
  · rintro ⟨⟨⟨-, -⟩, hT, hs⟩, hv_cont, hv_plus⟩
    exact ⟨⟨hv_cont, hv_plus⟩, fun t ht ↦ by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
      exact hT a ha, hs⟩
  · rintro ⟨⟨hv_cont, hv_plus⟩, hT, hs⟩
    have hv_spa : v ∈ spa Bplus := (mem_spa_iff Bplus v).mpr ⟨hv_cont, hv_plus⟩
    have hcomap_spa := (mem_spa_iff Aplus (comap φ v)).mp (comap_mem_spa hφ hplus hv_spa)
    have hcomap_spa' : (comap φ v).IsContinuous ∧
        ∀ a ∈ Aplus, v.toValuativeRel.vle (φ a) 1 := by
      simpa only [comap_vle, map_one] using hcomap_spa
    exact ⟨⟨hcomap_spa', fun a ha ↦ hT (φ a) (Finset.mem_image_of_mem φ ha), hs⟩,
      hv_cont, hv_plus⟩

/-- A point of `Spa (B, B⁺)` pulls back into `R(T/s)` if `φ` inverts `s` and makes the
fractions `t/s` sub-unit. No Huber hypothesis is needed, and `T` is arbitrary. -/
theorem comap_mem_rationalSubset {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : Finset A) (s : A) {c : B}
    (hc : φ s * c = 1) (hT : ∀ t ∈ T, φ t * c ∈ Bplus) {v : Spv B} (hv : v ∈ spa Bplus) :
    comap φ v ∈ rationalSubset Aplus T s := by
  rw [mem_rationalSubset_iff]
  refine ⟨comap_mem_spa hφ hplus hv, fun t ht ↦ ?_, ?_⟩
  · have hsub : v.toValuativeRel.vle (φ t * c) 1 := ((mem_spa_iff Bplus v).mp hv).2 _ (hT t ht)
    have hclear : φ t * c * φ s = φ t := by
      rw [mul_assoc, mul_comm c, hc, mul_one]
    rw [comap_vle]
    simpa only [hclear, one_mul] using v.toValuativeRel.mul_vle_mul_left hsub (φ s)
  · have hunit : IsUnit (φ s) := ⟨⟨φ s, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
    rw [comap_vle, map_zero]
    exact @TauCeti.ValuativeRel.not_vle_zero_of_isUnit B _ v.toValuativeRel _ hunit

open scoped Classical in
omit [TopologicalSpace A] in
/-- If `φ` inverts `s` and makes every fraction `φ(t) / φ(s)` sub-unit, the rational subset
presented by the images of `T` and `s` is the whole target adic spectrum. -/
theorem rationalSubset_image_eq_spa (φ : A →+* B) (Bplus : Subring B) (T : Finset A) (s : A)
    {c : B} (hc : φ s * c = 1) (hT : ∀ t ∈ T, φ t * c ∈ Bplus) :
    rationalSubset Bplus (T.image φ) (φ s) = spa Bplus := by
  refine Set.Subset.antisymm (rationalSubset_subset_spa _ _ _) fun v hv ↦ ?_
  have hmem := comap_mem_rationalSubset (φ := RingHom.id B) continuous_id
    (Aplus := Bplus) (Bplus := Bplus) (fun _ ha ↦ ha) (T.image φ) (φ s) (by simpa using hc)
    (fun _ ht ↦ by
      obtain ⟨t, htT, rfl⟩ := Finset.mem_image.mp ht
      simpa using hT t htT) hv
  rwa [congr_fun comap_id v] at hmem

open scoped Classical in
/-- The preimage of `R(T/s)` under `spaComap φ` is `R(φ(T)/φ(s))`. -/
theorem spaComap_preimage_rationalSubset (φ : A →+* B) (hφ : Continuous φ)
    (Aplus : Subring A) (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (T : Finset A) (s : A) :
    spaComap φ hφ Aplus Bplus hplus ⁻¹' (Subtype.val ⁻¹' rationalSubset Aplus T s) =
      Subtype.val ⁻¹' rationalSubset Bplus (T.image φ) (φ s) := by
  ext ⟨v, hv⟩
  simp only [Set.mem_preimage, spaComap_val]
  simpa only [Set.mem_inter_iff, Set.mem_preimage, hv, and_true] using
    Set.ext_iff.mp (comap_preimage_rationalSubset_inter_spa φ hφ hplus T s) v

/-- If pullback along `φ` embeds valuation spectra, then its restriction to compatible sub-unit
loci is also an embedding. -/
theorem isEmbedding_spaComap (φ : A →+* B) (hφ : Continuous φ) (Aplus : Subring A)
    (Bplus : Subring B) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hemb : Topology.IsEmbedding (comap φ)) :
    Topology.IsEmbedding (spaComap φ hφ Aplus Bplus hplus) := by
  have hcomp : Subtype.val ∘ spaComap φ hφ Aplus Bplus hplus =
      comap φ ∘ Subtype.val := by
    funext v
    exact spaComap_val φ hφ Aplus Bplus hplus v
  refine Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp ?_
  rw [hcomp]
  exact hemb.comp Topology.IsEmbedding.subtypeVal

section Quotient

/-- The map on sub-unit valuation loci for a quotient homomorphism and the image plus ring is a
topological embedding. -/
theorem isEmbedding_spaComap_quotientMk (J : Ideal A) (Aplus : Subring A) :
    Topology.IsEmbedding (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J))
      (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩)) :=
  isEmbedding_spaComap _ _ _ _ _ (isEmbedding_comap_quotientMk J)

/-- The range of the quotient map with the image plus ring is the points whose support contains
`J`. -/
theorem range_spaComap_quotientMk (J : Ideal A) (Aplus : Subring A) :
    Set.range (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J))
      (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩)) =
      Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} := by
  ext ⟨v, hv⟩
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨w, hw⟩, heq⟩
    have hval : comap (Ideal.Quotient.mk J) w = v := Subtype.ext_iff.mp heq
    rw [← hval]
    exact self_le_supp_comap J w
  · intro hJ
    have hlift_spa : quotientLift J hJ ∈ spa (Aplus.map (Ideal.Quotient.mk J)) := by
      rw [mem_spa_iff]
      refine ⟨IsContinuous.quotientLift J hJ (mem_spa_iff Aplus v |>.mp hv).1, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_one (Ideal.Quotient.mk J), ← comap_vle, comap_quotientLift]
      exact (mem_spa_iff Aplus v |>.mp hv).2 a ha
    refine ⟨⟨quotientLift J hJ, hlift_spa⟩, ?_⟩
    apply Subtype.ext
    exact (spaComap_val (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J)) _ ⟨quotientLift J hJ, hlift_spa⟩).trans
        (comap_quotientLift J hJ)

/-- The locus in a sub-unit valuation space where the support contains `J` is closed. -/
theorem isClosed_support_locus (Aplus : Subring A) (J : Ideal A) :
    IsClosed (Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} : Set (spa Aplus)) := by
  have hlocus : {v : Spv A | J ≤ v.supp} =
      suppFun ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) := by
    ext v
    simp [PrimeSpectrum.mem_zeroLocus, suppFun_asIdeal]
  rw [hlocus, ← Set.preimage_comp]
  exact (PrimeSpectrum.isClosed_zeroLocus (J : Set A)).preimage
    (continuous_suppFun.comp continuous_subtype_val)

/-- The quotient homomorphism with the image plus ring induces a closed embedding of sub-unit
valuation loci. -/
theorem isClosedEmbedding_spaComap_quotientMk (J : Ideal A) (Aplus : Subring A) :
    Topology.IsClosedEmbedding (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J))
      (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩)) :=
  ⟨isEmbedding_spaComap_quotientMk J Aplus,
    range_spaComap_quotientMk J Aplus ▸ isClosed_support_locus Aplus J⟩

end Quotient

end TauCeti.ValuationSpectrum
