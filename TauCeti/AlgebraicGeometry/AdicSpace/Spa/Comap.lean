/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset
public import TauCeti.RingTheory.Huber.Pair

/-!
# Pullbacks and quotient embeddings of the adic spectrum `Spa(A, A⁺)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.23, Remark 7.30, and
Proposition 7.38.**

This file constructs the contravariant continuous map on adic spectra induced by a continuous
ring homomorphism preserving the plus subrings:

```text
spaComap φ : Spa(B, B⁺) → Spa(A, A⁺)
```

and establishes its fundamental properties:
1. **Pullback of continuous sub-unit valuations** (`comap_mem_spa`).
2. **Continuity and functoriality** (`continuous_spaComap`, `spaComap_id`, `spaComap_comp`).
3. **Preimages of rational subsets** (`comap_preimage_rationalSubset`, `spaComap_preimage_rationalSubset`).
4. **Quotient embeddings (Wedhorn Proposition 7.38)** (`isEmbedding_spaComap_quotient`,
   `range_spaComap_quotient`): for an ideal `J ⊆ A`, the quotient map `A → A ⧸ J` induces a
   topological embedding `Spa(A ⧸ J, A⁺ ⧸ J) → Spa(A, A⁺)` whose image is the closed subset
   `{v ∈ Spa(A, A⁺) | J ≤ supp v}`.

## Main definitions

* `TauCeti.ValuationSpectrum.spaComap` : the continuous map `spa Bplus → spa Aplus` induced by a
  continuous ring homomorphism `φ : A →+* B` with `φ(Aplus) ⊆ Bplus`.
* `TauCeti.Huber.Pair.Hom.spaComap` : the bundled version for morphisms of Huber pairs `Pair.Hom S T`.

## Main results

* `TauCeti.ValuationSpectrum.comap_mem_spa` : `v ∈ spa Bplus` implies `comap φ v ∈ spa Aplus`.
* `TauCeti.ValuationSpectrum.continuous_spaComap` : `spaComap` is continuous for the subspace topologies.
* `TauCeti.ValuationSpectrum.spaComap_id`, `spaComap_comp` : `spaComap` is contravariantly functorial.
* `TauCeti.ValuationSpectrum.comap_preimage_rationalSubset`,
  `spaComap_preimage_rationalSubset` : preimages of rational subsets under `spaComap`.
* `TauCeti.ValuationSpectrum.isEmbedding_spaComap_quotient` : **Wedhorn Proposition 7.38**, the
  quotient map induces a topological embedding on adic spectra.
* `TauCeti.ValuationSpectrum.range_spaComap_quotient` : the image of the quotient embedding is
  the sub-locus of valuations whose support contains `J`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23, Remark 7.30, Proposition 7.38.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [CommRing C] [TopologicalSpace C]

/-- A continuous ring homomorphism mapping `A⁺` into `B⁺` pulls points of `Spa (B, B⁺)` back
to points of `Spa (A, A⁺)`. -/
theorem comap_mem_spa {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {v : Spv B} (hv : v ∈ spa Bplus) :
    comap φ v ∈ spa Aplus := by
  rw [mem_spa_iff] at hv ⊢
  refine ⟨hv.1.comap hφ, fun a ha ↦ ?_⟩
  rw [comap_vle]
  exact hv.2 (φ a) (hplus a ha)

/-- The contravariant map on adic spectra `spa Bplus → spa Aplus` induced by a continuous ring
homomorphism `φ : A →+* B` carrying `Aplus` into `Bplus`. -/
def spaComap (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (v : spa Bplus) : spa Aplus :=
  ⟨comap φ v.1, comap_mem_spa hφ hplus v.2⟩

@[simp]
theorem spaComap_val (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (v : spa Bplus) :
    (spaComap φ hφ hplus v).1 = comap φ v.1 := (rfl)

/-- `spaComap` is continuous for the subspace topologies on adic spectra. -/
theorem continuous_spaComap (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) :
    Continuous (spaComap φ hφ hplus) := by
  rw [continuous_induced_rng]
  exact (continuous_comap φ).comp continuous_subtype_val

/-- `spaComap` of the identity homomorphism is the identity map on `spa Aplus`. -/
@[simp]
theorem spaComap_id {Aplus : Subring A} :
    spaComap (RingHom.id A) continuous_id (fun _ ha ↦ ha) = id := by
  ext v
  exact Subtype.ext (congr_fun comap_id v.1)

/-- `spaComap` is contravariantly functorial: `spaComap (ψ ∘ φ) = spaComap φ ∘ spaComap ψ`. -/
theorem spaComap_comp {φ : A →+* B} (hφ : Continuous φ) {ψ : B →+* C} (hψ : Continuous ψ)
    {Aplus : Subring A} {Bplus : Subring B} {Cplus : Subring C}
    (hφ_plus : ∀ a ∈ Aplus, φ a ∈ Bplus) (hψ_plus : ∀ b ∈ Bplus, ψ b ∈ Cplus) :
    spaComap (ψ.comp φ) (hψ.comp hφ) (fun a ha ↦ hψ_plus (φ a) (hφ_plus a ha)) =
      spaComap φ hφ hφ_plus ∘ spaComap ψ hψ hψ_plus := by
  ext v
  exact Subtype.ext (congr_fun (comap_comp φ ψ) v.1)

/-- Preimage of a rational subset under `comap φ` in `spa Bplus`:
`(comap φ) ⁻¹' R(T/s) ∩ Spa (B, B⁺) = R(φ(T)/φ(s))`. -/
theorem comap_preimage_rationalSubset (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : Finset A) (s : A) :
    comap φ ⁻¹' (rationalSubset Aplus T s) ∩ spa Bplus =
      rationalSubset Bplus (T.image φ) (φ s) := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_rationalSubset_iff, mem_spa_iff,
    Finset.mem_image, comap_vle]
  constructor
  · rintro ⟨⟨-, hT, hs⟩, hv_cont, hv_plus⟩
    refine ⟨⟨hv_cont, hv_plus⟩, fun t ht ↦ ?_, hs⟩
    obtain ⟨a, ha, rfl⟩ := ht
    exact hT a ha
  · rintro ⟨⟨hv_cont, hv_plus⟩, hT, hs⟩
    have hcomap : comap φ v ∈ spa Aplus := comap_mem_spa hφ hplus ⟨hv_cont, hv_plus⟩
    exact ⟨⟨hcomap, fun a ha ↦ hT (φ a) (Finset.mem_image_of_mem φ ha), hs⟩, hv_cont, hv_plus⟩

/-- Preimage of a rational subset under `spaComap`: the preimage of `R(T/s)` under `spaComap φ` is
`R(φ(T)/φ(s))`. -/
theorem spaComap_preimage_rationalSubset (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : Finset A) (s : A) :
    spaComap φ hφ hplus ⁻¹' (Subtype.val ⁻¹' rationalSubset Aplus T s) =
      Subtype.val ⁻¹' rationalSubset Bplus (T.image φ) (φ s) := by
  ext ⟨v, hv⟩
  simp only [Set.mem_preimage, spaComap_val]
  have := congr_arg (fun (S : Set (Spv B)) ↦ v ∈ S)
    (comap_preimage_rationalSubset φ hφ hplus T s)
  simp only [Set.mem_inter_iff, Set.mem_preimage, hv, and_true] at this
  exact this

section Quotient

/-- Continuity of the lifted valuation on the quotient ring `A ⧸ J`. -/
theorem isContinuous_quotientLift (J : Ideal A) ⦃v : Spv A⦄ (hJ : J ≤ v.supp)
    (hv : v.IsContinuous) : (quotientLift J hJ).IsContinuous := by
  rw [isContinuous_def] at hv ⊢
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [isOpen_coinduced, Set.preimage_setOf_eq]
  have h_eq : ∀ y : A, (quotientLift J hJ).valuation (Ideal.Quotient.mk J y) <
      (quotientLift J hJ).valuation (Ideal.Quotient.mk J a) ↔ v.valuation y < v.valuation a := by
    intro y
    have h1 : (quotientLift J hJ).valuation (Ideal.Quotient.mk J y) =
        (comap (Ideal.Quotient.mk J) (quotientLift J hJ)).valuation y := rfl
    rw [h1, comap_quotientLift J hJ]
    have h2 : (quotientLift J hJ).valuation (Ideal.Quotient.mk J a) =
        (comap (Ideal.Quotient.mk J) (quotientLift J hJ)).valuation a := rfl
    rw [h2, comap_quotientLift J hJ]
  have h_set : {y : A | (quotientLift J hJ).valuation (Ideal.Quotient.mk J y) <
      (quotientLift J hJ).valuation (Ideal.Quotient.mk J a)} =
      {y : A | v.valuation y < v.valuation a} := by
    ext y
    exact h_eq y
  rw [h_set]
  exact hv a

/-- **Wedhorn Proposition 7.38 (Part 1)**: The contravariant map on adic spectra induced by the
quotient homomorphism `A → A ⧸ J` is a topological embedding. -/
theorem isEmbedding_spaComap_quotient (J : Ideal A) (Aplus : Subring A) :
    Topology.IsEmbedding
      (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk
        (fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩) :
        spa (Aplus.map (Ideal.Quotient.mk J)) → spa Aplus) := by
  refine Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp ?_
  have hcomp : Subtype.val ∘ spaComap (Ideal.Quotient.mk J) continuous_quotient_mk
        (fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩) =
      comap (Ideal.Quotient.mk J) ∘ Subtype.val := rfl
  rw [hcomp]
  exact (isEmbedding_comap_quotientMk J).comp Topology.IsEmbedding.subtypeVal

/-- **Wedhorn Proposition 7.38 (Part 2)**: The range of the quotient map on adic spectra is the
closed subset of points whose support contains `J`. -/
theorem range_spaComap_quotient (J : Ideal A) (Aplus : Subring A) :
    Set.range (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk
      (fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩) :
      spa (Aplus.map (Ideal.Quotient.mk J)) → spa Aplus) =
      Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} := by
  ext ⟨v, hv⟩
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨w, hw⟩, heq⟩
    have hval : comap (Ideal.Quotient.mk J) w = v := Subtype.ext_iff.mp heq
    rw [← hval]
    exact self_le_supp_comap J w
  · intro hJ
    have hlift := quotientLift J hJ
    have hlift_spa : hlift ∈ spa (Aplus.map (Ideal.Quotient.mk J)) := by
      rw [mem_spa_iff]
      refine ⟨isContinuous_quotientLift J hJ (mem_spa_iff Aplus v |>.mp hv).1, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [← comap_vle (Ideal.Quotient.mk J), comap_quotientLift J hJ]
      exact (mem_spa_iff Aplus v |>.mp hv).2 a ha
    refine ⟨⟨hlift, hlift_spa⟩, ?_⟩
    ext
    exact comap_quotientLift J hJ

end Quotient

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.Pair.Hom

open TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

/-- The contravariant continuous map on adic spectra induced by a morphism of Huber pairs:
`Spa(T) → Spa(S)`. -/
def spaComap (f : Hom S T) : spa T.plus → spa S.plus :=
  TauCeti.ValuationSpectrum.spaComap f.toRingHom f.continuous_toRingHom f.map_mem_plus

/-- `f.spaComap` is continuous. -/
theorem continuous_spaComap (f : Hom S T) : Continuous f.spaComap :=
  TauCeti.ValuationSpectrum.continuous_spaComap f.toRingHom f.continuous_toRingHom f.map_mem_plus

/-- `spaComap` for the identity morphism is the identity map on `Spa(S)`. -/
@[simp]
theorem spaComap_id (S : Pair A) : (Hom.id S).spaComap = id :=
  TauCeti.ValuationSpectrum.spaComap_id

/-- `spaComap` is contravariantly functorial for composition of morphisms of Huber pairs:
`(g ∘ f).spaComap = f.spaComap ∘ g.spaComap`. -/
theorem spaComap_comp (g : Hom T U) (f : Hom S T) :
    (g.comp f).spaComap = f.spaComap ∘ g.spaComap :=
  TauCeti.ValuationSpectrum.spaComap_comp f.continuous_toRingHom g.continuous_toRingHom
    f.map_mem_plus g.map_mem_plus

end TauCeti.Huber.Pair.Hom
