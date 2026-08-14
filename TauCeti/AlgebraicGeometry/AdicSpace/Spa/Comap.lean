/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Integral
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset
public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Valuation.Continuous.Basic

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
3. **Preimages of rational subsets** (`comap_preimage_rationalSubset`,
   `spaComap_preimage_rationalSubset`).
4. **Quotient closed embeddings (Wedhorn Proposition 7.38)**
   (`Huber.Pair.Hom.isClosedEmbedding_spaComap_quotient`): for an ideal `J ⊆ A`, the quotient
   pair map induces a closed embedding whose image is `{v ∈ Spa(A, A⁺) | J ≤ supp v}`.

## Main definitions

* `TauCeti.ValuationSpectrum.spaComap` : the continuous map `spa Bplus → spa Aplus` induced by a
  continuous ring homomorphism `φ : A →+* B` with `φ(Aplus) ⊆ Bplus`.
* `TauCeti.Huber.Pair.Hom.spaComap` : the bundled version for morphisms of Huber pairs
  `Pair.Hom S T`.

## Main results

* `TauCeti.ValuationSpectrum.comap_mem_spa` : `v ∈ spa Bplus` implies `comap φ v ∈ spa Aplus`.
* `TauCeti.ValuationSpectrum.continuous_spaComap` : `spaComap` is continuous for the subspace
  topologies.
* `TauCeti.ValuationSpectrum.spaComap_id`, `spaComap_comp` : `spaComap` is contravariantly
  functorial.
* `TauCeti.ValuationSpectrum.comap_preimage_rationalSubset`,
  `spaComap_preimage_rationalSubset` : preimages of rational subsets under `spaComap`.
* `TauCeti.Huber.Pair.Hom.isClosedEmbedding_spaComap_quotient` : **Wedhorn Proposition 7.38**,
  the canonical quotient-pair map induces a closed embedding on adic spectra.
* `TauCeti.Huber.Pair.Hom.range_spaComap_quotient` : the image of the quotient-pair embedding is
  the closed sub-locus of valuations whose support contains `J`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23, Remark 7.30, Proposition 7.38.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Valuation

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [CommRing C] [TopologicalSpace C]

/-- A continuous ring homomorphism mapping `A⁺` into `B⁺` pulls points of `Spa (B, B⁺)` back
to points of `Spa (A, A⁺)`. -/
theorem comap_mem_spa {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {v : Spv B} (hv : v ∈ spa Bplus) :
    comap φ v ∈ spa Aplus := by
  rw [mem_spa_iff] at hv ⊢
  refine ⟨hv.1.comap hφ, fun a ha ↦ ?_⟩
  rw [comap_vle, map_one]
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
theorem spaComap_id {A : Type*} [CommRing A] [TopologicalSpace A] {Aplus : Subring A} :
    spaComap (RingHom.id A) continuous_id (Aplus := Aplus) (Bplus := Aplus) (fun _ ha ↦ ha) =
      _root_.id :=
  funext fun ⟨v, _⟩ ↦ Subtype.ext (congr_fun comap_id v)

/-- `spaComap` is contravariantly functorial: `spaComap (ψ ∘ φ) = spaComap φ ∘ spaComap ψ`. -/
theorem spaComap_comp {φ : A →+* B} (hφ : Continuous φ) {ψ : B →+* C} (hψ : Continuous ψ)
    (Aplus : Subring A) {Bplus : Subring B} {Cplus : Subring C}
    (hφ_plus : ∀ a ∈ Aplus, φ a ∈ Bplus) (hψ_plus : ∀ b ∈ Bplus, ψ b ∈ Cplus) :
    spaComap (ψ.comp φ) (hψ.comp hφ) (fun a ha ↦ hψ_plus (φ a) (hφ_plus a ha)) =
      spaComap φ hφ hφ_plus ∘ spaComap ψ hψ hψ_plus :=
  funext fun ⟨v, _⟩ ↦ Subtype.ext (congr_fun (comap_comp φ ψ) v)

open scoped Classical in
/-- Preimage of a rational subset under `comap φ` in `spa Bplus`:
`(comap φ) ⁻¹' R(T/s) ∩ Spa (B, B⁺) = R(φ(T)/φ(s))`. -/
theorem comap_preimage_rationalSubset (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : Finset A) (s : A) :
    comap φ ⁻¹' (rationalSubset Aplus T s) ∩ spa Bplus =
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
    have hcomap_cont : (comap φ v).IsContinuous := hv_cont.comap hφ
    have hcomap_plus : ∀ a ∈ Aplus, v.toValuativeRel.vle (φ a) 1 :=
      fun a ha ↦ hv_plus (φ a) (hplus a ha)
    exact ⟨⟨⟨hcomap_cont, hcomap_plus⟩,
      fun a ha ↦ hT (φ a) (Finset.mem_image_of_mem φ ha), hs⟩, hv_cont, hv_plus⟩

open scoped Classical in
/-- Preimage of a rational subset under `spaComap`: the preimage of `R(T/s)` under `spaComap φ` is
`R(φ(T)/φ(s))`. -/
theorem spaComap_preimage_rationalSubset (φ : A →+* B) (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (T : Finset A) (s : A) :
    spaComap φ hφ hplus ⁻¹' (Subtype.val ⁻¹' rationalSubset Aplus T s) =
      Subtype.val ⁻¹' rationalSubset Bplus (T.image φ) (φ s) := by
  ext ⟨v, hv⟩
  simp only [Set.mem_preimage, spaComap_val]
  have h := congr_arg (fun S ↦ v ∈ S) (comap_preimage_rationalSubset φ hφ hplus T s)
  simp only [Set.mem_inter_iff, Set.mem_preimage, hv, and_true] at h
  exact Iff.of_eq h

section Quotient

/-- Replacing a subring by its integral closure does not change the sub-unit valuation locus. -/
theorem spa_integralClosure (R : Subring A) :
    spa (integralClosure R A).toSubring = spa R := by
  ext v
  rw [mem_spa_iff, mem_spa_iff]
  refine and_congr_right fun _ ↦ ⟨fun h r hr ↦ ?_, fun h x hx ↦ ?_⟩
  · exact h r (algebraMap_mem (integralClosure R A) ⟨r, hr⟩)
  · let φ : R →+* v.valuation.integer :=
      R.subtype.codRestrict v.valuation.integer fun r ↦ by
        rw [Valuation.mem_integer_iff, ← map_one v.valuation, valuation_le_iff]
        exact h r r.2
    have hint : IsIntegral v.valuation.integer x :=
      (show IsIntegral R x from hx).map_of_comp_eq φ (RingHom.id A) (by ext r; rfl)
    have hxint := (Valuation.integer.integers v.valuation).mem_of_integral hint
    rwa [Valuation.mem_integer_iff, ← map_one v.valuation, valuation_le_iff] at hxint

/-- Continuity of the lifted valuation on the quotient ring `A ⧸ J`. -/
theorem isContinuous_quotientLift (J : Ideal A) ⦃v : Spv A⦄ (hJ : J ≤ v.supp)
    (hv : v.IsContinuous) : (quotientLift J hJ).IsContinuous := by
  have hv_cont : Valuation.IsContinuous v.valuation := (isContinuous_def v).mp hv
  have hv_open : ∀ a : A, IsOpen {y : A | v.valuation y < v.valuation a} :=
    Valuation.isContinuous_def.mp hv_cont
  rw [isContinuous_def, Valuation.isContinuous_def]
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h_eq : Ideal.Quotient.mk J ⁻¹'
        {x : A ⧸ J | (quotientLift J hJ).valuation x <
          (quotientLift J hJ).valuation (Ideal.Quotient.mk J a)} =
      {y : A | v.valuation y < v.valuation a} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, valuation_lt_iff]
    have h1 : (quotientLift J hJ).toValuativeRel.vlt
          (Ideal.Quotient.mk J y) (Ideal.Quotient.mk J a) ↔
        (comap (Ideal.Quotient.mk J) (quotientLift J hJ)).toValuativeRel.vlt y a := by
      rw [comap_vlt]
    rw [h1, comap_quotientLift J hJ, ← valuation_lt_iff]
  have h_open : IsOpen (Ideal.Quotient.mk J ⁻¹'
        {x : A ⧸ J | (quotientLift J hJ).valuation x <
          (quotientLift J hJ).valuation (Ideal.Quotient.mk J a)}) := by
    rw [h_eq]
    exact hv_open a
  exact isOpen_coinduced.mp h_open

/-- The map on sub-unit valuation loci for the quotient homomorphism and the image plus ring is a
topological embedding. The canonical quotient-pair version is
`TauCeti.Huber.Pair.Hom.isClosedEmbedding_spaComap_quotient`. -/
theorem isEmbedding_spaComap_quotient (J : Ideal A) (Aplus : Subring A) :
    Topology.IsEmbedding
      (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk'
        (fun (a : A) (ha : a ∈ Aplus) ↦
          (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩) :
        spa (Aplus.map (Ideal.Quotient.mk J)) → spa Aplus) := by
  have hcomp : Subtype.val ∘ spaComap (Ideal.Quotient.mk J) continuous_quotient_mk'
        (fun (a : A) (ha : a ∈ Aplus) ↦
          (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩) =
      comap (Ideal.Quotient.mk J) ∘ Subtype.val := by
    ext ⟨v, hv⟩
    rfl
  refine Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp ?_
  rw [hcomp]
  exact (isEmbedding_comap_quotientMk J).comp Topology.IsEmbedding.subtypeVal

/-- The range of the quotient map with the image plus ring is the points whose support contains
`J`. -/
theorem range_spaComap_quotient (J : Ideal A) (Aplus : Subring A) :
    Set.range (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk'
      (fun (a : A) (ha : a ∈ Aplus) ↦
        (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩) :
      spa (Aplus.map (Ideal.Quotient.mk J)) → spa Aplus) =
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
      refine ⟨isContinuous_quotientLift J hJ (mem_spa_iff Aplus v |>.mp hv).1, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      have h1 : (quotientLift J hJ).toValuativeRel.vle (Ideal.Quotient.mk J a) 1 ↔
          (comap (Ideal.Quotient.mk J) (quotientLift J hJ)).toValuativeRel.vle a 1 := by
        rw [comap_vle, map_one]
      rw [h1, comap_quotientLift J hJ]
      exact (mem_spa_iff Aplus v |>.mp hv).2 a ha
    refine ⟨⟨quotientLift J hJ, hlift_spa⟩, ?_⟩
    apply Subtype.ext
    dsimp
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
theorem spaComap_id (S : Pair A) : (Hom.id S).spaComap = _root_.id := by
  funext ⟨v, hv⟩
  apply Subtype.ext
  dsimp [spaComap, TauCeti.ValuationSpectrum.spaComap]
  rw [Hom.toRingHom_id, comap_id]
  rfl

/-- `spaComap` is contravariantly functorial for composition of morphisms of Huber pairs:
`(g ∘ f).spaComap = f.spaComap ∘ g.spaComap`. -/
theorem spaComap_comp (g : Hom T U) (f : Hom S T) :
    (g.comp f).spaComap = f.spaComap ∘ g.spaComap := by
  funext ⟨v, hv⟩
  apply Subtype.ext
  dsimp [spaComap, TauCeti.ValuationSpectrum.spaComap]
  rw [Hom.toRingHom_comp, comap_comp]
  rfl

section Quotient

/-- The map on adic spectra induced by the canonical quotient-pair morphism is an embedding. -/
theorem isEmbedding_spaComap_quotient (S : Pair A) (J : Ideal A) :
    Topology.IsEmbedding (quotientHom S J).spaComap := by
  have hcomp : Subtype.val ∘ (quotientHom S J).spaComap =
      ValuationSpectrum.comap (Ideal.Quotient.mk J) ∘ Subtype.val := by
    funext ⟨v, hv⟩
    change ValuationSpectrum.comap (quotientHom S J).toRingHom v =
      ValuationSpectrum.comap (Ideal.Quotient.mk J) v
    rw [quotientHom_toRingHom]
  refine Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp ?_
  rw [hcomp]
  exact (ValuationSpectrum.isEmbedding_comap_quotientMk J).comp
    Topology.IsEmbedding.subtypeVal

/-- The range of the quotient-pair map on adic spectra is the support locus containing `J`. -/
theorem range_spaComap_quotient (S : Pair A) (J : Ideal A) :
    Set.range (quotientHom S J).spaComap =
      Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} := by
  ext ⟨v, hv⟩
  simp only [Set.mem_range, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨w, hw⟩, heq⟩
    have hval := Subtype.ext_iff.mp heq
    simp only [spaComap, TauCeti.ValuationSpectrum.spaComap, quotientHom_toRingHom] at hval
    rw [← hval]
    exact ValuationSpectrum.self_le_supp_comap J w
  · intro hJ
    have hlift_spa_image : ValuationSpectrum.quotientLift J hJ ∈
        spa (S.plus.map (Ideal.Quotient.mk J)) := by
      rw [ValuationSpectrum.mem_spa_iff]
      refine ⟨ValuationSpectrum.isContinuous_quotientLift J hJ
        (ValuationSpectrum.mem_spa_iff S.plus v |>.mp hv).1, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      have h1 : (ValuationSpectrum.quotientLift J hJ).toValuativeRel.vle
          (Ideal.Quotient.mk J a) 1 ↔
          (ValuationSpectrum.comap (Ideal.Quotient.mk J)
            (ValuationSpectrum.quotientLift J hJ)).toValuativeRel.vle a 1 := by
        rw [ValuationSpectrum.comap_vle, map_one]
      rw [h1, ValuationSpectrum.comap_quotientLift J hJ]
      exact (ValuationSpectrum.mem_spa_iff S.plus v |>.mp hv).2 a ha
    have hlift_spa : ValuationSpectrum.quotientLift J hJ ∈ spa (S.quotient J).plus := by
      rw [quotient_plus]
      rw [ValuationSpectrum.spa_integralClosure]
      exact hlift_spa_image
    refine ⟨⟨ValuationSpectrum.quotientLift J hJ, hlift_spa⟩, ?_⟩
    apply Subtype.ext
    simpa only [spaComap, TauCeti.ValuationSpectrum.spaComap, quotientHom_toRingHom] using
      ValuationSpectrum.comap_quotientLift J hJ

private theorem isClosed_support_locus (S : Pair A) (J : Ideal A) :
    IsClosed (Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} : Set (spa S.plus)) := by
  have hlocus : {v : Spv A | J ≤ v.supp} =
      ValuationSpectrum.suppFun ⁻¹' PrimeSpectrum.zeroLocus (J : Set A) := by
    ext v
    simp [PrimeSpectrum.mem_zeroLocus, ValuationSpectrum.suppFun_asIdeal]
  rw [hlocus, ← Set.preimage_comp]
  exact (PrimeSpectrum.isClosed_zeroLocus (J : Set A)).preimage
    (ValuationSpectrum.continuous_suppFun.comp continuous_subtype_val)

/-- **Wedhorn Proposition 7.38**: the canonical quotient-pair morphism induces a closed
embedding of adic spectra, with image the points whose support contains the quotient ideal. -/
theorem isClosedEmbedding_spaComap_quotient (S : Pair A) (J : Ideal A) :
    Topology.IsClosedEmbedding (quotientHom S J).spaComap :=
  ⟨isEmbedding_spaComap_quotient S J,
    range_spaComap_quotient S J ▸ isClosed_support_locus S J⟩

end Quotient

end TauCeti.Huber.Pair.Hom
