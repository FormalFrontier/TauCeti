/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.RingTheory.Huber.Pair

/-!
# Maps of adic spectra for Huber pairs

This file bundles the generic pullback API from
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap` for morphisms of Huber pairs and proves the
quotient-pair form of **Wedhorn, *Adic Spaces*, Proposition 7.38**.

## Main definitions

* `TauCeti.Huber.Pair.Hom.spaComap`: the contravariant map on adic spectra induced by a morphism
  of Huber pairs.

## Main results

* `TauCeti.Huber.Pair.Hom.continuous_spaComap`: the induced map is continuous.
* `TauCeti.Huber.Pair.Hom.spaComap_id`, `spaComap_comp`: contravariant functoriality.
* `TauCeti.Huber.Pair.Hom.spaComap_preimage_rationalSubset`: preimages of rational subsets.
* `TauCeti.Huber.Pair.Hom.isClosedEmbedding_spaComap_quotientHom`: the quotient-pair morphism
  induces a closed embedding of adic spectra.
* `TauCeti.Huber.Pair.Hom.range_spaComap_quotientHom`: its range is the locus of points whose
  support contains the quotient ideal.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.23, Remark 7.30, Proposition 7.38.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch `dev/adic-spaces` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, files `AffinoidRings.lean` and
`AdicSpectrum.lean`, was consulted rather than copied. AINTLIB bundles its affinoid-ring data;
this file instead delegates the topology and quotient-support arguments to the more general
subring-level results and supplies only the Huber-pair interface.
-/

public section

namespace TauCeti.Huber.Pair.Hom

open TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  {S : Pair A} {T : Pair B} {U : Pair C}

/-- The contravariant continuous map on adic spectra induced by a morphism of Huber pairs:
`Spa(T) → Spa(S)`. -/
def spaComap (f : Hom S T) : spa T.plus → spa S.plus :=
  ValuationSpectrum.spaComap f.toRingHom f.continuous_toRingHom S.plus T.plus f.map_mem_plus

/-- The underlying valuation of `f.spaComap v` is the pullback of `v` along the underlying ring
homomorphism of `f`. -/
@[simp]
theorem spaComap_val (f : Hom S T) (v : spa T.plus) :
    (f.spaComap v).1 = ValuationSpectrum.comap f.toRingHom v.1 :=
  ValuationSpectrum.spaComap_val f.toRingHom f.continuous_toRingHom S.plus T.plus
    f.map_mem_plus v

/-- `f.spaComap` is continuous. -/
theorem continuous_spaComap (f : Hom S T) : Continuous f.spaComap :=
  ValuationSpectrum.continuous_spaComap f.toRingHom f.continuous_toRingHom S.plus T.plus
    f.map_mem_plus

/-- `spaComap` for the identity morphism is the identity map on `Spa(S)`. -/
@[simp]
theorem spaComap_id (S : Pair A) : (Hom.id S).spaComap = _root_.id := by
  funext v
  apply Subtype.ext
  rw [spaComap_val, Hom.toRingHom_id]
  exact congr_fun ValuationSpectrum.comap_id v.1

/-- `spaComap` is contravariantly functorial for composition of morphisms of Huber pairs:
`(g ∘ f).spaComap = f.spaComap ∘ g.spaComap`. -/
@[simp]
theorem spaComap_comp (g : Hom T U) (f : Hom S T) :
    (g.comp f).spaComap = f.spaComap ∘ g.spaComap := by
  funext v
  apply Subtype.ext
  simp only [spaComap_val, Hom.toRingHom_comp, Function.comp_apply]
  exact congr_fun (ValuationSpectrum.comap_comp f.toRingHom g.toRingHom) v.1

open scoped Classical in
/-- The preimage of a rational subset under the map induced by a morphism of Huber pairs is the
rational subset obtained by mapping its defining functions. -/
theorem spaComap_preimage_rationalSubset (f : Hom S T) (T' : Finset A) (s : A) :
    f.spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset S.plus T' s) =
      Subtype.val ⁻¹' rationalSubset T.plus (T'.image f.toRingHom) (f.toRingHom s) := by
  simpa only [spaComap] using
    ValuationSpectrum.spaComap_preimage_rationalSubset f.toRingHom f.continuous_toRingHom
      S.plus T.plus f.map_mem_plus T' s

section Quotient

private theorem quotient_spa_eq (S : Pair A) (J : Ideal A) :
    spa (S.quotient J).plus = spa (S.plus.map (Ideal.Quotient.mk J)) := by
  simp

/-- The quotient pair's adic spectrum is canonically homeomorphic to the sub-unit locus for the
image plus ring. -/
private noncomputable def quotientSpaHomeomorph (S : Pair A) (J : Ideal A) :
    spa (S.quotient J).plus ≃ₜ spa (S.plus.map (Ideal.Quotient.mk J)) :=
  Homeomorph.setCongr (quotient_spa_eq S J)

private theorem spaComap_quotientHom_eq (S : Pair A) (J : Ideal A) :
    (quotientHom S J).spaComap =
      ValuationSpectrum.spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' S.plus
        (S.plus.map (Ideal.Quotient.mk J))
        (fun (a : A) (ha : a ∈ S.plus) ↦
          (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩) ∘
        quotientSpaHomeomorph S J := by
  funext v
  apply Subtype.ext
  have hev : ((quotientSpaHomeomorph S J) v).1 = v.1 := by
    exact congr_arg Subtype.val (Equiv.setCongr_apply (quotient_spa_eq S J) v)
  calc
    ((quotientHom S J).spaComap v).1 =
        ValuationSpectrum.comap (Ideal.Quotient.mk J) v.1 := by
      rw [spaComap_val, toRingHom_quotientHom]
    _ = ValuationSpectrum.comap (Ideal.Quotient.mk J) ((quotientSpaHomeomorph S J) v).1 :=
      congr_arg (ValuationSpectrum.comap (Ideal.Quotient.mk J)) hev.symm
    _ = (ValuationSpectrum.spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' S.plus
        (S.plus.map (Ideal.Quotient.mk J))
        (fun (a : A) (ha : a ∈ S.plus) ↦
          (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩)
        ((quotientSpaHomeomorph S J) v)).1 :=
      (ValuationSpectrum.spaComap_val (Ideal.Quotient.mk J) continuous_quotient_mk' S.plus
        (S.plus.map (Ideal.Quotient.mk J)) _ _).symm

/-- The range of the quotient-pair map on adic spectra is the support locus containing `J`. -/
theorem range_spaComap_quotientHom (S : Pair A) (J : Ideal A) :
    Set.range (quotientHom S J).spaComap =
      Subtype.val ⁻¹' {v : Spv A | J ≤ v.supp} := by
  rw [spaComap_quotientHom_eq, (quotientSpaHomeomorph S J).surjective.range_comp]
  exact ValuationSpectrum.range_spaComap_quotientMk J S.plus

/-- **Wedhorn Proposition 7.38:** the canonical quotient-pair morphism induces a closed embedding
of adic spectra. Its image is identified by `range_spaComap_quotientHom`. -/
theorem isClosedEmbedding_spaComap_quotientHom (S : Pair A) (J : Ideal A) :
    Topology.IsClosedEmbedding (quotientHom S J).spaComap := by
  rw [spaComap_quotientHom_eq]
  exact (ValuationSpectrum.isClosedEmbedding_spaComap_quotientMk J S.plus).comp
    (quotientSpaHomeomorph S J).isClosedEmbedding

end Quotient

end TauCeti.Huber.Pair.Hom
