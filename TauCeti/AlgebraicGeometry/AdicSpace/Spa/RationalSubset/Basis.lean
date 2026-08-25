/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sets.Opens
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Spectral
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# The rational basis of the adic spectrum

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.29, Remark 7.30(5),
and Theorem 7.35.**

Let `P = (A₀,I)` be a pair of definition of a Huber ring. The rational subsets

```text
R(T/s) = {v ∈ Spa(A,A⁺) : v(t) ≤ v(s) ≠ 0 for every t ∈ T}
```

for which the ideal `T · A` is open form a basis of quasi-compact opens of `Spa(A,A⁺)`.
The proof compares them with the rational basis of `Spv(A,IA)`. By Wedhorn Lemma 6.6,
openness of `T · A` implies admissibility for `IA`; conversely, an admissible pair `(T,s)`
has open numerator ideal after inserting `s` among the numerators, which does not change its
rational subset. This comparison also transports closure under intersections and quasi-compactness.

The plus ring is arbitrary here. The additional condition that it be a ring of integral
elements is part of calling the resulting space the adic spectrum of a Huber pair, but none of
the basis arguments uses it.

## Main definitions

* `TauCeti.ValuationSpectrum.spaRationalFamily`: the family of rational subsets with open
  numerator ideal, viewed as subsets of `spa Aplus`.
* `TauCeti.ValuationSpectrum.spaRationalOpens`: the same family presented as a set of `Opens`,
  the form the sheaf-theoretic consumers take.

## Main results

* `TauCeti.ValuationSpectrum.inter_mem_spaRationalFamily`: the family is closed under binary
  intersections, completing Wedhorn Remark 7.30(5).
* `TauCeti.ValuationSpectrum.isTopologicalBasis_spaRationalFamily`: the family is a basis for
  the topology of `spa Aplus`, with `TauCeti.ValuationSpectrum.isBasis_spaRationalOpens` the same
  statement in the `Opens.IsBasis` form.
* `TauCeti.ValuationSpectrum.isCompact_of_mem_spaRationalFamily`: every member of the family is
  quasi-compact. Each result also has an `_of_pairOfDefinition` form for use with a specified
  pair of definition.
* `TauCeti.ValuationSpectrum.exists_finite_spaRationalFamily_refinement`: every open cover of a
  member of the family admits a finite refinement by members of the family — the two results
  above combined, and the form a sheaf criterion on this basis consumes.
* `TauCeti.ValuationSpectrum.spa_eq_biUnion_rationalSubset_of_isTateRing_of_isOpen`: over a Tate
  ring, if a finite set `T` generates an open ideal, then the standard rational subsets cover
  `spa Aplus` (Wedhorn Corollary 7.53 specialization).

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.29, Remark 7.30, Theorem 7.35,
  Corollary 7.53, and Lemma 6.6.
-/

public section

namespace TauCeti.ValuationSpectrum

open Set Topology _root_.TopologicalSpace TauCeti TauCeti.Huber
open scoped Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### Open numerator ideals and admissibility -/

section TopologicalRing

variable [IsTopologicalRing A]

/-- An open numerator ideal is admissible for the extended ideal of every pair of definition.
This is Wedhorn Lemma 6.6 applied to the inclusion of the numerator span into the span obtained
after adjoining the denominator. -/
theorem isAdmissible_extendedIdealOfDefinition_of_isOpen_span (P : PairOfDefinition A)
    {T : Finset A} {s : A} (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    IsAdmissible P.extendedIdealOfDefinition T s := by
  rw [isAdmissible_iff]
  refine (P.isOpen_iff_le_radical _).mp hT |>.trans (Ideal.radical_mono ?_)
  exact Ideal.span_mono (Set.subset_insert s (T : Set A))

/-- An admissible numerator set becomes an open numerator ideal after adjoining its denominator.
The rational subset itself is unchanged by this operation. -/
theorem isOpen_span_insert_of_isAdmissible_extendedIdealOfDefinition (P : PairOfDefinition A)
    {T : Finset A} {s : A} (hT : IsAdmissible P.extendedIdealOfDefinition T s) :
    IsOpen (Ideal.span (insert s (T : Set A)) : Set A) := by
  rw [P.isOpen_iff_le_radical]
  exact isAdmissible_iff.mp hT

end TopologicalRing

/-! ### The rational family -/

/-- The rational family of `Spa(A,A⁺)`: rational subsets `R(T/s)` whose numerator ideal
`T · A` is open, viewed as subsets of the subtype `spa Aplus`. -/
def spaRationalFamily (Aplus : Subring A) : Set (Set (spa Aplus)) :=
  {U | ∃ (T : Finset A) (s : A), IsOpen (Ideal.span (T : Set A) : Set A) ∧
    U = Subtype.val ⁻¹' rationalSubset Aplus T s}

/-- Membership in the rational family is a presentation as `R(T/s)` with open numerator ideal. -/
@[simp]
theorem mem_spaRationalFamily_iff {Aplus : Subring A} {U : Set (spa Aplus)} :
    U ∈ spaRationalFamily Aplus ↔
      ∃ (T : Finset A) (s : A), IsOpen (Ideal.span (T : Set A) : Set A) ∧
        U = Subtype.val ⁻¹' rationalSubset Aplus T s := Iff.rfl

/-- The whole adic spectrum belongs to its rational family, presented as `R({1}/1)`. -/
theorem univ_mem_spaRationalFamily (Aplus : Subring A) :
    Set.univ ∈ spaRationalFamily Aplus := by
  refine ⟨{1}, 1, ?_, ?_⟩
  · have hspan : Ideal.span (({1} : Finset A) : Set A) = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span (by simp))
    rw [hspan]
    exact isOpen_univ
  · rw [rationalSubset_singleton_one]
    exact (Subtype.coe_preimage_self (spa Aplus)).symm

section TopologicalRing

variable [IsTopologicalRing A]

open Classical in
/-- If two numerator ideals are open, then so is the ideal spanned by the product of the
numerator sets after adjoining their respective denominators. This is the admissibility half of
the intersection formula for rational subsets. -/
private theorem isOpen_span_insert_mul_insert (P : PairOfDefinition A)
    {T₁ T₂ : Finset A} {s₁ s₂ : A}
    (hT₁ : IsOpen (Ideal.span (T₁ : Set A) : Set A))
    (hT₂ : IsOpen (Ideal.span (T₂ : Set A) : Set A)) :
    IsOpen (Ideal.span ((insert s₁ T₁ * insert s₂ T₂ : Finset A) : Set A) : Set A) := by
  classical
  rw [P.isOpen_iff_le_radical]
  have hmul :=
    (isAdmissible_extendedIdealOfDefinition_of_isOpen_span (s := s₁) P hT₁).mul
      (isAdmissible_extendedIdealOfDefinition_of_isOpen_span (s := s₂) P hT₂)
  rw [isAdmissible_iff] at hmul
  have hs : s₁ * s₂ ∈ insert s₁ T₁ * insert s₂ T₂ :=
    Finset.mul_mem_mul (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
  rwa [Set.insert_eq_self.mpr (Finset.mem_coe.mpr hs)] at hmul

/-- **Wedhorn Remark 7.30(5).** Rational subsets with open numerator ideal are closed under
intersection. The set identity is `rationalSubset_inter`; admissibility is multiplicative in
`Spv(A,IA)`, and adjoining the product denominator turns it back into openness. -/
theorem inter_mem_spaRationalFamily_of_pairOfDefinition (P : PairOfDefinition A)
    {Aplus : Subring A}
    {U V : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus)
    (hV : V ∈ spaRationalFamily Aplus) : U ∩ V ∈ spaRationalFamily Aplus := by
  classical
  obtain ⟨T₁, s₁, hT₁, rfl⟩ := hU
  obtain ⟨T₂, s₂, hT₂, rfl⟩ := hV
  refine ⟨insert s₁ T₁ * insert s₂ T₂, s₁ * s₂,
    isOpen_span_insert_mul_insert P hT₁ hT₂, ?_⟩
  rw [← Set.preimage_inter, rationalSubset_inter]

/-- **Wedhorn Remark 7.30(5).** Over a Huber ring, the rational family is closed under binary
intersection, without choosing a pair of definition. -/
theorem inter_mem_spaRationalFamily [IsHuberRing A] {Aplus : Subring A}
    {U V : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus)
    (hV : V ∈ spaRationalFamily Aplus) : U ∩ V ∈ spaRationalFamily Aplus :=
  (IsHuberRing.nonempty_pairOfDefinition (A := A)).elim
    fun P ↦ inter_mem_spaRationalFamily_of_pairOfDefinition P hU hV

/-! ### Basis and quasi-compactness -/

/-- **Rational subsets form a basis of `Spa(A,A⁺)`.** The statement is made from an explicit
pair of definition. Every rational neighbourhood in the basis of `Spv(A,IA)` becomes a member
of `spaRationalFamily` after adjoining its denominator. -/
theorem isTopologicalBasis_spaRationalFamily_of_pairOfDefinition
    (P : PairOfDefinition A) (Aplus : Subring A) :
    IsTopologicalBasis (spaRationalFamily Aplus) := by
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨T, s, -, rfl⟩
    exact isOpen_val_preimage_rationalSubset Aplus T s
  · intro x U hx hU
    obtain ⟨O, hO, rfl⟩ := Topology.IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp hU
    let hfg : ∃ J : Ideal A, J.FG ∧ P.extendedIdealOfDefinition.radical = J.radical :=
      ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩
    let xI : spvOfIdeal P.extendedIdealOfDefinition hfg :=
      ⟨x, spa_subset_spvOfIdeal P Aplus x.property⟩
    have hxO : xI ∈ Subtype.val ⁻¹' O := hx
    have hOI : IsOpen (Subtype.val ⁻¹' O : Set (spvOfIdeal P.extendedIdealOfDefinition hfg)) :=
      hO.preimage continuous_subtype_val
    obtain ⟨V, hVr, hxV, hVO⟩ :=
      (isTopologicalBasis_rationalFamily P.extendedIdealOfDefinition hfg).isOpen_iff.mp hOI xI hxO
    obtain ⟨T, s, hadm, rfl⟩ := mem_rationalFamily_iff.mp hVr
    let W : Set (spa Aplus) := Subtype.val ⁻¹' rationalSubset Aplus (insert s T) s
    have hOpen : IsOpen (Ideal.span ((insert s T : Finset A) : Set A) : Set A) := by
      simpa only [Finset.coe_insert] using
        isOpen_span_insert_of_isAdmissible_extendedIdealOfDefinition P hadm
    have hW : W ∈ spaRationalFamily Aplus :=
      mem_spaRationalFamily_iff.mpr ⟨insert s T, s, hOpen, rfl⟩
    refine ⟨W, hW, ?_, ?_⟩
    · simp only [W]
      rw [rationalSubset_insert_self, val_preimage_rationalSubset]
      exact hxV
    · intro y hy
      simp only [W] at hy
      rw [rationalSubset_insert_self, val_preimage_rationalSubset] at hy
      let yI : spvOfIdeal P.extendedIdealOfDefinition hfg :=
        ⟨y, spa_subset_spvOfIdeal P Aplus y.property⟩
      exact hVO (a := yI) hy

/-- **Rational subsets form a basis of `Spa(A,A⁺)`**, without choosing a pair of definition
of the Huber ring. -/
theorem isTopologicalBasis_spaRationalFamily [IsHuberRing A] (Aplus : Subring A) :
    IsTopologicalBasis (spaRationalFamily Aplus) :=
  (IsHuberRing.nonempty_pairOfDefinition (A := A)).elim
    fun P ↦ isTopologicalBasis_spaRationalFamily_of_pairOfDefinition P Aplus

/-- Every member of the rational family of `Spa(A,A⁺)` is quasi-compact. Its counterpart in
`Spv(A,IA)` is a quasi-compact open, and its intersection with the pro-constructible trace of
`spa Aplus` stays quasi-compact. -/
theorem isCompact_of_mem_spaRationalFamily_of_pairOfDefinition
    (P : PairOfDefinition A) {Aplus : Subring A}
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) : IsCompact U := by
  obtain ⟨T, s, hT, rfl⟩ := hU
  let hfg : ∃ J : Ideal A, J.FG ∧ P.extendedIdealOfDefinition.radical = J.radical :=
    ⟨P.extendedIdealOfDefinition, P.fg_extendedIdealOfDefinition, rfl⟩
  let S : Set (spvOfIdeal P.extendedIdealOfDefinition hfg) :=
    Subtype.val ⁻¹' spa Aplus
  let V : Set (spvOfIdeal P.extendedIdealOfDefinition hfg) :=
    Subtype.val ⁻¹' basicOpenFinset T s
  have := spectralSpace_spvOfIdeal P.extendedIdealOfDefinition hfg
  have hS : IsProConstructible S := isProConstructible_val_preimage_spa P Aplus
  have hVopen : IsOpen V := (isOpen_basicOpenFinset T s).preimage continuous_subtype_val
  have hVmem : V ∈ rationalFamily P.extendedIdealOfDefinition hfg :=
    mem_rationalFamily_iff.mpr
      ⟨T, s, isAdmissible_extendedIdealOfDefinition_of_isOpen_span P hT, rfl⟩
  have hVcompact : IsCompact V :=
    isCompact_of_mem_rationalFamily P.extendedIdealOfDefinition hfg hVmem
  let e : S ≃ₜ spa Aplus := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (fun x hx ↦ ⟨⟨x, spa_subset_spvOfIdeal P Aplus hx⟩, rfl⟩)
  apply e.isCompact_preimage.mp
  have heval (x : S) : ((e x : spa Aplus) : Spv A) =
      ((x : spvOfIdeal P.extendedIdealOfDefinition hfg) : Spv A) := by
    simpa only [e] using
      (Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe
        Topology.IsEmbedding.subtypeVal
        (fun x hx ↦ ⟨⟨x, spa_subset_spvOfIdeal P Aplus hx⟩, rfl⟩) x)
  have hpre : e ⁻¹' (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) =
      Subtype.val ⁻¹' V := by
    ext x
    simp only [Set.mem_preimage, val_preimage_rationalSubset, V]
    rw [heval]
  rw [hpre]
  exact hS.isSpectralMap_subtypeVal.isCompact_preimage_of_isOpen hVopen hVcompact

/-- Every rational subset with open numerator ideal in the adic spectrum of a Huber ring is
quasi-compact, without choosing a pair of definition. -/
theorem isCompact_of_mem_spaRationalFamily [IsHuberRing A] {Aplus : Subring A}
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) : IsCompact U :=
  (IsHuberRing.nonempty_pairOfDefinition (A := A)).elim
    fun P ↦ isCompact_of_mem_spaRationalFamily_of_pairOfDefinition P hU

/-! ### The rational basis as a family of opens -/

/-- The rational family of `Spa(A,A⁺)`, presented as a set of `Opens` rather than of sets. This is
the form `Opens.IsBasis` and the sheaf criteria on a basis take. -/
def spaRationalOpens (Aplus : Subring A) : Set (Opens (spa Aplus)) :=
  {U : Opens (spa Aplus) | (U : Set (spa Aplus)) ∈ spaRationalFamily Aplus}

omit [IsTopologicalRing A] in
/-- An open lies in `spaRationalOpens` exactly when its underlying set is rational. -/
@[simp]
theorem mem_spaRationalOpens {Aplus : Subring A} {U : Opens (spa Aplus)} :
    U ∈ spaRationalOpens Aplus ↔ (U : Set (spa Aplus)) ∈ spaRationalFamily Aplus := Iff.rfl

/-- **The rational opens are a basis** in the `Opens.IsBasis` sense, which is the form the sheaf
criterion on a basis consumes. -/
theorem isBasis_spaRationalOpens [IsHuberRing A] (Aplus : Subring A) :
    Opens.IsBasis (spaRationalOpens Aplus) :=
  TauCeti.TopologicalSpace.Opens.isBasis_of_isTopologicalBasis
    (isTopologicalBasis_spaRationalFamily Aplus)

/-! ### Finite rational refinements -/

/-- **Every open cover of a rational subset admits a finite refinement by rational subsets.**
This is the previous two results combined: being a basis shrinks each point's cover member to a
rational neighbourhood, and quasi-compactness then keeps finitely many of them. It is the shape a
sheaf criterion on the rational basis consumes, where the cover is arbitrary but the Čech complex
must be built from the basis itself.

The two-step argument follows AINTLIB's `exists_finite_rational_refinement_huber` and its Tate-only
`exists_finite_rational_refinement` (branch `dev/adic-spaces`, commit `37bbdaeb`, Apache 2.0), in
`projects/AdicSpaces/Adic spaces/RestrictedLimitSheaf.lean`. Two differences: quasi-compactness is a
hypothesis there and is discharged here by `isCompact_of_mem_spaRationalFamily`; and the conclusion
there is a `Finset` of a bundled index type over `RationalLocData`, whereas this states a finite
subfamily of `spaRationalFamily` with the containment as a side condition, matching the vocabulary
this file already uses. -/
theorem exists_finite_spaRationalFamily_refinement [IsHuberRing A] {Aplus : Subring A}
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) {ι : Type*}
    (V : ι → Set (spa Aplus)) (hVopen : ∀ i, IsOpen (V i)) (hcover : U ⊆ ⋃ i, V i) :
    ∃ 𝒲 ⊆ spaRationalFamily Aplus, 𝒲.Finite ∧ (∀ W ∈ 𝒲, ∃ i, W ⊆ V i) ∧ U ⊆ ⋃₀ 𝒲 := by
  have hcov : U ⊆ ⋃ W ∈ {W ∈ spaRationalFamily Aplus | ∃ i, W ⊆ V i}, W := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    obtain ⟨W, hWmem, hxW, hWV⟩ :=
      (isTopologicalBasis_spaRationalFamily Aplus).exists_subset_of_mem_open hi (hVopen i)
    exact Set.mem_biUnion ⟨hWmem, i, hWV⟩ hxW
  obtain ⟨𝒲, h𝒲G, h𝒲fin, h𝒲cov⟩ :=
    (isCompact_of_mem_spaRationalFamily hU).elim_finite_subcover_image
      (fun W hW ↦ (isTopologicalBasis_spaRationalFamily Aplus).isOpen hW.1) hcov
  exact ⟨𝒲, fun W hW ↦ (h𝒲G hW).1, h𝒲fin, fun W hW ↦ (h𝒲G hW).2,
    by simpa [Set.sUnion_eq_biUnion] using h𝒲cov⟩

/-! ### Standard rational covers -/

section Tate

variable [IsTateRing A]

/-- Over a Tate ring, if a finite set `T` generates an open ideal, then the standard rational
subsets `(R(T/t))_{t ∈ T}` cover `spa Aplus`. -/
theorem spa_eq_biUnion_rationalSubset_of_isTateRing_of_isOpen (Aplus : Subring A) {T : Finset A}
    (hT : IsOpen ((Ideal.span (T : Set A) : Ideal A) : Set A)) :
    spa Aplus = ⋃ t ∈ T, rationalSubset Aplus T t :=
  spa_eq_biUnion_rationalSubset_of_span_eq_top Aplus
    ((IsTateRing.isOpen_iff_eq_top (Ideal.span (T : Set A))).mp hT)

end Tate

end TopologicalRing

end TauCeti.ValuationSpectrum

end
