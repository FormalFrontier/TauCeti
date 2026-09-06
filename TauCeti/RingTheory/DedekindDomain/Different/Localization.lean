/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Localization.Integer

/-!
# Localization of the different ideal

This file proves that trace duals and different ideals commute with localization.  This is the
localization input needed to read the transitivity theorem for different ideals coefficientwise at
a tower of discrete valuations.

## References

- [AlgebraicCurves roadmap, Layer 7](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/AlgebraicCurves/README.md#layer-7-the-different-and-the-hurwitz-genus-formula)
- H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections III.4–III.5.
-/

public section

open Module

open scoped nonZeroDivisors

namespace TauCeti

universe uR uRm uS uSm uK uL

variable {R : Type uR} {Rₘ : Type uRm} {S : Type uS} {Sₘ : Type uSm}
variable {K : Type uK} {L : Type uL}
variable [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ] [Field K] [Field L]
variable {M : Submonoid R}
variable [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ]
variable [Algebra R Sₘ] [IsScalarTower R S Sₘ]
variable [Algebra R K] [Algebra Rₘ K] [IsScalarTower R Rₘ K]
variable [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L] [Algebra Sₘ L]
variable [IsScalarTower R K L] [IsScalarTower Rₘ K L]
variable [IsScalarTower R S L] [IsScalarTower Rₘ Sₘ L] [IsScalarTower S Sₘ L]
variable [IsScalarTower R Sₘ L]
variable [IsLocalization M Rₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable [Module.Finite R S]
variable [IsDomain R] [IsDomain Rₘ]
variable [IsFractionRing R K] [IsFractionRing Rₘ K]
variable (hM : M ≤ R⁰)

include M hM

omit [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Sₘ L]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] [IsDomain R] [IsDomain Rₘ]
  [IsFractionRing R K] [IsFractionRing Rₘ K] hM in
private theorem exists_smul_mem_traceDual_of_mem_traceDual {x : L}
    (hx : x ∈ Submodule.traceDual Rₘ K (1 : Submodule Sₘ L)) :
    ∃ b : M, algebraMap R K b • x ∈ Submodule.traceDual R K (1 : Submodule S L) := by
  rw [Submodule.mem_traceDual] at hx
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  choose c hc using fun i : s ↦ hx (algebraMap S L i) (Submodule.mem_one.mpr
    ⟨algebraMap S Sₘ i, by rw [← IsScalarTower.algebraMap_apply S Sₘ L]⟩)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M c
  refine ⟨b, ?_⟩
  rw [Submodule.mem_traceDual]
  intro a ha
  rw [Submodule.mem_one] at ha
  obtain ⟨a, rfl⟩ := ha
  let f : S →ₗ[R] K := ((Algebra.traceForm K L) (algebraMap R K b • x)).restrictScalars R
    ∘ₗ (Algebra.linearMap S L).restrictScalars R
  let N : Submodule R S := Submodule.comap f (1 : Submodule R K)
  have hsN : (s : Set S) ⊆ N := by
    intro i hi
    let j : s := ⟨i, hi⟩
    obtain ⟨r, hr⟩ := hb j
    apply Submodule.mem_comap.mpr
    rw [Submodule.mem_one]
    refine ⟨r, ?_⟩
    calc
      algebraMap R K r = algebraMap Rₘ K (algebraMap R Rₘ r) := by
        rw [IsScalarTower.algebraMap_apply R Rₘ K]
      _ = algebraMap Rₘ K ((b : R) • c j) := congrArg (algebraMap Rₘ K) hr
      _ = algebraMap R K b * algebraMap Rₘ K (c j) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R Rₘ K]
      _ = algebraMap R K b * (Algebra.traceForm K L x) (algebraMap S L j) := by
        rw [hc j]
      _ = (Algebra.trace K L) (algebraMap R K b • (x * algebraMap S L j)) := by
        rw [(Algebra.trace K L).map_smul, Algebra.traceForm_apply, Algebra.smul_def]
        simp only [Algebra.algebraMap_self_apply]
      _ = (Algebra.trace K L) ((algebraMap R K b • x) * algebraMap S L i) := by
        congr 1
        simp only [Algebra.smul_def, j]
        ring
      _ = ((Algebra.traceForm K L) (algebraMap R K b • x)) (algebraMap S L i) := by
        rw [Algebra.traceForm_apply]
      _ = f i := by
        simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
          Algebra.linearMap_apply]
  have hN : N = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr hsN
  have haN : a ∈ N := hN.symm ▸ Submodule.mem_top
  exact Submodule.mem_one.mp (Submodule.mem_comap.mp haN)

omit [IsDomain R] [IsDomain Rₘ] [IsFractionRing Rₘ K] in
/-- The trace dual of a finite algebra commutes with localization. -/
@[simp]
theorem span_traceDual_one_eq_traceDual_one :
    Submodule.span Sₘ (Submodule.traceDual R K (1 : Submodule S L) : Set L) =
      Submodule.traceDual Rₘ K (1 : Submodule Sₘ L) := by
  let _ : Nontrivial R := (algebraMap R K).domain_nontrivial
  apply le_antisymm
  -- Extension of scalars sends an integral trace value to its localized image.
  · rw [Submodule.span_le]
    intro x hx
    simp only [SetLike.mem_coe] at hx ⊢
    rw [Submodule.mem_traceDual] at hx ⊢
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨⟨s, _, m, hm, rfl⟩, hsm⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid S M) a
    obtain ⟨r, hr⟩ := hx (algebraMap S L s) (Submodule.mem_one.mpr ⟨s, rfl⟩)
    have hsmL : algebraMap Sₘ L a * algebraMap R L m = algebraMap S L s := by
      simpa only [map_mul, IsScalarTower.algebraMap_apply R S Sₘ,
        IsScalarTower.algebraMap_apply R Sₘ L, IsScalarTower.algebraMap_apply S Sₘ L]
        using congrArg (algebraMap Sₘ L) hsm
    have htrace : (Algebra.traceForm K L x) (algebraMap Sₘ L a) * algebraMap R K m =
        algebraMap R K r := by
      calc
        _ = algebraMap R K m * (Algebra.trace K L) (x * algebraMap Sₘ L a) := mul_comm _ _
        _ = (Algebra.trace K L) (algebraMap R K m • (x * algebraMap Sₘ L a)) :=
          ((Algebra.trace K L).map_smul _ _).symm
        _ = (Algebra.trace K L) (x * algebraMap S L s) := by
          congr 1
          rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L]
          calc
            algebraMap R L m * (x * algebraMap Sₘ L a) =
                x * (algebraMap Sₘ L a * algebraMap R L m) := by ring
            _ = x * algebraMap S L s := by rw [hsmL]
        _ = _ := hr.symm
    refine ⟨IsLocalization.mk' Rₘ r ⟨m, hm⟩, ?_⟩
    apply mul_right_cancel₀ (IsFractionRing.to_map_eq_zero_iff.ne.mpr
      (nonZeroDivisors.ne_zero (hM hm)))
    rw [IsScalarTower.algebraMap_apply R Rₘ K, ← map_mul, IsLocalization.mk'_spec]
    simpa only [IsScalarTower.algebraMap_apply R Rₘ K] using htrace.symm
  -- Conversely, clear one denominator for trace values on a finite set of algebra generators.
  · intro x hx
    obtain ⟨b, hbx⟩ := exists_smul_mem_traceDual_of_mem_traceDual
      (R := R) (Rₘ := Rₘ) (S := S) (Sₘ := Sₘ) (K := K) (L := L) (M := M) hx
    let bm : Algebra.algebraMapSubmonoid S M := ⟨algebraMap R S b, ⟨b, b.2, rfl⟩⟩
    have hbx' := Submodule.smul_mem (Submodule.span Sₘ
      (Submodule.traceDual R K (1 : Submodule S L) : Set L)) (IsLocalization.mk' Sₘ 1 bm)
      (Submodule.subset_span hbx)
    suffices IsLocalization.mk' Sₘ 1 bm • (algebraMap R K b • x) = x by rwa [this] at hbx'
    rw [Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply S Sₘ L,
      ← mul_assoc, ← map_mul, IsLocalization.mk'_spec]
    simp only [map_one, one_mul]

variable [IsFractionRing S L] [IsFractionRing Sₘ L]
variable [IsIntegrallyClosed R] [IsIntegrallyClosed Rₘ]
variable [IsIntegralClosure S R L] [IsIntegralClosure Sₘ Rₘ L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsTorsionFree R S] [IsTorsionFree Rₘ Sₘ]

omit M [Module.Finite R S] [IsTorsionFree R S] [IsTorsionFree Rₘ Sₘ] hM in
private theorem coe_dual_one [IsDomain S] :
    (↑(FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Submodule S L) =
      Submodule.traceDual R K (1 : Submodule S L) := by
  -- Mathlib's public coercion lemma is Dedekind-scoped; unfold once here to expose the
  -- domain-level definitional equality needed by the more general localization theorem.
  set_option backward.isDefEq.respectTransparency.types false in
    rw [FractionalIdeal.dual, dite_eq_right one_ne_zero, FractionalIdeal.coe_mk,
      FractionalIdeal.coe_one]

section

variable [IsDomain S] [IsDomain Sₘ]

omit [IsTorsionFree R S] [IsTorsionFree Rₘ Sₘ] in
/-- The trace-dual fractional ideal commutes with localization. -/
@[simp]
theorem extendedHom'_dual_one_eq_dual_one :
    FractionalIdeal.extendedHom' L
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (IsLocalization.injective Sₘ
            (show Algebra.algebraMapSubmonoid S M ≤ S⁰ from
              map_le_nonZeroDivisors_of_injective _
                (algebraMap_injective_of_field_isFractionRing R S K L) hM)))
        (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) =
      FractionalIdeal.dual Rₘ K (1 : FractionalIdeal Sₘ⁰ L) := by
  let hMS : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _
      (algebraMap_injective_of_field_isFractionRing R S K L) hM
  let h : S⁰ ≤ Submonoid.comap (algebraMap S Sₘ) Sₘ⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (IsLocalization.injective Sₘ hMS)
  -- `extendedHom'` takes the inclusion proof explicitly, so proof irrelevance identifies the
  -- canonical proof in the statement with the named proof `h` used throughout this proof.
  change FractionalIdeal.extendedHom' L h
      (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) = _
  rw [FractionalIdeal.extendedHom'_apply]
  apply FractionalIdeal.coeToSubmodule_injective
  refine (FractionalIdeal.coe_extended_eq_span L h _).trans ?_
  have hmap : IsLocalization.map L (algebraMap S Sₘ) h = RingHom.id L := by
    apply IsFractionRing.ringHom_ext (A := S)
    intro s
    rw [IsLocalization.map_eq, RingHom.id_apply, IsScalarTower.algebraMap_apply S Sₘ L]
  rw [hmap]
  simp only [RingHom.id_apply, Set.image_id']
  calc
    Submodule.span Sₘ
        ((↑(FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Submodule S L) : Set L) =
        Submodule.span Sₘ (Submodule.traceDual R K (1 : Submodule S L) : Set L) :=
      congrArg (Submodule.span Sₘ)
        (congrArg (fun N : Submodule S L ↦ (N : Set L)) coe_dual_one)
    _ = Submodule.traceDual Rₘ K (1 : Submodule Sₘ L) :=
      span_traceDual_one_eq_traceDual_one (M := M) hM
    _ = (↑(FractionalIdeal.dual Rₘ K (1 : FractionalIdeal Sₘ⁰ L)) : Submodule Sₘ L) :=
      (coe_dual_one (R := Rₘ) (S := Sₘ)).symm

end

variable [IsDedekindDomain S] [IsDedekindDomain Sₘ]

omit [IsTorsionFree R S] [IsTorsionFree Rₘ Sₘ] in
include K L in
/-- The different ideal commutes with localization. -/
@[simp]
theorem map_differentIdeal_eq_differentIdeal :
    let _ : IsTorsionFree R L := .trans_faithfulSMul R K L
    let _ : IsTorsionFree Rₘ L := .trans_faithfulSMul Rₘ K L
    let _ : IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L
    let _ : IsTorsionFree Rₘ Sₘ := IsIntegralClosure.isTorsionFree Rₘ L
    (differentIdeal R S).map (algebraMap S Sₘ) = differentIdeal Rₘ Sₘ := by
  have : IsTorsionFree R L := .trans_faithfulSMul R K L
  have : IsTorsionFree Rₘ L := .trans_faithfulSMul Rₘ K L
  have : IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L
  have : IsTorsionFree Rₘ Sₘ := IsIntegralClosure.isTorsionFree Rₘ L
  have hMS : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S) hM
  have hSSₘ : Function.Injective (algebraMap S Sₘ) := IsLocalization.injective Sₘ hMS
  let h : S⁰ ≤ Submonoid.comap (algebraMap S Sₘ) Sₘ⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hSSₘ
  rw [← FractionalIdeal.coeIdeal_inj (K := L),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := L) L h,
    ← FractionalIdeal.extendedHom'_apply]
  rw [coeIdeal_differentIdeal R K L S, coeIdeal_differentIdeal Rₘ K L Sₘ, map_inv₀,
    extendedHom'_dual_one_eq_dual_one (R := R) (Rₘ := Rₘ) (S := S)
      (Sₘ := Sₘ)
      (K := K) (L := L) (M := M) hM]

end TauCeti

end
