/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The fixed field of the automorphism group of a normal extension

For a normal extension `E / F`, the fixed field `E ^ Aut(E/F)` sits between `F` and `E` with
`F ⊆ E ^ Aut(E/F)` purely inseparable and `E ^ Aut(E/F) ⊆ E` Galois. This is the splitting of
Stacks, Fields, Lemma 9.27.3(2), whose proof reads "We set `E_insep = E^{Aut(E/F)}`. Details
omitted." Mathlib has the Galois half as `IsGalois.of_fixed_field`; the purely inseparable half
is new here. The two are stated separately, one conclusion each.

Order matters for the consumer (`TauCeti.IsIntegralClosure.finite_of_forall_isPurelyInseparable`):
the purely inseparable step has to sit *below* the separable one, because the integral closure
of a polynomial ring in a separable extension is no longer a polynomial ring.

## Main results

* `TauCeti.IntermediateField.isPurelyInseparable_fixedField_top`: for `E / F` normal, the fixed
  field of `Gal(E/F)` is purely inseparable over `F`.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The mathematics is Stacks, Fields,
Lemma 9.27.3(2) (tag 030M), the splitting used by Stacks 10.161.12 (tag 032N).
-/

public section

namespace TauCeti

/-- Source: Stacks, Fields, Lemma 9.27.3(2): "`F ⊂ E_insep` is purely inseparable", with
`E_insep = E^{Aut(E/F)}` (proof: "Details omitted"). For a normal extension `E / F`, the fixed
field of the full automorphism group is purely inseparable over `F`: an element fixed by every
automorphism has a single conjugate, since `minpoly F x` splits in `E` and its roots form one
orbit. -/
theorem IntermediateField.isPurelyInseparable_fixedField_top (F E : Type*) [Field F] [Field E]
    [Algebra F E] [Normal F E] :
    IsPurelyInseparable F (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) := by
  refine ⟨inferInstance, fun x hx ↦ ?_⟩
  have hinj : Function.Injective
      (algebraMap (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E) :=
    RingHom.injective _
  set y : E := (x : E) with hy
  have hint : IsIntegral F y := Normal.isIntegral ‹Normal F E› y
  have hyx : minpoly F y = minpoly F x := minpoly.algebraMap_eq hinj x
  have hsep : (minpoly F y).Separable := by rw [hyx]; exact hx
  -- Every Galois conjugate of `y` is `y` itself: a conjugate is `σ y` for some automorphism `σ`,
  -- and `y` lies in the fixed field of all of them.
  have hall : ∀ z : E, Polynomial.aeval z (minpoly F y) = 0 → z = y := by
    intro z hz
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic y) hz
    rw [← hσ]
    exact (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_top σ)
  -- `minpoly F y` splits in `E` and is separable, so it has `natDegree` many distinct roots;
  -- all of them are `y`, so that degree is one.
  set q : Polynomial E := (minpoly F y).map (algebraMap F E) with hq
  have hq0 : q ≠ 0 := ((minpoly.monic hint).map (algebraMap F E)).ne_zero
  have hcard : Multiset.card q.roots = q.natDegree :=
    Polynomial.splits_iff_card_roots.mp (Normal.splits ‹Normal F E› y)
  have hnodup : q.roots.Nodup := Polynomial.nodup_roots (Polynomial.Separable.map hsep)
  have hsub : q.roots ⊆ {y} := by
    intro z hz
    rw [Polynomial.mem_roots hq0] at hz
    refine Multiset.mem_singleton.mpr (hall z ?_)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hz
  have hle : Multiset.card q.roots ≤ 1 := by
    simpa using Multiset.card_le_card ((Multiset.le_iff_subset hnodup).mpr hsub)
  have h1 : 0 < (minpoly F y).natDegree := minpoly.natDegree_pos hint
  have h2 : q.natDegree = (minpoly F y).natDegree :=
    Polynomial.natDegree_map _
  have hnd : (minpoly F y).natDegree = 1 := by omega
  have hdeg : (minpoly F y).degree = 1 := by
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hnd]; rfl
  obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one F y hdeg
  refine ⟨a, hinj ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  simpa [hy] using ha

end TauCeti
