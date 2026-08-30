/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Finite-dimensionality of a fraction field over an intermediate field

Let `S` be finite as a module over `R`, and let `L` be a fraction field of `S`. Then `L` is
finite-dimensional over *any* intermediate field `K`, that is, any field sitting in a tower
`R → K → L`. Mathlib proves this only for the concrete `FractionRing R` and `FractionRing S`;
the statement here is about abstract fraction fields and an arbitrary intermediate field.

## Main results

* `TauCeti.IsFractionRing.finiteDimensional_of_finite`: `L` is finite-dimensional over `K`.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`). This is the fraction-field sentence of Stacks,
Lemma 10.161.5 (tag 032I).

## Implementation notes

The proof is elementary and does not use integral-closure *theory*, only the integrality of a
finite module element: `V` is the `K`-span of the image of a finite `R`-generating set of `S`, it
absorbs multiplication by the image of `S`, and it contains the inverse of every nonzero element
of that image because such an element is integral over `K` and the inverse of a nonzero integral
element lies in the algebra it generates. `L` is then `V` because every element of `L` is a
quotient of elements of the image of `S`.
-/

public section

namespace TauCeti

/-- A fraction field `L` of a ring `S` that is finite as an `R`-module is finite-dimensional
over any intermediate field `K`, that is, any field with `R → K → L`.

This is the content of Stacks, Lemma 10.161.5 (tag 032I) — "Let `M` be a finite field extension
of the fraction field of `S`. Then `M` is also a finite field extension of `K`" — but the
hypotheses here are weaker than that sentence suggests, and deliberately so: `K` need not be a
fraction field of `R`, and no assumption on `R` beyond `Module.Finite R S` is used. No *explicit*
`IsDomain S` hypothesis is needed either, but that is not extra generality: `IsFractionRing S L`
with `L` a field already forces `algebraMap S L` to be injective, and hence `S` to be a domain.
Mathlib covers only the concrete `FractionRing R` / `FractionRing S` case. -/
theorem IsFractionRing.finiteDimensional_of_finite (R S K L : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    [Field K] [Field L] [Algebra R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] :
    FiniteDimensional K L := by
  classical
  obtain ⟨t, ht⟩ := (Module.finite_def.mp ‹Module.Finite R S›)
  -- `V` is the `K`-span of the image of a finite `R`-generating set of `S`
  set V : Submodule K L := Submodule.span K ((algebraMap S L) '' (t : Set S)) with hV
  -- every element of `S` already lies in `V`: an `R`-scalar is a `K`-scalar along `R → K → L`
  -- the `R`-span of the mapped generators already contains the image of `S`, and the `K`-span
  -- contains the `R`-span
  have hS : ∀ x : S, algebraMap S L x ∈ V := fun x ↦
    Submodule.span_subset_span R K _
      (Submodule.map_mem_span_algebraMap_image (T := L) x (t : Set S)
        (ht ▸ Submodule.mem_top))
  -- `V` absorbs multiplication by the image of `S`
  have hmul : ∀ (x : S) (v : L), v ∈ V → algebraMap S L x * v ∈ V := by
    intro x v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨y, hy, rfl⟩ := hy
        simpa [← map_mul] using hS (x * y)
    | zero => simp
    | add y z _ _ hy hz => simpa [mul_add] using V.add_mem hy hz
    | smul k y _ hy =>
        rw [Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap S L x), mul_assoc,
          ← Algebra.smul_def]
        exact V.smul_mem _ hy
  -- a `K`-polynomial in an element of the image of `S` stays in `V`
  have hpoly : ∀ (b : S) (q : Polynomial K), Polynomial.aeval (algebraMap S L b) q ∈ V := by
    intro b q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simpa [map_add] using V.add_mem hq hr
    | monomial j k =>
        have : Polynomial.aeval (algebraMap S L b) (Polynomial.monomial j k)
            = k • algebraMap S L (b ^ j) := by
          simp [Polynomial.aeval_monomial, Algebra.smul_def, map_pow]
        rw [this]
        exact V.smul_mem _ (hS _)
  -- inverses: `b⁻¹` is a `K`-polynomial in `b` divided by a nonzero constant coefficient
  have hinv : ∀ b : S, b ∈ nonZeroDivisors S → (algebraMap S L b)⁻¹ ∈ V := by
    intro b _
    have hint : IsIntegral K (algebraMap S L b) :=
      (IsIntegral.map (IsScalarTower.toAlgHom R S L) (IsIntegral.of_finite R b)).tower_top
    -- the inverse of a nonzero integral element already lies in the algebra it generates
    obtain ⟨q, hq⟩ :=
      Algebra.adjoin_mem_exists_aeval K (algebraMap S L b) hint.inv_mem_adjoin
    rw [← hq]
    exact hpoly b q
  -- `L` is the fraction field of `S`, so `V` is everything
  have htop : V = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) (K := L) z
    rw [div_eq_mul_inv]
    exact hmul a _ (hinv b hb)
  exact Module.finite_def.mpr
    (htop ▸ Submodule.fg_span (Set.Finite.image _ t.finite_toSet))

end TauCeti

end
