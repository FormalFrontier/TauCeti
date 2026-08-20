/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.RingTheory.Huber.LocalizationTopology.Plus
public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction

/-!
# The adic spectrum of a rational localisation lies over the rational subset

Roadmap Layer 3.1 attaches to a rational subset `U = R(T/s)` of `X = Spa(A, A⁺)` the complete
topological coordinate ring `A_U = A⟨T/s⟩` together with its ring of integral elements `A_U⁺`,
and asks for a natural homeomorphism

```text
Spa (A_U, A_U⁺) ≃ U.
```

This file builds the map underlying that homeomorphism and proves that it lands in `U`. The
structure map `A → A⟨T/s⟩` is continuous and carries `A⁺` into `A_U⁺`, so
`TauCeti.ValuationSpectrum.spaComap` already gives a continuous map

```text
Spa (A_U, A_U⁺) → Spa (A, A⁺),
```

and the content here is that its image is contained in `R(T/s)`, so that it corestricts to a
continuous map into the rational subset.

The two valuation-theoretic conditions cutting out `R(T/s)` come from the two defining features
of the localisation. The denominator `s` becomes a *unit* in `A⟨T/s⟩`, so no point of
`Spa (A_U, A_U⁺)` has it in its support; and each fraction `t/s` lies in `A_U⁺`, so every point
is sub-unit on it, which after clearing the denominator says `v(t) ≤ v(s)`. Neither uses a Huber
hypothesis, so both are extracted first as a statement about an arbitrary continuous
homomorphism inverting `s`.

The reverse map — extending a point of `R(T/s)` to a continuous valuation on the *completed*
localisation — is not constructed here; it is the remaining half of the roadmap's homeomorphism.

## Main definitions

* `TauCeti.ValuationSpectrum.spaComapLoc` : the map `Spa (A_U, A_U⁺) → Spa (A, A⁺)` induced by
  the structure map `A → A⟨T/s⟩`.
* `TauCeti.ValuationSpectrum.spaLocToRationalSubset` : its corestriction to `R(T/s)`.

## Main results

* `TauCeti.ValuationSpectrum.spaComapLoc_mem_rationalSubset` and
  `TauCeti.ValuationSpectrum.range_spaComapLoc_subset` : the rational localisation satisfies that
  criterion, so `Spa (A_U, A_U⁺)` lies over `R(T/s)`.
* `TauCeti.ValuationSpectrum.continuous_spaLocToRationalSubset` : the corestriction is continuous.
* `TauCeti.ValuationSpectrum.rationalSubset_image_toCompletionLoc_eq_spa` : over `A_U` the
  conditions defining `R(T/s)` become vacuous — the rational subset presented by the images of
  `T` and `s` is all of `Spa (A_U, A_U⁺)`.
* `TauCeti.ValuationSpectrum.spa_completedPlusSubring_eq_empty_of_rationalSubset_eq_empty` : an
  empty rational subset has a coordinate ring with empty adic spectrum.

## Provenance

The mathematics is Wedhorn's §8.1 description of the coordinate ring of a rational subset; the
proofs here are direct and follow no existing formalisation. AINTLIB — the roadmap's designated
prior formalisation of this material — was **not** consulted for this file: no checkout of it was
available in the authoring environment. Nothing is ported.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], arXiv:1910.05934v1, Definition 7.29 and §8.1.
-/

public section

open TauCeti.Localization

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### The rational localisation

Throughout this section `S` is an algebraic localisation of `A` away from `s`, carrying the
localisation topology of `TauCeti.Huber.PairOfDefinition.locTopology`, and `A⟨T/s⟩` is its
separated completion. The three `letI`s that name the uniformity and its two companions are the
ones every statement about `A⟨T/s⟩` carries. -/

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable [IsTopologicalRing A]

/-- The map `Spa (A_U, A_U⁺) → Spa (A, A⁺)` induced by the structure map `A → A⟨T/s⟩`: the
structure map is continuous and carries `A⁺` into `A_U⁺`, which is all
`TauCeti.ValuationSpectrum.spaComap` needs. -/
noncomputable def spaComapLoc (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    spa (completedPlusSubring P Aplus T s S hden) → spa Aplus :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  spaComap (toCompletionLoc P T s S hden) (continuous_toCompletionLoc P T s S hden) Aplus
    (completedPlusSubring P Aplus T s S hden)
    fun _ ha ↦ toCompletionLoc_mem_completedPlusSubring P Aplus T s S hden ha

/-- The underlying point of `spaComapLoc` is the pullback along the structure map. The body is
sealed across the module boundary, so this is how a consumer computes with it. -/
@[simp]
theorem spaComapLoc_val (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ v : spa (completedPlusSubring P Aplus T s S hden),
      (spaComapLoc P Aplus T s S hden v).1 = comap (toCompletionLoc P T s S hden) v.1 := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  exact fun v ↦ spaComap_val _ _ _ _ _ v

/-- `spaComapLoc` is continuous. -/
theorem continuous_spaComapLoc (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (spaComapLoc P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  exact continuous_spaComap _ _ _ _ _

/-- **Every point of `Spa (A_U, A_U⁺)` lies over the rational subset `R(T/s)`** — the half of
roadmap Layer 3.1's homeomorphism `Spa (A_U, A_U⁺) ≃ R(T/s)` that the localisation supplies
directly.

The denominator is inverted in `A⟨T/s⟩`, so it is off the support of every point, and each
`t/s` lies in `A_U⁺`, so every point is sub-unit on it. -/
theorem spaComapLoc_mem_rationalSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ v : spa (completedPlusSubring P Aplus T s S hden),
      (spaComapLoc P Aplus T s S hden v).1 ∈ rationalSubset Aplus T s := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro v
  -- the denominator is a unit in `A⟨T/s⟩`, and its inverse is the image of `1/s`
  have hu : IsUnit (toCompletionLoc P T s S hden s) :=
    isUnit_toCompletionLoc_of_dvd P T s S hden dvd_rfl
  have hc : toCompletionLoc P T s S hden s * ↑hu.unit⁻¹ = 1 := by
    have h := hu.unit.mul_inv
    rwa [hu.unit_spec] at h
  have hinv : (↑hu.unit⁻¹ : UniformSpace.Completion S) =
      ((divBy 1 s : S) : UniformSpace.Completion S) :=
    toCompletionLoc_unit_inv_eq P T s S hden (mul_one s).symm hu
  rw [spaComapLoc_val]
  refine comap_mem_rationalSubset (continuous_toCompletionLoc P T s S hden)
    (fun _ ha ↦ toCompletionLoc_mem_completedPlusSubring P Aplus T s S hden ha) T s hc
    (fun t ht ↦ ?_) v.2
  -- and `t` times that inverse is the fraction `t/s`, which lies in `A_U⁺`
  rw [hinv, toCompletionLoc_apply, ← UniformSpace.Completion.coe_mul, divBy_one,
    algebraMap_mul_invSelf]
  exact divBy_mem_completedPlusSubring P Aplus T s S hden ht

/-- The range of `spaComapLoc` is contained in the rational subset `R(T/s)`, as a subset of the
subtype `↥(Spa (A, A⁺))`. -/
theorem range_spaComapLoc_subset (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Set.range (spaComapLoc P Aplus T s S hden) ⊆
      (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rintro _ ⟨v, rfl⟩
  exact spaComapLoc_mem_rationalSubset P Aplus T s S hden v

/-- **The canonical map `Spa (A_U, A_U⁺) → R(T/s)`**: `spaComapLoc` corestricted to the rational
subset it lands in. This is the map that roadmap Layer 3.1 asks to be a homeomorphism. -/
noncomputable def spaLocToRationalSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    spa (completedPlusSubring P Aplus T s S hden) →
      (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  Set.codRestrict (spaComapLoc P Aplus T s S hden) _
    fun v ↦ spaComapLoc_mem_rationalSubset P Aplus T s S hden v

/-- The corestriction forgets to `spaComapLoc`. -/
@[simp]
theorem spaLocToRationalSubset_val (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ v : spa (completedPlusSubring P Aplus T s S hden),
      (spaLocToRationalSubset P Aplus T s S hden v).1 = spaComapLoc P Aplus T s S hden v := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  exact fun _ ↦ (rfl)

/-- The canonical map into the rational subset is continuous. -/
theorem continuous_spaLocToRationalSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Continuous (spaLocToRationalSubset P Aplus T s S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  Continuous.codRestrict (continuous_spaComapLoc P Aplus T s S hden) _

open scoped Classical in
/-- **In the coordinate ring of `U = R(T/s)`, the rational subset cut out by the images of the
defining data is the whole adic spectrum.**

This is the point of passing to `A_U`: the conditions `v(t) ≤ v(s) ≠ 0` that carve `U` out of
`Spa (A, A⁺)` become vacuous over `A⟨T/s⟩`, because there `s` is a unit and each `t/s` is a
sub-unit. It is the degenerate case of Wedhorn's comparison of rational subsets of `U` with
rational subsets of `X` (§8.2), and it is what makes `Spa (A_U, A_U⁺)` a candidate for `U`
rather than for a proper subset of it. -/
@[simp]
theorem rationalSubset_image_toCompletionLoc_eq_spa (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    rationalSubset (completedPlusSubring P Aplus T s S hden)
        (T.image (toCompletionLoc P T s S hden)) (toCompletionLoc P T s S hden s) =
      spa (completedPlusSubring P Aplus T s S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have hu : IsUnit (toCompletionLoc P T s S hden s) :=
    isUnit_toCompletionLoc_of_dvd P T s S hden dvd_rfl
  have hc : toCompletionLoc P T s S hden s * ↑hu.unit⁻¹ = 1 := by
    have h := hu.unit.mul_inv
    rwa [hu.unit_spec] at h
  refine rationalSubset_image_eq_spa (toCompletionLoc P T s S hden)
    (completedPlusSubring P Aplus T s S hden) T s hc fun t ht ↦ ?_
  rw [toCompletionLoc_unit_inv_eq P T s S hden (mul_one s).symm hu, toCompletionLoc_apply,
    ← UniformSpace.Completion.coe_mul, divBy_one, algebraMap_mul_invSelf]
  exact divBy_mem_completedPlusSubring P Aplus T s S hden ht

/-- **The coordinate ring of an empty rational subset has empty adic spectrum.** Every point of
`Spa (A_U, A_U⁺)` lies over a point of `R(T/s)`, so there is none to have when `R(T/s)` is
empty. -/
theorem spa_completedPlusSubring_eq_empty_of_rationalSubset_eq_empty (P : PairOfDefinition A)
    (Aplus : Subring A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
    (h : rationalSubset Aplus T s = ∅) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    spa (completedPlusSubring P Aplus T s S hden) = ∅ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  refine Set.eq_empty_iff_forall_notMem.mpr fun v hv ↦ ?_
  have := spaComapLoc_mem_rationalSubset P Aplus T s S hden ⟨v, hv⟩
  rw [h] at this
  exact this

end TauCeti.ValuationSpectrum

end
