/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite
public import TauCeti.NumberTheory.NumberField.Units.Signature

/-!
# The narrow class number formula

The narrow class group `Cl⁺(K)` surjects onto the ordinary class group `Cl(K)` by forgetting the
positivity condition on generators, and the kernel of that surjection is an elementary abelian
`2`-group. This file identifies that kernel with the **relative signature quotient**: the sign
patterns `fieldSignatures K` realized by `Kˣ` modulo the subgroup `unitSignatures K` of those
realized by the units of `𝓞 K`.

The mechanism is that a principal fractional ideal `(x)` acquires a totally positive generator
exactly when some integer unit corrects the signs of `x`, and two generators of the same principal
ideal differ by an integer unit. So `mkPrincipal x = 1` holds precisely when the signature of `x`
lies in `unitSignatures K`, which is `mkPrincipal_eq_one_iff`. Everything else is the first
isomorphism theorem applied to that description of the kernel: `kerToClassGroupEquiv` presents the
relative signature quotient directly, and `card_ker_toClassGroup` records its order as the relative
index of the two ranges.

The consequences are the classical narrow class number formula in index form,

```text
h⁺(K) = h(K) · [fieldSignatures K : unitSignatures K],
```

together with `h⁺(K) ∣ h(K) · 2 ^ r₁`, since the ambient group of sign patterns has order `2 ^ r₁`
for `r₁` the number of real places. Both refine `exists_card_eq_card_classGroup_mul_two_pow`, which
records only that the extra factor is *some* power of `2`. For a totally complex field there are no
real places and the two class groups already coincide, by `toClassGroup_injective`; the content here
is the real case, where the correction is measured by which sign patterns the units realize.

Nothing here computes either range. Surjectivity of `fieldUnitSignature` — every sign pattern is
realized by some element of `Kˣ`, by weak approximation at the real places — would turn the index
above into `2 ^ r₁ / Nat.card (unitSignatures K)`; it is a separate archimedean input, and the
statements below are phrased against `fieldSignatures K` so that they stand without it.

## Main definitions and results

* `TauCeti.NumberField.NarrowClassGroup.mkPrincipal_eq_one_iff`: a principal narrow class is trivial
  exactly when the signature of a generator is realized by an integer unit.
* `TauCeti.NumberField.NarrowClassGroup.ker_mkPrincipal`: hence the kernel of the principal-class
  map is the preimage of `unitSignatures K`.
* `TauCeti.NumberField.NarrowClassGroup.kerToClassGroupEquiv`: **the kernel of `Cl⁺(K) → Cl(K)` is
  the relative signature quotient** `fieldSignatures K / unitSignatures K`.
* `TauCeti.NumberField.NarrowClassGroup.card_ker_toClassGroup`: its order is the relative index of
  the two signature ranges.
* `TauCeti.NumberField.NarrowClassGroup.card_eq_card_classGroup_mul_relIndex` and
  `TauCeti.NumberField.NarrowClassGroup.card_mul_card_unitSignatures`: **the narrow class number
  formula**, in index and in product form.
* `TauCeti.NumberField.NarrowClassGroup.card_dvd_card_classGroup_mul_two_pow_nrRealPlaces`:
  `h⁺ ∣ h · 2 ^ r₁`.
* `TauCeti.NumberField.NarrowClassGroup.toClassGroup_injective_iff`: `Cl⁺(K) → Cl(K)` is injective
  exactly when every sign pattern realized in `Kˣ` is realized by an integer unit.

## Roadmap

This advances Layer 3 of `TauCetiRoadmap/Multiquadratic/README.md`, whose `2`-rank formula
`2-rank = t - 1` is a theorem about the *narrow* class group and which asks for the narrow class
group as the prerequisite for the real quadratic case. For the classical genus theory this serves
see D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws: from Euler to
Eisenstein*; the exact sequence computing `h⁺/h` from the unit signatures is standard, see also
H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.2.
-/

public section

open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace TauCeti.NumberField.NarrowClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- **The principal narrow classes, computed by signatures.** The principal fractional ideal `(x)`
has trivial narrow class exactly when the signature of `x` is realized by a unit of `𝓞 K`. -/
@[simp] theorem mkPrincipal_eq_one_iff {x : Kˣ} :
    mkPrincipal x = 1 ↔ fieldUnitSignature x ∈ unitSignatures K := by
  rw [mkPrincipal_apply, mk_eq_one_iff, mem_narrowPrincipalSubgroup, mem_unitSignatures]
  constructor
  -- Two generators of the same principal ideal differ by an integer unit, so a totally positive
  -- generator `y` of `(x)` gives `x = y * a` with `a` an integer unit, whence `x` and `a` have the
  -- same signature.
  · rintro ⟨y, hy, hyx⟩
    have h1 : toPrincipalIdeal (𝓞 K) K (y⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    obtain ⟨a, ha⟩ := (FractionalIdeal.toPrincipalIdeal_eq_one_iff _).mp h1
    refine ⟨a, ?_⟩
    have hx : x = y * Units.map (algebraMap (𝓞 K) K : (𝓞 K) →* K) a := by
      rw [ha, mul_inv_cancel_left]
    rw [hx, map_mul, fieldUnitSignature_eq_one_iff.mpr hy, fieldUnitSignature_map_algebraMap]
    exact (one_mul (M := {w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) _).symm
  -- Conversely, if `a` is an integer unit with the signature of `x`, then `a⁻¹ * x` is totally
  -- positive and generates `(x)`.
  · rintro ⟨a, ha⟩
    refine ⟨(Units.map (algebraMap (𝓞 K) K : (𝓞 K) →* K) a)⁻¹ * x, ?_, ?_⟩
    · rw [← fieldUnitSignature_eq_one_iff, map_mul, map_inv,
        fieldUnitSignature_map_algebraMap, ha]
      funext w
      simp
    · rw [map_mul, map_inv, (FractionalIdeal.toPrincipalIdeal_eq_one_iff _).mpr ⟨a, rfl⟩, inv_one,
        one_mul]

/-- **The kernel of the principal-class map is cut out by signatures**: `x : Kˣ` has trivial narrow
principal class exactly when its signature is realized by an integer unit. -/
theorem ker_mkPrincipal :
    MonoidHom.ker (mkPrincipal (K := K)) =
      Subgroup.comap (fieldUnitSignature (K := K)) (unitSignatures K) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, mkPrincipal_eq_one_iff]

local instance : IsMulCommutative (fieldSignatures K) := ⟨⟨fun x y => mul_comm x y⟩⟩

-- Construction: by `toClassGroup_ker` the kernel is the image of the principal-class map, and by
-- `ker_mkPrincipal` that map's own kernel is the preimage of `unitSignatures K`. The first
-- isomorphism theorem for the field signature then identifies this quotient with the quotient of
-- the two signature ranges.
/-- **The kernel of `Cl⁺(K) → Cl(K)` is the relative signature quotient.** Forgetting positivity
loses exactly the sign patterns that `Kˣ` realizes and the units of `𝓞 K` do not. -/
noncomputable def kerToClassGroupEquiv :
    MonoidHom.ker (toClassGroup (K := K)) ≃*
      fieldSignatures K ⧸ (unitSignatures K).subgroupOf (fieldSignatures K) := by
  let fieldSignature : Kˣ →* fieldSignatures K :=
    (fieldUnitSignature (K := K)).codRestrict (fieldSignatures K)
      fun x => mem_fieldSignatures.mpr ⟨x, rfl⟩
  let signatureQuotient :
      Kˣ →* fieldSignatures K ⧸ (unitSignatures K).subgroupOf (fieldSignatures K) :=
    (QuotientGroup.mk' ((unitSignatures K).subgroupOf (fieldSignatures K))).comp
      fieldSignature
  have hfieldSur : Function.Surjective fieldSignature := by
    rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := mem_fieldSignatures.mp hs
    exact ⟨x, Subtype.ext hx⟩
  have hsur : Function.Surjective signatureQuotient :=
    (QuotientGroup.mk'_surjective _).comp hfieldSur
  have hker : MonoidHom.ker signatureQuotient =
      Subgroup.comap (fieldUnitSignature (K := K)) (unitSignatures K) := by
    ext x
    simp only [MonoidHom.mem_ker, signatureQuotient, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_comap, fieldSignature, MonoidHom.codRestrict_apply]
  exact (MulEquiv.subgroupCongr toClassGroup_ker).trans
    ((QuotientGroup.quotientKerEquivRange (mkPrincipal (K := K))).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (ker_mkPrincipal.trans hker.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective signatureQuotient hsur)))

/-- **The narrow-versus-ordinary defect is the relative index of the two signature ranges.** -/
theorem card_ker_toClassGroup :
    Nat.card (MonoidHom.ker (toClassGroup (K := K))) =
      (unitSignatures K).relIndex (fieldSignatures K) := by
  rw [Nat.card_congr kerToClassGroupEquiv.toEquiv, ← Subgroup.index_eq_card,
    Subgroup.relIndex]

/-- **The defect, in product form.** Multiplying by the number of sign patterns realized by the
units clears the index: the kernel of `Cl⁺(K) → Cl(K)` and the unit signatures together account for
all the sign patterns realized by `Kˣ`. -/
theorem card_ker_toClassGroup_mul_card_unitSignatures :
    Nat.card (MonoidHom.ker (toClassGroup (K := K))) * Nat.card (unitSignatures K) =
      Nat.card (fieldSignatures K) := by
  rw [card_ker_toClassGroup, Subgroup.relIndex,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe unitSignatures_le_fieldSignatures).toEquiv]
  exact Subgroup.index_mul_card _

/-- **The narrow class number formula.** The narrow class number is the ordinary class number times
the index, inside the sign patterns realized by `Kˣ`, of those realized by the units of `𝓞 K`:

```text
h⁺(K) = h(K) · [fieldSignatures K : unitSignatures K].
```

This sharpens `exists_card_eq_card_classGroup_mul_two_pow`, which records only that the second
factor is a power of `2`. -/
theorem card_eq_card_classGroup_mul_relIndex :
    Nat.card (NarrowClassGroup K) =
      Nat.card (ClassGroup (𝓞 K)) * (unitSignatures K).relIndex (fieldSignatures K) := by
  rw [card_eq_card_classGroup_mul_card_ker, card_ker_toClassGroup]

/-- **The narrow class number formula, in product form**:

```text
h⁺(K) · #(signature (𝓞 K)ˣ) = h(K) · #(signature Kˣ).
```

Once the signature of `Kˣ` is known to be onto — a separate archimedean input — the right-hand
factor is `2 ^ r₁` and this is the classical `h⁺ = h · 2 ^ r₁ / [E : E⁺]`. -/
theorem card_mul_card_unitSignatures :
    Nat.card (NarrowClassGroup K) * Nat.card (unitSignatures K) =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card (fieldSignatures K) := by
  rw [card_eq_card_classGroup_mul_card_ker, mul_assoc,
    card_ker_toClassGroup_mul_card_unitSignatures]

/-- **The narrow class number divides `h · 2 ^ r₁`.** The defect between the narrow and the ordinary
class number is bounded by the number of sign patterns at the real places. -/
theorem card_dvd_card_classGroup_mul_two_pow_nrRealPlaces :
    Nat.card (NarrowClassGroup K) ∣ Nat.card (ClassGroup (𝓞 K)) * 2 ^ nrRealPlaces K := by
  rw [card_eq_card_classGroup_mul_relIndex]
  exact Nat.mul_dvd_mul_left _
    ((Subgroup.relIndex_dvd_card _ _).trans
      TauCeti.NumberField.card_fieldSignatures_dvd_two_pow_nrRealPlaces)

/-- **The narrow and the ordinary class group agree exactly when the units realize every attainable
sign pattern.** For a totally complex field both ranges are trivial, which is the content of
`toClassGroup_injective`; the criterion is informative for a field with real places. -/
theorem toClassGroup_injective_iff :
    Function.Injective (toClassGroup (K := K)) ↔ fieldSignatures K = unitSignatures K := by
  rw [← MonoidHom.ker_eq_bot_iff, toClassGroup_ker, Subgroup.eq_bot_iff_forall]
  constructor
  · refine fun h => le_antisymm (fun z hz => ?_) unitSignatures_le_fieldSignatures
    obtain ⟨x, rfl⟩ := mem_fieldSignatures.mp hz
    exact mkPrincipal_eq_one_iff.mp (h _ ⟨x, rfl⟩)
  · rintro h _ ⟨x, rfl⟩
    exact mkPrincipal_eq_one_iff.mpr (h ▸ mem_fieldSignatures.mpr ⟨x, rfl⟩)

end TauCeti.NumberField.NarrowClassGroup
