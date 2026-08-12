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
`2`-group. This file identifies that kernel with the **cokernel of the unit signature**: the group
of all sign patterns at the real places, modulo the subgroup `unitSignatures K` of those realized
by the units of `𝓞 K`.

The mechanism is that a principal fractional ideal `(x)` acquires a totally positive generator
exactly when some integer unit corrects the signs of `x`, and two generators of the same principal
ideal differ by an integer unit. So `mkPrincipal x = 1` holds precisely when the signature of `x`
lies in `unitSignatures K`, which is `mkPrincipal_eq_one_iff`. Everything else is the first
isomorphism theorem applied to that description of the kernel, using that `fieldUnitSignature` is
onto (`fieldUnitSignature_surjective`): `kerToClassGroupEquiv` presents the cokernel directly, and
`card_ker_toClassGroup` records its order as the index of `unitSignatures K`.

The consequences are the classical narrow class number formula, in index form

```text
h⁺(K) = h(K) · [signature Kˣ : signature (𝓞 K)ˣ],
```

and, since the group of sign patterns has order `2 ^ r₁` for `r₁` the number of real places, in the
product form `h⁺(K) · #signature (𝓞 K)ˣ = h(K) · 2 ^ r₁` — that is, `h⁺ = h · 2 ^ r₁ / [E : E⁺]`
with `E` the units and `E⁺` the totally positive ones. Both refine
`exists_card_eq_card_classGroup_mul_two_pow`, which records only that the extra factor is *some*
power of `2`. For a totally complex field there are no real places and the two class groups already
coincide, by `toClassGroup_injective`; the content here is the real case, where the correction is
measured by which sign patterns the units realize.

## Main definitions and results

* `TauCeti.NumberField.NarrowClassGroup.mkPrincipal_eq_one_iff`: a principal narrow class is trivial
  exactly when the signature of a generator is realized by an integer unit.
* `TauCeti.NumberField.NarrowClassGroup.ker_mkPrincipal`: hence the kernel of the principal-class
  map is the preimage of `unitSignatures K`.
* `TauCeti.NumberField.NarrowClassGroup.kerToClassGroupEquiv`: **the kernel of `Cl⁺(K) → Cl(K)` is
  the cokernel of the unit signature**, with
  `TauCeti.NumberField.NarrowClassGroup.kerToClassGroupEquiv_mkPrincipal` evaluating it on the
  narrow class of a principal ideal `(x)` as the class of the signature of `x`.
* `TauCeti.NumberField.NarrowClassGroup.card_ker_toClassGroup`: its order is the index of the unit
  signatures.
* `TauCeti.NumberField.NarrowClassGroup.card_eq_card_classGroup_mul_index` and
  `TauCeti.NumberField.NarrowClassGroup.card_mul_card_unitSignatures`: **the narrow class number
  formula**, in index and in product form.
* `TauCeti.NumberField.NarrowClassGroup.card_dvd_card_classGroup_mul_two_pow_nrRealPlaces`:
  `h⁺ ∣ h · 2 ^ r₁`.
* `TauCeti.NumberField.NarrowClassGroup.toClassGroup_injective_iff`: `Cl⁺(K) → Cl(K)` is injective
  exactly when the units realize every sign pattern.

## Roadmap

This advances Layer 3 of `TauCetiRoadmap/Multiquadratic/README.md`, which says that "defining the
narrow class group is part of this layer and the prerequisite for the real case" of the `2`-rank
formula `2-rank = t - 1`. The definition, its finiteness and the surjection onto `Cl(K)` are on
`main`; what was missing is any computation of `Cl⁺(K)` itself, since
`exists_card_eq_card_classGroup_mul_two_pow` pins the extra factor only as *some* power of `2`.
This file computes it: `card_mul_card_unitSignatures` determines `h⁺` from `h` and the unit
signatures, and `toClassGroup_injective_iff` decides, for a given field, whether `Cl⁺(K)` and
`Cl(K)` agree — the case distinction the layer prescribes between the imaginary case, where "narrow
= ordinary", and the real one, where the roadmap's own example `ℚ(√3)` has `t = 2` ramified primes
and class number `1`. For the classical genus theory this serves see D. A. Cox, *Primes of the Form
x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws: from Euler to Eisenstein*; the exact sequence
computing `h⁺/h` from the unit signatures is standard, see also H. Cohen, *A Course in
Computational Algebraic Number Theory*, §5.2.
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

-- The sign group is a product of quotients of `ℝˣ`, so it is commutative; instance search finds
-- `Pi.group` for it and stops, so record the commutativity that makes `unitSignatures K` normal.
local instance : IsMulCommutative
    ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) := ⟨⟨fun x y => mul_comm x y⟩⟩

-- Construction: by `toClassGroup_ker` the kernel is the image of the principal-class map, and by
-- `ker_mkPrincipal` that map's own kernel is the preimage of `unitSignatures K`. The first
-- isomorphism theorem for the field signature, which is onto, then identifies this quotient with
-- the cokernel of the unit signature.
/-- **The kernel of `Cl⁺(K) → Cl(K)` is the cokernel of the unit signature.** Forgetting positivity
loses exactly the sign patterns that the units of `𝓞 K` do not realize. -/
noncomputable def kerToClassGroupEquiv :
    MonoidHom.ker (toClassGroup (K := K)) ≃*
      ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) ⧸ unitSignatures K := by
  let signatureQuotient :
      Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) ⧸ unitSignatures K :=
    (QuotientGroup.mk' (unitSignatures K)).comp (fieldUnitSignature (K := K))
  have hsur : Function.Surjective signatureQuotient :=
    (QuotientGroup.mk'_surjective _).comp fieldUnitSignature_surjective
  have hker : MonoidHom.ker signatureQuotient =
      Subgroup.comap (fieldUnitSignature (K := K)) (unitSignatures K) := by
    ext x
    simp only [MonoidHom.mem_ker, signatureQuotient, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  exact (MulEquiv.subgroupCongr toClassGroup_ker).trans
    ((QuotientGroup.quotientKerEquivRange (mkPrincipal (K := K))).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (ker_mkPrincipal.trans hker.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective signatureQuotient hsur)))

/-- **The kernel equivalence, on a principal class.** `kerToClassGroupEquiv` sends the narrow class
of `(x)` to the class of the signature of `x`, so it is the map the name advertises and not merely
some isomorphism of the right size. -/
@[simp] theorem kerToClassGroupEquiv_mkPrincipal (x : Kˣ)
    (hx : mkPrincipal x ∈ MonoidHom.ker (toClassGroup (K := K))) :
    kerToClassGroupEquiv ⟨mkPrincipal x, hx⟩ =
      (QuotientGroup.mk (fieldUnitSignature x) :
        ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) ⧸ unitSignatures K) := by
  -- The first isomorphism theorem for `mkPrincipal` sends `⟨mkPrincipal x, _⟩` back to the class of
  -- `x`, on which the remaining maps evaluate definitionally.
  have hsymm : (QuotientGroup.quotientKerEquivRange (mkPrincipal (K := K))).symm
      ((MulEquiv.subgroupCongr toClassGroup_ker) ⟨mkPrincipal x, hx⟩) = QuotientGroup.mk x :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext rfl)
  rw [kerToClassGroupEquiv]
  simp only [MulEquiv.trans_apply, hsymm]
  rfl

/-- **The narrow-versus-ordinary defect is the index of the unit signatures.** -/
theorem card_ker_toClassGroup :
    Nat.card (MonoidHom.ker (toClassGroup (K := K))) = (unitSignatures K).index := by
  rw [Nat.card_congr kerToClassGroupEquiv.toEquiv, ← Subgroup.index_eq_card]

/-- **The defect, in product form.** Multiplying by the number of sign patterns realized by the
units clears the index: the kernel of `Cl⁺(K) → Cl(K)` and the unit signatures together account for
all `2 ^ r₁` sign patterns at the real places. -/
theorem card_ker_toClassGroup_mul_card_unitSignatures :
    Nat.card (MonoidHom.ker (toClassGroup (K := K))) * Nat.card (unitSignatures K) =
      2 ^ nrRealPlaces K := by
  rw [card_ker_toClassGroup, mul_comm]
  exact TauCeti.NumberField.card_unitSignatures_mul_index

/-- **The narrow class number formula.** The narrow class number is the ordinary class number times
the index of the sign patterns realized by the units of `𝓞 K`:

```text
h⁺(K) = h(K) · [signature Kˣ : signature (𝓞 K)ˣ].
```

This sharpens `exists_card_eq_card_classGroup_mul_two_pow`, which records only that the second
factor is a power of `2`. -/
theorem card_eq_card_classGroup_mul_index :
    Nat.card (NarrowClassGroup K) =
      Nat.card (ClassGroup (𝓞 K)) * (unitSignatures K).index := by
  rw [card_eq_card_classGroup_mul_card_ker, card_ker_toClassGroup]

/-- **The narrow class number formula, in product form**:

```text
h⁺(K) · #(signature (𝓞 K)ˣ) = h(K) · 2 ^ r₁,
```

which is the classical `h⁺ = h · 2 ^ r₁ / [E : E⁺]` with `E` the units of `𝓞 K` and `E⁺` the
totally positive ones. -/
theorem card_mul_card_unitSignatures :
    Nat.card (NarrowClassGroup K) * Nat.card (unitSignatures K) =
      Nat.card (ClassGroup (𝓞 K)) * 2 ^ nrRealPlaces K := by
  rw [card_eq_card_classGroup_mul_card_ker, mul_assoc,
    card_ker_toClassGroup_mul_card_unitSignatures]

/-- **The narrow class number divides `h · 2 ^ r₁`.** The defect between the narrow and the ordinary
class number is bounded by the number of sign patterns at the real places. -/
theorem card_dvd_card_classGroup_mul_two_pow_nrRealPlaces :
    Nat.card (NarrowClassGroup K) ∣ Nat.card (ClassGroup (𝓞 K)) * 2 ^ nrRealPlaces K := by
  rw [card_eq_card_classGroup_mul_index]
  exact Nat.mul_dvd_mul_left _ ⟨Nat.card (unitSignatures K), by
    rw [mul_comm, TauCeti.NumberField.card_unitSignatures_mul_index]⟩

/-- **The narrow and the ordinary class group agree exactly when the units realize every sign
pattern.** For a totally complex field there are no real places and the sign group is trivial, which
is the content of `toClassGroup_injective`; the criterion is informative for a field with real
places. -/
theorem toClassGroup_injective_iff :
    Function.Injective (toClassGroup (K := K)) ↔ unitSignatures K = ⊤ := by
  rw [← MonoidHom.ker_eq_bot_iff, toClassGroup_ker, Subgroup.eq_bot_iff_forall]
  constructor
  · refine fun h => eq_top_iff.mpr fun z _ => ?_
    obtain ⟨x, rfl⟩ := fieldUnitSignature_surjective z
    exact mkPrincipal_eq_one_iff.mp (h _ ⟨x, rfl⟩)
  · rintro h _ ⟨x, rfl⟩
    exact mkPrincipal_eq_one_iff.mpr (h ▸ Subgroup.mem_top _)

end TauCeti.NumberField.NarrowClassGroup
