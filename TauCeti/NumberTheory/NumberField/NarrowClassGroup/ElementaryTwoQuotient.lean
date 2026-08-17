/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.TotallyComplex

/-!
# The elementary-2 quotient of the narrow class group

For a number field `K`, genus theory computes the maximal elementary-2 quotient

```text
Cl⁺(K) / Cl⁺(K)²
```

of the narrow class group. This quotient, rather than the ordinary class-group quotient, is the
object whose dimension is `t - 1` for a real quadratic field with `t` ramified rational primes.
For a totally complex field the positivity condition is vacuous, so the narrow and ordinary
elementary-2 quotients are linearly equivalent and their 2-ranks agree.

The underlying construction is the general `TauCeti.ElementaryTwoQuotient`. This file specializes
it to the finite group `NarrowClassGroup K`, records its induced map to
`TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K)`, and exposes the rank statements used by the
genus-field milestone of `TauCetiRoadmap/Multiquadratic/README.md`.

## Main definitions and results

* `NumberField.NarrowClassGroup.ElementaryTwoQuotient`: the quotient
  `Cl⁺(K) / Cl⁺(K)²`.
* `NumberField.NarrowClassGroup.toClassGroupElementaryTwoQuotient`: the surjective linear
  map to `Cl(K) / Cl(K)²` induced by forgetting positivity.
* `NumberField.NarrowClassGroup.twoRank` and
  `NumberField.NarrowClassGroup.card_elementaryTwoQuotient_eq_two_pow_twoRank`: the
  `ZMod 2`-dimension of the quotient, with cardinality `2 ^ twoRank K`.
* `NumberField.NarrowClassGroup.classGroupTwoRank_le_twoRank`: the ordinary class-group
  2-rank is at most the narrow class-group 2-rank.
* `NumberField.NarrowClassGroup.toClassGroupElementaryTwoQuotientEquiv`: for a totally
  complex field, the linear equivalence with the ordinary class-group quotient.
* `NumberField.NarrowClassGroup.twoRank_eq_classGroupTwoRank`: for a totally complex
  field, the narrow and ordinary class-group 2-ranks agree.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Chapter 3.
* F. Lemmermeyer, *Reciprocity Laws*, Chapter 6.
-/

public section

open NumberField

namespace NumberField.NarrowClassGroup

variable (K : Type*) [Field K] [NumberField K]

/-- **The maximal elementary-2 quotient of the narrow class group**,
`Cl⁺(K) / Cl⁺(K)²`. This is a finite-dimensional vector space over `ZMod 2`. -/
abbrev ElementaryTwoQuotient : Type _ :=
  TauCeti.ElementaryTwoQuotient (NarrowClassGroup K)

/-- Forgetting positivity induces a `ZMod 2`-linear map
`Cl⁺(K) / Cl⁺(K)² → Cl(K) / Cl(K)²`. -/
noncomputable def toClassGroupElementaryTwoQuotient :
    ElementaryTwoQuotient K →ₗ[ZMod 2] TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K) :=
  TauCeti.elementaryTwoQuotientMap (toClassGroup (K := K))

/-- The map on elementary-2 quotients induced by forgetting positivity sends the class of `C` to
the square class of its image in the ordinary class group. -/
@[simp] theorem toClassGroupElementaryTwoQuotient_mk (C : NarrowClassGroup K) :
    toClassGroupElementaryTwoQuotient K (TauCeti.elementaryTwoQuotientMk C) =
      TauCeti.elementaryTwoQuotientMk (toClassGroup C) :=
  TauCeti.elementaryTwoQuotientMap_mk (toClassGroup (K := K)) C

/-- The induced map `Cl⁺(K) / Cl⁺(K)² → Cl(K) / Cl(K)²` is surjective. -/
theorem toClassGroupElementaryTwoQuotient_surjective :
    Function.Surjective (toClassGroupElementaryTwoQuotient K) :=
  TauCeti.elementaryTwoQuotientMap_surjective
    (toClassGroup (K := K)) toClassGroup_surjective

/-- **The narrow class-group 2-rank**: the dimension over `ZMod 2` of
`Cl⁺(K) / Cl⁺(K)²`. -/
noncomputable def twoRank : ℕ :=
  TauCeti.twoRank (NarrowClassGroup K)

/-- The narrow class-group 2-rank is the dimension of its maximal elementary-2 quotient. -/
@[simp] theorem twoRank_def :
    twoRank K = Module.finrank (ZMod 2) (ElementaryTwoQuotient K) :=
  TauCeti.twoRank_def (NarrowClassGroup K)

/-- The maximal elementary-2 quotient of the narrow class group has `2 ^ twoRank K` elements. -/
theorem card_elementaryTwoQuotient_eq_two_pow_twoRank :
    Nat.card (ElementaryTwoQuotient K) = 2 ^ twoRank K :=
  TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank (NarrowClassGroup K)

/-- The ordinary class-group 2-rank is at most the narrow class-group 2-rank. The inequality can
be strict for real fields because forgetting positivity is only a surjection. -/
theorem classGroupTwoRank_le_twoRank :
    TauCeti.ClassGroup.twoRank (𝓞 K) ≤ twoRank K := by
  rw [TauCeti.ClassGroup.twoRank_def, ← TauCeti.twoRank_def]
  exact TauCeti.twoRank_le_twoRank_of_surjective
    (toClassGroup (K := K)) toClassGroup_surjective

/-- For a totally complex field, the elementary-2 quotients of the narrow and ordinary class
groups are linearly equivalent over `ZMod 2`. -/
noncomputable def toClassGroupElementaryTwoQuotientEquiv [IsTotallyComplex K] :
    ElementaryTwoQuotient K ≃ₗ[ZMod 2] TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K) :=
  TauCeti.elementaryTwoQuotientCongr (toClassGroupEquiv (K := K))

/-- For a totally complex field, the elementary-2 quotient equivalence is the linear map induced
by forgetting positivity. -/
@[simp] theorem toClassGroupElementaryTwoQuotientEquiv_apply [IsTotallyComplex K]
    (x : ElementaryTwoQuotient K) :
    toClassGroupElementaryTwoQuotientEquiv K x = toClassGroupElementaryTwoQuotient K x := by
  obtain ⟨C, rfl⟩ := TauCeti.elementaryTwoQuotientMk_surjective (G := NarrowClassGroup K) x
  rw [toClassGroupElementaryTwoQuotient_mk]
  dsimp only [toClassGroupElementaryTwoQuotientEquiv]
  rw [TauCeti.elementaryTwoQuotientCongr_mk, toClassGroupEquiv_apply]

/-- **For a totally complex field, the narrow and ordinary class-group 2-ranks agree.** -/
theorem twoRank_eq_classGroupTwoRank [IsTotallyComplex K] :
    twoRank K = TauCeti.ClassGroup.twoRank (𝓞 K) := by
  rw [TauCeti.ClassGroup.twoRank_def, ← TauCeti.twoRank_def]
  exact TauCeti.twoRank_eq_of_mulEquiv (toClassGroupEquiv (K := K))

end NumberField.NarrowClassGroup
