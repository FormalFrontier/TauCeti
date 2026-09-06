/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialIsogeny
public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Power

/-!
# The odd half-Frobenius power of a Suzuki--Ree index

The Steinberg endomorphism of a Suzuki, Ree or Tits group is not a Frobenius but an *odd power of
a half-Frobenius*: the exceptional isogeny `τ` of the pinned ambient group, which squares to the
prime-field Frobenius, raised to the odd exponent `2 * m + 1`. This file takes that odd power on
root data, where `τ` already lives as
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny`, and proves the relation the CFSG roadmap requires of
it,

```text
steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1)).
```

The exponent is not a new parameter. `TauCeti.LieTypeIndex.fieldExponent` already writes the field
order of an index as a power of its characteristic, and on all four half-Frobenius branches it is
odd: it is `2 * m + 1` on the three Suzuki--Ree families and `1` on the Tits index, whose Steinberg
map is `τ` itself. So `TauCeti.SuzukiReeIndex.halfExponent` reads off the `m` those four branches
share, `fieldExponent_eq_two_mul_halfExponent_add_one` is the odd decomposition, and the Steinberg
map is the `fieldExponent`-th power throughout. Squaring it then lands on the scaling by
`TauCeti.LieTypeIndex.fieldOrder` rather than on some separately tabulated field order, which is
the check that the exponent convention of milestone L2 and the numeric data of milestone I0 agree.

The odd power is genuinely a new map and not a rescaled identity: it is a scaling times `τ`, so it
permutes the roots exactly as `τ` does, by the length-exchanging permutation
`TauCeti.SuzukiReeIndex.lengthPerm` on the numbered simple roots, and merely multiplies the pinned
exponents of `τ` by `p ^ m`. The resulting relations on the numbered simple roots and coroots are
recorded below, since a consumer lifting this map to the pinned group scheme states its
conventions against them.

Nothing here is a group. Lifting these isogenies from root data to the pinned
Chevalley--Demazure group schemes, and the finite groups cut out as their fixed points, are later
work.

## Main definitions

* `TauCeti.SuzukiReeIndex.halfExponent`: the `m` in the field order `p ^ (2 * m + 1)`.
* `TauCeti.SuzukiReeIndex.datumSteinberg`: the odd power `τ ^ (2 * m + 1)` of the special isogeny
  selected by the index, on its pinned simply connected root datum.

## Main results

* `TauCeti.SuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one` and
  `TauCeti.SuzukiReeIndex.odd_fieldExponent`: the field exponent of a half-Frobenius index is odd,
  with half `halfExponent`.
* `TauCeti.SuzukiReeIndex.halfExponent_eq_zero_iff`: it vanishes exactly on the Tits index, and
  `TauCeti.SuzukiReeIndex.datumSteinberg_tits` is the resulting degeneration of the Steinberg map
  to the special isogeny itself there.
* `TauCeti.SuzukiReeIndex.datumSteinberg_mul_self`: the square of the Steinberg map is the scaling
  by the field order of the index, the root-datum form of
  `steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1))`.
* `TauCeti.SuzukiReeIndex.datumSteinberg_eq_smulId_mul`: it is the scaling by `p ^ m` times the
  special isogeny, which is what keeps the odd power from collapsing to a scaling.
* `TauCeti.SuzukiReeIndex.datumSteinberg_indexEquiv`,
  `TauCeti.SuzukiReeIndex.datumSteinberg_exponent`,
  `TauCeti.SuzukiReeIndex.datumSteinberg_weightMap` and
  `TauCeti.SuzukiReeIndex.datumSteinberg_coweightMap`: it permutes the roots exactly as the special
  isogeny does, and its exponents and its two lattice maps are those of the special isogeny scaled
  by `p ^ m`.
* `TauCeti.SuzukiReeIndex.datumSteinberg_weightMap_root_simpleIndex` and
  `TauCeti.SuzukiReeIndex.datumSteinberg_coweightMap_coroot_simpleIndex`: the defining relations on
  the numbered simple roots and coroots.

## References

The odd half-Frobenius power and the relation `steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1))` are
milestone L2 of `TauCetiRoadmap/CFSGStatement/README.md`, which fixes the convention followed here,
including the Tits index as the `m = 0` member. The upstream exceptional isogeny is the Layer 9
target of `TauCetiRoadmap/ReductiveGroups/README.md`.

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §13.
* *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  [arXiv:2108.06291](https://arxiv.org/abs/2108.06291), for the formulation `τ ^ 2 = Frob_p` and
  its odd powers.
-/

public section

namespace TauCeti

namespace SuzukiReeIndex

/-! ## The odd exponent -/

/-- The odd-power parameter `m` of a Suzuki--Ree index: the `m` in the field order
`p ^ (2 * m + 1)` recorded by the three Suzuki--Ree families, and `0` on the Tits index, whose
Steinberg map is the half-Frobenius itself.

The four branch equations below name it on each family, so no consumer needs this body. -/
def halfExponent (e : SuzukiReeIndex) : ℕ :=
  match e with
  | ⟨⟨.A _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedA _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.B _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.C _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.D _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedD _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E7 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E8 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.F4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.G2 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedE6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.trialityD4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.suzuki m, _⟩, _⟩ => m
  | ⟨⟨.reeG2 m, _⟩, _⟩ => m
  | ⟨⟨.reeF4 m, _⟩, _⟩ => m
  | ⟨⟨.tits, _⟩, _⟩ => 0

/-- A Suzuki index contributes its own parameter. -/
@[simp] theorem halfExponent_suzuki (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) :
    halfExponent ⟨⟨.suzuki m, hvalid⟩, by simp⟩ = m := by
  simp only [halfExponent]

/-- A Ree `G₂` index contributes its own parameter. -/
@[simp] theorem halfExponent_reeG2 (m : ℕ) (hvalid : (LieTypeIndex.reeG2 m).Valid) :
    halfExponent ⟨⟨.reeG2 m, hvalid⟩, by simp⟩ = m := by
  simp only [halfExponent]

/-- A Ree `F₄` index contributes its own parameter. -/
@[simp] theorem halfExponent_reeF4 (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid) :
    halfExponent ⟨⟨.reeF4 m, hvalid⟩, by simp⟩ = m := by
  simp only [halfExponent]

/-- The Tits index is the `m = 0` member of the `F₄` half-Frobenius family. -/
@[simp] theorem halfExponent_tits :
    halfExponent ⟨⟨.tits, by simp⟩, by simp⟩ = 0 := by
  simp only [halfExponent]

/-- **The field exponent of a half-Frobenius index is `2 * m + 1`.** The Steinberg map is the
`fieldExponent`-th power of the half-Frobenius, so this is what makes it an odd power. -/
theorem fieldExponent_eq_two_mul_halfExponent_add_one (e : SuzukiReeIndex) :
    e.1.fieldExponent = 2 * e.halfExponent + 1 := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  all_goals simp [halfExponent, ValidLieTypeIndex.fieldExponent]

/-- The field exponent of a half-Frobenius index is odd. -/
theorem odd_fieldExponent (e : SuzukiReeIndex) : Odd e.1.fieldExponent :=
  ⟨e.halfExponent, e.fieldExponent_eq_two_mul_halfExponent_add_one⟩

/-- **The odd-power parameter vanishes exactly on the Tits index.** The three Suzuki--Ree families
start at `m = 1`: their `m = 0` members are the nonsimple `²B₂(2)`, the likewise nonsimple
`²G₂(3)`, whose derived subgroup is the group the list carries as `A₁(8)`, and `²F₄(2)`, whose
derived subgroup the list carries under the separate Tits name. So the Tits index is the only
half-Frobenius index whose Steinberg map is the special isogeny itself. -/
theorem halfExponent_eq_zero_iff (e : SuzukiReeIndex) :
    e.halfExponent = 0 ↔ e.1.1 = .tits := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff] at hvalid
  cases d <;> try simp at hhalf
  case tits => simp [halfExponent]
  all_goals
    obtain ⟨hm, -⟩ := hvalid
    simp only [halfExponent, reduceCtorEq, iff_false]
    omega

/-! ## The Steinberg map on the root datum -/

/-- **The Steinberg map of a Suzuki--Ree index on its pinned simply connected root datum**: the
odd power `τ ^ (2 * m + 1)` of the special isogeny selected by the index, written as its
`fieldExponent`-th power. On the Tits index the exponent is `1` and the map is `τ` itself. -/
noncomputable def datumSteinberg (e : SuzukiReeIndex) :
    RootPairingIsogeny (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid)
      (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid) :=
  e.datumSpecialIsogeny ^ e.1.fieldExponent

/-- **The Steinberg map is a scaling times the special isogeny**, by `p ^ m`. Every computation
below is read off this decomposition. -/
theorem datumSteinberg_eq_smulId_mul (e : SuzukiReeIndex) :
    e.datumSteinberg =
      RootPairingIsogeny.smulId _ (⟨e.1.characteristic, e.1.characteristic_prime.pos⟩ ^
        e.halfExponent) * e.datumSpecialIsogeny := by
  rw [datumSteinberg, fieldExponent_eq_two_mul_halfExponent_add_one]
  exact RootPairingIsogeny.pow_two_mul_add_one_eq_smulId_mul _ e.datumSpecialIsogeny_mul_self _

/-- On the Tits index the Steinberg map is the special isogeny of `F₄` itself, the `m = 0` case of
the odd power. -/
@[simp] theorem datumSteinberg_tits :
    datumSteinberg ⟨⟨.tits, by simp⟩, by simp⟩ =
      datumSpecialIsogeny ⟨⟨.tits, by simp⟩, by simp⟩ := by
  have h : ValidLieTypeIndex.fieldExponent ⟨LieTypeIndex.tits, by simp⟩ = 1 :=
    LieTypeIndex.fieldExponent_tits
  rw [datumSteinberg, h, pow_one]

/-! ### The square relation -/

/-- **The square of the Steinberg map is the scaling by the field order of the index.** This is the
root-datum form of `steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1))`: squaring the odd power of the
half-Frobenius returns the Frobenius of the field the index names, `2 ^ (2 * m + 1)` for the Suzuki
and Ree `F₄` families, `3 ^ (2 * m + 1)` for Ree `G₂`, and `2` for the Tits index. -/
@[simp] theorem datumSteinberg_mul_self (e : SuzukiReeIndex) :
    e.datumSteinberg * e.datumSteinberg =
      RootPairingIsogeny.smulId _ e.1.1.fieldOrderPNat := by
  rw [datumSteinberg, RootPairingIsogeny.pow_mul_self_eq_smulId _ e.datumSpecialIsogeny_mul_self]
  -- The two scalings differ only in how their common value `p ^ (2 * m + 1)` is written, so all
  -- that is left is the numeric identity between the field order and that power.
  congr 1
  refine PNat.coe_injective ?_
  rw [LieTypeIndex.coe_fieldOrderPNat]
  exact e.1.fieldOrder_eq_characteristic_pow.symm

/-! ### The four pieces of data -/

/-- **The Steinberg map permutes the roots exactly as the special isogeny does**, since the
scaling separating the two fixes every index. -/
@[simp] theorem datumSteinberg_indexEquiv (e : SuzukiReeIndex) :
    e.datumSteinberg.indexEquiv = e.datumSpecialIsogeny.indexEquiv := by
  rw [datumSteinberg, fieldExponent_eq_two_mul_halfExponent_add_one]
  exact RootPairingIsogeny.indexEquiv_pow_two_mul_add_one _ e.datumSpecialIsogeny_mul_self _

/-- **The rescaling exponents of the Steinberg map** are those of the special isogeny multiplied by
`p ^ m`. At a numbered simple root the exponent of the special isogeny is the squared length of
that node, so this is `p ^ m` at a short simple root and `p ^ (m + 1)` at a long one.

The `exponent` field is indexed by the source of the character map, which is the image node of the
group-scheme isogeny, so this indexing is the one exchanged against the simple-root relation below:
the factor there is `TauCeti.SuzukiReeIndex.exponent i`, the squared length of the node paired with
`i`, and is therefore `p ^ m` at a long node and `p ^ (m + 1)` at a short one. -/
@[simp] theorem datumSteinberg_exponent (e : SuzukiReeIndex)
    (i : Fin e.1.dynkinType.numRoots) :
    e.datumSteinberg.exponent i =
      e.datumSpecialIsogeny.exponent i * (e.1.characteristic : ℤ) ^ e.halfExponent := by
  rw [datumSteinberg, fieldExponent_eq_two_mul_halfExponent_add_one]
  exact RootPairingIsogeny.exponent_pow_two_mul_add_one _ e.datumSpecialIsogeny_mul_self _ i

/-- **The character map of the Steinberg map** is `p ^ m` times that of the special isogeny. -/
@[simp] theorem datumSteinberg_weightMap (e : SuzukiReeIndex) :
    e.datumSteinberg.weightMap =
      (e.1.characteristic ^ e.halfExponent) • e.datumSpecialIsogeny.weightMap := by
  rw [datumSteinberg, fieldExponent_eq_two_mul_halfExponent_add_one]
  exact RootPairingIsogeny.weightMap_pow_two_mul_add_one _ e.datumSpecialIsogeny_mul_self _

/-- **The cocharacter map of the Steinberg map** is `p ^ m` times that of the special isogeny. -/
@[simp] theorem datumSteinberg_coweightMap (e : SuzukiReeIndex) :
    e.datumSteinberg.coweightMap =
      (e.1.characteristic ^ e.halfExponent) • e.datumSpecialIsogeny.coweightMap := by
  rw [datumSteinberg, fieldExponent_eq_two_mul_halfExponent_add_one]
  exact RootPairingIsogeny.coweightMap_pow_two_mul_add_one _ e.datumSpecialIsogeny_mul_self _

/-! ### The defining relations on the numbered simple roots -/

/-- **The relation defining the Steinberg map on the simple roots.** The character map carries the
simple root at the length-exchanged node to the simple root at `i`, rescaled by
`p ^ m * TauCeti.SuzukiReeIndex.exponent i`, which is `p ^ m` at a long node and `p ^ (m + 1)` at a
short one.

The character map is the pullback along the group-scheme isogeny, so this is the root-datum shadow
of `steinberg (x_{α_i}(t)) = x_{α_{σ i}}(t ^ (p ^ m * exponent i))`, with the exponent indexed by
`i` rather than by its image. -/
theorem datumSteinberg_weightMap_root_simpleIndex (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.datumSteinberg.weightMap
        ((e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i))) =
      ((e.exponent i : ℤ) * (e.1.characteristic : ℤ) ^ e.halfExponent) •
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i) := by
  -- The relation for the special isogeny is already proved; the Steinberg map only rescales it.
  rw [datumSteinberg_weightMap, LinearMap.smul_apply,
    e.datumSpecialIsogeny_weightMap_root_simpleIndex i]
  match_scalars
  ring

/-- **The relation defining the Steinberg map on the simple coroots.** Dually to
`TauCeti.SuzukiReeIndex.datumSteinberg_weightMap_root_simpleIndex`, the cocharacter map runs the
other way, so it carries the simple coroot at `i` to the one at the length-exchanged node, rescaled
by the same factor. -/
theorem datumSteinberg_coweightMap_coroot_simpleIndex (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.datumSteinberg.coweightMap
        ((e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).coroot
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i)) =
      ((e.exponent i : ℤ) * (e.1.characteristic : ℤ) ^ e.halfExponent) •
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).coroot
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i)) := by
  rw [datumSteinberg_coweightMap, LinearMap.smul_apply,
    e.datumSpecialIsogeny_coweightMap_coroot_simpleIndex i]
  match_scalars
  ring

end SuzukiReeIndex

end TauCeti
