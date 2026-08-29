/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.SpecialIsogeny

/-!
# Root-datum Steinberg maps for the Suzuki--Ree families

The Steinberg map defining a Suzuki or Ree group is not a field Frobenius composed with a diagram
automorphism. It is the odd power `τ ^ (2 * m + 1)` of the special isogeny `τ` in characteristic
two or three. The Tits group uses the same construction at `m = 0`, hence uses `τ` itself.

This file performs that construction on the pinned simply connected root datum. The selected
special isogeny is `TauCeti.SuzukiReeIndex.datumSpecialIsogeny`, and the odd exponent is already
recorded by the index as `TauCeti.ValidLieTypeIndex.fieldExponent`. Thus
`TauCeti.SuzukiReeIndex.datumSteinberg` contains no new family table. Its four branch equations
show that it is exactly `τ ^ (2 * m + 1)` on each uniform family and `τ` on the Tits branch.

The principal relation is

```text
datumSteinberg * datumSteinberg = smulId (p ^ fieldExponent),
```

the root-datum form of `steinberg(m) ^ 2 = Frob_(p ^ (2 * m + 1))`. Since the index already proves
`fieldOrder = p ^ fieldExponent`, the scalar on the right is its finite-field parameter. The
simple-root formulas also retain the pinned convention: the length permutation exchanges the
nodes, and the root-subgroup exponent is `p ^ m` times `1` on a long node or `p` on a short node.

Nothing here constructs a group scheme or a group of points. Lifting these maps to the pinned
Chevalley--Demazure carriers remains the upstream Layer 9 dependency of the group-valued part of
the CFSG roadmap.

## Main definitions and results

* `TauCeti.SuzukiReeIndex.datumSteinberg`: the odd power of the selected special isogeny.
* `TauCeti.SuzukiReeIndex.datumSteinberg_comp_self`: its square is the scaling by the field order.
* `TauCeti.SuzukiReeIndex.datumSteinberg_indexEquiv_simpleIndex`: its action on the numbered
  simple-root indices is the pinned length permutation.
* `TauCeti.SuzukiReeIndex.datumSteinberg_weightMap_root_simpleIndex` and
  `TauCeti.SuzukiReeIndex.datumSteinberg_coweightMap_coroot_simpleIndex`: the odd-power formulas
  on the numbered simple roots and coroots.

This is the odd-power target of milestone L2, "Suzuki--Ree Steinberg maps", in
`TauCetiRoadmap/CFSGStatement/README.md`. The construction and conventions follow R. Steinberg,
*Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11, and R. W. Carter,
*Simple Groups of Lie Type*, §§12.3--12.4.
-/

public section

namespace TauCeti

namespace SuzukiReeIndex

variable (e : SuzukiReeIndex)

/-- The field exponent of a Suzuki--Ree index is odd. It is `2 * m + 1` on the three uniform
families and `1` on the Tits branch. -/
theorem fieldExponent_odd : Odd e.1.fieldExponent := by
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  all_goals simp [ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_suzuki,
    LieTypeIndex.fieldExponent_reeG2, LieTypeIndex.fieldExponent_reeF4,
    LieTypeIndex.fieldExponent_tits]

noncomputable section

/-- **The root-datum Steinberg map of a Suzuki--Ree index**: the odd power of the selected special
isogeny. The exponent is `2 * m + 1` for the Suzuki and Ree constructors, and `1` for the Tits
constructor. -/
def datumSteinberg :
    RootPairingIsogeny (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid)
      (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid) :=
  e.datumSpecialIsogeny ^ e.1.fieldExponent

/-- The root-datum Steinberg map is the power recorded by the index's field exponent. -/
theorem datumSteinberg_def :
    e.datumSteinberg = e.datumSpecialIsogeny ^ e.1.fieldExponent := (rfl)

/-! ### Branch equations -/

/-- The Suzuki Steinberg map is the `(2 * m + 1)`-st power of the `B₂` special isogeny selected
by the index. -/
@[simp] theorem datumSteinberg_suzuki (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) :
    datumSteinberg ⟨⟨.suzuki m, hvalid⟩, by simp⟩ =
      datumSpecialIsogeny ⟨⟨.suzuki m, hvalid⟩, by simp⟩ ^ (2 * m + 1) := by
  rw [datumSteinberg_def]
  simp only [ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_suzuki]

/-- The Ree `G₂` Steinberg map is the `(2 * m + 1)`-st power of the selected `G₂` special
isogeny. -/
@[simp] theorem datumSteinberg_reeG2 (m : ℕ) (hvalid : (LieTypeIndex.reeG2 m).Valid) :
    datumSteinberg ⟨⟨.reeG2 m, hvalid⟩, by simp⟩ =
      datumSpecialIsogeny ⟨⟨.reeG2 m, hvalid⟩, by simp⟩ ^ (2 * m + 1) := by
  rw [datumSteinberg_def]
  simp only [ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_reeG2]

/-- The Ree `F₄` Steinberg map is the `(2 * m + 1)`-st power of the selected `F₄` special
isogeny. -/
@[simp] theorem datumSteinberg_reeF4 (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid) :
    datumSteinberg ⟨⟨.reeF4 m, hvalid⟩, by simp⟩ =
      datumSpecialIsogeny ⟨⟨.reeF4 m, hvalid⟩, by simp⟩ ^ (2 * m + 1) := by
  rw [datumSteinberg_def]
  simp only [ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_reeF4]

/-- The Tits Steinberg map is the selected `F₄` special isogeny itself, corresponding to
`m = 0`. -/
@[simp] theorem datumSteinberg_tits :
    datumSteinberg ⟨⟨.tits, by simp⟩, by simp⟩ =
      datumSpecialIsogeny ⟨⟨.tits, by simp⟩, by simp⟩ := by
  rw [datumSteinberg_def]
  simp only [ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_tits, pow_one]

/-! ### The odd-power relations -/

/-- An odd power of the special isogeny induces the same permutation of roots as the special
isogeny itself. -/
@[simp] theorem datumSteinberg_indexEquiv :
    e.datumSteinberg.indexEquiv = e.datumSpecialIsogeny.indexEquiv := by
  simpa only [datumSteinberg_def,
    Nat.two_mul_div_two_add_one_of_odd e.fieldExponent_odd] using
      RootPairingIsogeny.indexEquiv_pow_two_mul_add_one
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid)
        e.datumSpecialIsogeny_comp_self (e.1.fieldExponent / 2)

/-- The Steinberg map carries the numbered simple-root index `i` to its pinned length-exchanged
partner. -/
theorem datumSteinberg_indexEquiv_simpleIndex (i : Fin e.1.rank) :
    e.datumSteinberg.indexEquiv
        (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i) =
      e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i) := by
  rw [datumSteinberg_indexEquiv, datumSpecialIsogeny_indexEquiv_simpleIndex]

/-- The exponent of the root-datum Steinberg map at a numbered simple root. The factor from the
odd power is `p ^ (fieldExponent / 2)`; the remaining factor is the squared root length attached
to the selected special isogeny. -/
@[simp] theorem datumSteinberg_exponent_simpleIndex (i : Fin e.1.rank) :
    e.datumSteinberg.exponent
        (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i) =
      e.1.dynkinType.rootLength i *
        (e.1.characteristic : ℤ) ^ (e.1.fieldExponent / 2) := by
  rw [datumSteinberg_def]
  conv_lhs =>
    rw [← Nat.two_mul_div_two_add_one_of_odd e.fieldExponent_odd]
  rw [RootPairingIsogeny.exponent_pow_two_mul_add_one _ e.datumSpecialIsogeny_comp_self,
    datumSpecialIsogeny_exponent_simpleIndex]
  norm_cast

/-- **The Steinberg map on the Bourbaki-numbered simple roots.** It moves the root at `i` along
the pinned length permutation and rescales it by its squared length times
`p ^ (fieldExponent / 2)`. -/
theorem datumSteinberg_weightMap_root_simpleIndex (i : Fin e.1.rank) :
    e.datumSteinberg.weightMap
        ((e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i)) =
      (e.1.dynkinType.rootLength i *
          (e.1.characteristic : ℤ) ^ (e.1.fieldExponent / 2)) •
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i)) := by
  rw [e.datumSteinberg.root_weightMap, datumSteinberg_exponent_simpleIndex,
    datumSteinberg_indexEquiv_simpleIndex]
  simp only [Int.cast_id]

/-- **The Steinberg map in the CFSG root-subgroup orientation.** The root at the
length-exchanged node maps to the root at `i`; its scalar is the roadmap's root-subgroup exponent
at `i`, multiplied by the common factor `p ^ (fieldExponent / 2)`. -/
theorem datumSteinberg_weightMap_root_lengthPerm (i : Fin e.1.rank) :
    e.datumSteinberg.weightMap
        ((e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i))) =
      ((e.exponent i : ℤ) *
          (e.1.characteristic : ℤ) ^ (e.1.fieldExponent / 2)) •
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).root
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i) := by
  rw [datumSteinberg_weightMap_root_simpleIndex, lengthPerm_lengthPerm, rootLength_lengthPerm]

/-- **The Steinberg map on the Bourbaki-numbered simple coroots.** Contravariance reverses the
length permutation, which is an involution, and leaves the same scalar as the root-subgroup
orientation. -/
theorem datumSteinberg_coweightMap_coroot_simpleIndex (i : Fin e.1.rank) :
    e.datumSteinberg.coweightMap
        ((e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).coroot
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid i)) =
      ((e.exponent i : ℤ) *
          (e.1.characteristic : ℤ) ^ (e.1.fieldExponent / 2)) •
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid).coroot
          (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i)) := by
  have h := e.datumSteinberg.coroot_coweightMap
    (e.1.dynkinType.simpleIndex e.1.dynkinType_valid (e.lengthPerm i))
  rw [datumSteinberg_indexEquiv_simpleIndex, lengthPerm_lengthPerm,
    datumSteinberg_exponent_simpleIndex, rootLength_lengthPerm, Int.cast_id] at h
  exact h

/-- The positive-natural scalar `p ^ fieldExponent` underlying the Steinberg square has value the
field order recorded by the index. -/
theorem coe_characteristic_pow_fieldExponent :
    (((⟨e.1.characteristic, e.1.characteristic_prime.pos⟩ : ℕ+) ^
      e.1.fieldExponent : ℕ+) : ℕ) = e.1.fieldOrder := by
  exact e.1.fieldOrder_eq_characteristic_pow.symm

/-- **The square of the Suzuki--Ree root-datum Steinberg map is the field-order Frobenius
scaling.** This is `steinberg(m) ^ 2 = Frob_(p ^ (2 * m + 1))`, including the Tits value `m = 0`.
The preceding theorem identifies the positive-natural scalar on the right with
`e.1.fieldOrder`. -/
@[simp] theorem datumSteinberg_comp_self :
    e.datumSteinberg.comp e.datumSteinberg =
      RootPairingIsogeny.smulId _
        (⟨e.1.characteristic, e.1.characteristic_prime.pos⟩ ^ e.1.fieldExponent) := by
  calc
    e.datumSteinberg.comp e.datumSteinberg = e.datumSteinberg * e.datumSteinberg := rfl
    _ = RootPairingIsogeny.smulId _
        (⟨e.1.characteristic, e.1.characteristic_prime.pos⟩ ^ e.1.fieldExponent) := by
      rw [datumSteinberg_def]
      exact RootPairingIsogeny.pow_mul_self_eq_smulId
        (e.1.dynkinType.simplyConnectedRootDatum e.1.dynkinType_valid)
        e.datumSpecialIsogeny_comp_self e.1.fieldExponent

end

end SuzukiReeIndex

end TauCeti
