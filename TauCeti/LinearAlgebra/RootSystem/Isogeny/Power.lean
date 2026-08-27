/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special

/-!
# Odd powers of a special isogeny

This file applies the self-isogeny monoid and iterate API from
`TauCeti/LinearAlgebra/RootSystem/Isogeny/Basic.lean` to the special isogenies of the pinned `G₂`
and `F₄` root data. Their squares are scalings by three and two, respectively, so their even powers
are scalings and an odd power is a scaling composed with the original special isogeny.

For an odd power `τ ^ (2 * m + 1)`, the two root-datum exponents at a length-exchanged pair of
indices are `p ^ m` and `p ^ (m + 1)`. The root-datum exponent is `p ^ (m + 1)` at a long source
node and `p ^ m` at a short source node. The simple-node lemmas below also evaluate the exponent at
the length-exchanged source index, where the values are `p ^ m` for a long target node and
`p ^ (m + 1)` for a short target node.

Squaring any power returns a scaling, `τ ^ k * τ ^ k = smulId P (p ^ k)`. The corresponding
group-scheme relation is an intended downstream application; no group or group-scheme map is
constructed here.

## Main results

* `TauCeti.DynkinType.g2SpecialIsogeny_pow_mul_pow` and its `F₄` counterpart: the square relation
  for every power of the special isogeny.
* `TauCeti.DynkinType.g2SpecialIsogeny_pow_odd_weightMap_root` and its `F₄` counterpart: the action
  on roots; the corresponding `coroot_coweightMap` lemmas give the dual action.
* `TauCeti.DynkinType.g2SpecialIsogeny_pow_odd_exponent_at_lengthPerm_of_isLongSimpleRoot` and its
  three companions: the root-datum exponent at a length-exchanged simple index.

## Roadmap and references

Milestone L2 of `TauCetiRoadmap/CFSGStatement/README.md` selects the upstream special isogeny and
forms its odd powers. This file supplies the root-datum iterate prerequisite for that construction.
The special isogenies it powers are prerequisites for the target "Special isogenies in
characteristics two and three" of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`.

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* Schémas en groupes (SGA 3), Exposé XXI, 6.8, and Exposé XXII.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3--12.4.
-/

public section

namespace TauCeti

namespace DynkinType

open RootPairingIsogeny

/-! ## Odd powers of the special isogeny of `G₂` -/

/-- **The even powers of the special isogeny of `G₂` are Frobenius scalings.** -/
theorem g2SpecialIsogeny_pow_two_mul (m : ℕ) :
    g2SpecialIsogeny ^ (2 * m) = smulId g2SimplyConnectedRootDatum (3 ^ m) :=
  pow_two_mul_of_mul_self g2SpecialIsogeny_mul_self m

/-- **Every power of the special isogeny of `G₂` squares to a Frobenius scaling.** At
`k = 2 * m + 1` this is the root-datum form of `steinberg(m) ^ 2 = Frob_(3 ^ (2m+1))`, the relation
whose group-scheme counterpart cuts out the Ree groups `²G₂(3 ^ (2m+1))`. Nothing about a group is
proved here. -/
theorem g2SpecialIsogeny_pow_mul_pow (k : ℕ) :
    g2SpecialIsogeny ^ k * g2SpecialIsogeny ^ k =
      smulId g2SimplyConnectedRootDatum (3 ^ k) :=
  pow_mul_pow_of_mul_self g2SpecialIsogeny_mul_self k

/-- An odd power of the special isogeny of `G₂` permutes the twelve roots exactly as the isogeny
itself does.

This is deliberately not `@[simp]`: `TauCeti.RootPairingIsogeny.pow_indexEquiv` already pushes the
power inside, so the left-hand side is not in simp normal form. -/
theorem g2SpecialIsogeny_pow_odd_indexEquiv_apply (m : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ (2 * m + 1)).indexEquiv i = g2SpecialIsogenyIndex i := by
  rw [pow_odd_indexEquiv_of_mul_self_eq_smulId g2SpecialIsogeny_mul_self,
    g2SpecialIsogeny_indexEquiv_apply]

/-- **The root-datum exponent of an odd power of the special isogeny of `G₂`** is the squared
length of the source root, times `3 ^ m`. -/
@[simp] theorem g2SpecialIsogeny_pow_odd_exponent (m : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ (2 * m + 1)).exponent i = g2Length i * 3 ^ m := by
  rw [pow_odd_exponent_of_mul_self_eq_smulId g2SpecialIsogeny_mul_self,
    g2SpecialIsogeny_exponent]
  norm_num

/-- **The defining relation of an odd power of the special isogeny of `G₂` on the roots.** The
displayed coefficient is the root-datum exponent at the source index `i`. -/
theorem g2SpecialIsogeny_pow_odd_weightMap_root (m : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ (2 * m + 1)).weightMap (g2SimplyConnectedRootDatum.root i) =
      (g2Length i * 3 ^ m) • g2SimplyConnectedRootDatum.root (g2SpecialIsogenyIndex i) := by
  rw [root_weightMap_pow_odd_of_mul_self_eq_smulId g2SpecialIsogeny_mul_self,
    g2SpecialIsogeny_exponent, g2SpecialIsogeny_indexEquiv_apply]
  norm_num

/-- **The defining relation of an odd power of the special isogeny of `G₂` on the coroots.** -/
theorem g2SpecialIsogeny_pow_odd_coroot_coweightMap (m : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ (2 * m + 1)).coweightMap
        (g2SimplyConnectedRootDatum.coroot (g2SpecialIsogenyIndex i)) =
      (g2Length i * 3 ^ m) • g2SimplyConnectedRootDatum.coroot i := by
  rw [← g2SpecialIsogeny_indexEquiv_apply]
  rw [coroot_coweightMap_pow_odd_of_mul_self_eq_smulId g2SpecialIsogeny_mul_self,
    g2SpecialIsogeny_exponent]
  norm_num

/-- At the source index length-exchanged from a long simple node of `G₂`, the root-datum exponent
of the `(2m+1)`-st power is `3 ^ m`. -/
theorem g2SpecialIsogeny_pow_odd_exponent_at_lengthPerm_of_isLongSimpleRoot (m : ℕ) {i : Fin 2}
    (hi : G2.IsLongSimpleRoot i) :
    (g2SpecialIsogeny ^ (2 * m + 1)).exponent
        (Fin.castLE (by omega) (lengthPermRankTwo i)) = 3 ^ m := by
  have hshort : ¬ G2.IsLongSimpleRoot (lengthPermRankTwo i) := by simpa using hi
  rw [g2SpecialIsogeny_pow_odd_exponent,
    (g2Length_castLE_eq_one_iff (lengthPermRankTwo i)).mpr hshort, one_mul]

/-- At the source index length-exchanged from a short simple node of `G₂`, the root-datum exponent
of the `(2m+1)`-st power is `3 ^ (m + 1)`. -/
theorem g2SpecialIsogeny_pow_odd_exponent_at_lengthPerm_of_not_isLongSimpleRoot (m : ℕ)
    {i : Fin 2} (hi : ¬ G2.IsLongSimpleRoot i) :
    (g2SpecialIsogeny ^ (2 * m + 1)).exponent
        (Fin.castLE (by omega) (lengthPermRankTwo i)) = 3 ^ (m + 1) := by
  have hlong : G2.IsLongSimpleRoot (lengthPermRankTwo i) := by simpa using hi
  rw [g2SpecialIsogeny_pow_odd_exponent,
    (isLongSimpleRoot_iff_g2Length_eq_three (lengthPermRankTwo i)).mp hlong, pow_succ]
  ring

/-- **The two root-datum exponents of a power of the special isogeny of `G₂`, at a root and at its
image, multiply to `3 ^ k`.** -/
theorem g2SpecialIsogeny_pow_exponent_mul_exponent (k : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ k).exponent i *
        (g2SpecialIsogeny ^ k).exponent ((g2SpecialIsogeny ^ k).indexEquiv i) = 3 ^ k := by
  rw [pow_exponent_mul_exponent_indexEquiv_of_mul_self_eq_smulId
    g2SpecialIsogeny_mul_self]
  norm_num

/-! ## Odd powers of the special isogeny of `F₄` -/

/-- **The even powers of the special isogeny of `F₄` are Frobenius scalings.** -/
theorem f4SpecialIsogeny_pow_two_mul (m : ℕ) :
    f4SpecialIsogeny ^ (2 * m) = smulId f4SimplyConnectedRootDatum (2 ^ m) :=
  pow_two_mul_of_mul_self f4SpecialIsogeny_mul_self m

/-- **Every power of the special isogeny of `F₄` squares to a Frobenius scaling.** At
`k = 2 * m + 1` this is the root-datum form of `steinberg(m) ^ 2 = Frob_(2 ^ (2m+1))`, the relation
whose group-scheme counterpart cuts out the Ree groups `²F₄(2 ^ (2m+1))`. Nothing about a group is
proved here. -/
theorem f4SpecialIsogeny_pow_mul_pow (k : ℕ) :
    f4SpecialIsogeny ^ k * f4SpecialIsogeny ^ k =
      smulId f4SimplyConnectedRootDatum (2 ^ k) :=
  pow_mul_pow_of_mul_self f4SpecialIsogeny_mul_self k

/-- An odd power of the special isogeny of `F₄` permutes the forty-eight roots exactly as the
isogeny itself does.

This is deliberately not `@[simp]`: `TauCeti.RootPairingIsogeny.pow_indexEquiv` already pushes the
power inside, so the left-hand side is not in simp normal form. -/
theorem f4SpecialIsogeny_pow_odd_indexEquiv_apply (m : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ (2 * m + 1)).indexEquiv i = f4SpecialIsogenyIndex i := by
  rw [pow_odd_indexEquiv_of_mul_self_eq_smulId f4SpecialIsogeny_mul_self,
    f4SpecialIsogeny_indexEquiv_apply]

/-- **The root-datum exponent of an odd power of the special isogeny of `F₄`** is the squared
length of the source root, times `2 ^ m`. -/
@[simp] theorem f4SpecialIsogeny_pow_odd_exponent (m : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ (2 * m + 1)).exponent i = f4Length i * 2 ^ m := by
  rw [pow_odd_exponent_of_mul_self_eq_smulId f4SpecialIsogeny_mul_self,
    f4SpecialIsogeny_exponent]
  norm_num

/-- **The defining relation of an odd power of the special isogeny of `F₄` on the roots.** The
displayed coefficient is the root-datum exponent at the source index `i`. -/
theorem f4SpecialIsogeny_pow_odd_weightMap_root (m : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ (2 * m + 1)).weightMap (f4SimplyConnectedRootDatum.root i) =
      (f4Length i * 2 ^ m) • f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndex i) := by
  rw [root_weightMap_pow_odd_of_mul_self_eq_smulId f4SpecialIsogeny_mul_self,
    f4SpecialIsogeny_exponent, f4SpecialIsogeny_indexEquiv_apply]
  norm_num

/-- **The defining relation of an odd power of the special isogeny of `F₄` on the coroots.** -/
theorem f4SpecialIsogeny_pow_odd_coroot_coweightMap (m : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ (2 * m + 1)).coweightMap
        (f4SimplyConnectedRootDatum.coroot (f4SpecialIsogenyIndex i)) =
      (f4Length i * 2 ^ m) • f4SimplyConnectedRootDatum.coroot i := by
  rw [← f4SpecialIsogeny_indexEquiv_apply]
  rw [coroot_coweightMap_pow_odd_of_mul_self_eq_smulId f4SpecialIsogeny_mul_self,
    f4SpecialIsogeny_exponent]
  norm_num

/-- At the source index length-exchanged from a long simple node of `F₄`, the root-datum exponent
of the `(2m+1)`-st power is `2 ^ m`. -/
theorem f4SpecialIsogeny_pow_odd_exponent_at_lengthPerm_of_isLongSimpleRoot (m : ℕ) {i : Fin 4}
    (hi : F4.IsLongSimpleRoot i) :
    (f4SpecialIsogeny ^ (2 * m + 1)).exponent (Fin.castAdd 44 (lengthPermF4 i)) = 2 ^ m := by
  have hshort : ¬ F4.IsLongSimpleRoot (lengthPermF4 i) := by simpa using hi
  rw [f4SpecialIsogeny_pow_odd_exponent,
    (f4Length_castAdd_eq_one_iff (lengthPermF4 i)).mpr hshort, one_mul]

/-- At the source index length-exchanged from a short simple node of `F₄`, the root-datum exponent
of the `(2m+1)`-st power is `2 ^ (m + 1)`. -/
theorem f4SpecialIsogeny_pow_odd_exponent_at_lengthPerm_of_not_isLongSimpleRoot (m : ℕ)
    {i : Fin 4} (hi : ¬ F4.IsLongSimpleRoot i) :
    (f4SpecialIsogeny ^ (2 * m + 1)).exponent
        (Fin.castAdd 44 (lengthPermF4 i)) = 2 ^ (m + 1) := by
  have hlong : F4.IsLongSimpleRoot (lengthPermF4 i) := by simpa using hi
  rw [f4SpecialIsogeny_pow_odd_exponent,
    (isLongSimpleRoot_iff_f4Length_eq_two (lengthPermF4 i)).mp hlong, pow_succ]
  ring

/-- **The two root-datum exponents of a power of the special isogeny of `F₄`, at a root and at its
image, multiply to `2 ^ k`.** -/
theorem f4SpecialIsogeny_pow_exponent_mul_exponent (k : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ k).exponent i *
        (f4SpecialIsogeny ^ k).exponent ((f4SpecialIsogeny ^ k).indexEquiv i) = 2 ^ k := by
  rw [pow_exponent_mul_exponent_indexEquiv_of_mul_self_eq_smulId
    f4SpecialIsogeny_mul_self]
  norm_num

end DynkinType

end TauCeti
