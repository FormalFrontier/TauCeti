/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special

/-!
# Iterates of an isogeny, and the odd powers of a special isogeny

Composition makes the isogenies of a root pairing with itself a monoid, with the identity isogeny
as its unit, so an isogeny `f : RootPairingIsogeny P P` has iterates `f ^ k`. This file installs
that monoid, describes each of the four fields of `f ^ k`, and applies the result to the special
isogenies of the pinned `G₂` and `F₄` root data.

## Iterating an isogeny

The four fields behave in the four different ways one would expect. The character-lattice map is
multiplicative, `(f ^ k).weightMap = f.weightMap ^ k`; the cocharacter map is *anti*multiplicative
in a composite, but since a power commutes with itself it too satisfies
`(f ^ k).coweightMap = f.coweightMap ^ k`; the index bijection is multiplicative as a permutation,
`(f ^ k).indexEquiv = f.indexEquiv ^ k`; and the exponent, which is not a homomorphism of any kind,
accumulates along the forward orbit of the index bijection,

```text
(f ^ k).exponent i = ∏ j < k, f.exponent (f.indexEquiv ^ j i).
```

## Square roots of a scaling

The isogeny `TauCeti.RootPairingIsogeny.smulId P c` scales the character and cocharacter lattices
by a positive integer `c`, fixes every index, and has constant exponent `c`; at a prime `c = p` it
is the root-datum shadow of the `p`-power Frobenius isogeny. An isogeny `f` with
`f * f = smulId P c` is thus a square root of that scaling, and the special isogenies of `F₄` in
characteristic two and of `G₂` in characteristic three, which
`TauCeti/LinearAlgebra/RootSystem/Isogeny/Special.lean` constructs, are the examples this file
powers. For such an `f` the even powers collapse completely,

```text
f ^ (2 * m) = smulId P (c ^ m),
```

so an odd power `f ^ (2 * m + 1)` is that scaling composed with `f` itself: it acts on indices by
`f.indexEquiv` again, and its exponent at an index is `f.exponent i * c ^ m`. Squaring an odd power
returns a scaling, `f ^ k * f ^ k = smulId P (c ^ k)`, which at `k = 2 * m + 1` is the root-datum
form of the relation `τ ^ (2m+1)` squares to `Frob_{p ^ (2m+1)}` that cuts out the Suzuki and Ree
groups over the field with `p ^ (2m+1)` elements.

The two exponents at a length-exchanged pair of indices multiply to `c ^ k`. An even power has the
constant exponent `c ^ m`, so it is only in an odd power that this splits the field-order Frobenius
into two genuinely different exponents: at a simple node the exponent is `p ^ m` or `p ^ (m + 1)`
according to whether the node is short or long, and the two multiply to `p ^ (2m+1)`. That is the
splitting the Suzuki and Ree root subgroup parameters exhibit.

## Main definitions

* the `Monoid` instance on `TauCeti.RootPairingIsogeny P P`, whose multiplication is
  `TauCeti.RootPairingIsogeny.comp` and whose unit is `TauCeti.RootPairingIsogeny.id`.

## Main results

* `TauCeti.RootPairingIsogeny.pow_weightMap`, `pow_coweightMap`, `pow_indexEquiv` and
  `pow_exponent`: the four fields of an iterate.
* `TauCeti.RootPairingIsogeny.pow_two_mul_of_mul_self`: an isogeny squaring to a scaling has
  scalar even powers.
* `TauCeti.RootPairingIsogeny.pow_mul_pow_of_mul_self`: every power of such an isogeny again
  squares to a scaling.
* `TauCeti.RootPairingIsogeny.exponent_pow_odd_of_mul_self` and
  `indexEquiv_pow_odd_of_mul_self`: the exponent and the index action of an odd power.
* `TauCeti.DynkinType.g2SpecialIsogeny_pow_mul_pow` and its `F₄` counterpart: the square relation
  for every power of the special isogeny.
* `TauCeti.DynkinType.g2SpecialIsogeny_pow_odd_exponent_castLE_of_isLongSimpleRoot` and its three
  companions: the exponent of an odd power at a simple node, read off
  `TauCeti.DynkinType.G2.IsLongSimpleRoot` and its `F₄` counterpart.

## Roadmap and references

The odd power `τ ^ (2m+1)` of a special isogeny is the Steinberg map of milestone L2 of
`TauCetiRoadmap/CFSGStatement/README.md`, which sets `steinberg(m) = τ_X ^ (2m + 1)` with
`steinberg(m) ^ 2 = Frob_(p ^ (2m + 1))` and pins the exponent convention against
`TauCeti.DynkinType.IsLongSimpleRoot`. This file supplies that milestone's root-datum layer: the
odd powers themselves, their square relation, and their exponents at the numbered simple nodes.
The special isogenies it powers are the target "Special isogenies in characteristics two and
three" of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, at the level of root data.

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* Schémas en groupes (SGA 3), Exposé XXI, 6.8, and Exposé XXII.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3--12.4.
-/

public section

namespace TauCeti

namespace RootPairingIsogeny

section Iterate

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

/-- Composition of isogenies of a root pairing with itself, with the identity isogeny as unit.
Multiplication is `TauCeti.RootPairingIsogeny.comp`, in the same order as for endomorphisms of a
module: `f * g` applies `g` first. -/
instance : Monoid (RootPairingIsogeny P P) where
  mul := comp
  one := id P
  mul_assoc := comp_assoc
  one_mul := comp_id
  mul_one := id_comp

/-- The product in the monoid of self-isogenies is composition. -/
theorem mul_def (f g : RootPairingIsogeny P P) : f * g = comp f g := rfl

/-- The unit of the monoid of self-isogenies is the identity isogeny. -/
theorem one_def : (1 : RootPairingIsogeny P P) = id P := rfl

/-- The character-lattice map of a product is the composite of the two character-lattice maps. -/
@[simp] theorem mul_weightMap (f g : RootPairingIsogeny P P) :
    (f * g).weightMap = f.weightMap ∘ₗ g.weightMap := by
  rw [mul_def, comp_weightMap]

/-- The cocharacter map of a composite is the composite in the opposite order: an isogeny is
contravariant on coweight space. -/
@[simp] theorem mul_coweightMap (f g : RootPairingIsogeny P P) :
    (f * g).coweightMap = g.coweightMap ∘ₗ f.coweightMap := by
  rw [mul_def, comp_coweightMap]

/-- The index bijection of a product is the product of the two index bijections, as
permutations. -/
@[simp] theorem mul_indexEquiv (f g : RootPairingIsogeny P P) :
    (f * g).indexEquiv = f.indexEquiv * g.indexEquiv := by
  rw [mul_def, comp_indexEquiv, Equiv.Perm.mul_def]

/-- The exponent of a product at an index is the exponent of the first factor applied there,
times the exponent of the second factor at the image of that index. -/
@[simp] theorem mul_exponent (f g : RootPairingIsogeny P P) (i : ι) :
    (f * g).exponent i = g.exponent i * f.exponent (g.indexEquiv i) := by
  rw [mul_def, comp_exponent]

/-- The identity isogeny is the identity on the character lattice. -/
@[simp] theorem one_weightMap : (1 : RootPairingIsogeny P P).weightMap = LinearMap.id := by
  rw [one_def, id_weightMap]

/-- The identity isogeny is the identity on the cocharacter lattice. -/
@[simp] theorem one_coweightMap : (1 : RootPairingIsogeny P P).coweightMap = LinearMap.id := by
  rw [one_def, id_coweightMap]

/-- The identity isogeny fixes every index. -/
@[simp] theorem one_indexEquiv : (1 : RootPairingIsogeny P P).indexEquiv = Equiv.refl ι := by
  rw [one_def, id_indexEquiv]

/-- The identity isogeny rescales no root. -/
@[simp] theorem one_exponent (i : ι) : (1 : RootPairingIsogeny P P).exponent i = 1 := by
  rw [one_def, id_exponent]

/-- The character-lattice map of an iterate is the iterate of the character-lattice map. -/
@[simp] theorem pow_weightMap (f : RootPairingIsogeny P P) (k : ℕ) :
    (f ^ k).weightMap = f.weightMap ^ k := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => rw [pow_succ, mul_weightMap, ih, pow_succ, Module.End.mul_eq_comp]

/-- The cocharacter map of an iterate is the iterate of the cocharacter map. Composition reverses
the order, but a power of an endomorphism commutes with itself, so no reversal is visible. -/
@[simp] theorem pow_coweightMap (f : RootPairingIsogeny P P) (k : ℕ) :
    (f ^ k).coweightMap = f.coweightMap ^ k := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => rw [pow_succ, mul_coweightMap, ih, pow_succ', Module.End.mul_eq_comp]

/-- The index bijection of an iterate is the iterate of the index bijection. -/
@[simp] theorem pow_indexEquiv (f : RootPairingIsogeny P P) (k : ℕ) :
    (f ^ k).indexEquiv = f.indexEquiv ^ k := by
  induction k with
  | zero => simp [Equiv.Perm.one_def]
  | succ k ih => rw [pow_succ, mul_indexEquiv, ih, pow_succ]

/-- **The exponent of an iterate accumulates along the forward orbit of the index bijection.**
Unlike the other three fields the exponent is not multiplicative: the exponent of a composite at
an index is the product of the exponents met at the successive images of that index. -/
theorem pow_exponent (f : RootPairingIsogeny P P) (k : ℕ) (i : ι) :
    (f ^ k).exponent i = ∏ j ∈ Finset.range k, f.exponent ((f.indexEquiv ^ j) i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_exponent, ih, pow_indexEquiv, Finset.prod_range_succ]

end Iterate

section Scaling

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
  {P : RootPairing ι ℤ M N}

/-- Scaling by one is the identity isogeny. -/
@[simp] theorem smulId_one : smulId P 1 = 1 := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_ <;> ext <;> simp

/-- The scalings form a submonoid, isomorphic to the positive integers under multiplication. -/
@[simp] theorem smulId_mul (c d : ℕ+) : smulId P c * smulId P d = smulId P (c * d) := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_
  · ext x
    simp [mul_smul]
  · ext x
    rw [mul_comm c d]
    simp [mul_smul]
  · ext i
    simp
  · funext i
    simp only [mul_exponent, smulId_exponent, smulId_indexEquiv]
    push_cast
    ring

/-- Iterating a scaling raises the scalar to the corresponding power. -/
@[simp] theorem smulId_pow (c : ℕ+) (k : ℕ) : smulId P c ^ k = smulId P (c ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, smulId_mul, pow_succ]

variable {f : RootPairingIsogeny P P} {c : ℕ+}

/-- **An isogeny that squares to a scaling has scalar even powers.** The special isogenies in
characteristics two and three are square roots of the Frobenius scaling in this sense, and this is
what makes an odd power of one of them differ from a Frobenius by a single further application. -/
theorem pow_two_mul_of_mul_self (hf : f * f = smulId P c) (m : ℕ) :
    f ^ (2 * m) = smulId P (c ^ m) := by
  rw [pow_mul, pow_two, hf, smulId_pow]

/-- **Every power of an isogeny that squares to a scaling again squares to a scaling.** At
`k = 2 * m + 1` and `c` a prime `p` this is the root-datum form of the relation
`steinberg(m) ^ 2 = Frob_(p ^ (2m+1))` that defines the Suzuki and Ree parameters. -/
theorem pow_mul_pow_of_mul_self (hf : f * f = smulId P c) (k : ℕ) :
    f ^ k * f ^ k = smulId P (c ^ k) := by
  rw [← pow_add, ← two_mul, pow_two_mul_of_mul_self hf]

/-- An odd power of an isogeny that squares to a scaling acts on indices exactly as the isogeny
itself does. -/
theorem indexEquiv_pow_odd_of_mul_self (hf : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).indexEquiv = f.indexEquiv := by
  rw [pow_succ, mul_indexEquiv, pow_two_mul_of_mul_self hf, smulId_indexEquiv,
    ← Equiv.Perm.one_def, one_mul]

/-- **The exponent of an odd power of an isogeny that squares to scaling by `c`.** It is the
exponent of the isogeny itself, multiplied by `c ^ m`. -/
theorem exponent_pow_odd_of_mul_self (hf : f * f = smulId P c) (m : ℕ) (i : ι) :
    (f ^ (2 * m + 1)).exponent i = f.exponent i * (c : ℤ) ^ m := by
  rw [pow_succ, mul_exponent, pow_two_mul_of_mul_self hf, smulId_exponent]
  push_cast
  ring

/-- The character-lattice map of an odd power is that of the isogeny itself, scaled by `c ^ m`. -/
theorem weightMap_pow_odd_of_mul_self (hf : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).weightMap = ((c : ℕ) ^ m) • f.weightMap := by
  rw [pow_succ, mul_weightMap, pow_two_mul_of_mul_self hf, smulId_weightMap,
    LinearMap.smul_comp, LinearMap.id_comp, PNat.pow_coe]

/-- **The two exponents of a power at an index and at its image multiply to `c ^ k`.** For a
special isogeny in characteristic `p` and `k = 2 * m + 1` this is the statement that the two
exponents attached to a length-exchanged pair of simple nodes multiply to the order
`p ^ (2m+1)` of the field of definition. -/
theorem exponent_mul_exponent_indexEquiv_pow_of_mul_self (hf : f * f = smulId P c) (k : ℕ)
    (i : ι) :
    (f ^ k).exponent i * (f ^ k).exponent ((f ^ k).indexEquiv i) = (c : ℤ) ^ k := by
  have h := congrArg (fun g : RootPairingIsogeny P P => g.exponent i) (pow_mul_pow_of_mul_self hf k)
  simpa using h

end Scaling

end RootPairingIsogeny

namespace DynkinType

open RootPairingIsogeny

/-! ## Odd powers of the special isogeny of `G₂` -/

/-- The special isogeny of `G₂` squares to scaling by three, restated in the multiplicative
notation of the monoid of self-isogenies. This is the form the generic power lemmas above consume;
`TauCeti.RootPairingIsogeny.mul_def` is what makes it the same statement as
`TauCeti.DynkinType.g2SpecialIsogeny_comp_self`. -/
theorem g2SpecialIsogeny_mul_self :
    g2SpecialIsogeny * g2SpecialIsogeny = smulId g2SimplyConnectedRootDatum 3 :=
  g2SpecialIsogeny_comp_self

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
  rw [indexEquiv_pow_odd_of_mul_self g2SpecialIsogeny_mul_self, g2SpecialIsogeny_indexEquiv_apply]

/-- **The exponent of an odd power of the special isogeny of `G₂`** is the squared length of the
root, times `3 ^ m`. -/
@[simp] theorem g2SpecialIsogeny_pow_odd_exponent (m : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ (2 * m + 1)).exponent i = g2Length i * 3 ^ m := by
  rw [exponent_pow_odd_of_mul_self g2SpecialIsogeny_mul_self, g2SpecialIsogeny_exponent]
  norm_num

/-- **The defining relation of an odd power of the special isogeny of `G₂` on the roots.** This is
the root-datum form of `τ ^ (2m+1) (x_α (t)) = x_{σ(α)} (t ^ q)` with `q` the displayed
exponent. -/
theorem g2SpecialIsogeny_pow_odd_weightMap_root (m : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ (2 * m + 1)).weightMap (g2SimplyConnectedRootDatum.root i) =
      (g2Length i * 3 ^ m) • g2SimplyConnectedRootDatum.root (g2SpecialIsogenyIndex i) := by
  rw [(g2SpecialIsogeny ^ (2 * m + 1)).root_weightMap, g2SpecialIsogeny_pow_odd_exponent,
    g2SpecialIsogeny_pow_odd_indexEquiv_apply]
  simp only [Int.cast_id]

/-- At a long simple node of `G₂` the exponent of the `(2m+1)`-st power of the special isogeny is
`3 ^ (m + 1)`. -/
theorem g2SpecialIsogeny_pow_odd_exponent_castLE_of_isLongSimpleRoot (m : ℕ) {i : Fin 2}
    (hi : G2.IsLongSimpleRoot i) :
    (g2SpecialIsogeny ^ (2 * m + 1)).exponent (Fin.castLE (by omega) i) = 3 ^ (m + 1) := by
  rw [g2SpecialIsogeny_pow_odd_exponent, (isLongSimpleRoot_iff_g2Length_eq_three i).mp hi,
    pow_succ]
  ring

/-- At a short simple node of `G₂` the exponent of the `(2m+1)`-st power of the special isogeny is
`3 ^ m`. -/
theorem g2SpecialIsogeny_pow_odd_exponent_castLE_of_not_isLongSimpleRoot (m : ℕ) {i : Fin 2}
    (hi : ¬ G2.IsLongSimpleRoot i) :
    (g2SpecialIsogeny ^ (2 * m + 1)).exponent (Fin.castLE (by omega) i) = 3 ^ m := by
  rw [g2SpecialIsogeny_pow_odd_exponent, (g2Length_castLE_eq_one_iff i).mpr hi, one_mul]

/-- **The two exponents of a power of the special isogeny of `G₂`, at a root and at its image,
multiply to `3 ^ k`.** At `k = 2 * m + 1` that is the order of the field of definition of
`²G₂(3 ^ (2m+1))`, split as `3 ^ m` at a short simple node and `3 ^ (m+1)` at the long one. -/
theorem g2SpecialIsogeny_pow_exponent_mul_exponent (k : ℕ) (i : Fin 12) :
    (g2SpecialIsogeny ^ k).exponent i *
        (g2SpecialIsogeny ^ k).exponent ((g2SpecialIsogeny ^ k).indexEquiv i) = 3 ^ k := by
  rw [exponent_mul_exponent_indexEquiv_pow_of_mul_self g2SpecialIsogeny_mul_self]
  norm_num

/-! ## Odd powers of the special isogeny of `F₄` -/

/-- The special isogeny of `F₄` squares to scaling by two, restated in the multiplicative notation
of the monoid of self-isogenies. This is the form the generic power lemmas above consume;
`TauCeti.RootPairingIsogeny.mul_def` is what makes it the same statement as
`TauCeti.DynkinType.f4SpecialIsogeny_comp_self`. -/
theorem f4SpecialIsogeny_mul_self :
    f4SpecialIsogeny * f4SpecialIsogeny = smulId f4SimplyConnectedRootDatum 2 :=
  f4SpecialIsogeny_comp_self

/-- **The even powers of the special isogeny of `F₄` are Frobenius scalings.** -/
theorem f4SpecialIsogeny_pow_two_mul (m : ℕ) :
    f4SpecialIsogeny ^ (2 * m) = smulId f4SimplyConnectedRootDatum (2 ^ m) :=
  pow_two_mul_of_mul_self f4SpecialIsogeny_mul_self m

/-- **Every power of the special isogeny of `F₄` squares to a Frobenius scaling.** At
`k = 2 * m + 1` this is the root-datum form of `steinberg(m) ^ 2 = Frob_(2 ^ (2m+1))`, the relation
whose group-scheme counterpart cuts out the Ree groups `²F₄(2 ^ (2m+1))` and, at `m = 0`, the group
whose derived subgroup is the Tits group. Nothing about a group is proved here. -/
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
  rw [indexEquiv_pow_odd_of_mul_self f4SpecialIsogeny_mul_self, f4SpecialIsogeny_indexEquiv_apply]

/-- **The exponent of an odd power of the special isogeny of `F₄`** is the squared length of the
root, times `2 ^ m`. -/
@[simp] theorem f4SpecialIsogeny_pow_odd_exponent (m : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ (2 * m + 1)).exponent i = f4Length i * 2 ^ m := by
  rw [exponent_pow_odd_of_mul_self f4SpecialIsogeny_mul_self, f4SpecialIsogeny_exponent]
  norm_num

/-- **The defining relation of an odd power of the special isogeny of `F₄` on the roots.** This is
the root-datum form of `τ ^ (2m+1) (x_α (t)) = x_{σ(α)} (t ^ q)` with `q` the displayed
exponent. -/
theorem f4SpecialIsogeny_pow_odd_weightMap_root (m : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ (2 * m + 1)).weightMap (f4SimplyConnectedRootDatum.root i) =
      (f4Length i * 2 ^ m) • f4SimplyConnectedRootDatum.root (f4SpecialIsogenyIndex i) := by
  rw [(f4SpecialIsogeny ^ (2 * m + 1)).root_weightMap, f4SpecialIsogeny_pow_odd_exponent,
    f4SpecialIsogeny_pow_odd_indexEquiv_apply]
  simp only [Int.cast_id]

/-- At a long simple node of `F₄` the exponent of the `(2m+1)`-st power of the special isogeny is
`2 ^ (m + 1)`. -/
theorem f4SpecialIsogeny_pow_odd_exponent_castAdd_of_isLongSimpleRoot (m : ℕ) {i : Fin 4}
    (hi : F4.IsLongSimpleRoot i) :
    (f4SpecialIsogeny ^ (2 * m + 1)).exponent (Fin.castAdd 44 i) = 2 ^ (m + 1) := by
  rw [f4SpecialIsogeny_pow_odd_exponent, (isLongSimpleRoot_iff_f4Length_eq_two i).mp hi, pow_succ]
  ring

/-- At a short simple node of `F₄` the exponent of the `(2m+1)`-st power of the special isogeny is
`2 ^ m`. -/
theorem f4SpecialIsogeny_pow_odd_exponent_castAdd_of_not_isLongSimpleRoot (m : ℕ) {i : Fin 4}
    (hi : ¬ F4.IsLongSimpleRoot i) :
    (f4SpecialIsogeny ^ (2 * m + 1)).exponent (Fin.castAdd 44 i) = 2 ^ m := by
  rw [f4SpecialIsogeny_pow_odd_exponent, (f4Length_castAdd_eq_one_iff i).mpr hi, one_mul]

/-- **The two exponents of a power of the special isogeny of `F₄`, at a root and at its image,
multiply to `2 ^ k`.** At `k = 2 * m + 1` that is the order of the field of definition of
`²F₄(2 ^ (2m+1))`, split as `2 ^ m` at a short simple node and `2 ^ (m+1)` at a long one. -/
theorem f4SpecialIsogeny_pow_exponent_mul_exponent (k : ℕ) (i : Fin 48) :
    (f4SpecialIsogeny ^ k).exponent i *
        (f4SpecialIsogeny ^ k).exponent ((f4SpecialIsogeny ^ k).indexEquiv i) = 2 ^ k := by
  rw [exponent_mul_exponent_indexEquiv_pow_of_mul_self f4SpecialIsogeny_mul_self]
  norm_num

end DynkinType

end TauCeti
