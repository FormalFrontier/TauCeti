/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Special

/-!
# Powers of an isogeny of a root pairing with itself

An isogeny of a root pairing with itself can be composed with itself, and the Suzuki and Ree
groups are cut out by the *odd powers* of a special isogeny rather than by the isogeny itself.
This file gives the isogenies of a fixed root pairing with itself their monoid structure under
composition, so that `f ^ n` is available with the whole `Monoid` API, and computes the square of
a power of a special isogeny.

The monoid is the one composition already determines: `TauCeti.RootPairingIsogeny.comp` is
associative with `TauCeti.RootPairingIsogeny.id` as a two-sided unit, and nothing new is proved to
put it together. What the monoid buys is the identity

```text
f ^ n * f ^ n = smulId P (c ^ n)      whenever      f * f = smulId P c,
```

`TauCeti.RootPairingIsogeny.pow_mul_self_eq_smulId`, which is pure monoid algebra: `f ^ n * f ^ n`
is `(f * f) ^ n`. Read at `c` the defining characteristic and `n` odd, this is the root-datum form
of `steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1))` for `steinberg (m) = τ ^ (2 * m + 1)`. It is stated
for every `n`, since the restriction to odd exponents belongs to the finite-group construction and
not to this identity.

The weight map and the index bijection are monoid homomorphisms out of this monoid; the coweight
map is an anti-homomorphism, since `comp` reverses on that component, and is therefore left as the
existing `TauCeti.RootPairingIsogeny.comp_coweightMap`.

The same hypothesis also splits the powers themselves: an even power is a scaling, and an odd power
is a scaling times `f`, so an odd power permutes the roots exactly as `f` does while multiplying
its exponents and its weight map by `c ^ m`. The three special isogenies of `B₂`, `G₂` and `F₄` are
the instance the file exists for, and their power relations close it.

## Main definitions

* `TauCeti.RootPairingIsogeny.instMonoid`: the composition monoid of isogenies of a root pairing
  with itself.
* `TauCeti.RootPairingIsogeny.weightMapHom` and `TauCeti.RootPairingIsogeny.indexEquivHom`: the
  weight map and the index bijection as monoid homomorphisms.
* `TauCeti.RootPairingIsogeny.smulIdHom`: the scalings, as a monoid homomorphism out of `ℕ+`.

## Main results

* `TauCeti.RootPairingIsogeny.pow_mul_self_eq_smulId`: a power of an isogeny whose square is a
  scaling squares to the corresponding power of that scaling.
* `TauCeti.RootPairingIsogeny.pow_two_mul_eq_smulId` and
  `TauCeti.RootPairingIsogeny.pow_two_mul_add_one_eq_smulId_mul`: such an isogeny has scalings for
  its even powers, and a scaling times itself for its odd ones.
* `TauCeti.RootPairingIsogeny.pow_two_mul_add_one_indexEquiv`,
  `TauCeti.RootPairingIsogeny.pow_two_mul_add_one_exponent` and
  `TauCeti.RootPairingIsogeny.pow_two_mul_add_one_weightMap`: an odd power permutes the roots as
  the isogeny does and multiplies its exponents and weight map by `c ^ m`.
* `TauCeti.DynkinType.b2SpecialIsogeny_pow_mul_self`, and its `G₂` and `F₄` counterparts: the
  powers of the three special isogenies square to the powers of the defining characteristic.

## References

* Schémas en groupes (SGA 3), Exposé XXI, 6.8.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.

The odd powers of the special isogeny are what milestone L2 of
`TauCetiRoadmap/CFSGStatement/README.md` asks for, "`steinberg(m) = τ_X ^ (2m + 1)`,
`steinberg(m) ^ 2 = Frob_(p ^ (2m + 1))`", once the special isogeny itself has been lifted from
root data to the pinned group schemes of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

namespace TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}

namespace RootPairingIsogeny

/-! ## The composition monoid -/

/-- **The isogenies of a root pairing with itself form a monoid** under composition, with the
identity isogeny as unit. Multiplication is composition in the same order as
`TauCeti.RootPairingIsogeny.comp`, so `f * g` applies `g` first. -/
instance : Monoid (RootPairingIsogeny P P) where
  one := id P
  mul f g := comp f g
  mul_assoc := comp_assoc
  one_mul := comp_id
  mul_one := id_comp

theorem mul_def (f g : RootPairingIsogeny P P) : f * g = comp f g := (rfl)

theorem one_def : (1 : RootPairingIsogeny P P) = id P := (rfl)

@[simp] theorem mul_weightMap (f g : RootPairingIsogeny P P) :
    (f * g).weightMap = f.weightMap ∘ₗ g.weightMap := comp_weightMap f g

@[simp] theorem mul_coweightMap (f g : RootPairingIsogeny P P) :
    (f * g).coweightMap = g.coweightMap ∘ₗ f.coweightMap := comp_coweightMap f g

@[simp] theorem mul_indexEquiv (f g : RootPairingIsogeny P P) :
    (f * g).indexEquiv = g.indexEquiv.trans f.indexEquiv := comp_indexEquiv f g

@[simp] theorem mul_exponent (f g : RootPairingIsogeny P P) (i : ι) :
    (f * g).exponent i = g.exponent i * f.exponent (g.indexEquiv i) := comp_exponent f g i

@[simp] theorem one_weightMap : (1 : RootPairingIsogeny P P).weightMap = LinearMap.id :=
  id_weightMap P

@[simp] theorem one_coweightMap : (1 : RootPairingIsogeny P P).coweightMap = LinearMap.id :=
  id_coweightMap P

@[simp] theorem one_indexEquiv : (1 : RootPairingIsogeny P P).indexEquiv = Equiv.refl ι :=
  id_indexEquiv P

@[simp] theorem one_exponent (i : ι) : (1 : RootPairingIsogeny P P).exponent i = 1 :=
  id_exponent P i

/-! ## The two multiplicative components -/

/-- **The weight map of an isogeny, as a monoid homomorphism** into the endomorphism monoid of the
weight space. -/
def weightMapHom (P : RootPairing ι R M N) : RootPairingIsogeny P P →* Module.End R M where
  toFun f := f.weightMap
  map_one' := one_weightMap
  map_mul' := mul_weightMap

@[simp] theorem weightMapHom_apply (f : RootPairingIsogeny P P) :
    weightMapHom P f = f.weightMap := (rfl)

/-- The weight map of a power of an isogeny is the corresponding power of its weight map. -/
@[simp] theorem pow_weightMap (f : RootPairingIsogeny P P) (n : ℕ) :
    (f ^ n).weightMap = f.weightMap ^ n :=
  map_pow (weightMapHom P) f n

/-- **The index bijection of an isogeny, as a monoid homomorphism** into the permutation group of
the index set. -/
def indexEquivHom (P : RootPairing ι R M N) : RootPairingIsogeny P P →* Equiv.Perm ι where
  toFun f := f.indexEquiv
  map_one' := one_indexEquiv
  map_mul' := mul_indexEquiv

@[simp] theorem indexEquivHom_apply (f : RootPairingIsogeny P P) :
    indexEquivHom P f = f.indexEquiv := (rfl)

/-- The index bijection of a power of an isogeny is the corresponding power of its index
bijection. -/
@[simp] theorem pow_indexEquiv (f : RootPairingIsogeny P P) (n : ℕ) :
    (f ^ n).indexEquiv = f.indexEquiv ^ n :=
  map_pow (indexEquivHom P) f n

/-- The exponent of a power of an isogeny, in terms of the exponents of the lower power. -/
theorem pow_succ_exponent (f : RootPairingIsogeny P P) (n : ℕ) (i : ι) :
    (f ^ (n + 1)).exponent i = f.exponent i * (f ^ n).exponent (f.indexEquiv i) := by
  rw [pow_succ, mul_exponent]

/-! ## The scalings -/

section Scaling

variable [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
  (P : RootPairing ι ℤ M N)

@[simp] theorem smulId_one : smulId P 1 = 1 := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_ <;> ext <;> simp

@[simp] theorem smulId_mul_smulId (c d : ℕ+) : smulId P c * smulId P d = smulId P (c * d) := by
  refine RootPairingIsogeny.ext ?_ ?_ ?_ ?_ <;> ext <;> simp [← mul_smul, mul_comm]

/-- **The scalings of a root pairing, as a monoid homomorphism** out of the positive integers. At a
prime this picks out the root-datum shadow of the Frobenius isogeny. -/
def smulIdHom : ℕ+ →* RootPairingIsogeny P P where
  toFun c := smulId P c
  map_one' := smulId_one P
  map_mul' c d := (smulId_mul_smulId P c d).symm

@[simp] theorem smulIdHom_apply (c : ℕ+) : smulIdHom P c = smulId P c := (rfl)

/-- A power of a scaling is the scaling by the corresponding power. -/
@[simp] theorem smulId_pow (c : ℕ+) (n : ℕ) : smulId P c ^ n = smulId P (c ^ n) :=
  (map_pow (smulIdHom P) c n).symm

variable {f : RootPairingIsogeny P P} {c : ℕ+}

/-- **An even power of an isogeny whose square is a scaling is itself a scaling.** -/
theorem pow_two_mul_eq_smulId (h : f * f = smulId P c) (m : ℕ) :
    f ^ (2 * m) = smulId P (c ^ m) := by
  rw [pow_mul, pow_two, h, smulId_pow]

/-- **A power of an isogeny whose square is a scaling squares to the corresponding power of that
scaling.** For `c` the defining characteristic and `n = 2 * m + 1`, this is the root-datum form of
the relation `steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1))` satisfied by the odd powers of a special
isogeny; the identity itself holds at every exponent. -/
theorem pow_mul_self_eq_smulId (h : f * f = smulId P c) (n : ℕ) :
    f ^ n * f ^ n = smulId P (c ^ n) := by
  rw [← pow_add, ← two_mul, pow_two_mul_eq_smulId P h]

/-- **An odd power of an isogeny whose square is a scaling is a scaling times the isogeny.** This
is what makes the odd powers genuinely new maps rather than scalings: the factor `f` survives. -/
theorem pow_two_mul_add_one_eq_smulId_mul (h : f * f = smulId P c) (m : ℕ) :
    f ^ (2 * m + 1) = smulId P (c ^ m) * f := by
  rw [pow_succ, pow_two_mul_eq_smulId P h]

/-- **An odd power of an isogeny whose square is a scaling permutes the roots exactly as the
isogeny does**, since a scaling fixes every index. -/
theorem pow_two_mul_add_one_indexEquiv (h : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).indexEquiv = f.indexEquiv := by
  rw [pow_two_mul_add_one_eq_smulId_mul P h, mul_indexEquiv, smulId_indexEquiv, Equiv.trans_refl]

/-- **The rescaling exponents of an odd power** are those of the isogeny times `c ^ m`.

Read at a special isogeny in characteristic `p`, so at `c = p`: the `exponent` field is indexed by
the source of the character map, and is `1` at a short simple root and `p` at a long one
(`TauCeti.DynkinType.b2SpecialIsogeny_exponent_typeBSimpleIndex_eq_one_iff`), so the odd power has
exponent `p ^ m` at a short simple root and `p ^ (m + 1)` at a long one. -/
theorem pow_two_mul_add_one_exponent (h : f * f = smulId P c) (m : ℕ) (i : ι) :
    (f ^ (2 * m + 1)).exponent i = f.exponent i * (c : ℤ) ^ m := by
  rw [pow_two_mul_add_one_eq_smulId_mul P h, mul_exponent, smulId_exponent]
  push_cast [PNat.pow_coe]
  ring

/-- **The weight map of an odd power** is `c ^ m` times that of the isogeny. -/
theorem pow_two_mul_add_one_weightMap (h : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).weightMap = ((c : ℕ) ^ m) • f.weightMap := by
  rw [pow_two_mul_add_one_eq_smulId_mul P h, mul_weightMap, smulId_weightMap]
  ext x
  simp [PNat.pow_coe]

end Scaling

end RootPairingIsogeny

/-! ## The three special isogenies -/

namespace DynkinType

open RootPairingIsogeny

/-- **The powers of the special isogeny of `B₂` square to the powers of two.** At `n = 2 * m + 1`
this is the root-datum form of the square relation satisfied by the Steinberg endomorphism whose
fixed points are the Suzuki group `²B₂(2 ^ (2 * m + 1))`. -/
theorem b2SpecialIsogeny_pow_mul_self (n : ℕ) :
    b2SpecialIsogeny ^ n * b2SpecialIsogeny ^ n =
      smulId (typeBSimplyConnectedRootDatum 2) (2 ^ n) :=
  pow_mul_self_eq_smulId _ b2SpecialIsogeny_comp_self n

/-- **The powers of the special isogeny of `G₂` square to the powers of three.** At `n = 2 * m + 1`
this is the root-datum form of the square relation satisfied by the Steinberg endomorphism whose
fixed points are the Ree group `²G₂(3 ^ (2 * m + 1))`. -/
theorem g2SpecialIsogeny_pow_mul_self (n : ℕ) :
    g2SpecialIsogeny ^ n * g2SpecialIsogeny ^ n = smulId g2SimplyConnectedRootDatum (3 ^ n) :=
  pow_mul_self_eq_smulId _ g2SpecialIsogeny_comp_self n

/-- **The powers of the special isogeny of `F₄` square to the powers of two.** At `n = 2 * m + 1`
this is the root-datum form of the square relation satisfied by the Steinberg endomorphism whose
fixed points are the Ree group `²F₄(2 ^ (2 * m + 1))`; at `n = 1` it belongs to the Tits group. -/
theorem f4SpecialIsogeny_pow_mul_self (n : ℕ) :
    f4SpecialIsogeny ^ n * f4SpecialIsogeny ^ n = smulId f4SimplyConnectedRootDatum (2 ^ n) :=
  pow_mul_self_eq_smulId _ f4SpecialIsogeny_comp_self n

end DynkinType

end TauCeti
