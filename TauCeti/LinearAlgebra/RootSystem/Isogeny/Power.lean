/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Isogeny.Basic

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

All three of the weight map, the coweight map and the index bijection are monoid homomorphisms out
of this monoid, the coweight map into the opposite endomorphism monoid because `comp` reverses on
that component. These declarations adapt the Mathlib API `RootPairing.Hom.weightHom`,
`RootPairing.Hom.coweightHom` and `RootPairing.Hom.indexHom` for the endomorphism monoid of a root
pairing, and the powers of all three components are `map_pow`.

Two further maps into the monoid are recorded because the Steinberg endomorphisms of the twisted
families are built from them: the automorphisms of the root pairing land in it multiplicatively,
`TauCeti.RootPairingIsogeny.ofEquivHom`, and the scalings are central in it,
`TauCeti.RootPairingIsogeny.commute_smulId`. Together they let a power of an automorphism times a
scaling be separated into a power of each.

The same hypothesis also splits the powers themselves: an even power is a scaling, and an odd power
is a scaling times `f`, so an odd power permutes the roots exactly as `f` does while multiplying
its exponents and its weight and coweight maps by `c ^ m`. The three special isogenies of `B₂`,
`G₂` and `F₄` are the instance this exists for; their power relations are in
`TauCeti/LinearAlgebra/RootSystem/Isogeny/Special.lean`, where they join the square relations they
come from.

## Main definitions

* `TauCeti.RootPairingIsogeny.instMonoid`: the composition monoid of isogenies of a root pairing
  with itself.
* `TauCeti.RootPairingIsogeny.weightHom`, `TauCeti.RootPairingIsogeny.coweightHom` and
  `TauCeti.RootPairingIsogeny.indexHom`: the weight map, the coweight map and the index bijection
  as monoid homomorphisms, the coweight map into the opposite endomorphism monoid.
* `TauCeti.RootPairingIsogeny.smulIdHom`: the scalings, as a monoid homomorphism out of `ℕ+`.
* `TauCeti.RootPairingIsogeny.ofEquivHom`: the automorphisms of the root pairing, as a monoid
  homomorphism into the isogeny monoid.

## Main results

* `TauCeti.RootPairingIsogeny.ofEquiv_pow`: an automorphism and the isogeny it becomes have the
  same powers.
* `TauCeti.RootPairingIsogeny.commute_smulId`: a scaling commutes with every endo-isogeny.
* `TauCeti.RootPairingIsogeny.pow_mul_self_eq_smulId`: a power of an isogeny whose square is a
  scaling squares to the corresponding power of that scaling.
* `TauCeti.RootPairingIsogeny.pow_two_mul_eq_smulId` and
  `TauCeti.RootPairingIsogeny.pow_two_mul_add_one_eq_smulId_mul`: such an isogeny has scalings for
  its even powers, and a scaling times itself for its odd ones.
* `TauCeti.RootPairingIsogeny.exponent_pow`: the exponent of an iterate is the product along the
  corresponding orbit of indices.
* `TauCeti.RootPairingIsogeny.indexEquiv_pow_two_mul_add_one`,
  `TauCeti.RootPairingIsogeny.exponent_pow_two_mul_add_one`,
  `TauCeti.RootPairingIsogeny.weightMap_pow_two_mul_add_one` and
  `TauCeti.RootPairingIsogeny.coweightMap_pow_two_mul_add_one`: an odd power permutes the roots as
  the isogeny does and multiplies its exponents and its two lattice maps by `c ^ m`.

## References

* Scott Carnahan, `Mathlib/LinearAlgebra/RootSystem/Hom.lean`, for the `RootPairing.Hom`
  endomorphism monoid API adapted here.
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

@[simp] theorem weightMap_mul (f g : RootPairingIsogeny P P) :
    (f * g).weightMap = f.weightMap ∘ₗ g.weightMap := comp_weightMap f g

@[simp] theorem coweightMap_mul (f g : RootPairingIsogeny P P) :
    (f * g).coweightMap = g.coweightMap ∘ₗ f.coweightMap := comp_coweightMap f g

@[simp] theorem indexEquiv_mul (f g : RootPairingIsogeny P P) :
    (f * g).indexEquiv = g.indexEquiv.trans f.indexEquiv := comp_indexEquiv f g

@[simp] theorem exponent_mul (f g : RootPairingIsogeny P P) (i : ι) :
    (f * g).exponent i = g.exponent i * f.exponent (g.indexEquiv i) := comp_exponent f g i

@[simp] theorem weightMap_one : (1 : RootPairingIsogeny P P).weightMap = LinearMap.id :=
  id_weightMap P

@[simp] theorem coweightMap_one : (1 : RootPairingIsogeny P P).coweightMap = LinearMap.id :=
  id_coweightMap P

@[simp] theorem indexEquiv_one : (1 : RootPairingIsogeny P P).indexEquiv = Equiv.refl ι :=
  id_indexEquiv P

@[simp] theorem exponent_one (i : ι) : (1 : RootPairingIsogeny P P).exponent i = 1 :=
  id_exponent P i

/-- **The automorphisms of a root pairing sit inside its monoid of endo-isogenies**, as a monoid
homomorphism: an automorphism is an isogeny with every exponent `1`, and composition agrees on the
two sides. -/
def ofEquivHom (P : RootPairing ι R M N) : RootPairing.Aut P →* RootPairingIsogeny P P where
  toFun := ofEquiv
  map_one' := by rw [one_def]; exact ofEquiv_one
  map_mul' _ _ := by ext <;> simp

@[simp] theorem ofEquivHom_apply (f : RootPairing.Aut P) : ofEquivHom P f = ofEquiv f := (rfl)

/-- **An automorphism and the isogeny it becomes have the same powers**, since
`TauCeti.RootPairingIsogeny.ofEquiv` is multiplicative. -/
@[simp] theorem ofEquiv_pow (f : RootPairing.Aut P) (n : ℕ) :
    ofEquiv (f ^ n) = ofEquiv f ^ n :=
  map_pow (ofEquivHom P) f n

/-! ## The multiplicative components -/

/-- **The weight map of an isogeny, as a monoid homomorphism** into the endomorphism monoid of the
weight space. -/
def weightHom (P : RootPairing ι R M N) : RootPairingIsogeny P P →* Module.End R M where
  toFun f := f.weightMap
  map_one' := weightMap_one
  map_mul' := weightMap_mul

@[simp] theorem weightHom_apply (f : RootPairingIsogeny P P) :
    weightHom P f = f.weightMap := (rfl)

/-- The weight map of a power of an isogeny is the corresponding power of its weight map. -/
@[simp] theorem weightMap_pow (f : RootPairingIsogeny P P) (n : ℕ) :
    (f ^ n).weightMap = f.weightMap ^ n :=
  map_pow (weightHom P) f n

/-- **The coweight map of an isogeny, as a monoid homomorphism** into the opposite of the
endomorphism monoid of the coweight space. Composition reverses on this component, exactly as for
`RootPairing.Hom.coweightHom`. -/
def coweightHom (P : RootPairing ι R M N) : RootPairingIsogeny P P →* (Module.End R N)ᵐᵒᵖ where
  toFun f := MulOpposite.op f.coweightMap
  map_one' := by simp only [MulOpposite.op_eq_one_iff, coweightMap_one, Module.End.one_eq_id]
  map_mul' f g := by
    simp only [← MulOpposite.op_mul, coweightMap_mul, Module.End.mul_eq_comp]

@[simp] theorem coweightHom_apply (f : RootPairingIsogeny P P) :
    coweightHom P f = MulOpposite.op f.coweightMap := (rfl)

/-- The coweight map of a power of an isogeny is the corresponding power of its coweight map. The
reversal in `TauCeti.RootPairingIsogeny.coweightHom` is immaterial here, since the two factors of
`f ^ (n + 1)` are the same map. -/
@[simp] theorem coweightMap_pow (f : RootPairingIsogeny P P) (n : ℕ) :
    (f ^ n).coweightMap = f.coweightMap ^ n :=
  MulOpposite.op_injective <| by
    rw [MulOpposite.op_pow, ← coweightHom_apply, ← coweightHom_apply, map_pow]

/-- **The index bijection of an isogeny, as a monoid homomorphism** into the permutation group of
the index set. -/
def indexHom (P : RootPairing ι R M N) : RootPairingIsogeny P P →* Equiv.Perm ι where
  toFun f := f.indexEquiv
  map_one' := indexEquiv_one
  map_mul' := indexEquiv_mul

@[simp] theorem indexHom_apply (f : RootPairingIsogeny P P) :
    indexHom P f = f.indexEquiv := (rfl)

/-- The index bijection of a power of an isogeny is the corresponding power of its index
bijection. -/
@[simp] theorem indexEquiv_pow (f : RootPairingIsogeny P P) (n : ℕ) :
    (f ^ n).indexEquiv = f.indexEquiv ^ n :=
  map_pow (indexHom P) f n

/-- The exponent of a power of an isogeny, in terms of the exponents of the lower power. -/
theorem exponent_pow_succ (f : RootPairingIsogeny P P) (n : ℕ) (i : ι) :
    (f ^ (n + 1)).exponent i = f.exponent i * (f ^ n).exponent (f.indexEquiv i) := by
  rw [pow_succ, exponent_mul]

/-- **The exponent of an iterate accumulates along the forward orbit of the index bijection.**
Unlike the other three fields the exponent is not multiplicative: the exponent of a composite at
an index is the product of the exponents met at the successive images of that index. -/
@[simp] theorem exponent_pow (f : RootPairingIsogeny P P) (k : ℕ) (i : ι) :
    (f ^ k).exponent i = ∏ j ∈ Finset.range k, f.exponent ((f.indexEquiv ^ j) i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', exponent_mul, ih, indexEquiv_pow, Finset.prod_range_succ]

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

/-- **A scaling is central in the monoid of endo-isogenies**, the monoid form of
`TauCeti.RootPairingIsogeny.comp_smulId`. Since a scaling at a prime power `q` is the root-datum
shadow of the `q`-power Frobenius, this is the root-datum form of the fact that a Frobenius
commutes with every endomorphism of the datum. -/
theorem commute_smulId (f : RootPairingIsogeny P P) (c : ℕ+) : Commute (smulId P c) f :=
  (commute_iff_eq _ _).2 <| by rw [mul_def, mul_def, comp_smulId]

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
theorem indexEquiv_pow_two_mul_add_one (h : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).indexEquiv = f.indexEquiv := by
  rw [pow_two_mul_add_one_eq_smulId_mul P h, indexEquiv_mul, smulId_indexEquiv, Equiv.trans_refl]

/-- **The rescaling exponents of an odd power** are those of the isogeny times `c ^ m`.

Read at a special isogeny in characteristic `p`, so at `c = p`: the `exponent` field is indexed by
the source of the character map, and is `1` at a short simple root and `p` at a long one
(`TauCeti.DynkinType.b2SpecialIsogeny_exponent_typeBSimpleIndex_eq_one_iff`), so the odd power has
exponent `p ^ m` at a short simple root and `p ^ (m + 1)` at a long one. -/
theorem exponent_pow_two_mul_add_one (h : f * f = smulId P c) (m : ℕ) (i : ι) :
    (f ^ (2 * m + 1)).exponent i = f.exponent i * (c : ℤ) ^ m := by
  rw [pow_two_mul_add_one_eq_smulId_mul P h, exponent_mul, smulId_exponent]
  push_cast [PNat.pow_coe]
  ring

/-- **The weight map of an odd power** is `c ^ m` times that of the isogeny. -/
theorem weightMap_pow_two_mul_add_one (h : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).weightMap = ((c : ℕ) ^ m) • f.weightMap := by
  rw [pow_two_mul_add_one_eq_smulId_mul P h, weightMap_mul, smulId_weightMap]
  ext x
  simp [PNat.pow_coe]

/-- **The coweight map of an odd power** is `c ^ m` times that of the isogeny. Composition reverses
on this component, but a scaling is central, so the formula is the same as for the weight map. -/
theorem coweightMap_pow_two_mul_add_one (h : f * f = smulId P c) (m : ℕ) :
    (f ^ (2 * m + 1)).coweightMap = ((c : ℕ) ^ m) • f.coweightMap := by
  rw [pow_two_mul_add_one_eq_smulId_mul P h, coweightMap_mul, smulId_coweightMap]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, map_nsmul,
    PNat.pow_coe]

end Scaling

end RootPairingIsogeny

end TauCeti
