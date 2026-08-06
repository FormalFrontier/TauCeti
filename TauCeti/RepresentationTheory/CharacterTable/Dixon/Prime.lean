/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.PrimesCongruentOne
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.LinearAlgebra.End.FiniteOrder

/-!
# Good Dixon primes

The Burnside--Dixon--Schneider algorithm computes the complex character table of a finite group
`G` by working over a finite prime field `ZMod p` and lifting the answer back. The prime it works
over cannot be arbitrary: it has to make `ZMod p` behave, for the purposes of the computation, like
`ℂ`, and it has to be large enough that the lift is unambiguous. This file isolates that condition
as `TauCeti.IsGoodDixonPrime` and proves what it buys.

Three arithmetic conditions do the work. That `p` does not divide `|G|` makes `ZMod p [G]`
semisimple, by Maschke. That the exponent `e` of `G` divides `p - 1` makes every element of `G` act
with eigenvalues in `ZMod p`, because the `e`-th roots of unity are already there: `ZMod p` contains
a primitive `e`-th root of unity and `X ^ e - 1` splits into distinct linear factors over it. And
Dixon's size bound `2⌊√|G|⌋ < p` opens a residue window wide enough that an integer of absolute
value at most `√|G|` -- the size of the coefficients the algorithm has to reconstruct -- is
determined by its residue modulo `p`.

Such primes always exist: there are arbitrarily large primes congruent to `1` modulo `e`
(`Nat.exists_prime_gt_modEq_one`, itself a cyclotomic-polynomial argument), and any of them beyond
`|G|` is good. The existence proof is not part of any computation; a concrete group supplies a
concrete prime, as `TauCeti.dihedralFourDixonPrimeData` and `TauCeti.dihedralThreeDixonPrimeData`
do below.

## Main definitions

* `TauCeti.IsGoodDixonPrime`: the good-prime predicate.
* `TauCeti.DixonPrimeData`: a good prime together with a choice of primitive `e`-th root of unity
  modulo it, the data the algorithm consumes.

## Main results

* `TauCeti.IsGoodDixonPrime.isSemisimpleRing`: the modular group algebra is semisimple.
* `TauCeti.IsGoodDixonPrime.exists_isPrimitiveRoot` and
  `TauCeti.IsGoodDixonPrime.splits_X_pow_exponent_sub_one`: `ZMod p` splits `X ^ e - 1`, with `e`
  distinct roots.
* `TauCeti.IsGoodDixonPrime.isSemisimple_representation_apply`: every group element acts semisimply
  in a representation over `ZMod p`.
* `TauCeti.IsGoodDixonPrime.valMinAbs_intCast` and `TauCeti.IsGoodDixonPrime.intCast_inj`: an
  integer bounded by `√|G|` is recovered from, and so determined by, its residue modulo `p`. This
  is what the size bound is for.
* `TauCeti.exists_isGoodDixonPrime`: **good Dixon primes exist** for every finite group.

## Implementation notes

`TauCeti.DixonPrimeData` carries the primitive root as a field rather than choosing one with the
axiom of choice, because the algorithm that consumes it is meant to run: a noncomputable root would
make every downstream `def` noncomputable. The existence statement is therefore phrased twice, once
as the proposition `TauCeti.exists_isGoodDixonPrime` and once as
`TauCeti.instNonemptyDixonPrimeData`.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "Certified Dixon prime data".
-/

public section

namespace TauCeti

open Polynomial

/-! ### Primitive roots of unity in a finite field -/

/-- A finite field contains a primitive `d`-th root of unity for every `d` dividing the order of
its unit group, because that unit group is cyclic. -/
theorem exists_isPrimitiveRoot_of_dvd_card_units (F : Type*) [Field F] [Finite F] {d : ℕ}
    (hd : d ∣ Nat.card Fˣ) : ∃ ζ : F, IsPrimitiveRoot ζ d := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ ≠ 0 := Nat.card_pos.ne'
  refine ⟨((u ^ (Nat.card Fˣ / d) : Fˣ) : F), IsPrimitiveRoot.coe_units_iff.2 ?_⟩
  have hord : orderOf (u ^ (orderOf u / d)) = d :=
    orderOf_pow_orderOf_div (by rw [hu]; exact hcard) (by rw [hu]; exact hd)
  rw [hu] at hord
  have hprim := IsPrimitiveRoot.orderOf (u ^ (Nat.card Fˣ / d))
  rwa [hord] at hprim

/-! ### The good-prime predicate -/

/-- **`p` is a good Dixon prime for `G`**: it is prime, it does not divide `|G|`, the exponent of
`G` divides `p - 1`, and it exceeds Dixon's size bound `2⌊√|G|⌋`.

These are exactly the arithmetic hypotheses under which the Burnside--Dixon--Schneider algorithm
runs: the first makes `ZMod p [G]` semisimple, the second puts the `e`-th roots of unity into
`ZMod p`, and the third makes the lift back to characteristic zero unique. That the reduced central
characters stay pairwise distinct is *not* part of the definition; it is a consequence, the content
of the good-prime structure theorem. -/
def IsGoodDixonPrime (G : Type*) [Group G] (p : ℕ) : Prop :=
  p.Prime ∧ ¬p ∣ Nat.card G ∧ Monoid.exponent G ∣ p - 1 ∧ 2 * Nat.sqrt (Nat.card G) < p

namespace IsGoodDixonPrime

variable {G : Type*} [Group G] {p : ℕ}

theorem prime (hp : IsGoodDixonPrime G p) : p.Prime := hp.1

theorem not_dvd_natCard (hp : IsGoodDixonPrime G p) : ¬p ∣ Nat.card G := hp.2.1

theorem exponent_dvd (hp : IsGoodDixonPrime G p) : Monoid.exponent G ∣ p - 1 := hp.2.2.1

theorem two_mul_sqrt_lt (hp : IsGoodDixonPrime G p) : 2 * Nat.sqrt (Nat.card G) < p := hp.2.2.2

/-- The primality of a good Dixon prime, as the `Fact` that the field structure on `ZMod p` is
found from. -/
theorem fact_prime (hp : IsGoodDixonPrime G p) : Fact p.Prime := ⟨hp.prime⟩

theorem one_lt (hp : IsGoodDixonPrime G p) : 1 < p := hp.prime.one_lt

/-! #### The exponent condition -/

/-- Every element of `G` is a `(p - 1)`-st root of unity: this is the reformulation of
`Monoid.exponent G ∣ p - 1` that the eigenvalue arguments use. -/
theorem pow_sub_one_eq_one (hp : IsGoodDixonPrime G p) (g : G) : g ^ (p - 1) = 1 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hp.exponent_dvd g

theorem orderOf_dvd_sub_one (hp : IsGoodDixonPrime G p) (g : G) : orderOf g ∣ p - 1 :=
  (Monoid.order_dvd_exponent g).trans hp.exponent_dvd

/-- `ZMod p` contains a primitive `d`-th root of unity for every `d` dividing the exponent of `G`;
in particular, taking `d = orderOf g`, the eigenvalues of any element of `G` in any representation
over `ZMod p` are already in `ZMod p`. -/
theorem exists_isPrimitiveRoot_of_dvd_exponent (hp : IsGoodDixonPrime G p) {d : ℕ}
    (hd : d ∣ Monoid.exponent G) : ∃ ζ : ZMod p, IsPrimitiveRoot ζ d := by
  have := hp.fact_prime
  refine exists_isPrimitiveRoot_of_dvd_card_units (ZMod p) (hd.trans ?_)
  rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  exact hp.exponent_dvd

/-- **`ZMod p` contains a primitive root of unity of order the exponent of `G`.** -/
theorem exists_isPrimitiveRoot (hp : IsGoodDixonPrime G p) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ (Monoid.exponent G) :=
  hp.exists_isPrimitiveRoot_of_dvd_exponent dvd_rfl

/-! #### The order condition: Maschke -/

/-- The order of `G` is invertible modulo a good Dixon prime. -/
theorem natCard_ne_zero (hp : IsGoodDixonPrime G p) : (Nat.card G : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hp.not_dvd_natCard

theorem neZero_natCard (hp : IsGoodDixonPrime G p) : NeZero ((Nat.card G : ZMod p)) :=
  ⟨hp.natCard_ne_zero⟩

/-- **Maschke's theorem at a good Dixon prime**: the modular group algebra `ZMod p [G]` is a
semisimple ring. -/
theorem isSemisimpleRing [Finite G] (hp : IsGoodDixonPrime G p) :
    IsSemisimpleRing (MonoidAlgebra (ZMod p) G) := by
  have := hp.fact_prime
  have := hp.neZero_natCard
  infer_instance

/-! #### Splitting the roots of unity -/

/-- **`X ^ e - 1` splits over `ZMod p`**, `e` the exponent of `G`: this is the sense in which a
good Dixon prime makes `ZMod p` a substitute for `ℂ`. -/
theorem splits_X_pow_exponent_sub_one [Finite G] (hp : IsGoodDixonPrime G p) :
    (X ^ Monoid.exponent G - 1 : (ZMod p)[X]).Splits := by
  have := hp.fact_prime
  obtain ⟨ζ, hζ⟩ := hp.exists_isPrimitiveRoot
  rw [X_pow_sub_one_eq_prod (Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite) hζ]
  exact Splits.prod fun _ _ => Splits.X_sub_C _

/-- The `e`-th roots of unity in `ZMod p` are `e` in number: `X ^ e - 1` splits with *distinct*
roots, which is what makes the elements of `G` act semisimply. The `Fact` instance is what puts the
field structure on `ZMod p` that `Polynomial.nthRootsFinset` needs to be stated at all; it is
implied by `hp`. -/
theorem card_nthRootsFinset [Fact p.Prime] (hp : IsGoodDixonPrime G p) :
    (nthRootsFinset (Monoid.exponent G) (1 : ZMod p)).card = Monoid.exponent G := by
  obtain ⟨ζ, hζ⟩ := hp.exists_isPrimitiveRoot
  exact hζ.card_nthRootsFinset

/-! #### The size condition: the residue window -/

theorem neZero (hp : IsGoodDixonPrime G p) : NeZero p := ⟨hp.prime.ne_zero⟩

/-- **The certified rational-integer lift at a good Dixon prime.** Dixon's size bound opens a
residue window wide enough that an integer of absolute value at most `⌊√|G|⌋` is returned by
`ZMod.valMinAbs` from its residue. This is the first stage of the cyclotomic lift: a rational
character value, reduced modulo `p`, is recovered exactly. -/
theorem valMinAbs_intCast (hp : IsGoodDixonPrime G p) {z : ℤ}
    (hz : z.natAbs ≤ Nat.sqrt (Nat.card G)) : ((z : ZMod p)).valMinAbs = z := by
  have := hp.neZero
  have hlt := hp.two_mul_sqrt_lt
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_, ?_⟩ <;> omega

/-- **Dixon's size bound opens a wide enough residue window.** Two integers of absolute value at
most `⌊√|G|⌋` that agree modulo `p` are equal, so an integer of that size is determined by its
residue. This is why the lift is unambiguous. -/
theorem intCast_inj (hp : IsGoodDixonPrime G p) {z w : ℤ}
    (hz : z.natAbs ≤ Nat.sqrt (Nat.card G)) (hw : w.natAbs ≤ Nat.sqrt (Nat.card G))
    (h : (z : ZMod p) = w) : z = w := by
  rw [← hp.valMinAbs_intCast hz, ← hp.valMinAbs_intCast hw, h]

/-! #### Representations over `ZMod p` -/

section Representation

/- The `Fact` instance is again only what puts the field structure on `ZMod p` that a
representation over it needs in order to be stated; it is implied by the good-prime hypothesis. -/
variable [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- The order of a group element is invertible modulo a good Dixon prime, since it divides
`p - 1`. -/
theorem natCast_orderOf_ne_zero (hp : IsGoodDixonPrime G p) (g : G) :
    ((orderOf g : ℕ) : ZMod p) ≠ 0 := by
  have hdvd := hp.orderOf_dvd_sub_one g
  have h1 := hp.one_lt
  have hpos : 0 < orderOf g :=
    Nat.pos_of_ne_zero fun h => by rw [h, zero_dvd_iff] at hdvd; omega
  have hle : orderOf g ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun hdvd' => absurd (Nat.le_of_dvd hpos hdvd') (by omega)

/-- **At a good Dixon prime every group element acts semisimply.** In any finite-dimensional
representation over `ZMod p`, `ρ g` is annihilated by the squarefree polynomial
`X ^ orderOf g - 1`. Over `ℂ` this is where diagonalizability of the class-multiplication matrices
comes from, and the good-prime conditions are exactly what transports it to `ZMod p`. -/
theorem isSemisimple_representation_apply (hp : IsGoodDixonPrime G p)
    (ρ : Representation (ZMod p) G V) (g : G) : Module.End.IsSemisimple (ρ g) :=
  End.isSemisimple_of_pow_eq_one (hp.natCast_orderOf_ne_zero g)
    (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end Representation

end IsGoodDixonPrime

/-! ### Existence -/

/-- **Good Dixon primes exist.** Take a prime congruent to `1` modulo the exponent of `G` and
larger than `|G|`; there are arbitrarily large such primes. This is a statement about the
algorithm, not a step in it: a concrete group is handed a concrete prime instead. -/
theorem exists_isGoodDixonPrime (G : Type*) [Group G] [Finite G] :
    ∃ p : ℕ, IsGoodDixonPrime G p := by
  obtain ⟨p, hprime, hgt, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (k := Monoid.exponent G)
      (max (Nat.card G) (2 * Nat.sqrt (Nat.card G))) Monoid.exponent_ne_zero_of_finite
  have hcard : 0 < Nat.card G := Nat.card_pos
  have hlt : Nat.card G < p := lt_of_le_of_lt (le_max_left _ _) hgt
  refine ⟨p, hprime, fun hdvd => ?_, ?_, lt_of_le_of_lt (le_max_right _ _) hgt⟩
  · exact absurd (Nat.le_of_dvd hcard hdvd) (by omega)
  · exact (Nat.modEq_iff_dvd' hprime.one_lt.le).1 hmod.symm

/-- The data the Burnside--Dixon--Schneider algorithm runs on: a good Dixon prime `p` for `G`
together with a chosen primitive `e`-th root of unity modulo `p`, `e` the exponent of `G`. The root
is data rather than a choice made by `exists_isPrimitiveRoot`, so that the definitions consuming it
stay computable. -/
structure DixonPrimeData (G : Type*) [Group G] where
  /-- The prime the algorithm reduces modulo. -/
  p : ℕ
  /-- A primitive `e`-th root of unity modulo `p`, `e` the exponent of `G`. It pins the
  identification of the `e`-th roots of unity in `ZMod p` with those in `ℂ` that the lift uses. -/
  root : ZMod p
  /-- The certificate that `p` is a good Dixon prime. -/
  isGoodDixonPrime : IsGoodDixonPrime G p
  /-- The certificate that `root` is a primitive `e`-th root of unity. -/
  isPrimitiveRoot_root : IsPrimitiveRoot root (Monoid.exponent G)

namespace DixonPrimeData

variable {G : Type*} [Group G] (d : DixonPrimeData G)

theorem prime : d.p.Prime := d.isGoodDixonPrime.prime

theorem not_dvd_natCard : ¬d.p ∣ Nat.card G := d.isGoodDixonPrime.not_dvd_natCard

theorem exponent_dvd : Monoid.exponent G ∣ d.p - 1 := d.isGoodDixonPrime.exponent_dvd

theorem two_mul_sqrt_lt : 2 * Nat.sqrt (Nat.card G) < d.p := d.isGoodDixonPrime.two_mul_sqrt_lt

/-- The chosen root has order exactly the exponent of `G`. -/
theorem orderOf_root : orderOf d.root = Monoid.exponent G :=
  d.isPrimitiveRoot_root.eq_orderOf.symm

end DixonPrimeData

/-- Every finite group admits Dixon prime data. The witness is noncomputable, which is why concrete
instances are supplied by hand. -/
instance (G : Type*) [Group G] [Finite G] : Nonempty (DixonPrimeData G) := by
  obtain ⟨p, hp⟩ := exists_isGoodDixonPrime G
  obtain ⟨ζ, hζ⟩ := hp.exists_isPrimitiveRoot
  exact ⟨⟨p, ζ, hp, hζ⟩⟩

/-! ### Worked instances -/

section Dihedral

/-- The dihedral group of order `8` has exponent `4`. -/
theorem exponent_dihedral_four : Monoid.exponent (DihedralGroup 4) = 4 := by
  rw [DihedralGroup.exponent]
  decide

/-- **`5` is a good Dixon prime for the dihedral group of order `8`**, the worked example of the
character-table algorithm: `5 ∤ 8`, the exponent `4` divides `4 = 5 - 1`, and
`2⌊√8⌋ = 4 < 5`. -/
theorem isGoodDixonPrime_dihedral_four : IsGoodDixonPrime (DihedralGroup 4) 5 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [DihedralGroup.nat_card]; decide
  · rw [exponent_dihedral_four]
  · rw [DihedralGroup.nat_card]
    have h : Nat.sqrt (2 * 4) < 3 := Nat.sqrt_lt.2 (by norm_num)
    omega

/-- Dixon prime data for the dihedral group of order `8`: the prime `5`, with `2` as the primitive
fourth root of unity modulo `5`. -/
def dihedralFourDixonPrimeData : DixonPrimeData (DihedralGroup 4) where
  p := 5
  root := 2
  isGoodDixonPrime := isGoodDixonPrime_dihedral_four
  isPrimitiveRoot_root := by
    rw [exponent_dihedral_four]
    have h : orderOf (2 : ZMod 5) = 4 :=
      orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) fun q hq hq4 => by
        have h2 := hq.two_le
        have h4 := Nat.le_of_dvd (by norm_num) hq4
        interval_cases q <;> revert hq4 <;> decide
    exact h ▸ IsPrimitiveRoot.orderOf (2 : ZMod 5)

/-- The dihedral group of order `6`, the symmetric group on three letters, has exponent `6`. -/
theorem exponent_dihedral_three : Monoid.exponent (DihedralGroup 3) = 6 := by
  rw [DihedralGroup.exponent]
  decide

/-- **`7` is a good Dixon prime for the dihedral group of order `6`**: `7 ∤ 6`, the exponent `6`
divides `6 = 7 - 1`, and `2⌊√6⌋ = 4 < 7`. -/
theorem isGoodDixonPrime_dihedral_three : IsGoodDixonPrime (DihedralGroup 3) 7 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [DihedralGroup.nat_card]; decide
  · rw [exponent_dihedral_three]
  · rw [DihedralGroup.nat_card]
    have h : Nat.sqrt (2 * 3) < 3 := Nat.sqrt_lt.2 (by norm_num)
    omega

/-- Dixon prime data for the dihedral group of order `6`: the prime `7`, with `3` as the primitive
sixth root of unity modulo `7`. -/
def dihedralThreeDixonPrimeData : DixonPrimeData (DihedralGroup 3) where
  p := 7
  root := 3
  isGoodDixonPrime := isGoodDixonPrime_dihedral_three
  isPrimitiveRoot_root := by
    rw [exponent_dihedral_three]
    have h : orderOf (3 : ZMod 7) = 6 :=
      orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) fun q hq hq6 => by
        have h2 := hq.two_le
        have h6 := Nat.le_of_dvd (by norm_num) hq6
        interval_cases q <;> revert hq6 <;> decide
    exact h ▸ IsPrimitiveRoot.orderOf (3 : ZMod 7)

end Dihedral

end TauCeti
