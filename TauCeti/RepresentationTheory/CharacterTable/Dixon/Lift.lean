/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Prime
public import TauCeti.RingTheory.Cyclotomic.Lift

/-!
# The cyclotomic lift at a Dixon prime

`TauCeti.Cyclotomic.lift` reconstructs an exact cyclotomic integer from its residues at the
conjugate roots, and it returns the element it came from as soon as the coordinates of that element
lie inside the residue window `2 * |c| < p`.  A `TauCeti.DixonPrimeData` for a finite group `G`
supplies both of the things that needs: the primitive `e`-th root of unity `d.root` modulo `d.p`,
`e = Monoid.exponent G`, at which the conjugate roots are formed, and Dixon's size bound
`2⌊√|G|⌋ < d.p`, which turns the abstract window into the concrete one the algorithm works in,
`|c| ≤ ⌊√|G|⌋`.

The results here are therefore *conditional arithmetic specializations*: they take the coordinate
bound `|c| ≤ ⌊√|G|⌋` as a hypothesis and convert it into the abstract window, and they say nothing
about which elements satisfy it.  Nothing here asserts that the coordinates the
Burnside--Dixon--Schneider algorithm reconstructs really are that small: that claim is unverified,
it is proved nowhere in this repository, and the roadmap records the `2√|G|` constant as the
standard citation with low confidence as to the precise constant, to be re-checked against
Dixon 1967 before it is relied on.  Supplying the bound, as a hypothesis, is the caller's job.
What this file does establish is that once it is supplied, the modular phase is lossless: the exact
value is determined by its residues at the conjugate roots of a Dixon prime, and is returned by the
lift.

## Main results

* `TauCeti.DixonPrimeData.lift_conjugateResidues`: **correctness at Dixon's bound**, the lift
  returns an exact cyclotomic integer with coordinates bounded by `⌊√|G|⌋` from its residues.
* `TauCeti.DixonPrimeData.eq_of_conjugateResidues_eq`: **uniqueness at Dixon's bound**, two such
  integers with the same residues are equal.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "The structured cyclotomic lift".
-/

public section

namespace TauCeti

namespace DixonPrimeData

variable {G : Type*} [Group G] (d : DixonPrimeData G)
variable {x y : Cyclotomic (Monoid.exponent G)}

/-- **The lift at a Dixon prime is correct.**  An exact cyclotomic integer whose coordinates are
bounded by `⌊√|G|⌋` is returned by `TauCeti.Cyclotomic.lift` from its own residues at the conjugate
roots. -/
@[simp]
theorem lift_conjugateResidues
    (hx : ∀ j : Fin (Monoid.exponent G).totient,
      (x.coeff j).natAbs ≤ Nat.sqrt (Nat.card G)) :
    Cyclotomic.lift (Monoid.exponent G) d.root (Cyclotomic.conjugateResidues d.root x) = x :=
  Cyclotomic.lift_conjugateResidues d.isPrimitiveRoot_root fun j =>
    d.isGoodDixonPrime.two_mul_natAbs_lt_of_natAbs_le_sqrt (hx j)

/-- **An exact cyclotomic integer whose coordinates are bounded by `⌊√|G|⌋` is determined by its
residues at the conjugate roots of a Dixon prime.**  This is what makes the modular phase of the
Burnside--Dixon--Schneider algorithm lossless. -/
theorem eq_of_conjugateResidues_eq
    (hx : ∀ j : Fin (Monoid.exponent G).totient,
      (x.coeff j).natAbs ≤ Nat.sqrt (Nat.card G))
    (hy : ∀ j : Fin (Monoid.exponent G).totient,
      (y.coeff j).natAbs ≤ Nat.sqrt (Nat.card G))
    (h : Cyclotomic.conjugateResidues d.root x = Cyclotomic.conjugateResidues d.root y) :
    x = y :=
  Cyclotomic.eq_of_conjugateResidues_eq d.isPrimitiveRoot_root
    (fun j => d.isGoodDixonPrime.two_mul_natAbs_lt_of_natAbs_le_sqrt (hx j))
    (fun j => d.isGoodDixonPrime.two_mul_natAbs_lt_of_natAbs_le_sqrt (hy j)) h

/-- **The specification of the lift at a Dixon prime.**  A residue tuple coming from an exact
cyclotomic integer with coordinates bounded by `⌊√|G|⌋` is lifted back to that integer, which by
`TauCeti.DixonPrimeData.eq_of_conjugateResidues_eq` is the only one it could be lifted to. -/
theorem lift_eq_of_conjugateResidues_eq {r : Fin (Monoid.exponent G).totient → ZMod d.p}
    (hx : ∀ j : Fin (Monoid.exponent G).totient,
      (x.coeff j).natAbs ≤ Nat.sqrt (Nat.card G))
    (hr : Cyclotomic.conjugateResidues d.root x = r) :
    Cyclotomic.lift (Monoid.exponent G) d.root r = x :=
  Cyclotomic.lift_eq_of_conjugateResidues_eq d.isPrimitiveRoot_root
    (fun j => d.isGoodDixonPrime.two_mul_natAbs_lt_of_natAbs_le_sqrt (hx j)) hr

end DixonPrimeData

end TauCeti
