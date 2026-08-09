/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
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

That is the bound the Burnside--Dixon--Schneider algorithm has for the coordinates it reconstructs,
so these two statements are the form in which the lift is used: the modular phase of the algorithm
produces the residues of a central character value at the conjugate roots, and this file says that
the exact value is determined by them, and is returned by the lift.

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

/-- Dixon's size bound, in the form the residue window of `TauCeti.RingTheory.Cyclotomic.Lift`
asks for: a coordinate bounded by `⌊√|G|⌋` lies strictly inside the window of half-width
`d.p / 2`. -/
theorem two_mul_natAbs_lt_of_natAbs_le_sqrt {z : ℤ} (hz : z.natAbs ≤ Nat.sqrt (Nat.card G)) :
    2 * z.natAbs < d.p := by
  have := d.isGoodDixonPrime.two_mul_sqrt_lt
  omega

/-- **The lift at a Dixon prime is correct.**  An exact cyclotomic integer whose coordinates are
bounded by `⌊√|G|⌋` is returned by `TauCeti.Cyclotomic.lift` from its own residues at the conjugate
roots. -/
theorem lift_conjugateResidues (hx : ∀ j, (x.coeff j).natAbs ≤ Nat.sqrt (Nat.card G)) :
    Cyclotomic.lift (Monoid.exponent G) d.root (Cyclotomic.conjugateResidues d.root x) = x :=
  Cyclotomic.lift_conjugateResidues d.isPrimitiveRoot_root fun j =>
    d.two_mul_natAbs_lt_of_natAbs_le_sqrt (hx j)

/-- **An exact cyclotomic integer whose coordinates are bounded by `⌊√|G|⌋` is determined by its
residues at the conjugate roots of a Dixon prime.**  This is what makes the modular phase of the
Burnside--Dixon--Schneider algorithm lossless. -/
theorem eq_of_conjugateResidues_eq
    (hx : ∀ j, (x.coeff j).natAbs ≤ Nat.sqrt (Nat.card G))
    (hy : ∀ j, (y.coeff j).natAbs ≤ Nat.sqrt (Nat.card G))
    (h : Cyclotomic.conjugateResidues d.root x = Cyclotomic.conjugateResidues d.root y) :
    x = y :=
  Cyclotomic.eq_of_conjugateResidues_eq d.isPrimitiveRoot_root
    (fun j => d.two_mul_natAbs_lt_of_natAbs_le_sqrt (hx j))
    (fun j => d.two_mul_natAbs_lt_of_natAbs_le_sqrt (hy j)) h

/-- **The specification of the lift at a Dixon prime.**  A residue tuple coming from an exact
cyclotomic integer with coordinates bounded by `⌊√|G|⌋` is lifted back to that integer, which by
`TauCeti.DixonPrimeData.eq_of_conjugateResidues_eq` is the only one it could be lifted to. -/
theorem lift_eq_of_conjugateResidues_eq {r : Fin (Monoid.exponent G).totient → ZMod d.p}
    (hx : ∀ j, (x.coeff j).natAbs ≤ Nat.sqrt (Nat.card G))
    (hr : Cyclotomic.conjugateResidues d.root x = r) :
    Cyclotomic.lift (Monoid.exponent G) d.root r = x :=
  Cyclotomic.lift_eq_of_conjugateResidues_eq d.isPrimitiveRoot_root
    (fun j => d.two_mul_natAbs_lt_of_natAbs_le_sqrt (hx j)) hr

/-- The lift at a Dixon prime is a section of the residue tuple: whatever tuple it is given, the
exact cyclotomic integer it returns has exactly those residues.  Only the size of the coordinates
is at stake in the correctness statements above. -/
theorem conjugateResidues_lift (r : Fin (Monoid.exponent G).totient → ZMod d.p) :
    Cyclotomic.conjugateResidues d.root (Cyclotomic.lift (Monoid.exponent G) d.root r) = r :=
  Cyclotomic.conjugateResidues_lift d.isPrimitiveRoot_root r

end DixonPrimeData

end TauCeti
