/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Ramification indices in finite flat towers

This file records two consequences of the fundamental identity for ramification and inertia in a
finite flat extension of domains. First, the ramification index at any prime is at most the rank of
the extension. Second, ramification cancels in a tower when the absolute ramification index at the
top equals the absolute ramification index at the intermediate prime: multiplicativity then forces
the relative ramification index to be one.

The cancellation result is the local step used in the finite-place half of the genus-field
construction. At a rational prime dividing a prime discriminant, both the quadratic base and the
prime-discriminant compositum have absolute ramification index two; cancellation then shows that
the compositum is unramified over the quadratic base.

## Main results

* `TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank`: the contribution of one
  prime to the fundamental identity is at most the rank of the extension.
* `TauCeti.RamificationInertia.ramificationIdx_le_finrank`: a ramification index is at most the
  rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_eq_one_of_eq_ramificationIdx`: equal absolute
  ramification indices at two levels of a tower force relative ramification index one.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_eq_ramificationIdx`: if that equality
  holds at every prime above an intermediate prime, then the intermediate prime is unramified in
  the top ring.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le`: it suffices to bound
  every absolute ramification index upstairs by the intermediate absolute ramification index.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one`: a
  transverse unramified subextension of sufficiently small relative degree supplies that bound.
-/

public section

open Ideal Module

namespace TauCeti.RamificationInertia

section Bounds

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]

/-- **One prime's contribution to the fundamental identity is at most the extension rank.**
For a prime `q` of `S` above a prime `p` of `R`, the product of its ramification index and inertia
degree is at most `Module.finrank R S`. -/
theorem ramificationIdx_mul_inertiaDeg_le_finrank (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx R * q.inertiaDeg R ≤ finrank R S := by
  classical
  have : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  let q' : p.primesOver S := ⟨q, inferInstance, inferInstance⟩
  calc
    q.ramificationIdx R * q.inertiaDeg R =
        q'.1.ramificationIdx R * q'.1.inertiaDeg R := rfl
    _ ≤ ∑ Q : p.primesOver S, Q.1.ramificationIdx R * Q.1.inertiaDeg R :=
      Finset.single_le_sum
        (f := fun Q : p.primesOver S => Q.1.ramificationIdx R * Q.1.inertiaDeg R)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ q')
    _ = finrank R S := Ideal.sum_ramification_inertia_eq_finrank p S

/-- **A ramification index is at most the rank of a finite flat extension.** For a prime `q` of
`S` above a prime `p` of `R`, `e(q / p) ≤ Module.finrank R S`. -/
theorem ramificationIdx_le_finrank (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] [q.LiesOver p] : q.ramificationIdx R ≤ finrank R S :=
  le_trans (Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos q R))
    (ramificationIdx_mul_inertiaDeg_le_finrank p q)

end Bounds

section Tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Module.Finite R S] [Module.Flat S T]

/-- **Ramification-index cancellation in a tower.** Let `r` be a prime of `T` above a prime `q`
of `S`. If their absolute ramification indices over `R` agree, then the relative ramification
index `e(r / q)` is one. Indeed, multiplicativity gives
`e(r / R) = e(q / R) * e(r / S)`, and `e(q / R)` is positive in a finite extension. -/
theorem ramificationIdx_eq_one_of_eq_ramificationIdx (q : Ideal S) (r : Ideal T)
    [q.IsPrime] [r.IsPrime] [r.LiesOver q] (h : r.ramificationIdx R = q.ramificationIdx R) :
    r.ramificationIdx S = 1 := by
  apply Nat.eq_of_mul_eq_mul_left (q.ramificationIdx_pos R)
  rw [mul_one, ← Ideal.ramificationIdx_tower (R := R) q r, h]

/-- **Absolute ramification-index equality implies relative unramifiedness.** Let `q` be a prime
of `S`. If every prime `r` of `T` above `q` has the same absolute ramification index over `R` as
`q`, then `q` is unramified in `T`. This is the all-primes form of
`ramificationIdx_eq_one_of_eq_ramificationIdx`. -/
theorem isUnramifiedIn_of_forall_eq_ramificationIdx [IsDomain S] [Module.Finite ℤ S]
    [CharZero S] [Module.Finite S T] (q : Ideal S) [q.IsPrime]
    (h : ∀ (r : Ideal T) [r.IsPrime], r.LiesOver q →
      r.ramificationIdx R = q.ramificationIdx R) : Algebra.IsUnramifiedIn T q := by
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro r _ hr
  exact ramificationIdx_eq_one_of_eq_ramificationIdx q r (h r hr)

/-- **No increase in absolute ramification implies relative unramifiedness.** Let `q` be a prime
of `S`. If every prime `r` of `T` above `q` has absolute ramification index at most that of `q`,
then `q` is unramified in `T`. The reverse inequality is automatic from multiplicativity in the
tower, so the absolute indices are equal and
`isUnramifiedIn_of_forall_eq_ramificationIdx` applies. -/
theorem isUnramifiedIn_of_forall_ramificationIdx_le [IsDomain S] [Module.Finite ℤ S]
    [CharZero S] [Module.Finite S T] (q : Ideal S) [q.IsPrime]
    (h : ∀ (r : Ideal T) [r.IsPrime], r.LiesOver q →
      r.ramificationIdx R ≤ q.ramificationIdx R) : Algebra.IsUnramifiedIn T q := by
  have := Module.Finite.trans (R := R) S T
  apply isUnramifiedIn_of_forall_eq_ramificationIdx (R := R) (S := S) (T := T) q
  intro r _ hr
  have : r.LiesOver q := hr
  exact le_antisymm (h r hr) (Ideal.ramificationIdx_below_le (R := R) q r)

/-- **A transverse unramified subextension cancels the base ramification.** Suppose `T` is also an
extension of a domain `U` over `R`. Let `q` be a prime of `S`, assume
`Module.finrank U T ≤ e(q / R)`, and assume that for every prime `r` above `q`, its contraction
to `U` has absolute ramification index one. Then `q` is unramified in `T`.

Indeed, the tower through `U` identifies `e(r / R)` with `e(r / U)`, which is at most
`Module.finrank U T`; hence `e(r / R) ≤ e(q / R)`, and
`isUnramifiedIn_of_forall_ramificationIdx_le` applies. For a biquadratic compositum at a shared
ramified prime, `S / R` has ramification index two while `T / U` has degree two. -/
theorem isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one
    [IsDomain S] [Module.Finite ℤ S]
    [CharZero S] [Module.Finite S T] {U : Type*} [CommRing U] [IsDomain U] [Algebra R U]
    [Algebra U T] [IsScalarTower R U T] [Module.Finite U T] [Module.Flat U T]
    (q : Ideal S) [q.IsPrime] (hrank : finrank U T ≤ q.ramificationIdx R)
    (hunr : ∀ (r : Ideal T) [r.IsPrime], r.LiesOver q →
      (r.under U).ramificationIdx R = 1) : Algebra.IsUnramifiedIn T q := by
  apply isUnramifiedIn_of_forall_ramificationIdx_le (R := R) q
  intro r _ hr
  have : r.LiesOver q := hr
  calc
    r.ramificationIdx R = (r.under U).ramificationIdx R * r.ramificationIdx U :=
      Ideal.ramificationIdx_tower (R := R) (r.under U) r
    _ = r.ramificationIdx U := by rw [hunr r hr, one_mul]
    _ ≤ finrank U T := ramificationIdx_le_finrank (r.under U) r
    _ ≤ q.ramificationIdx R := hrank

end Tower

end TauCeti.RamificationInertia
