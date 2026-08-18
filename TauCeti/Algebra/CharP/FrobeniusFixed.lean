/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The subring fixed by an iterated Frobenius

Let `A` be a commutative ring of exponential characteristic `p` and let `q = p ^ n`. The elements
of `A` satisfying `a ^ q = a` are the equalizer of the ring homomorphism `iterateFrobenius A p n`
and the identity, hence a subring: this file names it `TauCeti.frobeniusFixedSubring` and records
its elementary properties.

For `p` prime, `0 < n` and `A` an algebraic closure of `ZMod p` this subring is the field of `q`
elements sitting inside `A`, which is why the construction is the ring-theoretic half of "the fixed
points of the `q`-power Frobenius are the `𝔽_q`-points"; at `n = 0` it is instead the whole of `A`,
since `q = 1`. Nothing about finiteness or about the field of `q` elements is proved here: the
statements below are about an arbitrary commutative ring of exponential characteristic `p`, and
Mathlib's `iterateFrobenius` supplies every proof.

## Main definitions

* `TauCeti.frobeniusFixedSubring`: the subring of elements fixed by the `p ^ n`-power Frobenius.

## Main results

* `TauCeti.mem_frobeniusFixedSubring`: membership is the equation `a ^ p ^ n = a`.
* `TauCeti.frobeniusFixedSubring_zero`: the zeroth iterate fixes everything.
* `TauCeti.frobeniusFixedSubring_le_of_dvd`: the fixed subrings grow along divisibility of the
  exponent, the inclusion `𝔽_{p ^ m} ⊆ 𝔽_{p ^ k}` in the motivating case.
* `TauCeti.map_le_frobeniusFixedSubring`: a ring homomorphism carries fixed elements to fixed
  elements.

## References

This is a prerequisite of the "points over an algebraically closed field, functorially in the
field" target of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose first requested
field endomorphism is the `q`-power Frobenius.
-/

public section

namespace TauCeti

variable (A : Type*) [CommRing A] (p n : ℕ) [ExpChar A p]

/-- The subring of elements of `A` fixed by the `p ^ n`-power Frobenius, that is, the solutions of
`a ^ p ^ n = a`. It is the equalizer of `iterateFrobenius A p n` with the identity.

When `p` is prime, `0 < n` and `A` is an algebraic closure of `ZMod p` this is the subring of
`p ^ n` elements, but nothing of the sort is asserted here: `A` is an arbitrary commutative ring of
exponential characteristic `p`, and for `p = 1` — that is, in characteristic zero — or for `n = 0`
the whole of `A` is fixed. -/
def frobeniusFixedSubring : Subring A :=
  (iterateFrobenius A p n).eqLocus (RingHom.id A)

/-- The Frobenius-fixed subring is again of exponential characteristic `p`, so it is itself a
legitimate value algebra for the Frobenius: `iterateFrobenius` and everything built on it apply to
it. Mathlib has this for a `Subfield` (`Subfield.expChar`) but not for a `Subring`. -/
instance : ExpChar (frobeniusFixedSubring A p n) p :=
  (frobeniusFixedSubring A p n).subtype.expChar
    (frobeniusFixedSubring A p n).subtype_injective p

variable {A p n}

/-- Membership in the Frobenius-fixed subring is the equation `a ^ p ^ n = a`. -/
@[simp]
theorem mem_frobeniusFixedSubring {a : A} :
    a ∈ frobeniusFixedSubring A p n ↔ a ^ p ^ n = a := Iff.rfl

variable (A p n)

/-- The zeroth Frobenius iterate is the identity, so it fixes every element. -/
@[simp]
theorem frobeniusFixedSubring_zero : frobeniusFixedSubring A p 0 = ⊤ := by
  refine Subring.ext fun a => ?_
  simp

variable {A p n}

/-- Fixed subrings grow along divisibility of the exponent: an element fixed by the `p ^ m`-power
Frobenius is fixed by the `p ^ k`-power Frobenius whenever `m ∣ k`. In the motivating case this is
the inclusion `𝔽_{p ^ m} ⊆ 𝔽_{p ^ k}` of subfields of an algebraic closure. -/
theorem frobeniusFixedSubring_le_of_dvd {m k : ℕ} (h : m ∣ k) :
    frobeniusFixedSubring A p m ≤ frobeniusFixedSubring A p k := by
  obtain ⟨c, rfl⟩ := h
  intro a ha
  -- membership is `RingHom.eqLocus` membership by definition, so it *is* the equation
  -- `iterateFrobenius A p m a = a`; Mathlib's `RingHom.mem_eqLocus` is the bridge.
  refine RingHom.mem_eqLocus.mpr ?_
  rw [iterateFrobenius_mul_apply, Function.iterate_fixed (RingHom.mem_eqLocus.mp ha)]
  rfl

variable {B : Type*} [CommRing B] [ExpChar B p]

/-- A ring homomorphism commutes with the Frobenius, so it carries elements fixed by the
`p ^ n`-power Frobenius to elements fixed by it. -/
theorem map_le_frobeniusFixedSubring (φ : A →+* B) :
    (frobeniusFixedSubring A p n).map φ ≤ frobeniusFixedSubring B p n := by
  rintro _ ⟨a, ha, rfl⟩
  refine RingHom.mem_eqLocus.mpr ?_
  rw [← φ.map_iterateFrobenius p a n, RingHom.mem_eqLocus.mp ha]
  rfl

/-- The pointwise form of `map_le_frobeniusFixedSubring`. -/
theorem map_mem_frobeniusFixedSubring (φ : A →+* B) {a : A}
    (ha : a ∈ frobeniusFixedSubring A p n) : φ a ∈ frobeniusFixedSubring B p n :=
  map_le_frobeniusFixedSubring φ ⟨a, ha, rfl⟩

end TauCeti
