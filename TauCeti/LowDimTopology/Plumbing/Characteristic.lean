/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.ModEq
public import TauCeti.LowDimTopology.Plumbing.IntersectionForm

/-!
# Characteristic covectors of a plumbing lattice

This file adds the characteristic-covector parity condition for the integral lattice attached
to a plumbing graph. For a plumbing graph `P`, a covector `k : V → ℤ` is characteristic when its
value on each basis sphere is congruent modulo two to the sphere's self-intersection, namely
`P.weight v`.

This is the first parity layer used in Némethi's lattice homology: the chain groups are indexed
by lattice points together with characteristic covectors, and later weight functions are built
from these covectors and the plumbing intersection form.

## Main definitions

* `TauCeti.PlumbingGraph.IsCharacteristicVector`: the vertex-wise parity condition
  `k v ≡ P.weight v [ZMOD 2]`.
* `TauCeti.PlumbingGraph.characteristicVectors`: the subtype of characteristic covectors.
* `TauCeti.PlumbingGraph.canonicalCharacteristic`: the canonical covector satisfying the
  adjunction coordinates `K(E_v) + E_v · E_v = -2`.
* `TauCeti.PlumbingGraph.conjugate`: spin^c conjugation, negating a characteristic covector.

## Main results

* `TauCeti.PlumbingGraph.isCharacteristicVector_iff_intersection_single`: the parity condition
  can be read from the self-pairing of each basis vector.
* `TauCeti.PlumbingGraph.isCharacteristicVector_iff_forall_modEq_intersectionForm`: the
  characteristic condition against every lattice vector.
* Characteristic covectors are stable under adding twice an integral covector, and the
  difference of two characteristic covectors is pointwise even.
* `TauCeti.PlumbingGraph.conjugate_conjugate`: spin^c conjugation is an involution.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), which asks for plumbing graphs and their lattices together with lattice
points and weight functions. The characteristic-covector convention follows Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} (P : PlumbingGraph V)

/-- A covector of the plumbing lattice is characteristic when its value on every basis sphere is
congruent modulo two to that sphere's self-intersection. For the plumbing basis this is the
usual condition `k(v) ≡ v · v (mod 2)`, since `v · v = P.weight v`. -/
def IsCharacteristicVector (k : V → ℤ) : Prop :=
  ∀ v : V, k v ≡ P.weight v [ZMOD 2]

/-- The subtype of characteristic covectors of the plumbing lattice. -/
abbrev characteristicVectors :=
  { k : V → ℤ // P.IsCharacteristicVector k }

/-- Characteristic covectors are exactly the covectors satisfying the vertex-wise parity
condition. This is a `_def`-style restatement: it is not a `@[simp]` lemma, so that the
per-instance characteristic lemmas (such as `isCharacteristicVector_canonicalCharacteristic`)
keep their `IsCharacteristicVector` head for `simp` to match; it is exposed to `grind` for
unfolding the predicate. -/
@[grind =]
theorem isCharacteristicVector_iff (k : V → ℤ) :
    P.IsCharacteristicVector k ↔ ∀ v : V, k v ≡ P.weight v [ZMOD 2] :=
  Iff.rfl

/-- The canonical characteristic covector, in the plumbing convention
`K(E_v) + E_v · E_v = -2`. Since `E_v · E_v = P.weight v`, its coordinate at `v` is
`-P.weight v - 2`. The body is not part of the interface: use `canonicalCharacteristic_apply`
for its coordinates and the characteristic/adjunction lemmas below. -/
def canonicalCharacteristic : V → ℤ :=
  fun v => -P.weight v - 2

/-- The canonical characteristic covector has coordinates `-P.weight v - 2`. -/
@[simp]
theorem canonicalCharacteristic_apply (v : V) :
    P.canonicalCharacteristic v = -P.weight v - 2 := by
  simp only [canonicalCharacteristic]

/-- The canonical covector is characteristic. -/
@[simp, grind .]
theorem isCharacteristicVector_canonicalCharacteristic :
    P.IsCharacteristicVector P.canonicalCharacteristic := by
  intro v
  rw [canonicalCharacteristic_apply]
  exact Int.modEq_iff_dvd.mpr ⟨P.weight v + 1, by ring⟩

section Form

variable [DecidableEq V] [Fintype V]

-- This is the `p = 2` case of `ZMod.pow_card`, but that lemma lives in
-- `Mathlib.FieldTheory.Finite.Basic`, whose import closure (finite fields, Galois theory) is far
-- wider than the elementary parity this file needs; `ZMod 2` has two elements, so `decide` proves
-- it outright.
private theorem zmod_two_sq (a : ZMod 2) : a ^ 2 = a := by
  revert a; decide

omit [DecidableEq V] in
private theorem adjacency_sum_cast_zmod_two_eq_zero (x : V → ℤ) :
    (∑ i, ∑ j, ((if P.toSimpleGraph.Adj i j then x i * x j else 0 : ℤ) : ZMod 2)) = 0 := by
  classical
  let f : {p : V × V // P.toSimpleGraph.Adj p.1 p.2} → ZMod 2 :=
    fun p => (x p.1.1 : ZMod 2) * (x p.1.2 : ZMod 2)
  -- Reindex the iterated sum over `i` then `j` as a single sum over the pair `(i, j) : V × V`.
  have hpair :
      (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then
          (x i : ZMod 2) * (x j : ZMod 2) else 0) =
        ∑ p : V × V, if P.toSimpleGraph.Adj p.1 p.2 then
          (x p.1 : ZMod 2) * (x p.2 : ZMod 2) else 0 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  -- Drop the `if` by restricting to the subtype of adjacent pairs, identifying the sum with `∑ f`.
  have hsum :
      (∑ i, ∑ j, ((if P.toSimpleGraph.Adj i j then x i * x j else 0 : ℤ) : ZMod 2)) =
        ∑ p, f p := by
    simp only [Int.cast_ite, Int.cast_mul, Int.cast_zero]
    rw [hpair, ← Finset.sum_filter]
    rw [Finset.sum_subtype
      (s := (Finset.univ : Finset (V × V)).filter fun p => P.toSimpleGraph.Adj p.1 p.2)]
    intro p
    simp
  rw [hsum]
  -- Adjacency is symmetric, so `(i, j) ↦ (j, i)` is a fixed-point-free involution on adjacent
  -- pairs; it pairs `f` with itself, and `a + a = 0` in `ZMod 2`.
  exact Finset.sum_involution (s := Finset.univ) (f := f)
    (fun p _ => ⟨(p.1.2, p.1.1), p.2.symm⟩)
    (fun p _ => by
      dsimp [f]
      rw [mul_comm]
      exact CharTwo.add_self_eq_zero _)
    (fun p _ _ h => by
      exact p.2.ne (Prod.ext_iff.mp (Subtype.ext_iff.mp h)).2)
    (fun _ _ => Finset.mem_univ _) (fun p _ => by
      ext <;> rfl)

/-- Characteristicness can be read from the self-pairing of the plumbing basis vectors. -/
theorem isCharacteristicVector_iff_intersection_single (k : V → ℤ) :
    P.IsCharacteristicVector k ↔
      ∀ v : V, k v ≡ P.intersectionForm (Pi.single v 1) (Pi.single v 1) [ZMOD 2] := by
  constructor
  · intro hk v
    simpa using hk v
  · intro hk v
    simpa using hk v

/-- A covector is characteristic exactly when its evaluation on every lattice vector is congruent
modulo two to that vector's self-pairing under the plumbing intersection form. -/
theorem isCharacteristicVector_iff_forall_modEq_intersectionForm (k : V → ℤ) :
    P.IsCharacteristicVector k ↔
      ∀ x : V → ℤ, (∑ v, k v * x v) ≡ P.intersectionForm x x [ZMOD 2] := by
  constructor
  · intro hk x
    apply (ZMod.intCast_eq_intCast_iff (∑ v, k v * x v) (P.intersectionForm x x) 2).mp
    rw [P.intersectionForm_self x]
    simp only [Int.cast_sum, Int.cast_add, Int.cast_mul, Int.cast_pow]
    rw [adjacency_sum_cast_zmod_two_eq_zero]
    simp only [add_zero]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hkz : (k v : ZMod 2) = P.weight v :=
      (ZMod.intCast_eq_intCast_iff (k v) (P.weight v) 2).mpr (hk v)
    rw [hkz, zmod_two_sq]
  · intro h v
    have hv := h (Pi.single v (1 : ℤ) : V → ℤ)
    simp only [Pi.single_apply] at hv
    simpa using hv

/-- The canonical characteristic covector satisfies the adjunction coordinate equation
`K(E_v) + E_v · E_v = -2`. -/
theorem canonicalCharacteristic_apply_add_intersection_single (v : V) :
    P.canonicalCharacteristic v +
      P.intersectionForm (Pi.single v 1) (Pi.single v 1) = -2 := by
  rw [canonicalCharacteristic_apply, intersectionForm_single, intersectionMatrix_diag]
  ring

end Form

/-- Adding an even-valued covector preserves characteristicness. -/
theorem IsCharacteristicVector.add_of_forall_even {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) (hl : ∀ v : V, Even (l v)) :
    P.IsCharacteristicVector fun v => k v + l v := by
  intro v
  simpa using (hk v).add (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp (hl v)))

/-- Adding twice an integral covector preserves characteristicness. -/
theorem IsCharacteristicVector.add_two_mul {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) : P.IsCharacteristicVector fun v => k v + 2 * l v :=
  PlumbingGraph.IsCharacteristicVector.add_of_forall_even (P := P) hk fun v =>
    even_iff_two_dvd.mpr ⟨l v, by ring_nf⟩

/-- Negating a characteristic covector preserves characteristicness. -/
theorem IsCharacteristicVector.neg {k : V → ℤ}
    (hk : P.IsCharacteristicVector k) : P.IsCharacteristicVector fun v => -k v := by
  intro v
  have hweight : -P.weight v ≡ P.weight v [ZMOD 2] :=
    Int.modEq_iff_dvd.mpr ⟨P.weight v, by ring⟩
  exact (hk v).neg.trans hweight

/-- Spin^c conjugation on characteristic covectors: negate the covector. Characteristicness is
preserved because `-1 ≡ 1 [ZMOD 2]` (see `IsCharacteristicVector.neg`), so this is a well-defined
involution of `characteristicVectors`. On the level of spin^c structures it is the conjugation
involution. -/
def conjugate (k : P.characteristicVectors) : P.characteristicVectors :=
  ⟨-k.val, k.property.neg⟩

/-- The conjugate covector is the pointwise negation of the original. -/
private theorem conjugate_val_aux (k : P.characteristicVectors) : (P.conjugate k).val = -k.val :=
  rfl

/-- The conjugate covector is the pointwise negation of the original. -/
@[simp]
theorem conjugate_val (k : P.characteristicVectors) : (P.conjugate k).val = -k.val :=
  conjugate_val_aux P k

/-- Spin^c conjugation is an involution. -/
@[simp]
theorem conjugate_conjugate (k : P.characteristicVectors) :
    P.conjugate (P.conjugate k) = k :=
  Subtype.ext (by simp)

/-- The pointwise difference of two characteristic covectors is even. -/
theorem IsCharacteristicVector.even_sub {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) (hl : P.IsCharacteristicVector l) (v : V) :
    Even (k v - l v) := by
  have hmod : k v - l v ≡ 0 [ZMOD 2] := by
    simpa using (hk v).sub (hl v)
  exact even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod)

/-- The pointwise difference of two characteristic covectors is congruent to zero modulo two. -/
theorem IsCharacteristicVector.sub_modEq_zero {k l : V → ℤ}
    (hk : P.IsCharacteristicVector k) (hl : P.IsCharacteristicVector l) (v : V) :
    k v - l v ≡ 0 [ZMOD 2] := by
  simpa using (hk v).sub (hl v)

/-- A covector obtained from the canonical characteristic covector by adding twice another
covector is characteristic. -/
theorem isCharacteristicVector_canonical_add_two_mul (l : V → ℤ) :
    P.IsCharacteristicVector fun v => P.canonicalCharacteristic v + 2 * l v :=
  P.isCharacteristicVector_canonicalCharacteristic.add_two_mul

/-- A characteristic covector differs from the canonical characteristic covector by an
even-valued covector. -/
theorem IsCharacteristicVector.even_sub_canonical {k : V → ℤ}
    (hk : P.IsCharacteristicVector k) (v : V) :
    Even (k v - P.canonicalCharacteristic v) :=
  PlumbingGraph.IsCharacteristicVector.even_sub (P := P) hk
    P.isCharacteristicVector_canonicalCharacteristic v

end PlumbingGraph

end TauCeti
