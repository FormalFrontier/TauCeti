/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.Algebra.CharP.FrobeniusFixed
public import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# The finite subfields of a separably closed field of positive characteristic

`TauCeti.frobeniusFixedSubfield K p n` is the subfield of solutions of `a ^ p ^ n = a`, defined for
an arbitrary field of exponential characteristic `p`. When the field is separably closed and
`n ≠ 0` it is the field of `q = p ^ n` elements sitting inside it.

The counting is the standard one: `a ^ q = a` says exactly that `a` is a root of `X ^ q - X`, a
polynomial whose derivative is `-1` and which therefore has no repeated roots, so over a separably
closed field it splits and has as many roots as its degree. In any field of characteristic `p` a
subfield with `q` elements is *the* Frobenius-fixed one, since being fixed by the `q`-power map
characterises the elements of a finite subfield of order `q`. In the other direction every element
of an algebraic closure of `ZMod p` lies in one of these subfields, since it generates a finite
extension of the prime field.

## Main results

* `TauCeti.card_frobeniusFixedSubfield`: over a separably closed field and for `n ≠ 0` it has
  exactly `p ^ n` elements.
* `TauCeti.eq_frobeniusFixedSubfield_of_natCard`: it is the unique subfield with that many elements.
* `TauCeti.nonempty_frobeniusFixedSubfield_ringEquiv_galoisField`: it is therefore a copy of
  `GaloisField p n`.
* `TauCeti.exists_mem_frobeniusFixedSubfield`: an algebraic closure of the prime field is the union
  of these subfields.

## References

This is the field-theoretic half of "the fixed points of the `q`-power Frobenius are the
`𝔽_q`-points", the ring-theoretic half being `TauCeti.frobeniusFixedSubring` itself. It is a
prerequisite of the "points over an algebraically closed field, functorially in the field" target
of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, and of milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md`, whose ordinary and graph-twisted Steinberg maps start
from the `q`-power Frobenius of an algebraic closure of `ZMod p`.

* S. Lang, *Algebra*, 3rd ed., V.5.
* R. Lidl and H. Niederreiter, *Finite Fields*, §2.1.
-/

public section

open Polynomial

namespace TauCeti

/-! ## The root set of `X ^ q - X` -/

section RootSet

variable (K : Type*) [Field K] (p n : ℕ) [Fact p.Prime] [CharP K p]

/-- Over any field of characteristic `p` and for `n ≠ 0`, being fixed by the `p ^ n`-power
Frobenius is being a root of `X ^ p ^ n - X`. That polynomial is then separable of degree `p ^ n`,
which is where the count below comes from. At `n = 0` the two sides differ: the subfield is the
whole of `K` while `X ^ 1 - X = 0` has empty root set. -/
theorem coe_frobeniusFixedSubfield_eq_rootSet (hn : n ≠ 0) :
    (frobeniusFixedSubfield K p n : Set K) = (X ^ p ^ n - X : K[X]).rootSet K := by
  have hne : (X ^ p ^ n - X : K[X]) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero K hn (Fact.out (p := p.Prime)).one_lt
  ext a
  simp [Polynomial.mem_rootSet, hne, sub_eq_zero]

/-- The equivalence used to count the Frobenius-fixed subfield: its elements are exactly the roots
of `X ^ p ^ n - X`, a separable polynomial of degree `p ^ n`. The public form of this is
`coe_frobeniusFixedSubfield_eq_rootSet`. -/
private def frobeniusFixedSubfieldEquivRootSet (hn : n ≠ 0) :
    frobeniusFixedSubfield K p n ≃ (X ^ p ^ n - X : K[X]).rootSet K :=
  Equiv.setCongr (coe_frobeniusFixedSubfield_eq_rootSet K p n hn)

/-- The Frobenius-fixed subfield of a field of characteristic `p` is finite once `n ≠ 0`, being a
set of roots of a nonzero polynomial. This is not an instance: at `n = 0` the subfield is the whole
of `K`, which need not be finite. -/
theorem finite_frobeniusFixedSubfield (hn : n ≠ 0) : Finite (frobeniusFixedSubfield K p n) :=
  .of_equiv _ (frobeniusFixedSubfieldEquivRootSet K p n hn).symm

/-- **Uniqueness of the subfield of `q` elements.** A subfield with `p ^ n` elements of a field of
characteristic `p` is the subfield fixed by the `p ^ n`-power Frobenius.

An element of the ambient field satisfies `a ^ q = a` exactly when it lies in a subfield with `q`
elements, by `TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap`; no counting, and no
algebraic closedness, is involved. -/
theorem eq_frobeniusFixedSubfield_of_natCard {F : Subfield K} (hF : Nat.card F = p ^ n) :
    F = frobeniusFixedSubfield K p n := by
  have hne : Nat.card F ≠ 0 := by
    rw [hF]
    exact pow_ne_zero n (Fact.out (p := p.Prime)).ne_zero
  have _ : Finite F := Nat.finite_of_card_ne_zero hne
  have _ : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  refine SetLike.coe_injective (Set.ext fun a => ?_)
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_frobeniusFixedSubfield, ← hcard,
    FiniteField.pow_card_eq_self_iff_mem_range_algebraMap, Subfield.algebraMap_ofSubfield,
    Subfield.coe_subtype, Subtype.range_coe_subtype, Set.mem_ofPred_eq]

end RootSet

section IsSepClosed

variable (K : Type*) [Field K] [IsSepClosed K] (p n : ℕ) [Fact p.Prime] [CharP K p]

/-- **The field of `q` elements inside a separably closed field.** For `q = p ^ n` with
`n ≠ 0`, the elements of a separably closed field of characteristic `p` fixed by the
`q`-power Frobenius form a subfield with exactly `q` elements.

The count is the number of roots of the separable polynomial `X ^ q - X`, which is its degree. -/
theorem card_frobeniusFixedSubfield (hn : n ≠ 0) :
    Nat.card (frobeniusFixedSubfield K p n) = p ^ n := by
  have hsep : Separable (X ^ p ^ n - X : K[X]) :=
    galois_poly_separable p (p ^ n) (dvd_pow_self p hn)
  have hsplit : ((X ^ p ^ n - X : K[X]).map (algebraMap K K)).Splits :=
    IsSepClosed.splits_domain _ hsep
  rw [Nat.card_congr (frobeniusFixedSubfieldEquivRootSet K p n hn), Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree hsep hsplit,
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hn (Fact.out (p := p.Prime)).one_lt]

/-- The Frobenius-fixed subfield of a separably closed field is a copy of Mathlib's
`GaloisField p n`, the two being finite fields of the same cardinality. The isomorphism is not
canonical, which is why only its existence is recorded. -/
theorem nonempty_frobeniusFixedSubfield_ringEquiv_galoisField (hn : n ≠ 0) :
    Nonempty (frobeniusFixedSubfield K p n ≃+* GaloisField p n) := by
  have _ : Finite (frobeniusFixedSubfield K p n) := finite_frobeniusFixedSubfield K p n hn
  have _ : Fintype (frobeniusFixedSubfield K p n) := Fintype.ofFinite _
  have _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_frobeniusFixedSubfield K p n hn, GaloisField.card p n hn]

end IsSepClosed

/-! ## Exhaustion over an algebraic prime field -/

section Algebraic

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
  [Algebra.IsAlgebraic (ZMod p) K]

/-- **An algebraic extension of `ZMod p` is the union of its Frobenius-fixed subfields.** Every
element generates a finite extension of the prime field, and so is fixed by the `p ^ n`-power
Frobenius for the degree `n` of that extension.

Only algebraicity over the prime field is used, so the statement covers an algebraic closure of
`ZMod p` without assuming algebraic closedness. -/
theorem exists_mem_frobeniusFixedSubfield (x : K) :
    ∃ n ≠ 0, x ∈ frobeniusFixedSubfield K p n := by
  set E := IntermediateField.adjoin (ZMod p) ({x} : Set K)
  have hx : x ∈ E := IntermediateField.mem_adjoin_simple_self (ZMod p) x
  have _ : FiniteDimensional (ZMod p) E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have _ : Finite E := Module.finite_of_finite (ZMod p)
  refine ⟨Module.finrank (ZMod p) E, (Module.finrank_pos (R := ZMod p) (M := E)).ne', ?_⟩
  have hcard : Nat.card E.toSubfield = p ^ Module.finrank (ZMod p) E := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (E.mem_toSubfield ·))]
    exact (FiniteField.pow_finrank_eq_natCard p E).symm
  rw [← eq_frobeniusFixedSubfield_of_natCard K p _ hcard]
  exact (E.mem_toSubfield x).mpr hx

end Algebraic

end TauCeti
