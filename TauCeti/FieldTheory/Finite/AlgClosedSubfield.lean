/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.CharP.FrobeniusFixed

/-!
# The finite subfields of an algebraically closed field of positive characteristic

`TauCeti.frobeniusFixedSubring A p n` is the subring of solutions of `a ^ p ^ n = a`, defined for an
arbitrary commutative ring of exponential characteristic `p`. Over a field it is closed under
inverses, so it is a subfield, `TauCeti.frobeniusFixedSubfield`; and when the field is
algebraically closed and `n ≠ 0` it is the field of `q = p ^ n` elements sitting inside it.

The counting is the standard one: `a ^ q = a` says exactly that `a` is a root of `X ^ q - X`, a
polynomial whose derivative is `-1` and which therefore has no repeated roots, so over an
algebraically closed field it has as many roots as its degree. Being closed under inverses is what
turns the resulting `q`-element subring into a copy of `𝔽_q`, and a counting argument then shows it
is the *only* subfield with `q` elements. In the other direction every element of an algebraic
closure of `ZMod p` lies in one of these subfields, since it generates a finite extension of the
prime field.

## Main definitions

* `TauCeti.frobeniusFixedSubfield`: the subfield of a field of exponential characteristic `p` fixed
  by the `p ^ n`-power Frobenius.

## Main results

* `TauCeti.card_frobeniusFixedSubfield`: over an algebraically closed field and for `n ≠ 0` it has
  exactly `p ^ n` elements.
* `TauCeti.eq_frobeniusFixedSubfield_of_natCard`: it is the unique subfield with that many elements.
* `TauCeti.nonempty_ringEquiv_galoisField`: it is therefore a copy of `GaloisField p n`.
* `TauCeti.exists_mem_frobeniusFixedSubfield`: an algebraic closure of the prime field is the union
  of these subfields.

## References

This is the field-theoretic half of "the fixed points of the `q`-power Frobenius are the
`𝔽_q`-points", the ring-theoretic half being `TauCeti.frobeniusFixedSubring` itself. It is a
prerequisite of the "points over an algebraically closed field, functorially in the field" target
of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, and of milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md`, whose Steinberg maps start from the `q`-power Frobenius
of an algebraic closure of `ZMod p`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* S. Lang, *Algebra*, 3rd ed., V.5.
-/

public section

open Polynomial

namespace TauCeti

/-! ## The fixed subfield -/

section Field

variable (K : Type*) [Field K] (p n : ℕ) [ExpChar K p]

/-- The subfield of elements of a field `K` fixed by the `p ^ n`-power Frobenius, that is, the
solutions of `a ^ p ^ n = a`.

This is `TauCeti.frobeniusFixedSubring` together with closure under inverses, which holds because
`(a⁻¹) ^ p ^ n = (a ^ p ^ n)⁻¹`. As with the subring, nothing about finiteness is asserted at this
level of generality: at `n = 0`, or in characteristic zero, it is the whole of `K`. -/
@[expose]
def frobeniusFixedSubfield : Subfield K where
  __ := frobeniusFixedSubring K p n
  inv_mem' a ha := by
    simp only [Subring.mem_carrier, mem_frobeniusFixedSubring] at ha ⊢
    rw [inv_pow, ha]

variable {K p n}

/-- Membership in the Frobenius-fixed subfield is the equation `a ^ p ^ n = a`. -/
@[simp]
theorem mem_frobeniusFixedSubfield {a : K} :
    a ∈ frobeniusFixedSubfield K p n ↔ a ^ p ^ n = a := mem_frobeniusFixedSubring

variable (K p n)

/-- The Frobenius-fixed subfield has the Frobenius-fixed subring as its underlying subring. -/
@[simp]
theorem toSubring_frobeniusFixedSubfield :
    (frobeniusFixedSubfield K p n).toSubring = frobeniusFixedSubring K p n := rfl

end Field

/-! ## Counting over an algebraically closed field -/

section RootSet

variable (K : Type*) [Field K] (p n : ℕ) [Fact p.Prime] [CharP K p]

/-- Over any field of characteristic `p`, being fixed by the `p ^ n`-power Frobenius is being a
root of `X ^ p ^ n - X`. That polynomial is separable of degree `p ^ n`, which is where the count
below comes from. -/
theorem coe_frobeniusFixedSubfield_eq_rootSet (hn : n ≠ 0) :
    (frobeniusFixedSubfield K p n : Set K) = (X ^ p ^ n - X : K[X]).rootSet K := by
  have hne : (X ^ p ^ n - X : K[X]) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero K hn (Fact.out (p := p.Prime)).one_lt
  ext a
  simp [Polynomial.mem_rootSet, hne, sub_eq_zero]

/-- The equivalence used to count the Frobenius-fixed subfield: its elements are exactly the roots
of `X ^ p ^ n - X`, a separable polynomial of degree `p ^ n`. -/
def frobeniusFixedSubfieldEquivRootSet (hn : n ≠ 0) :
    frobeniusFixedSubfield K p n ≃ (X ^ p ^ n - X : K[X]).rootSet K :=
  Equiv.setCongr (coe_frobeniusFixedSubfield_eq_rootSet K p n hn)

/-- The Frobenius-fixed subfield of a field of characteristic `p` is finite once `n ≠ 0`, being a
set of roots of a nonzero polynomial. This is not an instance: at `n = 0` the subfield is the whole
of `K`, which need not be finite. -/
theorem finite_frobeniusFixedSubfield (hn : n ≠ 0) : Finite (frobeniusFixedSubfield K p n) :=
  .of_equiv _ (frobeniusFixedSubfieldEquivRootSet K p n hn).symm

end RootSet

section IsAlgClosed

variable (K : Type*) [Field K] [IsAlgClosed K] (p n : ℕ) [Fact p.Prime] [CharP K p]

/-- **The field of `q` elements inside an algebraically closed field.** For `q = p ^ n` with
`n ≠ 0`, the elements of an algebraically closed field of characteristic `p` fixed by the
`q`-power Frobenius form a subfield with exactly `q` elements.

The count is the number of roots of the separable polynomial `X ^ q - X`, which is its degree. -/
theorem card_frobeniusFixedSubfield (hn : n ≠ 0) :
    Nat.card (frobeniusFixedSubfield K p n) = p ^ n := by
  have hsep : Separable (X ^ p ^ n - X : K[X]) :=
    galois_poly_separable p (p ^ n) (dvd_pow_self p hn)
  have hsplit : ((X ^ p ^ n - X : K[X]).map (algebraMap K K)).Splits :=
    IsAlgClosed.splits_domain _
  rw [Nat.card_congr (frobeniusFixedSubfieldEquivRootSet K p n hn), Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree hsep hsplit,
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hn (Fact.out (p := p.Prime)).one_lt]

/-- **Uniqueness of the subfield of `q` elements.** A finite subfield of an algebraically closed
field of characteristic `p` with `p ^ n` elements is the subfield fixed by the `p ^ n`-power
Frobenius.

Every element of a finite field of cardinality `q` satisfies `a ^ q = a`, so such a subfield is
contained in the fixed one; the two then agree because they have the same finite cardinality. -/
theorem eq_frobeniusFixedSubfield_of_natCard {F : Subfield K} [Finite F]
    (hn : n ≠ 0) (hF : Nat.card F = p ^ n) : F = frobeniusFixedSubfield K p n := by
  have _ : Fintype F := Fintype.ofFinite F
  have _ : Finite (frobeniusFixedSubfield K p n) := finite_frobeniusFixedSubfield K p n hn
  rw [Nat.card_eq_fintype_card] at hF
  have hsub : (F : Set K) ⊆ (frobeniusFixedSubfield K p n : Set K) := by
    intro a ha
    have hpow := FiniteField.pow_card (⟨a, ha⟩ : F)
    rw [hF] at hpow
    exact mem_frobeniusFixedSubfield.mpr (congrArg (Subtype.val : F → K) hpow)
  have hcard : (frobeniusFixedSubfield K p n : Set K).ncard ≤ (F : Set K).ncard := by
    have h₁ : (frobeniusFixedSubfield K p n : Set K).ncard = p ^ n := by
      simp only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
      exact card_frobeniusFixedSubfield K p n hn
    have h₂ : (F : Set K).ncard = p ^ n := by
      simp only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
      rw [Nat.card_eq_fintype_card, hF]
    rw [h₁, h₂]
  exact SetLike.coe_injective
    (Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _))

/-- The Frobenius-fixed subfield of an algebraically closed field is a copy of Mathlib's
`GaloisField p n`, the two being finite fields of the same cardinality. The isomorphism is not
canonical, which is why only its existence is recorded. -/
theorem nonempty_ringEquiv_galoisField (hn : n ≠ 0) :
    Nonempty (frobeniusFixedSubfield K p n ≃+* GaloisField p n) := by
  have _ : Finite (frobeniusFixedSubfield K p n) := finite_frobeniusFixedSubfield K p n hn
  have _ : Fintype (frobeniusFixedSubfield K p n) := Fintype.ofFinite _
  have _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine ⟨FiniteField.ringEquivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_frobeniusFixedSubfield K p n hn, GaloisField.card p n hn]

end IsAlgClosed

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
  classical
  set E := IntermediateField.adjoin (ZMod p) ({x} : Set K) with hE
  have hx : x ∈ E := IntermediateField.mem_adjoin_simple_self (ZMod p) x
  have _ : FiniteDimensional (ZMod p) E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have _ : Finite E := Module.finite_of_finite (ZMod p)
  have _ : Fintype E := Fintype.ofFinite E
  refine ⟨Module.finrank (ZMod p) E, ?_, ?_⟩
  · exact (Module.finrank_pos (R := ZMod p) (M := E)).ne'
  · have hcard : p ^ Module.finrank (ZMod p) E = Nat.card E :=
      FiniteField.pow_finrank_eq_natCard p E
    have hpow := FiniteField.pow_card (⟨x, hx⟩ : E)
    rw [← Nat.card_eq_fintype_card, ← hcard] at hpow
    exact mem_frobeniusFixedSubfield.mpr (congrArg (Subtype.val : E → K) hpow)

end Algebraic

end TauCeti
