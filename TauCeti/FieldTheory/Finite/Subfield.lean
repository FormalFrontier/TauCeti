/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# The finite subfields cut out by the Frobenius

Let `K` be a field of characteristic `p`. The `p ^ n`-power Frobenius is a ring endomorphism of
`K`, and the elements it fixes form a subfield `TauCeti.frobeniusFixedField K p n`. When `K` is
algebraically closed and `n ≠ 0` that subfield has exactly `p ^ n` elements, so it is a copy of
`𝔽_q` for `q = p ^ n` sitting inside `K`; and when `K` is moreover algebraic over its prime field,
every element of `K` lies in one of them.

## Main definitions

* `TauCeti.frobeniusFixedField`: the subfield of `K` fixed by the `p ^ n`-power Frobenius.

## Main results

* `TauCeti.card_frobeniusFixedField`: over an algebraically closed field the fixed subfield of the
  `p ^ n`-power Frobenius has `p ^ n` elements.
* `TauCeti.frobeniusFixedFieldRingEquivGaloisField`: it is therefore isomorphic to Mathlib's
  `GaloisField p n`.
* `TauCeti.frobeniusFixedField_one`: the Frobenius itself fixes exactly the prime field.
* `TauCeti.eq_frobeniusFixedField_of_card`: conversely a subfield with `p ^ n` elements is that
  fixed subfield, so it is the only one of its order.
* `TauCeti.frobeniusFixedField_le_iff`: the fixed subfields are ordered by divisibility of the
  exponents, so they reproduce the usual lattice of finite subfields of `𝔽̄_p`.
* `TauCeti.exists_mem_frobeniusFixedField` and `TauCeti.iSup_frobeniusFixedField`: a field
  algebraic over its prime field is the union of these finite subfields.

## Implementation notes

The fixed subfield is Mathlib's `RingHom.eqLocusField` of `iterateFrobenius` against the identity,
so the whole `Subfield` structure is Mathlib's. Membership is definitionally `x ^ p ^ n = x`, which
is what `TauCeti.mem_frobeniusFixedField` records.

The cardinality count is the classical one: `X ^ q - X` is separable in characteristic `p` for
`p ∣ q`, an algebraically closed field splits it, and its root set is exactly the fixed set, so
`Polynomial.card_rootSet_eq_natDegree` counts `q` roots. Nothing here needs `K` to be an algebraic
closure of `𝔽_p`; that hypothesis appears only in the last section, where it is what makes the
finite subfields exhaust `K`.

Mathlib has the converse direction of the count, that a finite field of cardinality `p ^ n` is
`GaloisField p n` (`FiniteField.ringEquivOfCardEq`), and, in Tau Ceti,
`TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap` identifies the fixed points of the
`q`-power map of an extension of a *given* finite field with that field. What is missing, and is
supplied here, is the existence half: inside an algebraically closed field of characteristic `p`
the Frobenius produces such a subfield for every exponent, with no finite subfield given in
advance.

## Roadmap

This advances Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose "points over an
algebraically closed field" item asks for the group endomorphism induced by a field endomorphism
and names the `q`-power Frobenius as the first case a consumer wants. The consumer is milestone L3
of `TauCetiRoadmap/CFSGStatement/README.md`, which builds a finite group of Lie type as the fixed
points of a Steinberg endomorphism on the points over `AlgebraicClosure (ZMod p)`; on the untwisted
branches that endomorphism is induced by the `q`-power map of the coefficient field, and the
subfield identified here is what makes those fixed points the `𝔽_q`-points.

## References

The count of the roots of `X ^ q - X` is J. S. Milne, *Fields and Galois Theory*, §4; the resulting
description of the finite subfields of an algebraic closure of `𝔽_p` is S. Lang, *Algebra*, V.5.
-/

public section

open Polynomial

namespace TauCeti

variable (K : Type*) [Field K] (p n : ℕ)

section ExpChar

variable [ExpChar K p]

/-- The subfield of `K` fixed by the `p ^ n`-power Frobenius, that is, the set of `x` with
`x ^ p ^ n = x`. Over an algebraically closed field of characteristic `p` and for `n ≠ 0` this is a
copy of the field with `p ^ n` elements; see `TauCeti.card_frobeniusFixedField`. -/
def frobeniusFixedField : Subfield K :=
  (iterateFrobenius K p n).eqLocusField (RingHom.id K)

@[simp]
theorem mem_frobeniusFixedField {x : K} : x ∈ frobeniusFixedField K p n ↔ x ^ p ^ n = x :=
  Iff.rfl

/-- The zeroth Frobenius is the identity, so it fixes everything. -/
@[simp]
theorem frobeniusFixedField_zero : frobeniusFixedField K p 0 = ⊤ := by
  ext x
  simp

/-- **The fixed subfields grow along divisibility of the exponents**: an element fixed by the
`p ^ m`-power Frobenius is fixed by every iterate of that map. -/
theorem frobeniusFixedField_mono {m n : ℕ} (h : m ∣ n) :
    frobeniusFixedField K p m ≤ frobeniusFixedField K p n := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  rw [mem_frobeniusFixedField] at hx ⊢
  rw [pow_mul p m k]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hx]

end ExpChar

section PrimeField

variable [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]

/-- **The Frobenius itself fixes exactly the prime field.** Together with
`TauCeti.frobeniusFixedField_mono` this puts the prime field inside every fixed subfield. -/
theorem frobeniusFixedField_one :
    frobeniusFixedField K p 1 = (algebraMap (ZMod p) K).fieldRange := by
  ext x
  have hx := FiniteField.pow_card_eq_self_iff_mem_range_algebraMap (K := ZMod p) (L := K) x
  rw [ZMod.card p] at hx
  rw [mem_frobeniusFixedField, pow_one, hx, RingHom.mem_fieldRange]
  exact Set.mem_range

end PrimeField

section AlgClosed

variable [Fact p.Prime] [CharP K p]

/-- The fixed set of the `p ^ n`-power Frobenius is the root set of `X ^ p ^ n - X`, for `n ≠ 0`.
The hypothesis is needed only to know that the polynomial is nonzero. -/
theorem coe_frobeniusFixedField (hn : n ≠ 0) :
    (frobeniusFixedField K p n : Set K) = (X ^ p ^ n - X : K[X]).rootSet K := by
  have hq : 1 < p ^ n := Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt
  have hne : (X ^ p ^ n - X : K[X]) ≠ 0 := _root_.FiniteField.X_pow_card_sub_X_ne_zero K hq
  ext x
  simp [mem_rootSet_of_ne hne, sub_eq_zero]

variable [IsAlgClosed K]

/-- **The `p ^ n`-power Frobenius of an algebraically closed field of characteristic `p` fixes
exactly `p ^ n` elements.** The fixed subfield is therefore a copy of `𝔽_{p ^ n}` inside `K`. -/
theorem card_frobeniusFixedField (hn : n ≠ 0) :
    Nat.card (frobeniusFixedField K p n) = p ^ n := by
  have hq : 1 < p ^ n := Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt
  have hsep : (X ^ p ^ n - X : K[X]).Separable :=
    galois_poly_separable p (p ^ n) (dvd_pow_self p hn)
  have hroots : Nat.card ((X ^ p ^ n - X : K[X]).rootSet K) = p ^ n := by
    rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep (IsAlgClosed.splits_domain _),
      _root_.FiniteField.X_pow_card_sub_X_natDegree_eq K hq]
  rw [← hroots]
  exact Nat.card_congr (Equiv.setCongr (coe_frobeniusFixedField K p n hn))

/-- The fixed subfield of a nonzero iterate of the Frobenius is finite. -/
theorem finite_frobeniusFixedField (hn : n ≠ 0) : Finite (frobeniusFixedField K p n) :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_frobeniusFixedField K p n hn]
    exact pow_ne_zero n (Fact.out : p.Prime).pos.ne'

/-- **The fixed subfield of the `p ^ n`-power Frobenius is the Galois field of order `p ^ n`.**
Like every identification of finite fields of equal cardinality this is noncanonical. -/
noncomputable def frobeniusFixedFieldRingEquivGaloisField (hn : n ≠ 0) :
    frobeniusFixedField K p n ≃+* GaloisField p n := by
  haveI := finite_frobeniusFixedField K p n hn
  haveI : Fintype (frobeniusFixedField K p n) := Fintype.ofFinite _
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine _root_.FiniteField.ringEquivOfCardEq ?_
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_frobeniusFixedField K p n hn,
    GaloisField.card p n hn]

/-- **A subfield with `p ^ n` elements is the fixed subfield of the `p ^ n`-power Frobenius**, so
the fixed subfields exhaust the finite subfields of `K` and there is exactly one of each admissible
order. Every element of a finite field is a root of `X ^ q - X`, which forces the inclusion, and the
two subfields then have the same finite cardinality. -/
theorem eq_frobeniusFixedField_of_card {L : Subfield K} [Finite L] (hn : n ≠ 0)
    (hcard : Nat.card L = p ^ n) : L = frobeniusFixedField K p n := by
  have _ : Fintype L := Fintype.ofFinite _
  have hle : L ≤ frobeniusFixedField K p n := by
    intro x hx
    rw [mem_frobeniusFixedField, ← hcard, Nat.card_eq_fintype_card]
    simpa using congrArg (Subtype.val : L → K) (_root_.FiniteField.pow_card (⟨x, hx⟩ : L))
  have _ := finite_frobeniusFixedField K p n hn
  refine SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _))
  change Nat.card (frobeniusFixedField K p n) ≤ Nat.card L
  rw [hcard, card_frobeniusFixedField K p n hn]

/-- **The finite subfields cut out by the Frobenius are ordered by divisibility.** The forward
direction counts: the larger field is a vector space over the smaller one, so `p ^ n` is a power of
`p ^ m`. -/
theorem frobeniusFixedField_le_iff {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    frobeniusFixedField K p m ≤ frobeniusFixedField K p n ↔ m ∣ n := by
  refine ⟨fun h ↦ ?_, frobeniusFixedField_mono K p⟩
  have := finite_frobeniusFixedField K p m hm
  have := finite_frobeniusFixedField K p n hn
  let _ : Algebra (frobeniusFixedField K p m) (frobeniusFixedField K p n) :=
    (Subfield.inclusion h).toAlgebra
  have hd : Nat.card (frobeniusFixedField K p n) =
      Nat.card (frobeniusFixedField K p m) ^
        Module.finrank (frobeniusFixedField K p m) (frobeniusFixedField K p n) :=
    Module.natCard_eq_pow_finrank
  rw [card_frobeniusFixedField K p m hm, card_frobeniusFixedField K p n hn, ← pow_mul] at hd
  exact ⟨_, Nat.pow_right_injective (Fact.out : p.Prime).two_le hd⟩

end AlgClosed

section Algebraic

open IntermediateField

variable [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

/-- **Every element of a field algebraic over `𝔽_p` is fixed by some nonzero iterate of the
Frobenius**, because it generates a finite subfield. -/
theorem exists_mem_frobeniusFixedField (x : K) :
    ∃ m ≠ 0, x ∈ frobeniusFixedField K p m := by
  have : FiniteDimensional (ZMod p) (ZMod p)⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite (ZMod p)⟮x⟯ := Module.finite_of_finite (ZMod p)
  have : Fintype (ZMod p)⟮x⟯ := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := _root_.FiniteField.card (ZMod p)⟮x⟯ p
  refine ⟨m, m.ne_zero, ?_⟩
  have hfix :=
    _root_.FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : (ZMod p)⟮x⟯)
  rw [hm] at hfix
  have := congrArg (Subtype.val : (ZMod p)⟮x⟯ → K) hfix
  simpa using this

/-- **A field algebraic over `𝔽_p` is the union of the finite subfields cut out by the
Frobenius.** The exponent is written `m + 1` rather than `m` because the zeroth Frobenius is the
identity, whose fixed subfield is all of `K`; the union over the positive exponents is what carries
content. -/
theorem iSup_frobeniusFixedField : ⨆ m : ℕ, frobeniusFixedField K p (m + 1) = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  obtain ⟨m, hm0, hmem⟩ := exists_mem_frobeniusFixedField K p x
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
    ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hm0)).symm⟩
  exact le_iSup (fun k : ℕ ↦ frobeniusFixedField K p (k + 1)) k hmem

end Algebraic

end TauCeti
