/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.RingTheory.Valuation.Approximation

/-!
# Weak approximation for the places of an algebraic function field

Finitely many distinct places of a function field `F/k` impose independent conditions on `F`:
given pairwise distinct places `P₁, …, Pₙ`, target functions `f₁, …, fₙ : F` and prescribed
integers `r₁, …, rₙ`, there is a single `g : F` with `ord_{Pᵢ} (g - fᵢ) = rᵢ` for every `i`.
This is the **weak approximation theorem**, Stichtenoth, *Algebraic Function Fields and Codes*,
Theorem 1.3.1, in the equality form; it is `TauCeti.Place.exists_forall_ord_sub_eq`.

The analytic content is not reproved here. `TauCeti.Valuation.exists_forall_sub_eq_exp` already
proves weak approximation for an arbitrary finite family of surjective, pairwise inequivalent
`ℤᵐ⁰`-valued valuations of a field, by way of Mathlib's
`AbsoluteValue.denseRange_algebraMap_pi`. What a place adds is exactly the two hypotheses that
engine consumes: its valuation is surjective by normalization, and distinct places have
inequivalent valuations because a normalized valuation is determined by its equivalence class
(`TauCeti.Place.eq_of_isEquiv`). So the work in this file is to package the conclusion in the
additive `ord` vocabulary and to draw the consequences the divisor theory uses.

Taking all targets to be `0` prescribes the orders themselves
(`TauCeti.Place.exists_forall_ord_eq`), which is the form in which independence of places is
usually met: a function may be asked to have a simple zero at one place and a pole of any
prescribed order at each of finitely many others. Taking all prescribed orders to be `1`
instead makes `g` agree with each target to first order. When the targets are integral, so is
`g`; choosing integral lifts of prescribed residue classes therefore shows that the residue
maps of finitely many distinct places are simultaneously surjective
(`TauCeti.Place.exists_forall_residue_eq`), a Chinese-remainder statement for the places of `F`.

## Main results

* `TauCeti.Place.exists_forall_ord_sub_eq`: **weak approximation** (Stichtenoth, Theorem 1.3.1).
* `TauCeti.Place.exists_forall_ord_eq` and `TauCeti.Place.exists_ne_zero_forall_ord_eq`:
  prescribed orders at finitely many distinct places, by an arbitrary and by a nonzero function.
* `TauCeti.Place.exists_ord_eq_one_and_forall_mem_ord_eq_zero`: a function with a simple zero at
  a given place which is a unit at each of finitely many other places.
* `TauCeti.Place.exists_mem_integers_notMem_integers`: the valuation rings of two distinct
  places are incomparable.
* `TauCeti.Place.exists_forall_residue_eq`: simultaneous surjectivity of the residue maps of
  finitely many distinct places.

## Implementation notes

The families are indexed by a `Finite` type together with an injective map to `Place k F`,
matching the shape of the approximation engine. The `Finset` restatements
(`TauCeti.Place.exists_forall_mem_ord_sub_eq` and
`TauCeti.Place.exists_forall_mem_ord_eq`) are what the divisor theory, which meets places as
elements of the support of a divisor rather than as a numbered list, actually applies.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.3.
-/

public section

open scoped WithZero

namespace TauCeti.Place

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

section Approximation

variable {ι : Type*} [Finite ι] {P : ι → Place k F}

/-- **The weak approximation theorem** for the places of an algebraic function field
(Stichtenoth, Theorem 1.3.1), in the equality form: for finitely many pairwise distinct places
`P i`, arbitrary target functions `f i` and arbitrary prescribed integers `r i`, some single
`g : F` satisfies `ord_{P i} (g - f i) = r i` for every `i`.

The prescription is an equality, not an inequality: the error `g - f i` is not merely small at
`P i`, its order there is exactly `r i`. In particular `g - f i ≠ 0` whenever `r i ≠ 0`. -/
theorem exists_forall_ord_sub_eq (hP : Function.Injective P) (f : ι → F) (r : ι → ℤ) :
    ∃ g : F, ∀ i, (P i).ord (g - f i) = r i := by
  obtain ⟨g, hg⟩ :=
    Valuation.exists_forall_sub_eq_exp (fun i ↦ (P i).valuation)
      (fun i ↦ (P i).valuation_surjective)
      (fun _ _ hij ↦ by simpa only [valuation_isEquiv_iff] using hP.ne hij) f r
  refine ⟨g, fun i ↦ ?_⟩
  have hne : g - f i ≠ 0 :=
    (P i).valuation.ne_zero_iff.mp (by rw [hg i]; exact WithZero.exp_ne_zero)
  exact ((P i).ord_eq_iff_valuation_eq_exp_neg hne).mpr (hg i)

/-- **Prescribed orders**: the orders of a function at finitely many distinct places may be
prescribed arbitrarily and independently. This is weak approximation with all targets `0`, and
it is the statement that finitely many places of `F` are independent. -/
theorem exists_forall_ord_eq (hP : Function.Injective P) (r : ι → ℤ) :
    ∃ g : F, ∀ i, (P i).ord g = r i := by
  simpa using exists_forall_ord_sub_eq hP 0 r

/-- Prescribed orders realized by a *nonzero* function, which is the form the principal-divisor
map `Fˣ → Divisor k F` consumes. Because `ord_P` has the junk value `ord_P 0 = 0`, the witness
of `TauCeti.Place.exists_forall_ord_eq` can only fail to be nonzero when every prescribed order
is `0`, and then a constant serves. -/
theorem exists_ne_zero_forall_ord_eq (hP : Function.Injective P) (r : ι → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ i, (P i).ord g = r i := by
  obtain ⟨g, hg⟩ := exists_forall_ord_eq hP r
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨1, one_ne_zero, fun i ↦ by simpa using hg i⟩
  · exact ⟨g, hg0, hg⟩

/-- Weak approximation for a finite *set* of places, which is how the divisor theory meets
them: the places of the support of a divisor carry no numbering. -/
theorem exists_forall_mem_ord_sub_eq (s : Finset (Place k F)) (f : Place k F → F)
    (r : Place k F → ℤ) : ∃ g : F, ∀ P ∈ s, P.ord (g - f P) = r P := by
  obtain ⟨g, hg⟩ :=
    exists_forall_ord_sub_eq (P := fun P : {P // P ∈ s} ↦ (P : Place k F)) Subtype.val_injective
      (fun P ↦ f P) (fun P ↦ r P)
  exact ⟨g, fun P hP ↦ hg ⟨P, hP⟩⟩

/-- Prescribed orders along a finite set of places. -/
theorem exists_forall_mem_ord_eq (s : Finset (Place k F)) (r : Place k F → ℤ) :
    ∃ g : F, ∀ P ∈ s, P.ord g = r P := by
  simpa using exists_forall_mem_ord_sub_eq s 0 r

/-- Prescribed orders along a finite set of places, realized by a nonzero function. -/
theorem exists_ne_zero_forall_mem_ord_eq (s : Finset (Place k F)) (r : Place k F → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ P ∈ s, P.ord g = r P := by
  obtain ⟨g, hg0, hg⟩ :=
    exists_ne_zero_forall_ord_eq (P := fun P : {P // P ∈ s} ↦ (P : Place k F))
      Subtype.val_injective fun P ↦ r P
  exact ⟨g, hg0, fun P hP ↦ hg ⟨P, hP⟩⟩

end Approximation

section Independence

variable (P : Place k F) (s : Finset (Place k F))

/-- A **global uniformizer** at a place, away from finitely many others: some `t : F` has a
simple zero at `P` and is a unit of the valuation ring of every other place of `s`. Such a `t`
is in particular a prime element at `P` (`TauCeti.Place.isUniformizer_iff_ord_eq_one`), so a
uniformizer may always be chosen to interfere with no prescribed finite set of places. -/
theorem exists_ord_eq_one_and_forall_mem_ord_eq_zero :
    ∃ t : F, P.ord t = 1 ∧ ∀ Q ∈ s, Q ≠ P → Q.ord t = 0 := by
  classical
  obtain ⟨t, ht⟩ := exists_forall_mem_ord_eq (insert P s) fun Q ↦ if Q = P then 1 else 0
  refine ⟨t, ?_, fun Q hQ hQP ↦ ?_⟩
  · simpa using ht P (Finset.mem_insert_self P s)
  · simpa [hQP] using ht Q (Finset.mem_insert_of_mem hQ)

variable {P}

/-- Two distinct places are independent already on their own: some function has a zero at one
and a pole at the other. -/
theorem exists_ord_pos_and_ord_neg {Q : Place k F} (h : P ≠ Q) :
    ∃ g : F, 0 < P.ord g ∧ Q.ord g < 0 := by
  classical
  obtain ⟨g, hg⟩ :=
    exists_forall_mem_ord_eq ({P, Q} : Finset (Place k F)) fun R ↦ if R = P then 1 else -1
  refine ⟨g, ?_, ?_⟩
  · have hgP : P.ord g = 1 := by simpa using hg P (Finset.mem_insert_self P {Q})
    omega
  · have hgQ : Q.ord g = -1 := by simpa [h.symm] using hg Q (by simp)
    omega

/-- The valuation rings of two distinct places are incomparable: neither contains the other.
Together with `TauCeti.Place.integers_injective` this is the sense in which the places of `F`
are its maximal proper subrings containing `k`, no two of them comparable (Stichtenoth,
Theorem 1.1.13). -/
theorem exists_mem_integers_notMem_integers {Q : Place k F} (h : P ≠ Q) :
    ∃ g : F, g ∈ P.integers ∧ g ∉ Q.integers := by
  obtain ⟨g, hgP, hgQ⟩ := exists_ord_pos_and_ord_neg h
  exact ⟨g, P.mem_integers_iff_ord_nonneg.mpr hgP.le,
    fun hg ↦ absurd (Q.mem_integers_iff_ord_nonneg.mp hg) (by omega)⟩

end Independence

section Residues

variable {ι : Type*} [Finite ι] {P : ι → Place k F}

/-- **Approximation to first order**: some `g : F` agrees with a prescribed target at each of
finitely many distinct places to first order, that is, up to an element of the maximal ideal
there. -/
theorem exists_forall_valuation_sub_lt_one (hP : Function.Injective P) (z : ι → F) :
    ∃ g : F, ∀ i, (P i).valuation (g - z i) < 1 := by
  obtain ⟨g, hg⟩ := exists_forall_ord_sub_eq hP z fun _ ↦ 1
  refine ⟨g, fun i ↦ ?_⟩
  have hi := hg i
  have hne : g - z i ≠ 0 := fun h ↦ by simp [h] at hi
  rw [(P i).valuation_eq_exp_neg_ord hne, hi, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/-- **Simultaneous evaluation** at finitely many distinct places: any prescribed family of
residues, one in the residue field of each place, is realized by a single function of `F` that
is integral at all of them. Equivalently, the residue maps of finitely many distinct places are
jointly surjective on `⋂ᵢ 𝒪_{P i}`; this is the Chinese remainder theorem for the places of a
function field. -/
theorem exists_forall_residue_eq (hP : Function.Injective P) (y : ∀ i, (P i).ResidueField) :
    ∃ g : F, ∃ hg : ∀ i, g ∈ (P i).integers,
      ∀ i, IsLocalRing.residue (P i).integers ⟨g, hg i⟩ = y i := by
  choose z hz using fun i ↦ IsLocalRing.residue_surjective (y i)
  obtain ⟨g, hg⟩ := exists_forall_valuation_sub_lt_one hP fun i ↦ (z i : F)
  have hsub : ∀ i, g - (z i : F) ∈ (P i).integers := fun i ↦
    (P i).mem_integers_iff.mpr (hg i).le
  have hmem : ∀ i, g ∈ (P i).integers := by
    intro i
    have : g = g - (z i : F) + (z i : F) := by ring
    rw [this]
    exact add_mem (hsub i) (z i).2
  refine ⟨g, hmem, fun i ↦ ?_⟩
  have key : IsLocalRing.residue (P i).integers (⟨g, hmem i⟩ - z i) = 0 := by
    rw [(P i).residue_eq_zero_iff_valuation_lt_one]
    simpa using hg i
  rw [map_sub, sub_eq_zero] at key
  rw [key, hz i]

end Residues

end TauCeti.Place
