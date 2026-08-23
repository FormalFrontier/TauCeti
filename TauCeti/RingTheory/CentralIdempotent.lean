/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.SimpleRing.Field
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Central idempotents

A **central idempotent** of a ring `R` is an element `e` with `e * e = e` that commutes with
everything.  Such an element splits `R` as a product of the two rings `eR` and `(1 - e)R`, so the
central idempotents record how far `R` is from being indecomposable as a ring.

This file collects the three facts that make `TauCeti.centralIdempotents` a *counting* invariant.
It is preserved by ring isomorphisms (`TauCeti.centralIdempotentsCongr`); it is computed
coordinatewise on a product (`TauCeti.centralIdempotentsPiEquiv`); and a simple ring has exactly
two of them, `0` and `1` (`TauCeti.centralIdempotents_eq_pair`).  Together these say that a finite
product of simple rings has exactly `2 ^ (number of factors)` central idempotents
(`TauCeti.card_centralIdempotents_pi_of_isSimpleRing`), so the number of factors can be read off
the isomorphism class of the ring alone; `TauCeti/RingTheory/Semisimple/BlockCount.lean` draws that
conclusion.

Mathlib has `IsIdempotentElem` and the orthogonal decompositions of `1` it generates
(`Mathlib/RingTheory/Idempotents.lean`), and `Subring.center`, but nothing about the idempotents
that are also central.  The one nontrivial ingredient below,
`TauCeti.centralIdempotents_eq_pair`, is the observation that a central idempotent of `R` is an
idempotent of `Subring.center R`, which for simple `R` is a field by
`IsSimpleRing.isField_center`; a field has only the idempotents `0` and `1`.

## Main definitions

* `TauCeti.centralIdempotents R`: the set of central idempotents of `R`.
* `TauCeti.centralIdempotentsCongr`: a ring isomorphism `R ≃+* S` restricts to an equivalence
  between the central idempotents of `R` and those of `S`.
* `TauCeti.centralIdempotentsPiEquiv`: the central idempotents of a product of rings are the
  families of central idempotents of the factors.

## Main results

* `TauCeti.centralIdempotents_eq_pair`: **a simple ring has exactly the two central idempotents
  `0` and `1`**, and `TauCeti.card_centralIdempotents_of_isSimpleRing` counts them.
* `TauCeti.card_centralIdempotents_pi`: the count is multiplicative over a finite product, whence
  `TauCeti.card_centralIdempotents_pi_of_isSimpleRing`: a finite product of simple rings has
  `2 ^ (number of factors)` central idempotents.

## Implementation notes

`centralIdempotents R` is a `Set R` rather than a subtype or a bundled structure: the only thing
done with it here is to transport it along isomorphisms and to count it, and `Nat.card` of the
coercion is the count.  Centrality is spelled as membership in `Subring.center R`, which is
Mathlib's canonical form; `TauCeti.mul_comm_of_mem_centralIdempotents` unpacks it to the bare
commutation equation.
-/

public section

namespace TauCeti

variable {R S : Type*} [Ring R] [Ring S]

/-- The set of **central idempotents** of a ring: the idempotents lying in the centre. -/
def centralIdempotents (R : Type*) [Ring R] : Set R :=
  {e | IsIdempotentElem e ∧ e ∈ Subring.center R}

-- Not `@[simp]`: unfolding membership everywhere would rewrite the left-hand side of
-- `mem_centralIdempotents_pi` below, so only one of the two can be a simp lemma, and the
-- coordinatewise form is the useful normal form.
theorem mem_centralIdempotents {e : R} :
    e ∈ centralIdempotents R ↔ IsIdempotentElem e ∧ e ∈ Subring.center R := (Iff.rfl)

/-- A central idempotent is idempotent. -/
theorem isIdempotentElem_of_mem_centralIdempotents {e : R} (he : e ∈ centralIdempotents R) :
    IsIdempotentElem e :=
  he.1

/-- A central idempotent commutes with every element. -/
theorem mul_comm_of_mem_centralIdempotents {e : R} (he : e ∈ centralIdempotents R) (x : R) :
    e * x = x * e :=
  (Subring.mem_center_iff.mp he.2 x).symm

theorem zero_mem_centralIdempotents : (0 : R) ∈ centralIdempotents R :=
  ⟨IsIdempotentElem.zero, Subring.zero_mem _⟩

theorem one_mem_centralIdempotents : (1 : R) ∈ centralIdempotents R :=
  ⟨IsIdempotentElem.one, Subring.one_mem _⟩

section Congr

/-- A ring isomorphism preserves central idempotents. -/
theorem map_mem_centralIdempotents (f : R ≃+* S) {e : R} (he : e ∈ centralIdempotents R) :
    f e ∈ centralIdempotents S :=
  ⟨he.1.map f, MulEquivClass.apply_mem_center f he.2⟩

/-- **A ring isomorphism restricts to a bijection of central idempotents.** -/
def centralIdempotentsCongr (f : R ≃+* S) : centralIdempotents R ≃ centralIdempotents S where
  toFun e := ⟨f e, map_mem_centralIdempotents f e.2⟩
  invFun e := ⟨f.symm e, map_mem_centralIdempotents f.symm e.2⟩
  left_inv e := Subtype.ext (f.symm_apply_apply e)
  right_inv e := Subtype.ext (f.apply_symm_apply e)

@[simp]
theorem coe_centralIdempotentsCongr_apply (f : R ≃+* S) (e : centralIdempotents R) :
    (centralIdempotentsCongr f e : S) = f e := (rfl)

@[simp]
theorem coe_centralIdempotentsCongr_symm_apply (f : R ≃+* S) (e : centralIdempotents S) :
    ((centralIdempotentsCongr f).symm e : R) = f.symm e := (rfl)

/-- Isomorphic rings have the same number of central idempotents. -/
theorem card_centralIdempotents_congr (f : R ≃+* S) :
    Nat.card (centralIdempotents R) = Nat.card (centralIdempotents S) :=
  Nat.card_congr (centralIdempotentsCongr f)

end Congr

section Pi

variable {ι : Type*} (A : ι → Type*) [∀ i, Ring (A i)]

/-- Both halves of being a central idempotent are coordinatewise conditions on a product of
rings. -/
@[simp]
theorem mem_centralIdempotents_pi {e : ∀ i, A i} :
    e ∈ centralIdempotents (∀ i, A i) ↔ ∀ i, e i ∈ centralIdempotents (A i) := by
  have hcenter : e ∈ Subring.center (∀ i, A i) ↔ ∀ i, e i ∈ Subring.center (A i) := by
    rw [← SetLike.mem_coe, Subring.coe_center, Set.center_pi, Set.mem_univ_pi]
    exact forall_congr' fun _ => Iff.rfl
  simp only [mem_centralIdempotents, hcenter, IsIdempotentElem, funext_iff, Pi.mul_apply,
    ← forall_and]

/-- **The central idempotents of a product of rings are the families of central idempotents.** -/
def centralIdempotentsPiEquiv :
    centralIdempotents (∀ i, A i) ≃ ∀ i, centralIdempotents (A i) :=
  (Equiv.subtypeEquivRight fun _ => mem_centralIdempotents_pi A).trans Equiv.subtypePiEquivPi

@[simp]
theorem coe_centralIdempotentsPiEquiv_apply (e : centralIdempotents (∀ i, A i)) (i : ι) :
    (centralIdempotentsPiEquiv A e i : A i) = (e : ∀ i, A i) i := (rfl)

@[simp]
theorem coe_centralIdempotentsPiEquiv_symm_apply (e : ∀ i, centralIdempotents (A i)) (i : ι) :
    ((centralIdempotentsPiEquiv A).symm e : ∀ i, A i) i = (e i : A i) := (rfl)

/-- The number of central idempotents is multiplicative over a finite product of rings. -/
theorem card_centralIdempotents_pi [Fintype ι] :
    Nat.card (centralIdempotents (∀ i, A i)) = ∏ i, Nat.card (centralIdempotents (A i)) :=
  (Nat.card_congr (centralIdempotentsPiEquiv A)).trans Nat.card_pi

end Pi

section IsSimpleRing

variable (R) in
/-- **A simple ring has exactly two central idempotents, `0` and `1`.**

A central idempotent of `R` is exactly an idempotent of the subring `Subring.center R`, which is a
field because `R` is simple (`IsSimpleRing.isField_center`); and a field has no idempotents besides
`0` and `1` (`IsIdempotentElem.iff_eq_zero_or_one`). -/
theorem centralIdempotents_eq_pair [IsSimpleRing R] : centralIdempotents R = {0, 1} := by
  let _ := (IsSimpleRing.isField_center R).toField
  refine Set.eq_of_subset_of_subset (fun e he => ?_) ?_
  · have hidem : IsIdempotentElem (⟨e, he.2⟩ : Subring.center R) := Subtype.ext he.1
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h | h
    · exact Or.inl (by simpa [Subtype.ext_iff] using h)
    · exact Or.inr (by simpa [Subtype.ext_iff] using h)
  · rintro e (rfl | rfl)
    · exact zero_mem_centralIdempotents
    · exact one_mem_centralIdempotents

variable (R) in
/-- A simple ring has exactly two central idempotents. -/
theorem card_centralIdempotents_of_isSimpleRing [IsSimpleRing R] :
    Nat.card (centralIdempotents R) = 2 := by
  rw [centralIdempotents_eq_pair R, Nat.card_coe_set_eq, Set.ncard_pair zero_ne_one]

/-- A finite product of simple rings has `2 ^ (number of factors)` central idempotents: one
independent binary choice per factor. -/
theorem card_centralIdempotents_pi_of_isSimpleRing {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)] :
    Nat.card (centralIdempotents (∀ i, A i)) = 2 ^ Nat.card ι := by
  have := Fintype.ofFinite ι
  rw [card_centralIdempotents_pi A, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.prod_const]
  exact Finset.prod_congr rfl fun i _ => card_centralIdempotents_of_isSimpleRing (A i)

end IsSimpleRing

end TauCeti
