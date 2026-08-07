/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.SimpleRing.Basic
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
product of simple rings has exactly `2 ^ (number of factors)` central idempotents, so the number of
factors can be read off the isomorphism class of the ring alone;
`TauCeti/RingTheory/Semisimple/BlockCount.lean` draws that conclusion.

Mathlib has `IsIdempotentElem` and the orthogonal decompositions of `1` it generates
(`Mathlib/RingTheory/Idempotents.lean`), and `Subring.center`, but nothing about the idempotents
that are also central.  The one nontrivial ingredient below,
`TauCeti.centralIdempotents_eq_pair`, is the observation that for a central idempotent `e` the
principal left ideal `eR = {x | e * x = x}` is automatically **two-sided**, so simplicity of `R`
pins it down to `⊥` or `⊤`, which forces `e = 0` or `e = 1`.

## Main definitions

* `TauCeti.centralIdempotents R`: the set of central idempotents of `R`.
* `TauCeti.centralIdempotentsCongr`: a ring isomorphism `R ≃+* S` restricts to an equivalence
  between the central idempotents of `R` and those of `S`.
* `TauCeti.centralIdempotentsPiEquiv`: the central idempotents of a product of rings are the
  families of central idempotents of the factors.

## Main results

* `TauCeti.centralIdempotents_eq_pair`: **a simple ring has exactly the two central idempotents
  `0` and `1`**, and `TauCeti.card_centralIdempotents_of_isSimpleRing` counts them.
* `TauCeti.card_centralIdempotents_pi`: the count is multiplicative over a finite product.

## Implementation notes

`centralIdempotents R` is a `Set R` rather than a subtype or a bundled structure: the only thing
done with it here is to transport it along isomorphisms and to count it, and `Nat.card` of the
coercion is the count.  Centrality is spelled as membership in `Subring.center R`, which is
Mathlib's canonical form; `TauCeti.mul_comm_of_mem_centralIdempotents` unpacks it to the
commutation equation every proof below actually uses.
-/

public section

namespace TauCeti

variable {R S : Type*} [Ring R] [Ring S]

/-- The set of **central idempotents** of a ring: the idempotents lying in the centre. -/
def centralIdempotents (R : Type*) [Ring R] : Set R :=
  {e | IsIdempotentElem e ∧ e ∈ Subring.center R}

@[simp]
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
    f e ∈ centralIdempotents S := by
  refine ⟨he.1.map f, Subring.mem_center_iff.mpr fun y => ?_⟩
  obtain ⟨x, rfl⟩ := f.surjective y
  rw [← map_mul, ← map_mul, mul_comm_of_mem_centralIdempotents he]

/-- **A ring isomorphism restricts to a bijection of central idempotents.** -/
def centralIdempotentsCongr (f : R ≃+* S) : centralIdempotents R ≃ centralIdempotents S where
  toFun e := ⟨f e, map_mem_centralIdempotents f e.2⟩
  invFun e := ⟨f.symm e, map_mem_centralIdempotents f.symm e.2⟩
  left_inv e := Subtype.ext (f.symm_apply_apply e)
  right_inv e := Subtype.ext (f.apply_symm_apply e)

@[simp]
theorem coe_centralIdempotentsCongr_apply (f : R ≃+* S) (e : centralIdempotents R) :
    (centralIdempotentsCongr f e : S) = f e := (rfl)

/-- Isomorphic rings have the same number of central idempotents. -/
theorem card_centralIdempotents_congr (f : R ≃+* S) :
    Nat.card (centralIdempotents R) = Nat.card (centralIdempotents S) :=
  Nat.card_congr (centralIdempotentsCongr f)

end Congr

section Pi

variable {ι : Type*} (A : ι → Type*) [∀ i, Ring (A i)]

/-- Both halves of being a central idempotent are coordinatewise conditions on a product of
rings. -/
theorem mem_centralIdempotents_pi {e : ∀ i, A i} :
    e ∈ centralIdempotents (∀ i, A i) ↔ ∀ i, e i ∈ centralIdempotents (A i) := by
  classical
  constructor
  · refine fun he i => ⟨congrFun he.1 i, Subring.mem_center_iff.mpr fun a => ?_⟩
    -- Test centrality of `e` against the family supported at `i` with value `a`.
    have := congrFun (Subring.mem_center_iff.mp he.2 (Pi.single i a)) i
    simpa using this
  · exact fun he =>
      ⟨funext fun i => (he i).1, Subring.mem_center_iff.mpr fun x =>
        funext fun i => Subring.mem_center_iff.mp (he i).2 (x i)⟩

/-- **The central idempotents of a product of rings are the families of central idempotents.** -/
def centralIdempotentsPiEquiv :
    centralIdempotents (∀ i, A i) ≃ ∀ i, centralIdempotents (A i) :=
  (Equiv.subtypeEquivRight fun _ => mem_centralIdempotents_pi A).trans Equiv.subtypePiEquivPi

@[simp]
theorem coe_centralIdempotentsPiEquiv_apply (e : centralIdempotents (∀ i, A i)) (i : ι) :
    (centralIdempotentsPiEquiv A e i : A i) = (e : ∀ i, A i) i := (rfl)

/-- The number of central idempotents is multiplicative over a finite product of rings. -/
theorem card_centralIdempotents_pi [Fintype ι] :
    Nat.card (centralIdempotents (∀ i, A i)) = ∏ i, Nat.card (centralIdempotents (A i)) :=
  (Nat.card_congr (centralIdempotentsPiEquiv A)).trans Nat.card_pi

end Pi

section IsSimpleRing

variable (R) in
/-- **A simple ring has exactly two central idempotents, `0` and `1`.**

For a central idempotent `e` the principal left ideal `eR = {x | e * x = x}` is two-sided, because
`e` commutes past the multiplier on either side.  Simplicity leaves it two values: it is `⊥`, and
then `e` — which lies in it — is `0`; or it is `⊤`, and then `1` lies in it, which says `e = 1`. -/
theorem centralIdempotents_eq_pair [IsSimpleRing R] : centralIdempotents R = {0, 1} := by
  refine Set.eq_of_subset_of_subset (fun e he => ?_) ?_
  · have hcomm := mul_comm_of_mem_centralIdempotents he
    have hset : ∀ x : R, x ∈ {y : R | e * y = y} ↔ e * x = x := fun x => by
      rw [Set.mem_ofPred_eq]
    -- The principal left ideal `eR = {x | e * x = x}`, two-sided because `e` is central.
    obtain ⟨I, hI⟩ : ∃ I : TwoSidedIdeal R, ∀ x : R, x ∈ I ↔ e * x = x :=
      ⟨TwoSidedIdeal.mk' {y : R | e * y = y}
        ((hset 0).mpr (mul_zero e))
        (fun {x y} hx hy =>
          (hset _).mpr (by rw [mul_add, (hset x).mp hx, (hset y).mp hy]))
        (fun {x} hx => (hset _).mpr (by rw [mul_neg, (hset x).mp hx]))
        (fun {x y} hy =>
          (hset _).mpr (by rw [← mul_assoc, hcomm x, mul_assoc, (hset y).mp hy]))
        (fun {x y} hx => (hset _).mpr (by rw [← mul_assoc, (hset x).mp hx])),
        fun x => by rw [TwoSidedIdeal.mem_mk']; exact hset x⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases IsSimpleOrder.eq_bot_or_eq_top I with h | h
    · exact Or.inl (by simpa [h] using (hI e).mpr he.1)
    · exact Or.inr (by simpa using (hI 1).mp (by simp [h]))
  · rintro e (rfl | rfl)
    · exact zero_mem_centralIdempotents
    · exact one_mem_centralIdempotents

variable (R) in
/-- A simple ring has exactly two central idempotents. -/
theorem card_centralIdempotents_of_isSimpleRing [IsSimpleRing R] :
    Nat.card (centralIdempotents R) = 2 := by
  rw [centralIdempotents_eq_pair R, Nat.card_coe_set_eq, Set.ncard_pair zero_ne_one]

end IsSimpleRing

end TauCeti
