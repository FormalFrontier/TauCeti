/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.GroupAction.Burnside
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Double cosets as the orbits of a group on a product of coset spaces

For subgroups `H` and `K` of a group `G`, the diagonal action of `G` on `(G ⧸ H) × (G ⧸ K)` has
orbits in bijection with the double cosets `H \ G / K`: the orbit of `(aH, bK)` is recorded by the
double coset `H a⁻¹ b K`, and every orbit meets the slice `{(H, gK) | g : G}`.

Combining that bijection with Burnside's lemma counts double cosets by a sum of fixed-point
numbers, which is the group-theoretic half of the statement that the permutation character of
`G` on `G ⧸ H` pairs with the permutation character on `G ⧸ K` to `#(H \ G / K)`.

## Main definitions

* `TauCeti.doubleCosetEquivOrbitQuotient`: the bijection
  `H \ G / K ≃ ((G ⧸ H) × (G ⧸ K)) / G`.

## Main statements

* `TauCeti.card_doubleCosetQuotient_eq_card_orbitQuotient`: the two sides of that bijection have
  the same cardinality.
* `TauCeti.sum_card_fixedBy_mul_card_fixedBy_eq_card_doubleCosetQuotient_mul_card_group`:
  Burnside's lemma read through that bijection,
  `∑ g, |(G ⧸ H)^g| * |(G ⧸ K)^g| = #(H \ G / K) * |G|`.

## Implementation notes

Mathlib's `DoubleCoset.Quotient (H : Set G) K` takes the two subgroups as sets, and its
representatives multiply as `h * a * k`. The bijection below is built from the slice map
`g ↦ orbit of (H, gK)`, which is surjective because `a • (H, a⁻¹bK) = (aH, bK)`, and injective
because the pair `(aH, bK)` determines `H a⁻¹ b K`.

## References

This supplies the "`⟨Ind_H^G 1, Ind_H^G 1⟩_G = #(H \ G / H)`" item of Layer 2 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` with its group-theoretic
input.

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.3.
-/

public section

open MulAction

namespace TauCeti

variable {G : Type*} [Group G]

section Orbits

variable (H K : Subgroup G)

/-- The orbit of the pair of cosets `(H, gK)` under the diagonal action of `G` on
`(G ⧸ H) × (G ⧸ K)`. Every orbit is of this form, and `doubleCosetOrbit_eq_iff` says that the
double coset `HgK` is a complete invariant of it. -/
def doubleCosetOrbit (g : G) : orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K)) :=
  Quotient.mk'' (((1 : G) : G ⧸ H), ((g : G) : G ⧸ K))

variable {H K}

/-- Two points of the slice `{(H, gK) | g : G}` lie in the same orbit exactly when their labels
lie in the same double coset. -/
@[simp]
theorem doubleCosetOrbit_eq_iff {a b : G} :
    doubleCosetOrbit H K a = doubleCosetOrbit H K b ↔
      DoubleCoset.mk H K a = DoubleCoset.mk H K b := by
  rw [doubleCosetOrbit, doubleCosetOrbit, Quotient.eq'', eq_comm, DoubleCoset.eq]
  constructor
  · rintro ⟨g, hg⟩
    rw [Prod.ext_iff] at hg
    obtain ⟨hg₁, hg₂⟩ := hg
    have hgH : g ∈ H := by simpa using H.inv_mem (QuotientGroup.eq.mp hg₁)
    refine ⟨g, hgH, (g * b)⁻¹ * a, QuotientGroup.eq.mp hg₂, ?_⟩
    simp [mul_assoc]
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨h, ?_⟩
    rw [Prod.ext_iff]
    exact ⟨QuotientGroup.eq.mpr (by simpa using H.inv_mem hh),
      QuotientGroup.eq.mpr (by simpa [mul_assoc] using hk)⟩

variable (H K)

/-- **Double cosets are orbits.** The double cosets `H \ G / K` are in bijection with the orbits
of `G` acting diagonally on `(G ⧸ H) × (G ⧸ K)`, the double coset of `g` corresponding to the
orbit of `(H, gK)`. -/
noncomputable def doubleCosetEquivOrbitQuotient :
    DoubleCoset.Quotient (H : Set G) K ≃ orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K)) :=
  Equiv.ofBijective
    (Quotient.lift (doubleCosetOrbit H K)
      fun _ _ hab => doubleCosetOrbit_eq_iff.mpr (Quotient.sound hab))
    ⟨by
      refine fun x y => Quotient.inductionOn₂ x y fun a b hab => ?_
      exact doubleCosetOrbit_eq_iff.mp hab, by
      refine fun x => Quotient.inductionOn x fun p => ?_
      obtain ⟨x, y⟩ := p
      refine QuotientGroup.induction_on x fun a => QuotientGroup.induction_on y fun b => ?_
      refine ⟨DoubleCoset.mk H K (a⁻¹ * b), Quotient.sound ⟨a⁻¹, ?_⟩⟩
      rw [Prod.ext_iff]
      exact ⟨by simp, by simp⟩⟩

@[simp]
theorem doubleCosetEquivOrbitQuotient_apply_mk (g : G) :
    doubleCosetEquivOrbitQuotient H K (DoubleCoset.mk H K g) = doubleCosetOrbit H K g :=
  -- The parentheses keep this out of `@[defeq]` inference: the proof is `rfl`, but the two sides
  -- are only definitionally equal after unfolding the (unexposed) definitions above.
  (rfl)

/-- The number of double cosets `H \ G / K` is the number of orbits of `G` on
`(G ⧸ H) × (G ⧸ K)`. -/
theorem card_doubleCosetQuotient_eq_card_orbitQuotient :
    Nat.card (DoubleCoset.Quotient (H : Set G) K) =
      Nat.card (orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K))) :=
  Nat.card_congr (doubleCosetEquivOrbitQuotient H K)

end Orbits

/-- **Double cosets are counted by fixed cosets.** For a finite group `G` and subgroups `H` and
`K`, the sum over `g : G` of the number of cosets of `H` fixed by `g` times the number of cosets
of `K` fixed by `g` is the number of double cosets `H \ G / K`, times the order of `G`. -/
theorem sum_card_fixedBy_mul_card_fixedBy_eq_card_doubleCosetQuotient_mul_card_group
    [Fintype G] (H K : Subgroup G) :
    ∑ g : G, Nat.card (fixedBy (G ⧸ H) g) * Nat.card (fixedBy (G ⧸ K) g) =
      Nat.card (DoubleCoset.Quotient (H : Set G) K) * Nat.card G := by
  have : Finite G := Finite.of_fintype G
  rw [card_doubleCosetQuotient_eq_card_orbitQuotient]
  exact sum_card_fixedBy_mul_card_fixedBy_eq_card_orbits_mul_card_group (G ⧸ H) (G ⧸ K)

end TauCeti
