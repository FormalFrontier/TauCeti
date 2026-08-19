/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.LinearAlgebra.RootSystem.BraidRelation

public section

/-!
# The Weyl group of a rank-two root system is dihedral

A base with two simple roots presents its Weyl group by two generators: the two simple reflections
generate it (`TauCeti.weylGroup_eq_closure_simple`), they are involutions, and the order of their
product is the corresponding entry of the Coxeter matrix of the base
(`TauCeti.RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase`). That is exactly
the input of `TauCeti.nonempty_dihedralGroup_mulEquiv`, so the Weyl group *is* the dihedral group
of order twice that entry — and, unlike the presentation of the Weyl group in general, this needs
no completeness statement for the braid relations, since in rank two there is only one of them.

Reading the entry off the Cartan type —
`TauCeti.coxeterMatrixOfBase_eq_six_of_hasCartanType_G2` and its two companions — turns this into
the three rank-two cases. The Weyl groups of the types `A₂`, `B₂`
and `G₂` are the dihedral groups of orders `6`, `8` and `12`, the last of these being the
Weyl-group clause of the `G₂` worked example of the root-systems roadmap.

## Main results

* `TauCeti.nonempty_dihedralGroup_mulEquiv_weylGroup`: **the Weyl group of a base with two simple
  roots is the dihedral group of order twice the Coxeter entry of its two simple roots**, and
  `TauCeti.card_weylGroup_of_card_support_eq_two` is its order.
* `TauCeti.nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_G2`: **a root system of type
  `G₂` has Weyl group the dihedral group of order `12`**, with
  `TauCeti.card_weylGroup_of_hasCartanType_G2` its order; the same for types `A₂` and `B₂`.

## References

This file proves the Weyl-group clause of the `G₂` worked example of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` ("its Weyl group is the dihedral group
of order 12, `P.weylGroup ≃* DihedralGroup 6`"), together with the two other rank-two types. The
computation is the one in N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI §1.3,
and J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §9.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-! ## Two simple reflections generating the Weyl group -/

/-- With two simple roots the two corresponding simple reflections generate the Weyl group. -/
theorem closure_pair_ofIdx_eq_top (hb : b.support.card = 2) {i j : b.support} (hij : i ≠ j) :
    Subgroup.closure ({RootPairing.weylGroup.ofIdx P (i : ι),
      RootPairing.weylGroup.ofIdx P (j : ι)} : Set P.weylGroup) = ⊤ := by
  classical
  have hpair : ({i, j} : Finset b.support) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hij, Fintype.card_coe, hb]
  have hrange : (Set.range fun k : b.support => RootPairing.weylGroup.ofIdx P (k : ι)) =
      ({RootPairing.weylGroup.ofIdx P (i : ι),
        RootPairing.weylGroup.ofIdx P (j : ι)} : Set P.weylGroup) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩
      have hk : k ∈ ({i, j} : Finset b.support) := by rw [hpair]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl)
      exacts [⟨i, rfl⟩, ⟨j, rfl⟩]
  rw [← hrange, ← weylGroup_eq_closure_simple P b]

/-! ## The dihedral structure -/

/-- **The Weyl group of a base with two simple roots is dihedral.** Its order is twice the entry of
the Coxeter matrix of the base at the two simple roots, which is the order of the product of the two
simple reflections.

Only rank two is available this cheaply. In higher rank the braid relations still hold, but that
they *present* the Weyl group is the Coxeter-presentation theorem, which is not proved here; in
rank two the single braid relation is the whole presentation. -/
theorem nonempty_dihedralGroup_mulEquiv_weylGroup (hb : b.support.card = 2) {i j : b.support}
    (hij : i ≠ j) :
    Nonempty (DihedralGroup (coxeterMatrixOfBase P b i j) ≃* P.weylGroup) :=
  nonempty_dihedralGroup_mulEquiv (RootPairing.weylGroup.ofIdx_mul_self P i)
    (RootPairing.weylGroup.ofIdx_mul_self P j) (RootPairing.weylGroup.ofIdx_ne_one P i)
    (RootPairing.weylGroup.ofIdx_ne_one P j)
    (RootPairing.weylGroup.orderOf_ofIdx_mul_ofIdx_eq_coxeterMatrixOfBase P b i j)
    (closure_pair_ofIdx_eq_top P b hb hij)

/-- The Weyl group of a base with two simple roots has order twice the Coxeter entry of those two
roots, read through `DihedralGroup.nat_card`. -/
theorem card_weylGroup_of_card_support_eq_two (hb : b.support.card = 2) {i j : b.support}
    (hij : i ≠ j) :
    Nat.card P.weylGroup = 2 * coxeterMatrixOfBase P b i j := by
  obtain ⟨e⟩ := nonempty_dihedralGroup_mulEquiv_weylGroup P b hb hij
  rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-! ## The three rank-two Cartan types -/

section CartanType

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
/-- A base of a rank-two Cartan type comes with a distinct pair of simple roots. -/
private lemma exists_ne_support (hb : b.support.card = 2) : ∃ i j : b.support, i ≠ j := by
  classical
  obtain ⟨x, y, hxy, hsupp⟩ := Finset.card_eq_two.mp hb
  exact ⟨⟨x, by simp [hsupp]⟩, ⟨y, by simp [hsupp]⟩, by simpa using hxy⟩

/-- **A root system of type `A₂` has Weyl group the symmetric group on three letters**, in the
guise of the dihedral group of order `6`. -/
theorem nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_A_two
    (h : HasCartanType P b (.A 2)) : Nonempty (DihedralGroup 3 ≃* P.weylGroup) := by
  have hb : b.support.card = 2 := by simpa using h.card_support
  obtain ⟨i, j, hij⟩ := exists_ne_support P b hb
  exact coxeterMatrixOfBase_eq_three_of_hasCartanType_A_two P b h hij ▸
    nonempty_dihedralGroup_mulEquiv_weylGroup P b hb hij

/-- **A root system of type `B₂` has Weyl group the dihedral group of order `8`.** -/
theorem nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_B_two
    (h : HasCartanType P b (.B 2)) : Nonempty (DihedralGroup 4 ≃* P.weylGroup) := by
  have hb : b.support.card = 2 := by simpa using h.card_support
  obtain ⟨i, j, hij⟩ := exists_ne_support P b hb
  exact coxeterMatrixOfBase_eq_four_of_hasCartanType_B_two P b h hij ▸
    nonempty_dihedralGroup_mulEquiv_weylGroup P b hb hij

/-- **A root system of type `G₂` has Weyl group the dihedral group of order `12`.** This is the
Weyl-group clause of the `G₂` worked example of the root-systems roadmap. -/
theorem nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_G2
    (h : HasCartanType P b .G2) : Nonempty (DihedralGroup 6 ≃* P.weylGroup) := by
  have hb : b.support.card = 2 := by simpa using h.card_support
  obtain ⟨i, j, hij⟩ := exists_ne_support P b hb
  exact coxeterMatrixOfBase_eq_six_of_hasCartanType_G2 P b h hij ▸
    nonempty_dihedralGroup_mulEquiv_weylGroup P b hb hij

/-- The Weyl group of a root system of type `A₂` has order `6`. -/
theorem card_weylGroup_of_hasCartanType_A_two (h : HasCartanType P b (.A 2)) :
    Nat.card P.weylGroup = 6 := by
  obtain ⟨e⟩ := nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_A_two P b h
  rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- The Weyl group of a root system of type `B₂` has order `8`. -/
theorem card_weylGroup_of_hasCartanType_B_two (h : HasCartanType P b (.B 2)) :
    Nat.card P.weylGroup = 8 := by
  obtain ⟨e⟩ := nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_B_two P b h
  rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- The Weyl group of a root system of type `G₂` has order `12`. -/
theorem card_weylGroup_of_hasCartanType_G2 (h : HasCartanType P b .G2) :
    Nat.card P.weylGroup = 12 := by
  obtain ⟨e⟩ := nonempty_dihedralGroup_mulEquiv_weylGroup_of_hasCartanType_G2 P b h
  rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

end CartanType

end TauCeti
