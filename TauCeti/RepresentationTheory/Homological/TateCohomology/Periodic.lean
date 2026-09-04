/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Positive Tate cohomology of finite cyclic groups

For a finite cyclic group, the standard periodic resolution alternates the norm map with
`g - 1`, where `g` is a chosen generator. Consequently all positive Tate cohomology groups of a
fixed parity are isomorphic: even degrees are the homology of

`M --N--> M --(g - 1)--> M`,

and odd degrees are the homology of the same two maps in the opposite order.

Mathlib already constructs this periodic resolution and identifies its homology with ordinary
group cohomology. It also identifies positive Tate cohomology with ordinary group cohomology.
This file composes those two canonical comparisons and records the resulting positive-degree
periodicity. The degree-zero and negative-degree comparisons are separate low-degree questions.

## Provenance

The corresponding all-degree construction is `Rep.periodicTateCohomology` in
`ClassFieldTheory/Cohomology/FiniteCyclic/UpDown.lean` from `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`. Its positive-degree specialization has the same
mathematical content as the periodicity below, expressed through the periodic-resolution
calculations `Rep.FiniteCyclicGroup.groupCohomologyIsoEven` and `groupCohomologyIsoOdd`.

## Main definitions

* `Rep.FiniteCyclicGroup.positiveEvenIso`: the common explicit model for positive even
  degrees.
* `Rep.FiniteCyclicGroup.positiveOddIso`: the common explicit model for positive odd
  degrees.
* `Rep.FiniteCyclicGroup.positivePeriodicIso`: the two-periodicity isomorphism between
  positive degrees of the same parity.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §2.
* J.-P. Serre, *Local Fields*, Chapter VIII, §4.
-/

public noncomputable section

universe u

open CategoryTheory

namespace Rep.FiniteCyclicGroup

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- In a positive even degree, Tate cohomology of a finite cyclic group is the homology of
`M --N--> M --(g - 1)--> M` for a chosen generator `g`.

The isomorphism is the composite of Mathlib's Tate-to-ordinary-cohomology comparison and its
calculation from the standard periodic resolution. -/
def positiveEvenIso (M : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) [NeZero n] (hn : Even n) :
    let _ : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.zpowers g).eq_top_iff'.mpr hg⟩
    let _ : CommGroup G := IsCyclic.commGroup
    tateCohomology M n ≅ (_root_.Rep.FiniteCyclicGroup.normHomCompSub M g).homology := by
  letI : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨g, (Subgroup.zpowers g).eq_top_iff'.mpr hg⟩
  letI : CommGroup G := IsCyclic.commGroup
  exact (_root_.TateCohomology.isoGroupCohomology n).app M ≪≫
    _root_.Rep.FiniteCyclicGroup.groupCohomologyIsoEven M g hg n hn

/-- In a positive odd degree, Tate cohomology of a finite cyclic group is the homology of
`M --(g - 1)--> M --N--> M` for a chosen generator `g`.

The isomorphism is the composite of Mathlib's Tate-to-ordinary-cohomology comparison and its
calculation from the standard periodic resolution. -/
def positiveOddIso (M : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : Odd n) :
    let _ : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.zpowers g).eq_top_iff'.mpr hg⟩
    let _ : CommGroup G := IsCyclic.commGroup
    tateCohomology M n ≅ (_root_.Rep.FiniteCyclicGroup.subCompNormHom M g).homology := by
  letI : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨g, (Subgroup.zpowers g).eq_top_iff'.mpr hg⟩
  letI : CommGroup G := IsCyclic.commGroup
  haveI : NeZero n := ⟨hn.pos.ne'⟩
  exact (_root_.TateCohomology.isoGroupCohomology n).app M ≪≫
    _root_.Rep.FiniteCyclicGroup.groupCohomologyIsoOdd M g hg n hn

/-- The generator-dependent comparison underlying positive-degree two-periodicity. It compares
both degrees with the same homology object of the standard periodic resolution, using the even
model or the odd model according to their common parity. -/
def positivePeriodicIsoOfGenerator (M : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (m n : ℕ) [NeZero m] [NeZero n] (hmn : m ≡ n [MOD 2]) :
    tateCohomology M m ≅ tateCohomology M n := by
  by_cases hm : Even m
  · have hn : Even n := by
      have hmn' : m % 2 = n % 2 := hmn
      rw [Nat.even_iff]
      rw [Nat.even_iff] at hm
      exact hmn'.symm.trans hm
    exact (positiveEvenIso M g hg m hm).trans (positiveEvenIso M g hg n hn).symm
  · have hn : Odd n := by
      have hm' : Odd m := Nat.not_even_iff_odd.mp hm
      have hmn' : m % 2 = n % 2 := hmn
      rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hm'
      exact hmn'.symm.trans hm'
    exact (positiveOddIso M g hg m (Nat.not_even_iff_odd.mp hm)).trans
      (positiveOddIso M g hg n hn).symm

/-- **Positive-degree two-periodicity for Tate cohomology of a finite cyclic group.** Positive
Tate degrees congruent modulo two are isomorphic. -/
def positivePeriodicIso (M : Rep R G) [IsCyclic G]
    (m n : ℕ) [NeZero m] [NeZero n] (hmn : m ≡ n [MOD 2]) :
    tateCohomology M m ≅ tateCohomology M n := by
  let hgen := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  let g := hgen.choose
  exact positivePeriodicIsoOfGenerator M g
    (fun x ↦ hgen.choose_spec.ge (Subgroup.mem_top x)) m n hmn

/-- In even degrees, `positivePeriodicIsoOfGenerator` is the unique comparison obtained by
identifying both Tate groups with the even homology object of the periodic resolution. -/
@[simp, reassoc]
theorem positivePeriodicIsoOfGenerator_hom_comp_positiveEvenIso_hom
    (M : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (m n : ℕ) [NeZero m] [NeZero n] (hmn : m ≡ n [MOD 2])
    (hm : Even m) (hn : Even n) :
    (positivePeriodicIsoOfGenerator M g hg m n hmn).hom ≫
        (positiveEvenIso M g hg n hn).hom =
      (positiveEvenIso M g hg m hm).hom := by
  simp [positivePeriodicIsoOfGenerator, hm]

/-- In odd degrees, `positivePeriodicIsoOfGenerator` is the unique comparison obtained by
identifying both Tate groups with the odd homology object of the periodic resolution. -/
@[simp, reassoc]
theorem positivePeriodicIsoOfGenerator_hom_comp_positiveOddIso_hom
    (M : Rep R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (m n : ℕ) [NeZero m] [NeZero n] (hmn : m ≡ n [MOD 2])
    (hm : Odd m) (hn : Odd n) :
    (positivePeriodicIsoOfGenerator M g hg m n hmn).hom ≫
        (positiveOddIso M g hg n hn).hom =
      (positiveOddIso M g hg m hm).hom := by
  simp [positivePeriodicIsoOfGenerator, Nat.not_even_iff_odd.mpr hm]

/-- Positive Tate cohomology groups in degrees congruent modulo two have the same cardinality.
This is the form used in Herbrand-quotient computations. -/
theorem natCard_tateCohomology_eq_of_pos_of_modEq
    (M : Rep R G) [IsCyclic G]
    (m n : ℕ) [NeZero m] [NeZero n] (hmn : m ≡ n [MOD 2]) :
    Nat.card (tateCohomology M m) = Nat.card (tateCohomology M n) :=
  Nat.card_congr (positivePeriodicIso M m n hmn).toLinearEquiv.toEquiv

end Rep.FiniteCyclicGroup
