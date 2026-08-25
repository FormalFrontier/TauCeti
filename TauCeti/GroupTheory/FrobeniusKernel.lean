/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# The Frobenius kernel and its size

The **Frobenius kernel** of a subgroup `H` of `G` is the identity together with the elements of `G`
lying in no conjugate of `H`,

`frobeniusKernel H = {1} ∪ (G ∖ ⋃_g g H g⁻¹)`.

That union of conjugates is Mathlib's `Group.conjugatesOfSet (H : Set G)`, the set of elements
conjugate to an element of `H`.

Frobenius's theorem says that when `G` is finite and `H` is a Frobenius complement — proper,
nontrivial, and meeting each of its distinct conjugates trivially
(`TauCeti.IsFrobeniusComplement`) — this set is a normal subgroup, and that is not elementary: the
known proofs go through the character theory of `G`. What *is* elementary, and is what this file
proves, is everything about the kernel except its closure under multiplication: it contains the
identity, it is closed under inversion and under conjugation, it meets every conjugate of `H` only
in the identity, and — the counting statement the roadmap records — for a finite `G` it has exactly
`|G : H|` elements.

The count is the inclusion-exclusion that gives Frobenius's theorem its shape, and it is really a
statement about a trivial-intersection *set* `S` for `H` (`TauCeti.IsTISet`): the conjugates
`g S g⁻¹` are pairwise disjoint for distinct cosets `g H` and depend only on the coset, so the
elements they cover are indexed bijectively by the pairs (a coset of `H`, an element of `S`) and
number `|G : H| · |S|`. That is `TauCeti.IsTISet.ncard_conjugatesOfSet`, proved alongside
`TauCeti.IsTISet` itself in `TauCeti/GroupTheory/TrivialIntersection.lean`. The complement of the
kernel is the set of conjugates of the nonidentity elements of `H`, which for a
trivial-intersection subgroup is such a set (`TauCeti.IsTISubgroup.isTISet_diff_one`), and the
count specializes to `TauCeti.IsTISubgroup.ncard_compl_frobeniusKernel`, the `Set.ncard` identity
`((frobeniusKernel H)ᶜ).ncard = |G : H| · (|H| - 1)`. That identity holds for any `G`, finite or
not, but for an infinite `G` it does not in general represent a count of elements: an infinite side
reads as the junk value `0` that `Set.ncard` and `Subgroup.index` take on infinite arguments. A
degenerate case can of course still be a genuine count — for `H = ⊥` the kernel is everything and
its complement is honestly empty — but nothing outside the finite case says so. For a finite `G`
there are indeed `|G : H| · (|H| - 1)` elements outside the kernel, and the remaining
`|G| - |G : H| · (|H| - 1) = |G : H|` elements are the kernel, and the rest is arithmetic.

Together with normality the count is exactly what makes the kernel a *complement*:
`TauCeti.IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel` says that, for a finite `G`, a
subgroup whose carrier is the Frobenius kernel is automatically a complement to `H`, so once
Frobenius's theorem supplies the subgroup, the semidirect decomposition `G = N ⋊ H` is free.
Nothing here asserts that a subgroup with that carrier exists.

No subgroup hypothesis beyond `TauCeti.IsTISubgroup` is needed for the count once `G` is finite, and
the two degenerate cases are honest instances rather than exclusions:
`frobeniusKernel ⊤ = {1}` has one element and `⊤` has index `1`, while `frobeniusKernel ⊥` is
everything and `⊥` has index `|G|`.

## Main definitions

* `TauCeti.frobeniusKernel`: the identity together with the elements in no conjugate of `H`.

## Main results

* `TauCeti.mem_frobeniusKernel`: membership, elementwise.
* `TauCeti.inv_mem_frobeniusKernel_iff` and `TauCeti.conj_mem_frobeniusKernel_iff`: the kernel is
  closed under inversion and invariant under conjugation, for every subgroup `H`.
* `TauCeti.frobeniusKernel_inter_conj_smul_eq_singleton` and
  `TauCeti.frobeniusKernel_inter_eq_singleton`: the kernel meets every conjugate of `H`, and in
  particular `H` itself, exactly in the identity.
* `TauCeti.IsTISubgroup.ncard_compl_frobeniusKernel`: the `Set.ncard` identity
  `((frobeniusKernel H)ᶜ).ncard = |G : H| · (|H| - 1)`, which for a finite `G` counts the elements
  *outside* the kernel — the nonidentity elements of the conjugates of `H`, each counted once — and
  for an infinite `G` reads `0 = 0`.
* `TauCeti.IsTISubgroup.ncard_frobeniusKernel` and
  `TauCeti.IsTISubgroup.natCard_frobeniusKernel`: **for a finite `G` the kernel has `|G : H|`
  elements.**
* `TauCeti.IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel`: for a finite `G`, a subgroup
  whose carrier is the kernel is a complement to `H`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 7, Section 7B.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8 (`frobeniusKernel`, "a set of size `|G : H|`", and `frobeniusKernel_isComplement'`).
-/

public section

namespace TauCeti

open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G}

/-- **The Frobenius kernel** of a subgroup: the identity together with the elements of `G` lying in
no conjugate of `H`, the conjugates being collected by `Group.conjugatesOfSet`.  For a Frobenius
complement `H` of a finite group this set is a normal subgroup of `G`, but that is Frobenius's
theorem and needs character theory; as a *set* it is available for any `H`, and
`TauCeti.mem_frobeniusKernel` is the elementwise description everything below uses. -/
def frobeniusKernel (H : Subgroup G) : Set G :=
  {1} ∪ (Group.conjugatesOfSet (H : Set G))ᶜ

/-- The Frobenius kernel is the identity together with the complement of the set of conjugates of
elements of `H`, by definition. -/
theorem frobeniusKernel_def (H : Subgroup G) :
    frobeniusKernel H = {1} ∪ (Group.conjugatesOfSet (H : Set G))ᶜ := (rfl)

/-- **Membership in the Frobenius kernel**: an element is the identity, or no conjugate of it lands
in `H`. -/
theorem mem_frobeniusKernel {y : G} :
    y ∈ frobeniusKernel H ↔ y = 1 ∨ ∀ x : G, x⁻¹ * y * x ∉ H := by
  have key : y ∈ Group.conjugatesOfSet (H : Set G) ↔ ∃ x : G, x⁻¹ * y * x ∈ H := by
    rw [Group.mem_conjugatesOfSet_iff]
    constructor
    · rintro ⟨a, ha, hc⟩
      obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      have hcancel : c⁻¹ * (c * a * c⁻¹) * c = a := by group
      refine ⟨c, ?_⟩
      rw [hcancel]
      exact ha
    · rintro ⟨x, hx⟩
      have hcancel : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      exact ⟨x⁻¹ * y * x, hx, isConj_iff.2 ⟨x, hcancel⟩⟩
  simp only [frobeniusKernel_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff, key,
    not_exists]

/-- Being outside the Frobenius kernel means being a nonidentity element of some conjugate of
`H`. -/
@[simp]
theorem notMem_frobeniusKernel_iff {y : G} :
    y ∉ frobeniusKernel H ↔ y ≠ 1 ∧ ∃ x : G, x⁻¹ * y * x ∈ H := by
  rw [mem_frobeniusKernel]
  push Not
  rfl

@[simp]
theorem one_mem_frobeniusKernel : (1 : G) ∈ frobeniusKernel H :=
  mem_frobeniusKernel.2 (Or.inl rfl)

/-- The Frobenius kernel is closed under inversion: `x⁻¹ y⁻¹ x` is the inverse of `x⁻¹ y x`, and a
subgroup contains an element exactly when it contains its inverse. -/
@[simp]
theorem inv_mem_frobeniusKernel_iff {y : G} :
    y⁻¹ ∈ frobeniusKernel H ↔ y ∈ frobeniusKernel H := by
  simp only [mem_frobeniusKernel, inv_eq_one]
  refine or_congr Iff.rfl (forall_congr' fun x => not_congr ?_)
  have hinv : x⁻¹ * y⁻¹ * x = (x⁻¹ * y * x)⁻¹ := by group
  rw [hinv, H.inv_mem_iff]

/-- The Frobenius kernel is invariant under conjugation: it is the identity together with the
complement of a conjugation-closed set, and `Group.conj_mem_conjugatesOfSet` is that closure.  This
is the half of normality that costs nothing; closure under multiplication is Frobenius's theorem. -/
@[simp]
theorem conj_mem_frobeniusKernel_iff {y g : G} :
    g * y * g⁻¹ ∈ frobeniusKernel H ↔ y ∈ frobeniusKernel H := by
  simp only [frobeniusKernel_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff,
    conj_eq_one_iff]
  refine or_congr Iff.rfl (not_congr ⟨fun h => ?_, Group.conj_mem_conjugatesOfSet⟩)
  have hcancel : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  exact hcancel ▸ Group.conj_mem_conjugatesOfSet h

/-- **The Frobenius kernel meets each conjugate of `H` exactly in the identity.**  A nonidentity
element of `g H g⁻¹` lies in a conjugate of `H`, so it is outside the kernel. -/
@[simp]
theorem frobeniusKernel_inter_conj_smul_eq_singleton (g : G) :
    frobeniusKernel H ∩ MulAut.conj g • (H : Set G) = {1} := by
  have key : ∀ y : G, y ∈ MulAut.conj g • (H : Set G) ↔ g⁻¹ * y * g ∈ H := fun y => by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · rcases mem_frobeniusKernel.1 hy.1 with h1 | h
    · exact h1
    · exact absurd ((key y).1 hy.2) (h g)
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨one_mem_frobeniusKernel, (key 1).2 (by simp)⟩

/-- **The Frobenius kernel meets `H` exactly in the identity**, the case `g = 1` of
`TauCeti.frobeniusKernel_inter_conj_smul_eq_singleton`. -/
@[simp]
theorem frobeniusKernel_inter_eq_singleton : frobeniusKernel H ∩ (H : Set G) = {1} := by
  simpa using frobeniusKernel_inter_conj_smul_eq_singleton (H := H) 1

/-- The Frobenius kernel of the whole group is trivial: every element lies in `⊤`. -/
@[simp]
theorem frobeniusKernel_top : frobeniusKernel (⊤ : Subgroup G) = {1} := by
  ext y
  simp [mem_frobeniusKernel]

/-- The Frobenius kernel of the trivial subgroup is everything: no conjugate of a nonidentity
element is the identity. -/
@[simp]
theorem frobeniusKernel_bot : frobeniusKernel (⊥ : Subgroup G) = Set.univ := by
  ext y
  simp only [mem_frobeniusKernel, Set.mem_univ, iff_true, Subgroup.mem_bot]
  refine (eq_or_ne y 1).imp id fun hy x hx => hy ?_
  -- `conj_eq_one_iff` is stated for `a * y * a⁻¹`, so the conjugator is exhibited as `x⁻¹`.
  have hconj : x⁻¹ * y * x = x⁻¹ * y * (x⁻¹)⁻¹ := by group
  exact conj_eq_one_iff.1 (hconj ▸ hx)

/-! ### Counting the kernel -/

/-- The complement of the Frobenius kernel is the set of conjugates of the nonidentity elements of
`H`: lying outside the kernel means being a nonidentity element of some conjugate of `H`, and
conjugation fixes the identity. -/
private theorem compl_frobeniusKernel (H : Subgroup G) :
    (frobeniusKernel H)ᶜ = Group.conjugatesOfSet ((H : Set G) \ {1}) := by
  ext y
  simp only [Set.mem_compl_iff, notMem_frobeniusKernel_iff, Group.mem_conjugatesOfSet_iff,
    Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff, ne_eq]
  constructor
  · rintro ⟨hy1, x, hx⟩
    refine ⟨x⁻¹ * y * x, ⟨hx, ?_⟩, isConj_iff.2 ⟨x, by group⟩⟩
    -- `conj_eq_one_iff` is stated for `a * y * a⁻¹`, so the conjugator is exhibited as `x⁻¹`.
    have hconj : x⁻¹ * y * x = x⁻¹ * y * (x⁻¹)⁻¹ := by group
    rw [hconj, conj_eq_one_iff]
    exact hy1
  · rintro ⟨a, ⟨haH, ha1⟩, hconj⟩
    obtain ⟨x, rfl⟩ := isConj_iff.1 hconj
    refine ⟨fun h => ha1 (conj_eq_one_iff.1 h), x, ?_⟩
    have hcancel : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    rw [hcancel]
    exact haH

/-- **The complement of the Frobenius kernel has `Set.ncard` equal to `|G : H| · (|H| - 1)`.**  For
a trivial-intersection subgroup the elements outside the kernel are exactly the conjugates of the
nonidentity elements of `H`, which `TauCeti.IsTISet.ncard_conjugatesOfSet` counts as `|G : H|`
times the `|H| - 1` elements of `H` that are conjugated.  No finiteness is assumed — but this is an
`ncard` identity, which for an infinite `G` need not be an element count: an infinite side reads as
the junk value `0` that `Set.ncard` and `Subgroup.index` take on infinite arguments, even though a
degenerate case may still be a genuine count (for `H = ⊥` the complement of the kernel is honestly
empty).  The count that is guaranteed to be one is
`TauCeti.IsTISubgroup.ncard_frobeniusKernel`, stated for a finite `G`. -/
theorem IsTISubgroup.ncard_compl_frobeniusKernel (hH : IsTISubgroup H) :
    ((frobeniusKernel H)ᶜ).ncard = H.index * (Nat.card H - 1) := by
  have hcoe : (H : Set G).ncard = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm
  rw [compl_frobeniusKernel, hH.isTISet_diff_one.ncard_conjugatesOfSet,
    Set.ncard_sdiff_singleton_of_mem H.one_mem, hcoe]

/-- **The Frobenius kernel of a trivial-intersection subgroup of a finite group has `|G : H|`
elements.**  The conjugates of `H` cover `|G : H| · (|H| - 1)` nonidentity elements between them,
and `|G| = |G : H| · |H|`, so `|G : H|` elements are left over. -/
theorem IsTISubgroup.ncard_frobeniusKernel [Finite G] (hH : IsTISubgroup H) :
    (frobeniusKernel H).ncard = H.index := by
  obtain ⟨m, hm⟩ : ∃ m, Nat.card H = m + 1 := ⟨Nat.card H - 1, by
    have := Nat.card_pos (α := H)
    omega⟩
  have hcard := H.index_mul_card
  rw [hm, Nat.mul_add, Nat.mul_one] at hcard
  -- `Set.ncard_compl_of_ncard_eq_add` reads the count of the kernel off the count of its
  -- complement, once `compl_compl` presents the kernel as that complement.
  rw [← compl_compl (frobeniusKernel H)]
  refine Set.ncard_compl_of_ncard_eq_add _ ?_
  rw [hH.ncard_compl_frobeniusKernel, hm, Nat.add_sub_cancel]
  omega

/-- The Frobenius kernel of a trivial-intersection subgroup of a finite group has `|G : H|`
elements, read as the cardinality of its coercion to a type. -/
theorem IsTISubgroup.natCard_frobeniusKernel [Finite G] (hH : IsTISubgroup H) :
    Nat.card (frobeniusKernel H) = H.index :=
  (Nat.card_coe_set_eq _).trans hH.ncard_frobeniusKernel

/-- **A subgroup of a finite group carried by the Frobenius kernel is a complement to `H`.**
Frobenius's theorem provides such a subgroup for a Frobenius complement; that it is a complement is
then pure counting, the kernel having `|G : H|` elements and meeting `H` only in the identity.
Nothing here asserts that such a subgroup exists. -/
theorem IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel [Finite G] (hH : IsTISubgroup H)
    {N : Subgroup G} (hN : (N : Set G) = frobeniusKernel H) : N.IsComplement' H := by
  have hcard : Nat.card N * Nat.card H = Nat.card G := by
    have hcardN : Nat.card N = Nat.card (frobeniusKernel H) := Nat.card_congr (Equiv.setCongr hN)
    rw [hcardN, hH.natCard_frobeniusKernel]
    exact H.index_mul_card
  refine Subgroup.isComplement'_of_card_mul_and_disjoint hcard (Subgroup.disjoint_def.2 ?_)
  intro y hyN hyH
  have hmem : y ∈ frobeniusKernel H ∩ (H : Set G) :=
    ⟨hN ▸ SetLike.mem_coe.2 hyN, SetLike.mem_coe.2 hyH⟩
  rwa [frobeniusKernel_inter_eq_singleton, Set.mem_singleton_iff] at hmem

end TauCeti
