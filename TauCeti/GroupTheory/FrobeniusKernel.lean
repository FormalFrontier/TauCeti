/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# The Frobenius kernel and its size

The **Frobenius kernel** of a subgroup `H` of `G` is the identity together with the elements of `G`
lying in no conjugate of `H`,

`frobeniusKernel H = {1} ∪ (G ∖ ⋃_g g H g⁻¹)`.

Frobenius's theorem says that when `H` is a Frobenius complement — proper, nontrivial, and meeting
each of its distinct conjugates trivially (`TauCeti.IsFrobeniusComplement`) — this set is a normal
subgroup, and that is not elementary: the known proofs go through the character theory of `G`.
What *is* elementary, and is what this file proves, is everything about the kernel except its
closure under multiplication: it contains the identity, it is closed under inversion and under
conjugation, it meets `H` only in the identity, and — the counting statement the roadmap records —
it has exactly `|G : H|` elements.

The count is the inclusion-exclusion that gives Frobenius's theorem its shape. For a
trivial-intersection subgroup the conjugates `g H g⁻¹` meet pairwise in the identity alone and
depend only on the coset `g H`, so the elements they cover other than `1` are indexed bijectively
by the pairs (a coset of `H`, a nonidentity element of `H`); there are `|G : H| · (|H| - 1)` of
them, and the remaining `|G| - |G : H| · (|H| - 1) = |G : H|` elements of `G` are the kernel. That
bijection is `TauCeti.IsTISubgroup.ncard_compl_frobeniusKernel`, and the rest is arithmetic.

Together with normality the count is exactly what makes the kernel a *complement*:
`TauCeti.IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel` says that a subgroup whose carrier
is the Frobenius kernel is automatically a complement to `H`, so once Frobenius's theorem supplies
the subgroup, the semidirect decomposition `G = N ⋊ H` is free. Nothing here asserts that a
subgroup with that carrier exists.

No hypothesis beyond `TauCeti.IsTISubgroup` is needed for the count, and the two degenerate cases
are honest instances rather than exclusions: `frobeniusKernel ⊤ = {1}` has one element and `⊤` has
index `1`, while `frobeniusKernel ⊥` is everything and `⊥` has index `|G|`.

## Main definitions

* `TauCeti.frobeniusKernel`: the identity together with the elements in no conjugate of `H`.

## Main results

* `TauCeti.mem_frobeniusKernel`: membership, elementwise.
* `TauCeti.inv_mem_frobeniusKernel_iff` and `TauCeti.conj_mem_frobeniusKernel_iff`: the kernel is
  closed under inversion and invariant under conjugation, for every subgroup `H`.
* `TauCeti.frobeniusKernel_inter_coe`: the kernel meets `H` exactly in the identity.
* `TauCeti.IsTISubgroup.ncard_compl_frobeniusKernel`: the elements *outside* the kernel are the
  `|G : H| · (|H| - 1)` nonidentity elements of the conjugates of `H`, each counted once.
* `TauCeti.IsTISubgroup.ncard_frobeniusKernel` and
  `TauCeti.IsTISubgroup.natCard_frobeniusKernel`: **the kernel has `|G : H|` elements.**
* `TauCeti.IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel`: a subgroup whose carrier is the
  kernel is a complement to `H`.

## Implementation notes

The bijection is set up as a map *into* `G` out of `(G ⧸ H) × H#`, rather than as an `Equiv` onto
the complement of the kernel, because the two facts it is used through are cleaner apart than
bundled: that its range is the complement needs no hypothesis on `H` at all, while its injectivity
is exactly the trivial-intersection condition. The coset representatives are `Quotient.out`, so the
map is noncomputable and needs no well-definedness argument; the price is that hitting an element
of the complement has to move a witness `x` to `(x H).out` by `QuotientGroup.mk_out_eq_mul`,
conjugating the element of `H` along the way.

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
no conjugate of `H`.  For a Frobenius complement `H` this set is a normal subgroup of `G`, but that
is Frobenius's theorem and needs character theory; as a *set* it is available for any `H`, and
`TauCeti.mem_frobeniusKernel` is the elementwise description everything below uses. -/
def frobeniusKernel (H : Subgroup G) : Set G :=
  {1} ∪ (⋃ g : G, ((MulAut.conj g • H : Subgroup G) : Set G))ᶜ

/-- **Membership in the Frobenius kernel**: an element is the identity, or no conjugate of it lands
in `H`. -/
theorem mem_frobeniusKernel {y : G} :
    y ∈ frobeniusKernel H ↔ y = 1 ∨ ∀ x : G, x⁻¹ * y * x ∉ H := by
  have key : ∀ g : G, y ∈ (MulAut.conj g • H : Subgroup G) ↔ g⁻¹ * y * g ∈ H := fun g => by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  simp only [frobeniusKernel, Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff,
    Set.mem_iUnion, not_exists, SetLike.mem_coe, key]

/-- Being outside the Frobenius kernel means being a nonidentity element of some conjugate of
`H`. -/
theorem notMem_frobeniusKernel_iff {y : G} :
    y ∉ frobeniusKernel H ↔ y ≠ 1 ∧ ∃ x : G, x⁻¹ * y * x ∈ H := by
  rw [mem_frobeniusKernel]
  push Not
  rfl

@[simp]
theorem one_mem_frobeniusKernel : (1 : G) ∈ frobeniusKernel H :=
  mem_frobeniusKernel.2 (Or.inl rfl)

/-- A conjugate of an element is the identity only if the element is; the `x⁻¹ • x` form of
Mathlib's `conj_eq_one_iff`, which is how the conjugates appear in
`TauCeti.mem_frobeniusKernel`. -/
private theorem inv_conj_eq_one_iff {y x : G} : x⁻¹ * y * x = 1 ↔ y = 1 := by
  simpa using conj_eq_one_iff (a := x⁻¹) (b := y)

/-- The Frobenius kernel is closed under inversion: `x⁻¹ y⁻¹ x` is the inverse of `x⁻¹ y x`, and a
subgroup contains an element exactly when it contains its inverse. -/
@[simp]
theorem inv_mem_frobeniusKernel_iff {y : G} :
    y⁻¹ ∈ frobeniusKernel H ↔ y ∈ frobeniusKernel H := by
  simp only [mem_frobeniusKernel, inv_eq_one]
  refine or_congr Iff.rfl (forall_congr' fun x => not_congr ?_)
  rw [show x⁻¹ * y⁻¹ * x = (x⁻¹ * y * x)⁻¹ by group, H.inv_mem_iff]

/-- The Frobenius kernel is invariant under conjugation: it is cut out by a condition quantified
over all conjugates, which conjugating merely reindexes.  This is the half of normality that costs
nothing; closure under multiplication is Frobenius's theorem. -/
@[simp]
theorem conj_mem_frobeniusKernel_iff {y g : G} :
    g * y * g⁻¹ ∈ frobeniusKernel H ↔ y ∈ frobeniusKernel H := by
  simp only [mem_frobeniusKernel, conj_eq_one_iff]
  refine or_congr Iff.rfl ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [show x⁻¹ * y * x = (g * x)⁻¹ * (g * y * g⁻¹) * (g * x) by group]
    exact h (g * x)
  · rw [show x⁻¹ * (g * y * g⁻¹) * x = (g⁻¹ * x)⁻¹ * y * (g⁻¹ * x) by group]
    exact h (g⁻¹ * x)

/-- **The Frobenius kernel meets `H` exactly in the identity.**  A nonidentity element of `H` lies
in a conjugate of `H`, namely `H` itself. -/
theorem frobeniusKernel_inter_coe : frobeniusKernel H ∩ (H : Set G) = {1} := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · rcases mem_frobeniusKernel.1 hy.1 with h1 | h
    · exact h1
    · exact absurd (by simpa using hy.2) (h 1)
  · rw [Set.mem_singleton_iff] at hy
    exact ⟨hy ▸ one_mem_frobeniusKernel, hy ▸ H.one_mem⟩

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
  simp only [mem_frobeniusKernel, Set.mem_univ, iff_true, Subgroup.mem_bot, inv_conj_eq_one_iff]
  exact (eq_or_ne y 1).imp id fun hy _ => hy

/-! ### Counting the kernel -/

/-- The parametrization of the elements *outside* the Frobenius kernel by a coset of `H` together
with a nonidentity element of `H`: the coset picks a conjugate `g H g⁻¹` through the representative
`Quotient.out`, and the element of `H` is transported into it.  Its range is the complement of the
kernel (`TauCeti.range_frobeniusKernelCompl`) for every `H`, and it is injective exactly when the
conjugates of `H` meet pairwise trivially
(`TauCeti.IsTISubgroup.frobeniusKernelCompl_injective`). -/
private noncomputable def frobeniusKernelCompl (H : Subgroup G) :
    (G ⧸ H) × ((H : Set G) \ {1} : Set G) → G :=
  fun p => p.1.out * (p.2 : G) * p.1.out⁻¹

private theorem range_frobeniusKernelCompl :
    Set.range (frobeniusKernelCompl H) = (frobeniusKernel H)ᶜ := by
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨⟨C, ⟨h, hhH, hh1⟩⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hh1
    simp only [frobeniusKernelCompl, Set.mem_compl_iff, notMem_frobeniusKernel_iff, ne_eq,
      conj_eq_one_iff]
    refine ⟨hh1, C.out, ?_⟩
    rw [show C.out⁻¹ * (C.out * h * C.out⁻¹) * C.out = h by group]
    exact hhH
  · obtain ⟨hy1, x, hx⟩ := notMem_frobeniusKernel_iff.1 hy
    obtain ⟨s, hout⟩ := QuotientGroup.mk_out_eq_mul H x
    refine ⟨⟨QuotientGroup.mk x, ⟨(s : G)⁻¹ * (x⁻¹ * y * x) * s, ?_, ?_⟩⟩, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem s.2) hx) s.2
    · rw [Set.mem_singleton_iff, show (s : G)⁻¹ * (x⁻¹ * y * x) * s
        = (x * s)⁻¹ * y * (x * s) by group, inv_conj_eq_one_iff]
      exact hy1
    · simp only [frobeniusKernelCompl, hout]
      group

private theorem IsTISubgroup.frobeniusKernelCompl_injective (hH : IsTISubgroup H) :
    Function.Injective (frobeniusKernelCompl H) := by
  rintro ⟨C, ⟨h, hhH, hh1⟩⟩ ⟨D, ⟨h', hh'H, hh'1⟩⟩ hEq
  rw [Set.mem_singleton_iff] at hh1
  simp only [frobeniusKernelCompl] at hEq
  -- The two coset representatives differ by an element conjugating `h` into `H`, so the
  -- trivial-intersection condition puts that difference inside `H`: the cosets agree.
  have hconj : D.out⁻¹ * C.out * h * (D.out⁻¹ * C.out)⁻¹ = h' := by
    rw [show D.out⁻¹ * C.out * h * (D.out⁻¹ * C.out)⁻¹
      = D.out⁻¹ * (C.out * h * C.out⁻¹) * D.out by group, hEq]
    group
  have hmem : D.out⁻¹ * C.out ∈ H := by
    by_contra hx
    exact hh1 (hH.eq_one hx hhH (hconj ▸ hh'H))
  have hCD : C = D := by
    have h1 : (QuotientGroup.mk C.out : G ⧸ H) = QuotientGroup.mk D.out :=
      (QuotientGroup.eq.2 hmem).symm
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
  subst hCD
  have hhh : h = h' := mul_left_cancel (mul_right_cancel hEq)
  subst hhh
  rfl

/-- **The elements outside the Frobenius kernel number `|G : H| · (|H| - 1)`.**  For a
trivial-intersection subgroup they are exactly the nonidentity elements of the conjugates of `H`,
and each is hit once by the parametrization: such an element determines the conjugate containing
it, hence the coset, hence the element of `H` it comes from. -/
theorem IsTISubgroup.ncard_compl_frobeniusKernel [Finite G] (hH : IsTISubgroup H) :
    ((frobeniusKernel H)ᶜ).ncard = H.index * (Nat.card H - 1) := by
  have hsub : ((H : Set G) \ {1}).ncard + 1 = (H : Set G).ncard :=
    Set.ncard_sdiff_singleton_add_one H.one_mem
  have hcoe : (H : Set G).ncard = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm
  have hH1 : ((H : Set G) \ {1}).ncard = Nat.card H - 1 := by omega
  rw [← range_frobeniusKernelCompl, ← Set.image_univ,
    Set.ncard_image_of_injective _ hH.frobeniusKernelCompl_injective, Set.ncard_univ,
    Nat.card_prod, ← Subgroup.index_eq_card, Nat.card_coe_set_eq, hH1]

/-- **The Frobenius kernel of a trivial-intersection subgroup has `|G : H|` elements.**  The
conjugates of `H` cover `|G : H| · (|H| - 1)` nonidentity elements between them, and
`|G| = |G : H| · |H|`, so `|G : H|` elements are left over. -/
theorem IsTISubgroup.ncard_frobeniusKernel [Finite G] (hH : IsTISubgroup H) :
    (frobeniusKernel H).ncard = H.index := by
  obtain ⟨m, hm⟩ : ∃ m, Nat.card H = m + 1 := ⟨Nat.card H - 1, by
    have := Nat.card_pos (α := H)
    omega⟩
  have htotal := Set.ncard_add_ncard_compl (frobeniusKernel H)
  have hcard := H.index_mul_card
  rw [hH.ncard_compl_frobeniusKernel, hm, Nat.add_sub_cancel] at htotal
  rw [hm, Nat.mul_add, Nat.mul_one] at hcard
  omega

/-- The Frobenius kernel of a trivial-intersection subgroup has `|G : H|` elements, read as the
cardinality of its coercion to a type. -/
theorem IsTISubgroup.natCard_frobeniusKernel [Finite G] (hH : IsTISubgroup H) :
    Nat.card (frobeniusKernel H) = H.index :=
  (Nat.card_coe_set_eq _).trans hH.ncard_frobeniusKernel

/-- **A subgroup carried by the Frobenius kernel is a complement to `H`.**  Frobenius's theorem
provides such a subgroup for a Frobenius complement; that it is a complement is then pure counting,
the kernel having `|G : H|` elements and meeting `H` only in the identity.  Nothing here asserts
that such a subgroup exists. -/
theorem IsTISubgroup.isComplement'_of_coe_eq_frobeniusKernel [Finite G] (hH : IsTISubgroup H)
    {N : Subgroup G} (hN : (N : Set G) = frobeniusKernel H) : N.IsComplement' H := by
  have hcard : Nat.card N * Nat.card H = Nat.card G := by
    rw [show Nat.card N = Nat.card (frobeniusKernel H) from Nat.card_congr (Equiv.setCongr hN),
      hH.natCard_frobeniusKernel]
    exact H.index_mul_card
  refine Subgroup.isComplement'_of_card_mul_and_disjoint hcard (Subgroup.disjoint_def.2 ?_)
  intro y hyN hyH
  have hmem : y ∈ frobeniusKernel H ∩ (H : Set G) :=
    ⟨hN ▸ SetLike.mem_coe.2 hyN, SetLike.mem_coe.2 hyH⟩
  rwa [frobeniusKernel_inter_coe, Set.mem_singleton_iff] at hmem

end TauCeti
