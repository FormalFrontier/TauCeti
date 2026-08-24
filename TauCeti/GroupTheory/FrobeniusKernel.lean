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

The count is the inclusion-exclusion that gives Frobenius's theorem its shape. For a
trivial-intersection subgroup the conjugates `g H g⁻¹` meet pairwise in the identity alone and
depend only on the coset `g H`, so the elements they cover other than `1` are indexed bijectively
by the pairs (a coset of `H`, a nonidentity element of `H`). That parametrization is the private
`frobeniusKernelCompl`, whose range is the complement of the kernel and which is injective exactly
because `H` has trivial intersections; the count it yields is
`TauCeti.IsTISubgroup.ncard_compl_frobeniusKernel`, the `Set.ncard` identity
`((frobeniusKernel H)ᶜ).ncard = |G : H| · (|H| - 1)`. That identity holds for any `G`, finite or
not, but it counts elements only when `G` is finite: for an infinite `G` both of its sides are the
junk value `0` that `Set.ncard` and `Subgroup.index` take on infinite arguments. For a finite `G`
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
* `TauCeti.frobeniusKernel_inter_conj_eq_singleton` and
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
theorem frobeniusKernel_inter_conj_eq_singleton (g : G) :
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
`TauCeti.frobeniusKernel_inter_conj_eq_singleton`. -/
@[simp]
theorem frobeniusKernel_inter_eq_singleton : frobeniusKernel H ∩ (H : Set G) = {1} := by
  simpa using frobeniusKernel_inter_conj_eq_singleton (H := H) 1

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
    have hcancel : C.out⁻¹ * (C.out * h * C.out⁻¹) * C.out = h := by group
    rw [hcancel]
    exact hhH
  · obtain ⟨hy1, x, hx⟩ := notMem_frobeniusKernel_iff.1 hy
    obtain ⟨s, hout⟩ := QuotientGroup.mk_out_eq_mul H x
    refine ⟨⟨QuotientGroup.mk x, ⟨(s : G)⁻¹ * (x⁻¹ * y * x) * s, ?_, ?_⟩⟩, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem s.2) hx) s.2
    · -- Again the conjugator is exhibited as `(x * s)⁻¹`, the form `conj_eq_one_iff` rewrites.
      have hconj : (s : G)⁻¹ * (x⁻¹ * y * x) * s = (x * s)⁻¹ * y * ((x * s)⁻¹)⁻¹ := by group
      rw [Set.mem_singleton_iff, hconj, conj_eq_one_iff]
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
    have hshift : D.out⁻¹ * C.out * h * (D.out⁻¹ * C.out)⁻¹
        = D.out⁻¹ * (C.out * h * C.out⁻¹) * D.out := by group
    rw [hshift, hEq]
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

/-- **The complement of the Frobenius kernel has `Set.ncard` equal to `|G : H| · (|H| - 1)`.**  For
a trivial-intersection subgroup the elements outside the kernel are exactly the nonidentity elements
of the conjugates of `H`, and each is hit once by the parametrization: such an element determines
the conjugate containing it, hence the coset, hence the element of `H` it comes from.  The
parametrization argument is uniform, so no finiteness is assumed — but this is an `ncard` identity,
not an element count, unless `G` is finite: for an infinite `G` both sides are the junk value `0`
that `Set.ncard` and `Subgroup.index` take on infinite arguments.  The genuine count is
`TauCeti.IsTISubgroup.ncard_frobeniusKernel`, stated for a finite `G`. -/
theorem IsTISubgroup.ncard_compl_frobeniusKernel (hH : IsTISubgroup H) :
    ((frobeniusKernel H)ᶜ).ncard = H.index * (Nat.card H - 1) := by
  have hcoe : (H : Set G).ncard = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm
  have hH1 : ((H : Set G) \ {1}).ncard = Nat.card H - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem H.one_mem, hcoe]
  rw [← range_frobeniusKernelCompl,
    Set.ncard_range_of_injective hH.frobeniusKernelCompl_injective, Nat.card_prod,
    ← Subgroup.index_eq_card, Nat.card_coe_set_eq, hH1]

/-- **The Frobenius kernel of a trivial-intersection subgroup of a finite group has `|G : H|`
elements.**  The conjugates of `H` cover `|G : H| · (|H| - 1)` nonidentity elements between them,
and `|G| = |G : H| · |H|`, so `|G : H|` elements are left over. -/
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
