/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.LinearAlgebra.RootSystem.Base

public section

/-!
# Positive and negative roots

This file packages Mathlib's positivity predicate for a root-pairing base as the sets of positive
and negative root indices. It records their partition, their exchange under root negation, and the
fact that a simple reflection permutes the positive roots other than its own simple root.

A base `b` of a root pairing `P` is simultaneously a base `b.flip` of the flipped pairing `P.flip`,
so the same positivity predicate measures both a root against the simple roots and the
corresponding coroot against the simple coroots. The last part of the file proves that the two
measurements agree, so that a base and its flip have the same positive roots and the coroot of a
positive root is a nonnegative integer combination of the simple coroots.

## Main definitions

* `TauCeti.posRoots` is the set of positive roots relative to a base.
* `TauCeti.negRoots` is its complementary set of negative roots.
* `TauCeti.posRootsFinset` and `TauCeti.negRootsFinset` are the same two sets as finsets, for a
  finite root index type, so that they can be summed over.
* `TauCeti.posRootCone` is the additive monoid `Q⁺` of nonnegative integer combinations of the
  simple roots.

## Main results

* `TauCeti.image_reflectionPerm_self_posRoots` says root negation exchanges the two sets.
* `TauCeti.ncard_posRoots_eq_natCard_div_two` says that, for a finite root index type, exactly
  half of the roots are positive, and `TauCeti.posRootsFinset_eq_filter`,
  `TauCeti.card_posRootsFinset` read `TauCeti.posRootsFinset` as the filter of the positivity
  predicate and its cardinality as the cardinality of `TauCeti.posRoots`.
* `TauCeti.add_mem_posRoots` and `TauCeti.add_mem_negRoots` say each of the two sets is closed
  under those sums of its members that are again roots, and
  `TauCeti.reflectionPerm_self_notMem_posRoots`, `TauCeti.reflectionPerm_self_notMem_negRoots` say
  neither contains a root together with its negative.
* `TauCeti.bijOn_reflectionPerm_posRoots_diff_singleton` says a simple reflection permutes the
  positive roots other than its own simple root, and
  `TauCeti.sum_posRootsFinset_erase_comp_reflectionPerm` is the resulting reindexing rule for sums
  over those roots.
* `TauCeti.mem_support_iff_isPos_and_forall_ne_add` says the simple roots are exactly the
  indecomposable positive roots: those that are not the sum of two positive roots.
* `TauCeti.RootPairing.Base.isPos_flip_iff` says a root is positive for a base exactly when its
  coroot is positive for that base, and `TauCeti.posRoots_flip` restates it for the sets.
* `TauCeti.root_mem_posRootCone_of_mem_posRoots` says the positive roots lie in `Q⁺`,
  `TauCeti.isPointed_posRootCone` says `Q⁺` is pointed,
  `TauCeti.eq_zero_of_add_eq_zero_of_mem_posRootCone` is the same fact as a cancellation rule,
  `TauCeti.root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone` specializes that to a positive root
  added to a member of `Q⁺`, and `TauCeti.sum_root_ne_zero_of_mem_posRoots` deduces that a nonempty
  sum of positive roots is nonzero.
* `TauCeti.eq_of_nsmul_root_sub_root_mem_posRootCone` says that the only positive root lying below
  a natural multiple of a simple root, in the order defined by `Q⁺`, is that simple root itself.
* `TauCeti.one_le_height_of_mem_posRoots` says every positive root has height at least one.
* `TauCeti.exists_coroot_eq_sum_nat_of_mem_posRoots` says the coroot of a positive root is a
  nonnegative integer combination of the simple coroots.

## Implementation notes

The indecomposability characterisation is stated with root vectors rather than with an index-level
sum, matching Mathlib's `RootPairing.Base.height_add` and `RootPairing.Base.IsPos.add`, whose
hypothesis is an equation between root vectors: an index-level statement would need a chosen index
for the sum, which need not be unique for a non-reduced pairing.

## References

This file implements the “Positive and negative roots” item in Layer 1 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signatures in
`TauCetiRoadmap/RepresentationTheory/RootSystems/Suggested.lean`. The coroot-side positivity at the
end of the file is the prerequisite that the fundamental-domain item of Layer 4 consumes; that
argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*,
GTM 9, Ch. III, §10. The decomposition half of `TauCeti.mem_support_iff_isPos_and_forall_ne_add` is
the step that Mathlib currently performs only inside the proof of
`RootPairing.Base.IsPos.induction_on_add`, isolated here as a statement of its own.
-/

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- Root negation is an involution of the root index type: it is the `InvolutiveNeg` supplied by
`RootPairing.indexNeg`, written through the self-reflection permutation. -/
lemma reflectionPerm_self_involutive : Function.Involutive fun i : ι ↦ P.reflectionPerm i i := by
  let := P.indexNeg
  simpa only [← RootPairing.indexNeg_neg] using neg_involutive

/-- The positive roots relative to a base. -/
def posRoots [CharZero R] (b : P.Base) : Set ι := {i | b.IsPos i}

/-- The negative roots relative to a base. -/
def negRoots [CharZero R] (b : P.Base) : Set ι := {i | ¬ b.IsPos i}

variable [CharZero R] (b : P.Base)

/-- Membership in the set of positive roots. -/
@[simp]
lemma mem_posRoots (i : ι) : i ∈ posRoots P b ↔ b.IsPos i := Iff.rfl

/-- A positive root has height at least one. -/
theorem one_le_height_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) : 1 ≤ b.height i := by
  rw [mem_posRoots, RootPairing.Base.isPos_iff] at hi
  omega

/-- Membership in the set of negative roots. -/
@[simp]
lemma mem_negRoots (i : ι) : i ∈ negRoots P b ↔ ¬ b.IsPos i := Iff.rfl

/-- The negative roots are the complement of the positive roots. -/
lemma compl_posRoots : (posRoots P b)ᶜ = negRoots P b := by
  ext i
  simp only [Set.mem_compl_iff, mem_posRoots, mem_negRoots]

/-- The negative roots are the complement of the positive roots. -/
lemma negRoots_eq_compl : negRoots P b = (posRoots P b)ᶜ := compl_posRoots P b |>.symm

/-- No root is both positive and negative. -/
lemma disjoint_posRoots_negRoots : Disjoint (posRoots P b) (negRoots P b) := by
  rw [Set.disjoint_left]
  simp

/-- Every root is either positive or negative. -/
lemma posRoots_union_negRoots : posRoots P b ∪ negRoots P b = Set.univ := by
  rw [negRoots_eq_compl]
  exact Set.union_compl_self _

/-- Every root is either positive or negative. -/
lemma mem_posRoots_or_mem_negRoots (i : ι) : i ∈ posRoots P b ∨ i ∈ negRoots P b := by
  classical
  exact em _

/-- A root is negative exactly when it is not positive. -/
lemma not_mem_posRoots_iff_mem_negRoots (i : ι) :
    i ∉ posRoots P b ↔ i ∈ negRoots P b := by
  rfl

/-- The positive roots form a finite set when the root index type is finite. -/
lemma posRoots_finite [Finite ι] : (posRoots P b).Finite := Set.toFinite _

/-- The negative roots form a finite set when the root index type is finite. -/
lemma negRoots_finite [Finite ι] : (negRoots P b).Finite := Set.toFinite _

/-- The positive roots of a base, as a finset, so that they can be summed over. -/
noncomputable def posRootsFinset [Finite ι] : Finset ι := (posRoots_finite P b).toFinset

/-- The negative roots of a base, as a finset, so that they can be summed over. -/
noncomputable def negRootsFinset [Finite ι] : Finset ι := (negRoots_finite P b).toFinset

@[simp]
lemma mem_posRootsFinset [Finite ι] (i : ι) : i ∈ posRootsFinset P b ↔ i ∈ posRoots P b :=
  (posRoots_finite P b).mem_toFinset

@[simp]
lemma mem_negRootsFinset [Finite ι] (i : ι) : i ∈ negRootsFinset P b ↔ i ∈ negRoots P b :=
  (negRoots_finite P b).mem_toFinset

/-- The finset of positive roots is the filter of the positivity predicate, which is the shape a
consumer that counts positive roots by `Finset.filter` meets them in. -/
lemma posRootsFinset_eq_filter [Fintype ι] [DecidablePred b.IsPos] :
    posRootsFinset P b = Finset.univ.filter fun i ↦ b.IsPos i := by
  ext i
  simp

/-- Counting the positive roots as a finset agrees with counting them as a set. -/
lemma card_posRootsFinset [Finite ι] : (posRootsFinset P b).card = (posRoots P b).ncard :=
  (Set.ncard_eq_toFinset_card _ (posRoots_finite P b)).symm

/-- Every simple root is positive. -/
lemma support_subset_posRoots : ↑b.support ⊆ posRoots P b := by
  intro i hi
  exact b.isPos_of_mem_support hi

/-- A nonempty root index type has a positive root. -/
lemma posRoots_nonempty [Nonempty ι] : (posRoots P b).Nonempty := by
  let := P.indexNeg
  obtain ⟨i⟩ := ‹Nonempty ι›
  rcases RootPairing.Base.IsPos.or_neg b i with hi | hi
  · exact ⟨i, hi⟩
  · exact ⟨-i, hi⟩

/-- The negative of a positive root is negative. -/
lemma reflectionPerm_self_mem_negRoots_iff_mem_posRoots (i : ι) :
    P.reflectionPerm i i ∈ negRoots P b ↔ i ∈ posRoots P b := by
  let := P.indexNeg
  rw [← RootPairing.indexNeg_neg, mem_negRoots, mem_posRoots,
    RootPairing.Base.IsPos.neg_iff_not]
  exact not_not

/-- The self-reflection of a root is positive exactly when the root is negative. -/
@[simp]
lemma isPos_reflectionPerm_self_iff_mem_negRoots (i : ι) :
    b.IsPos (P.reflectionPerm i i) ↔ i ∈ negRoots P b := by
  let := P.indexNeg
  rw [← RootPairing.indexNeg_neg, mem_negRoots]
  exact RootPairing.Base.IsPos.neg_iff_not b i

/-- The negative of a negative root is positive. -/
lemma reflectionPerm_self_mem_posRoots_iff_mem_negRoots (i : ι) :
    P.reflectionPerm i i ∈ posRoots P b ↔ i ∈ negRoots P b := by
  exact (mem_posRoots P b _).trans (isPos_reflectionPerm_self_iff_mem_negRoots P b i)

/-- Neither set contains a root together with its negative. -/
lemma reflectionPerm_self_notMem_posRoots {i : ι} (hi : i ∈ posRoots P b) :
    P.reflectionPerm i i ∉ posRoots P b := fun hcon =>
  (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mp hcon hi

/-- Neither set contains a root together with its negative. -/
lemma reflectionPerm_self_notMem_negRoots {i : ι} (hi : i ∈ negRoots P b) :
    P.reflectionPerm i i ∉ negRoots P b := fun hcon =>
  hi ((reflectionPerm_self_mem_negRoots_iff_mem_posRoots P b i).mp hcon)

/-- The positive roots are closed under addition: a root that is the sum of two positive roots is
positive, because heights add. -/
lemma add_mem_posRoots {i j k : ι} (hi : i ∈ posRoots P b) (hj : j ∈ posRoots P b)
    (hk : P.root k = P.root i + P.root j) : k ∈ posRoots P b :=
  RootPairing.Base.IsPos.add hi hj hk

/-- The negative roots are closed under addition: a root that is the sum of two negative roots is
negative. -/
lemma add_mem_negRoots {i j k : ι} (hi : i ∈ negRoots P b) (hj : j ∈ negRoots P b)
    (hk : P.root k = P.root i + P.root j) : k ∈ negRoots P b := by
  rw [← isPos_reflectionPerm_self_iff_mem_negRoots] at hi hj ⊢
  refine RootPairing.Base.IsPos.add hi hj ?_
  simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  rw [hk]
  abel

/-- A positive root is a nonnegative natural-number combination of simple roots. -/
lemma exists_root_eq_sum_nat_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) :
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧
      P.root i = ∑ j ∈ b.support, f j • P.root j := by
  obtain ⟨f, hf, hpos | hneg⟩ := b.exists_root_eq_sum_nat_or_neg i
  · exact ⟨f, hf, hpos⟩
  · exfalso
    let g : ι → ℤ := fun j ↦ -(f j : ℤ)
    have hroot : P.root i = ∑ j ∈ b.support, g j • P.root j := by
      rw [hneg]
      simp only [g, Finset.sum_neg_distrib, neg_smul, Nat.cast_smul_eq_nsmul]
    have hheight : b.height i = ∑ j ∈ b.support, g j := b.height_eq_sum hroot
    rw [mem_posRoots, RootPairing.Base.isPos_iff] at hi
    rw [hheight] at hi
    have hnonpos : ∑ j ∈ b.support, g j ≤ 0 :=
      Finset.sum_nonpos fun j _ ↦ by simp [g]
    exact (not_lt_of_ge hnonpos hi).elim

/-! ### The cone of nonnegative combinations of the simple roots -/

omit [CharZero R] in
/-- The **positive root cone** `Q⁺` of a base: the additive submonoid generated by the simple
roots, that is the set of nonnegative integer combinations of them. -/
def posRootCone : AddSubmonoid M := AddSubmonoid.closure (P.root '' b.support)

omit [CharZero R] in
/-- Membership in the positive root cone, spelled out as a nonnegative integer combination of the
simple roots. -/
theorem mem_posRootCone {v : M} :
    v ∈ posRootCone P b ↔ ∃ f : ι → ℕ, v = ∑ j ∈ b.support, f j • P.root j := by
  rw [posRootCone, ← Submodule.span_nat_eq_addSubmonoidClosure, Submodule.mem_toAddSubmonoid,
    Submodule.mem_span_image_finset_iff_exists_fun']
  exact exists_congr fun _ => eq_comm

/-- Every positive root lies in the positive root cone. -/
theorem root_mem_posRootCone_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) :
    P.root i ∈ posRootCone P b :=
  let ⟨f, _, hf⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b hi
  (mem_posRootCone P b).mpr ⟨f, hf⟩

/-- **The positive root cone is pointed**: the only member whose negative is again a member is
zero. Expanding a member and its negative in the simple roots, the total coefficient vector is
nonnegative and sums to zero and, the simple roots being linearly independent, must vanish, so each
coefficient vector does.

This is what makes the cone an order on weights: `μ ≤ λ` defined by `λ - μ ∈ Q⁺` is antisymmetric,
and a weight cannot be reached from itself through a nonempty chain of positive roots. -/
theorem isPointed_posRootCone : (posRootCone P b).IsPointed := by
  classical
  refine AddSubmonoid.IsPointed.mk fun u hu hu' => ?_
  obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hu
  obtain ⟨g, hg⟩ := (mem_posRootCone P b).mp hu'
  have huv : (∑ j ∈ b.support, f j • P.root j) + ∑ j ∈ b.support, g j • P.root j = 0 := by
    rw [← hg, add_neg_cancel]
  have hcomb : ∑ j ∈ b.support, ((f j + g j : ℕ) : ℤ) • P.root j = 0 := by
    rw [← huv, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by push_cast; rw [add_smul, natCast_zsmul, natCast_zsmul]
  have hli : LinearIndepOn ℤ P.root (b.support : Set ι) :=
    b.linearIndepOn_root.restrict_scalars' ℤ
  have hzero : ∀ j ∈ b.support, ((f j + g j : ℕ) : ℤ) = 0 :=
    linearIndepOn_iff'.mp hli b.support _ subset_rfl hcomb
  refine Finset.sum_eq_zero fun j hj => ?_
  have : f j = 0 := by have := hzero j hj; omega
  rw [this, zero_smul]

/-- **A member of the positive root cone that is cancelled by another member is zero**: pointedness
of the cone, in the additive form the weight order uses. -/
theorem eq_zero_of_add_eq_zero_of_mem_posRootCone {u v : M} (hu : u ∈ posRootCone P b)
    (hv : v ∈ posRootCone P b) (huv : u + v = 0) : u = 0 :=
  (isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem hu
    (by rwa [neg_eq_of_add_eq_zero_right huv])

/-- **A positive root is never cancelled inside the positive root cone.** A positive root is a
nonzero member of the cone, so `TauCeti.eq_zero_of_add_eq_zero_of_mem_posRootCone` forbids it. -/
theorem root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone {i : ι} (hi : i ∈ posRoots P b)
    {v : M} (hv : v ∈ posRootCone P b) : P.root i + v ≠ 0 := fun hsum =>
  P.ne_zero i (eq_zero_of_add_eq_zero_of_mem_posRootCone P b
    (root_mem_posRootCone_of_mem_posRoots P b hi) hv hsum)

/-- **A nonempty sum of positive roots is nonzero.** Splitting off one summand, the rest is a
nonnegative integer combination of the simple roots, and a positive root is never cancelled inside
that cone.

This is the integral form of the statement that the positive roots lie in an open half space. It is
what rules out a cycle of weights each obtained from the previous one by adding a positive root, and
so is the reason a maximal weight exists. -/
theorem sum_root_ne_zero_of_mem_posRoots {κ : Type*} {s : Finset κ} (hs : s.Nonempty) {f : κ → ι}
    (hf : ∀ x ∈ s, f x ∈ posRoots P b) :
    ∑ x ∈ s, P.root (f x) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hs
  rw [← Finset.add_sum_erase _ _ hx₀]
  exact root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone P b (hf x₀ hx₀)
    (AddSubmonoid.sum_mem _ fun x hx =>
      root_mem_posRootCone_of_mem_posRoots P b (hf x (Finset.mem_of_mem_erase hx)))

/-- **A simple root dominates only itself.** If a natural multiple of a simple root `αᵢ` exceeds a
positive root `αⱼ` inside the cone `Q⁺`, then `αⱼ` is `αᵢ`.

Expanding both `αⱼ` and the difference in the simple roots and comparing coefficients, which is
legitimate because the simple roots are linearly independent, leaves `αⱼ` a natural multiple of
`αᵢ`; the multiple is `1` because a base contains no proper multiple of one of its members
(`RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem`).

This is the combinatorial input to the integrability relation of a highest weight module: it is
what confines a positive root vector raising the weight `lam - (n + 1) αᵢ` to the single direction
`αᵢ`. -/
theorem eq_of_nsmul_root_sub_root_mem_posRootCone [Finite ι] [IsAddTorsionFree M]
    [IsAddTorsionFree N] {i : ι} (hi : i ∈ b.support) {j : ι} (hj : j ∈ posRoots P b) {n : ℕ}
    (h : n • P.root i - P.root j ∈ posRootCone P b) : j = i := by
  classical
  obtain ⟨c, -, hc⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b hj
  obtain ⟨d, hd⟩ := (mem_posRootCone P b).mp h
  set g : ι → R := fun k => (c k : R) + (d k : R) - (if k = i then (n : R) else 0) with hgdef
  have hsingle : ∑ k ∈ b.support, (if k = i then (n : R) else 0) • P.root k
      = (n : R) • P.root i := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (fun hni => absurd hi hni)]
    simp
  have hzero : ∑ k ∈ b.support, g k • P.root k = 0 := by
    have hsplit : ∑ k ∈ b.support, g k • P.root k
        = ((∑ k ∈ b.support, c k • P.root k) + ∑ k ∈ b.support, d k • P.root k)
          - ∑ k ∈ b.support, (if k = i then (n : R) else 0) • P.root k := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        simp [hgdef, add_smul, sub_smul, Nat.cast_smul_eq_nsmul]
    rw [hsplit, hsingle, ← hc, ← hd, Nat.cast_smul_eq_nsmul]
    abel
  have hg0 : ∀ k ∈ b.support, g k = 0 :=
    linearIndepOn_iff'.mp b.linearIndepOn_root b.support g subset_rfl hzero
  have hc0 : ∀ k ∈ b.support, k ≠ i → c k = 0 := by
    intro k hk hki
    have hif : (if k = i then (n : R) else 0) = 0 := by simp [hki]
    have hgk := hg0 k hk
    rw [hgdef] at hgk
    simp only [hif, sub_zero] at hgk
    have hcast : ((c k + d k : ℕ) : R) = 0 := by push_cast; exact hgk
    have : c k + d k = 0 := by exact_mod_cast hcast
    omega
  have hroot : P.root j = (c i : ℕ) • P.root i := by
    rw [hc, Finset.sum_eq_single i (fun k hk hki => by rw [hc0 k hk hki, zero_smul])
      (fun hni => absurd hi hni)]
  have hmem : (c i : R) • P.root i ∈ Set.range P.root := by
    rw [Nat.cast_smul_eq_nsmul, ← hroot]
    exact Set.mem_range_self j
  rcases b.eq_one_or_neg_one_of_mem_support_of_smul_mem i hi _ hmem with h1 | h1
  · have hci : c i = 1 := by exact_mod_cast h1
    exact P.root.injective (by rw [hroot, hci, one_smul])
  · have hcast : ((c i + 1 : ℕ) : R) = 0 := by push_cast [h1]; ring
    exact absurd (by exact_mod_cast hcast : c i + 1 = 0) (Nat.succ_ne_zero (c i))

/-- Root negation exchanges positive and negative roots. -/
theorem image_reflectionPerm_self_posRoots :
    (fun i ↦ P.reflectionPerm i i) '' posRoots P b = negRoots P b := by
  let := P.indexNeg
  simp_rw [← RootPairing.indexNeg_neg]
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [mem_negRoots, mem_posRoots] at hj ⊢
    intro hneg
    exact (RootPairing.Base.IsPos.neg_iff_not b j).mp hneg hj
  · intro hi
    refine ⟨-i, ?_, neg_neg i⟩
    simp only [mem_negRoots, mem_posRoots] at hi ⊢
    exact (RootPairing.Base.IsPos.neg_iff_not b i).mpr hi

/-- Root negation exchanges negative and positive roots. -/
theorem image_reflectionPerm_self_negRoots :
    (fun i ↦ P.reflectionPerm i i) '' negRoots P b = posRoots P b := by
  have hinv := reflectionPerm_self_involutive P
  calc
    (fun i ↦ P.reflectionPerm i i) '' negRoots P b =
        (fun i ↦ P.reflectionPerm i i) '' (posRoots P b)ᶜ := by rw [negRoots_eq_compl]
    _ = ((fun i ↦ P.reflectionPerm i i) '' posRoots P b)ᶜ :=
      Set.image_compl_eq hinv.bijective
    _ = (negRoots P b)ᶜ := by rw [image_reflectionPerm_self_posRoots]
    _ = posRoots P b := by
      ext i
      simp only [Set.mem_compl_iff, mem_negRoots, mem_posRoots]
      tauto

/-! ### The number of positive roots -/

/-- A root pairing has equally many positive and negative roots. Root negation gives the bijection
between the two sets. -/
@[simp]
theorem ncard_negRoots_eq_ncard_posRoots :
    (negRoots P b).ncard = (posRoots P b).ncard := by
  rw [← image_reflectionPerm_self_posRoots P b]
  exact Set.ncard_image_of_injective _ (reflectionPerm_self_involutive P).injective

/-- The numbers of positive and negative roots add up to the total number of roots. -/
theorem ncard_posRoots_add_ncard_negRoots [Finite ι] :
    (posRoots P b).ncard + (negRoots P b).ncard = Nat.card ι := by
  rw [negRoots_eq_compl]
  exact Set.ncard_add_ncard_compl _

/-- Twice the number of positive roots is the total number of roots. -/
theorem two_mul_ncard_posRoots [Finite ι] :
    2 * (posRoots P b).ncard = Nat.card ι := by
  calc
    2 * (posRoots P b).ncard =
        (posRoots P b).ncard + (posRoots P b).ncard := two_mul _
    _ = (posRoots P b).ncard + (negRoots P b).ncard := by
      rw [ncard_negRoots_eq_ncard_posRoots P b]
    _ = Nat.card ι := ncard_posRoots_add_ncard_negRoots P b

/-- Exactly half of a finite root index type consists of positive roots. -/
theorem ncard_posRoots_eq_natCard_div_two [Finite ι] :
    (posRoots P b).ncard = Nat.card ι / 2 :=
  Nat.eq_div_of_mul_eq_right (by norm_num) (two_mul_ncard_posRoots P b)

/-- Reflecting a positive root in a simple root never produces that simple root: the only root
sent to a simple root `αᵢ` by `sᵢ` is `-αᵢ`, which is negative. -/
lemma reflectionPerm_ne_of_mem_posRoots {i j : ι} (hi : i ∈ b.support)
    (hj : j ∈ posRoots P b) :
    P.reflectionPerm i j ≠ i := by
  intro h
  have hji : j = P.reflectionPerm i i := by
    rw [← P.reflectionPerm_self i j, h]
  rw [mem_posRoots, hji, isPos_reflectionPerm_self_iff_mem_negRoots, mem_negRoots] at hj
  exact hj (b.isPos_of_mem_support hi)

/-! ### The simple roots are the indecomposable positive roots -/

section Indecomposable

variable {P b} in
/-- **A simple root is not the sum of two positive roots.** -/
theorem root_ne_add_of_mem_support {i : ι} (hi : i ∈ b.support) {j k : ι}
    (hj : b.IsPos j) (hk : b.IsPos k) : P.root i ≠ P.root j + P.root k := fun h ↦ by
  -- Heights add, a positive root has height at least `1`, and a simple root has height exactly `1`.
  have hadd := b.height_add h
  rw [b.height_one_of_mem_support hi] at hadd
  rw [RootPairing.Base.isPos_iff] at hj hk
  omega

variable [Finite ι] [IsDomain R] [P.IsCrystallographic]

variable {P b} in
/-- **A positive root that is not simple is a positive root plus a simple root.** -/
theorem exists_isPos_root_eq_add_of_notMem_support {i : ι} (hi : b.IsPos i)
    (hi' : i ∉ b.support) :
    ∃ j ∈ b.support, ∃ k, b.IsPos k ∧ P.root i = P.root k + P.root j := by
  -- Some simple root pairs positively with `i`, so subtracting it leaves a root, and that root is
  -- still positive because only a height `1` was removed.
  obtain ⟨j, hj, hj'⟩ := hi.exists_mem_support_pos_pairingIn
  rw [P.zero_lt_pairingIn_iff'] at hj'
  have hij : i ≠ j := by rintro rfl; exact hi' hj
  obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
  exact ⟨j, hj, k, hi.sub hj hk, by rw [hk]; module⟩

variable {P b} in
/-- **The simple roots are exactly the indecomposable positive roots.** This is the description of
the base that mentions only the additive structure of the positive roots, so it is the one that
transports along an additive bijection of the positive roots. -/
theorem mem_support_iff_isPos_and_forall_ne_add {i : ι} :
    i ∈ b.support ↔
      b.IsPos i ∧ ∀ j k, b.IsPos j → b.IsPos k → P.root i ≠ P.root j + P.root k := by
  refine ⟨fun hi ↦ ⟨RootPairing.Base.isPos_of_mem_support hi,
    fun _ _ hj hk ↦ root_ne_add_of_mem_support hi hj hk⟩, fun ⟨hi, hne⟩ ↦ ?_⟩
  by_contra hi'
  obtain ⟨j, hj, k, hk, hjk⟩ := exists_isPos_root_eq_add_of_notMem_support hi hi'
  exact hne k j hk (RootPairing.Base.isPos_of_mem_support hj) hjk

end Indecomposable

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection preserves the set of positive roots other than its own simple root. Both
directions follow from the forward implication because `P.reflectionPerm i` is an involution. -/
lemma reflectionPerm_mem_posRoots_diff_singleton_iff {i : ι} (hi : i ∈ b.support) (j : ι) :
    P.reflectionPerm i j ∈ posRoots P b \ {i} ↔ j ∈ posRoots P b \ {i} := by
  have key : ∀ k : ι, k ∈ posRoots P b \ {i} → P.reflectionPerm i k ∈ posRoots P b \ {i} := by
    rintro k ⟨hkpos, hkne⟩
    have hkne' : k ≠ i := by simpa using hkne
    exact ⟨(mem_posRoots P b _).mpr (((mem_posRoots P b k).mp hkpos).reflectionPerm hi hkne'),
      by simpa using reflectionPerm_ne_of_mem_posRoots P b hi hkpos⟩
  refine ⟨fun h ↦ ?_, key j⟩
  simpa only [P.reflectionPerm_self i j] using key _ h

/-- A simple reflection permutes the positive roots other than its own simple root. -/
theorem bijOn_reflectionPerm_posRoots_diff_singleton {i : ι} (hi : i ∈ b.support) :
    Set.BijOn (P.reflectionPerm i) (posRoots P b \ {i}) (posRoots P b \ {i}) :=
  Set.InvOn.bijOn ⟨fun j _ ↦ P.reflectionPerm_self i j, fun j _ ↦ P.reflectionPerm_self i j⟩
    (fun _ hj ↦ (reflectionPerm_mem_posRoots_diff_singleton_iff P b hi _).mpr hj)
    (fun _ hj ↦ (reflectionPerm_mem_posRoots_diff_singleton_iff P b hi _).mpr hj)

/-- The image form of `bijOn_reflectionPerm_posRoots_diff_singleton`: a simple reflection maps the
positive roots other than its own simple root onto themselves. -/
theorem image_reflectionPerm_posRoots_diff_singleton {i : ι} (hi : i ∈ b.support) :
    P.reflectionPerm i '' (posRoots P b \ {i}) = posRoots P b \ {i} :=
  (bijOn_reflectionPerm_posRoots_diff_singleton P b hi).image_eq

/-- The finset form of `reflectionPerm_mem_posRoots_diff_singleton_iff`. -/
lemma reflectionPerm_mem_posRootsFinset_erase_iff [DecidableEq ι] {i : ι} (hi : i ∈ b.support)
    (j : ι) :
    P.reflectionPerm i j ∈ (posRootsFinset P b).erase i ↔ j ∈ (posRootsFinset P b).erase i := by
  have h := reflectionPerm_mem_posRoots_diff_singleton_iff P b hi j
  simp only [Set.mem_sdiff, Set.mem_singleton_iff] at h
  simp only [Finset.mem_erase, mem_posRootsFinset]
  tauto

/-- **Reindexing along a simple reflection leaves a sum over the other positive roots unchanged.**
Since `sᵢ` permutes the positive roots other than `αᵢ`, summing any function over them is
insensitive to precomposition with `sᵢ`. -/
lemma sum_posRootsFinset_erase_comp_reflectionPerm [DecidableEq ι] {A : Type*} [AddCommMonoid A]
    {i : ι} (hi : i ∈ b.support) (f : ι → A) :
    ∑ j ∈ (posRootsFinset P b).erase i, f (P.reflectionPerm i j)
      = ∑ j ∈ (posRootsFinset P b).erase i, f j :=
  Finset.sum_equiv (P.reflectionPerm i)
    (fun j ↦ (reflectionPerm_mem_posRootsFinset_erase_iff P b hi j).symm) fun _ _ ↦ rfl

namespace RootPairing.Base

/-- A simple reflection preserves and reflects positivity of every root other than its own simple
root and the negative of that simple root. -/
lemma isPos_reflectionPerm_iff {i j : ι} (hj : j ∈ b.support) (hij : i ≠ j)
    (hij' : i ≠ P.reflectionPerm j j) :
    b.IsPos (P.reflectionPerm j i) ↔ b.IsPos i := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reflectionPerm hj hij⟩
  have hne : P.reflectionPerm j i ≠ j := fun hc ↦ hij' (by rw [← P.reflectionPerm_self j i, hc])
  simpa [P.reflectionPerm_self] using h.reflectionPerm hj hne

/-- **A root is positive for a base exactly when its coroot is positive for that base.** -/
@[simp]
theorem isPos_flip_iff [P.flip.IsReduced] (i : ι) : b.flip.IsPos i ↔ b.IsPos i := by
  -- Both sides hold for a simple root, both are exchanged by root negation, and away from a
  -- simple root and its negative both are preserved by the corresponding simple reflection, so
  -- the positive-root induction propagates the equivalence over the whole index type.
  -- The flipped pairing reflects root indices by the very same permutations.
  have hflip : ∀ k l : ι, P.flip.reflectionPerm k l = P.reflectionPerm k l := fun k l ↦ by
    rw [P.flip_reflectionPerm k]
  have hsimple : ∀ k ∈ b.support, (b.flip.IsPos k ↔ b.IsPos k) := fun k hk ↦ by
    simp only [b.isPos_of_mem_support hk, iff_true]
    exact b.flip.isPos_of_mem_support (by simpa using hk)
  have hneg : ∀ k : ι, (b.flip.IsPos k ↔ b.IsPos k) →
      (b.flip.IsPos (P.reflectionPerm k k) ↔ b.IsPos (P.reflectionPerm k k)) := fun k hk ↦ by
    rw [isPos_reflectionPerm_self_iff_mem_negRoots P b k, mem_negRoots P b k, ← hflip k k,
      isPos_reflectionPerm_self_iff_mem_negRoots P.flip b.flip k, mem_negRoots P.flip b.flip k, hk]
  refine b.induction_reflect (p := fun k ↦ b.flip.IsPos k ↔ b.IsPos k) i hneg hsimple
    fun j k hj hk ↦ ?_
  rcases eq_or_ne j k with rfl | hjk
  · exact hneg j hj
  rcases eq_or_ne j (P.reflectionPerm k k) with rfl | hjk'
  · rw [P.reflectionPerm_self k k]
    exact hsimple k hk
  · rw [isPos_reflectionPerm_iff P b hk hjk hjk', ← hflip k j,
      isPos_reflectionPerm_iff P.flip b.flip (by simpa using hk) hjk (by rwa [hflip k k])]
    exact hj

end RootPairing.Base

variable [P.flip.IsReduced]

/-- A base and its flip have the same positive roots. -/
@[simp]
theorem posRoots_flip : posRoots P.flip b.flip = posRoots P b := by
  ext i
  simpa only [mem_posRoots] using RootPairing.Base.isPos_flip_iff P b i

/-- A base and its flip have the same negative roots. -/
@[simp]
theorem negRoots_flip : negRoots P.flip b.flip = negRoots P b := by
  ext i
  simpa only [mem_negRoots] using not_congr (RootPairing.Base.isPos_flip_iff P b i)

/-- The coroot of a positive root is a nonnegative integer combination of the simple coroots. -/
theorem exists_coroot_eq_sum_nat_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) :
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧
      P.coroot i = ∑ j ∈ b.support, f j • P.coroot j := by
  obtain ⟨f, hf, hsum⟩ := exists_root_eq_sum_nat_of_mem_posRoots P.flip b.flip
    (by rw [posRoots_flip]; exact hi)
  exact ⟨f, by simpa using hf, by simpa using hsum⟩

end TauCeti
