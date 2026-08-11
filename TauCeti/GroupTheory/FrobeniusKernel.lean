/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# The Frobenius kernel and its size

Let `H` be a trivial-intersection subgroup of a group `G` (`TauCeti.IsTISubgroup`). The
**Frobenius kernel** of `H` is the set of elements of `G` lying in no conjugate of `H`, together
with the identity:

`frobeniusKernel H = {1} ∪ (G ∖ ⋃ g, g H g⁻¹)`.

This file builds that set and computes its size: it has exactly `H.index` elements
(`TauCeti.IsTISubgroup.ncard_frobeniusKernel`), equivalently
`#(frobeniusKernel H) * |H| = |G|`. That `frobeniusKernel H` is moreover a *subgroup*, and a
normal complement to `H`, is Frobenius's theorem, which is not proved here: it needs the
exceptional-character machinery, and the counting below is the numerical half that leaves
"complement" as the only possible answer once the subgroup property is known.

The count is a fibre count, not an inclusion-exclusion. The elements *outside* the kernel are the
values of `(g, x) ↦ g x g⁻¹` on the pairs with `x ∈ H` and `x ≠ 1`, and the trivial-intersection
hypothesis says exactly that every fibre of that map is a left coset of `H`, so has `|H|` elements.
There are `|G| * (|H| - 1)` such pairs, so the complement of the kernel has `|G| * (|H| - 1) / |H|`
elements and the kernel has the remaining `|G| / |H|`.

The trivial-intersection hypothesis alone is what the count needs; properness and nontriviality of
`H`, the two further conditions in `TauCeti.IsFrobeniusComplement`, are not used, and the two
degenerate cases are honest instances of the formula: `frobeniusKernel ⊥ = Set.univ` with `⊥` of
index `|G|`, and `frobeniusKernel ⊤ = {1}` with `⊤` of index `1`.

## Main definitions

* `TauCeti.frobeniusKernel`: the identity together with the elements lying in no conjugate of `H`.

## Main results

* `TauCeti.frobeniusKernel_eq_insert_one_compl_iUnion`: the kernel written as
  `{1} ∪ (⋃ g, g H g⁻¹)ᶜ`, the shape the name refers to.
* `TauCeti.frobeniusKernel_inter_coe`: the kernel meets `H` only in the identity, so a complement
  is the most it could be.
* `TauCeti.conj_mem_frobeniusKernel_iff`: the kernel is closed under conjugation, the set-level
  shadow of the normality that Frobenius's theorem asserts.
* `TauCeti.IsTISubgroup.ncard_frobeniusKernel_mul_card` and
  `TauCeti.IsTISubgroup.ncard_frobeniusKernel`: **the kernel has `H.index` elements.**
* `TauCeti.IsTISubgroup.exists_ne_one_mem_frobeniusKernel`: for a proper trivial-intersection
  subgroup the kernel contains a nonidentity element, its number of elements being the index of
  `H`, which is greater than one. Whether that set is a subgroup is not settled here.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 7.
* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 8, "Frobenius groups and Frobenius's theorem", whose second item asks for
  `frobeniusKernel H = {1} ∪ (G ∖ ⋃_g (g H g⁻¹))`, "a set of size `|G : H|`".
-/

public section

namespace TauCeti

open scoped Pointwise

variable {G : Type*} [Group G] {H : Subgroup G}

/-! ### The Frobenius kernel as a set -/

/-- **The Frobenius kernel** of a subgroup `H` of `G`: the elements of `G` lying in no conjugate of
`H`, together with the identity.

Stated as the implication "if some conjugate of `x` lies in `H` then `x = 1`", which is the form
every proof below uses; `TauCeti.frobeniusKernel_eq_insert_one_compl_iUnion` is the equivalent
description `{1} ∪ (⋃ g, g H g⁻¹)ᶜ` that the name refers to. Frobenius's theorem, for `H` a
Frobenius complement, says this set is a normal subgroup complementing `H`; here only its size is
computed. -/
def frobeniusKernel (H : Subgroup G) : Set G := {x | ∀ g : G, g * x * g⁻¹ ∈ H → x = 1}

/-- The defining condition of `TauCeti.frobeniusKernel`, as an `Iff`: the definition is not
exposed, so this is how membership is introduced and eliminated outside this file. -/
theorem mem_frobeniusKernel {x : G} :
    x ∈ frobeniusKernel H ↔ ∀ g : G, g * x * g⁻¹ ∈ H → x = 1 :=
  Iff.rfl

/-- Failure to lie in the Frobenius kernel: `x` is a nonidentity element some conjugate of which
lies in `H`. -/
theorem notMem_frobeniusKernel {x : G} :
    x ∉ frobeniusKernel H ↔ x ≠ 1 ∧ ∃ g : G, g * x * g⁻¹ ∈ H := by
  constructor
  · intro hx
    have hx1 : x ≠ 1 := fun h => hx (mem_frobeniusKernel.mpr fun _ _ => h)
    refine ⟨hx1, ?_⟩
    by_contra hcon
    exact hx (mem_frobeniusKernel.mpr fun g hg => absurd ⟨g, hg⟩ hcon)
  · rintro ⟨hx1, g, hg⟩ hmem
    exact hx1 (mem_frobeniusKernel.mp hmem g hg)

/-- The identity lies in the Frobenius kernel. -/
@[simp]
theorem one_mem_frobeniusKernel : (1 : G) ∈ frobeniusKernel H :=
  mem_frobeniusKernel.mpr fun _ _ => rfl

/-- **The Frobenius kernel is closed under inverses**: a conjugate of `x⁻¹` lies in `H` exactly
when the corresponding conjugate of `x` does. -/
@[simp]
theorem inv_mem_frobeniusKernel_iff {x : G} :
    x⁻¹ ∈ frobeniusKernel H ↔ x ∈ frobeniusKernel H := by
  have key : ∀ y : G, y ∈ frobeniusKernel H → y⁻¹ ∈ frobeniusKernel H := by
    refine fun y hy => mem_frobeniusKernel.mpr fun g hg => ?_
    have hmem : g * y * g⁻¹ ∈ H := by
      simpa [mul_assoc] using H.inv_mem hg
    simp [mem_frobeniusKernel.mp hy g hmem]
  exact ⟨fun hx => by simpa using key x⁻¹ hx, key x⟩

/-- **The Frobenius kernel is closed under conjugation.** This is the set-level shadow of the
normality that Frobenius's theorem asserts once the kernel is known to be a subgroup: conjugating
`x` only reindexes the conjugates of `H` that `x` is tested against. -/
@[simp]
theorem conj_mem_frobeniusKernel_iff {x a : G} :
    a * x * a⁻¹ ∈ frobeniusKernel H ↔ x ∈ frobeniusKernel H := by
  have key : ∀ y b : G, y ∈ frobeniusKernel H → b * y * b⁻¹ ∈ frobeniusKernel H := by
    refine fun y b hy => mem_frobeniusKernel.mpr fun g hg => ?_
    have hmem : g * b * y * (g * b)⁻¹ ∈ H := by
      simpa [mul_assoc] using hg
    simp [mem_frobeniusKernel.mp hy (g * b) (by simpa [mul_assoc] using hmem)]
  refine ⟨fun hx => ?_, fun hx => key x a hx⟩
  have h := key _ a⁻¹ hx
  rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at h

/-- **The Frobenius kernel meets `H` only in the identity**, `H` being one of its own conjugates.
A complement to `H` is therefore the most the kernel could be, which is what Frobenius's theorem
confirms. -/
theorem frobeniusKernel_inter_coe : frobeniusKernel H ∩ (H : Set G) = {1} := by
  ext x
  refine ⟨fun hx => mem_frobeniusKernel.mp hx.1 1 (by simpa using hx.2), ?_⟩
  rintro rfl
  exact ⟨one_mem_frobeniusKernel, H.one_mem⟩

/-- **The Frobenius kernel in the shape its name refers to**: the identity together with the
elements lying in no conjugate of `H`. -/
theorem frobeniusKernel_eq_insert_one_compl_iUnion :
    frobeniusKernel H = insert 1 (⋃ g : G, ((MulAut.conj g • H : Subgroup G) : Set G))ᶜ := by
  have key : ∀ g y : G, y ∈ (MulAut.conj g • H : Subgroup G) ↔ g⁻¹ * y * g ∈ H := by
    intro g y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, key,
    not_exists, mem_frobeniusKernel]
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr fun g hg => hx1 (hx g⁻¹ (by simpa using hg))
  · rintro (rfl | hx) g hg
    · rfl
    · exact absurd (by simpa using hg) (hx g⁻¹)

/-- The Frobenius kernel of the trivial subgroup is everything: no nonidentity element lies in a
conjugate of `⊥`. Matching the count below, `⊥` has index `|G|`. -/
@[simp]
theorem frobeniusKernel_bot : frobeniusKernel (⊥ : Subgroup G) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, mem_frobeniusKernel, Subgroup.mem_bot]
  exact fun g hg => mul_eq_left.mp (mul_inv_eq_one.mp hg)

/-- The Frobenius kernel of the whole group is trivial: every element lies in the only conjugate of
`⊤`. Matching the count below, `⊤` has index `1`. -/
@[simp]
theorem frobeniusKernel_top : frobeniusKernel (⊤ : Subgroup G) = {1} := by
  ext x
  exact ⟨fun hx => mem_frobeniusKernel.mp hx 1 (by simp),
    fun hx => mem_frobeniusKernel.mpr fun _ _ => hx⟩

/-! ### The size of the kernel

The complement of the kernel is the image of `(g, x) ↦ g x g⁻¹` on the pairs with `x` a
nonidentity element of `H`, and the trivial-intersection hypothesis makes each fibre of that map a
left coset of `H`; that fibre description is
`TauCeti.IsTISubgroup.inv_mul_mem_and_eq_of_conj_eq_conj`, stated about group elements before any
counting happens. -/

namespace IsTISubgroup

variable [Finite G]

/-- **The Frobenius kernel of a trivial-intersection subgroup has `|G| / |H|` elements**, in the
multiplicative form that avoids the division.

Both sides are counted inside `G`: the elements outside the kernel are exactly the values
`g x g⁻¹` for `x` a nonidentity element of `H`; there are `|G| * (|H| - 1)` such pairs `(g, x)`;
and every fibre of `(g, x) ↦ g x g⁻¹` is a left coset of `H`
(`TauCeti.IsTISubgroup.inv_mul_mem_and_eq_of_conj_eq_conj`), so has `|H|` elements. -/
theorem ncard_frobeniusKernel_mul_card (hH : IsTISubgroup H) :
    (frobeniusKernel H).ncard * Nat.card H = Nat.card G := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  -- The cardinality of a subset of `G`, read as the cardinality of the corresponding filter.
  have hfilter : ∀ s : Set G, (Finset.univ.filter fun x => x ∈ s).card = s.ncard := fun s => by
    rw [Set.ncard_eq_toFinset_card' s]
    congr 1
    ext x
    simp
  have hcardH : (Finset.univ.filter fun x : G => x ∈ H).card = Nat.card H := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- The pairs to be counted, and the conjugation map on them.
  set P : Finset (G × G) := Finset.univ.filter fun p : G × G => p.2 ∈ H ∧ p.2 ≠ 1 with hPdef
  have hmemP : ∀ p : G × G, p ∈ P ↔ p.2 ∈ H ∧ p.2 ≠ 1 := fun p => by rw [hPdef]; simp
  set m : G × G → G := fun p => p.1 * p.2 * p.1⁻¹ with hmdef
  -- There are `|G| * (|H| - 1)` pairs.
  have hP : P.card = Nat.card G * (Nat.card H - 1) := by
    have hprod : P = Finset.univ ×ˢ ((Finset.univ.filter fun x : G => x ∈ H).erase 1) := by
      ext p
      rw [hmemP p, Finset.mem_product]
      simp [and_comm]
    rw [hprod, Finset.card_product, Finset.card_erase_of_mem (by simp), hcardH, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  -- Their image is the complement of the kernel.
  have himage : P.image m = Finset.univ.filter fun x : G => x ∉ frobeniusKernel H := by
    ext u
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      notMem_frobeniusKernel]
    constructor
    · rintro ⟨⟨g, x⟩, hgx, rfl⟩
      obtain ⟨hxH, hx1⟩ := (hmemP (g, x)).mp hgx
      refine ⟨fun hcon => hx1 ?_, g⁻¹, by simp [hmdef, mul_assoc, hxH]⟩
      have := congrArg (fun y : G => g⁻¹ * y * g) hcon
      simpa [hmdef, mul_assoc] using this
    · rintro ⟨hu1, g, hg⟩
      refine ⟨(g⁻¹, g * u * g⁻¹), (hmemP _).mpr ⟨hg, ?_⟩, by simp [hmdef]; group⟩
      intro hcon
      refine hu1 ?_
      have := congrArg (fun y : G => g⁻¹ * y * g) hcon
      simpa [mul_assoc] using this
  -- Every fibre of the map is a left coset of `H`.
  have hfibre : ∀ u ∈ P.image m, (P.filter fun p => m p = u).card = Nat.card H := by
    intro u hu
    obtain ⟨⟨g₀, x₀⟩, hg₀, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hx₀H, hx₀1⟩ := (hmemP (g₀, x₀)).mp hg₀
    rw [← hcardH]
    refine (Finset.card_bij (fun h _ => ((g₀ * h, h⁻¹ * x₀ * h) : G × G)) ?_ ?_ ?_).symm
    · intro h hh
      have hh' : h ∈ H := by simpa using hh
      refine Finset.mem_filter.mpr ⟨(hmemP _).mpr ⟨H.mul_mem (H.mul_mem (H.inv_mem hh') hx₀H) hh',
        ?_⟩, by simp only [hmdef]; group⟩
      intro hcon
      have hcon' : h⁻¹ * x₀ * h = 1 := hcon
      refine hx₀1 ?_
      calc x₀ = h * (h⁻¹ * x₀ * h) * h⁻¹ := by group
        _ = 1 := by rw [hcon']; group
    · intro h₁ _ h₂ _ heq
      exact mul_left_cancel (congrArg Prod.fst heq)
    · rintro ⟨g, x⟩ hgx
      obtain ⟨hmem, hconj⟩ := Finset.mem_filter.mp hgx
      obtain ⟨hxH, -⟩ := (hmemP (g, x)).mp hmem
      obtain ⟨hcos, hxeq⟩ := hH.inv_mul_mem_and_eq_of_conj_eq_conj hx₀H hx₀1 hxH hconj
      refine ⟨g₀⁻¹ * g, by simpa using hcos, ?_⟩
      rw [Prod.ext_iff]
      exact ⟨by group, hxeq.symm⟩
  -- Counting the pairs fibre by fibre.
  have hcount : P.card =
      (Finset.univ.filter fun x : G => x ∉ frobeniusKernel H).card * Nat.card H := by
    rw [Finset.card_eq_sum_card_image m P, Finset.sum_congr rfl hfibre, Finset.sum_const,
      smul_eq_mul, himage]
  -- The kernel and its complement partition `G`.
  have hpart : (Finset.univ.filter fun x : G => x ∈ frobeniusKernel H).card +
      (Finset.univ.filter fun x : G => x ∉ frobeniusKernel H).card = Nat.card G := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Nat.card_eq_fintype_card]
  -- Arithmetic: `|H|` is positive, so the two counts determine the size of the kernel.
  obtain ⟨n, hn⟩ : ∃ n, Nat.card H = n + 1 :=
    ⟨Nat.card H - 1, (Nat.succ_pred_eq_of_pos Nat.card_pos).symm⟩
  rw [← hfilter (frobeniusKernel H), hn]
  rw [hn, Nat.add_sub_cancel] at hP
  rw [hn] at hcount
  refine Nat.add_right_cancel (m := Nat.card G * n) ?_
  calc (Finset.univ.filter fun x : G => x ∈ frobeniusKernel H).card * (n + 1) + Nat.card G * n
      = (Finset.univ.filter fun x : G => x ∈ frobeniusKernel H).card * (n + 1) +
          (Finset.univ.filter fun x : G => x ∉ frobeniusKernel H).card * (n + 1) := by
        rw [← hcount, hP]
    _ = ((Finset.univ.filter fun x : G => x ∈ frobeniusKernel H).card +
          (Finset.univ.filter fun x : G => x ∉ frobeniusKernel H).card) * (n + 1) := by ring
    _ = Nat.card G * (n + 1) := by rw [hpart]
    _ = Nat.card G + Nat.card G * n := by ring

/-- **The Frobenius kernel of a trivial-intersection subgroup has exactly `H.index` elements.**
This is the count that Frobenius's theorem upgrades: the kernel is a normal subgroup, and a
subgroup of that size meeting `H` trivially (`TauCeti.frobeniusKernel_inter_coe`) is a complement
to `H`. -/
theorem ncard_frobeniusKernel (hH : IsTISubgroup H) :
    (frobeniusKernel H).ncard = H.index :=
  Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (hH.ncard_frobeniusKernel_mul_card.trans H.index_mul_card.symm)

/-- **The Frobenius kernel of a proper trivial-intersection subgroup is nontrivial**: a proper
subgroup has index greater than one, and that index is the size of the kernel. -/
theorem one_lt_ncard_frobeniusKernel (hH : IsTISubgroup H) (hne : H ≠ ⊤) :
    1 < (frobeniusKernel H).ncard := by
  rw [hH.ncard_frobeniusKernel]
  refine lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr H.index_ne_zero_of_finite) fun hcon => ?_
  exact hne (Subgroup.index_eq_one.mp hcon.symm)

/-- There is a nonidentity element lying in no conjugate of a proper trivial-intersection
subgroup. -/
theorem exists_ne_one_mem_frobeniusKernel (hH : IsTISubgroup H) (hne : H ≠ ⊤) :
    ∃ x, x ∈ frobeniusKernel H ∧ x ≠ 1 :=
  Set.exists_ne_of_one_lt_ncard (hH.one_lt_ncard_frobeniusKernel hne) 1

end IsTISubgroup

namespace IsFrobeniusComplement

variable [Finite G]

/-- The Frobenius kernel of a Frobenius complement has `H.index` elements. -/
theorem ncard_frobeniusKernel (hH : IsFrobeniusComplement H) :
    (frobeniusKernel H).ncard = H.index :=
  hH.isTISubgroup.ncard_frobeniusKernel

/-- **The Frobenius kernel of a Frobenius complement is nontrivial**: a Frobenius complement is a
proper subgroup, so its index is greater than one. -/
theorem one_lt_ncard_frobeniusKernel (hH : IsFrobeniusComplement H) :
    1 < (frobeniusKernel H).ncard :=
  hH.isTISubgroup.one_lt_ncard_frobeniusKernel hH.ne_top

/-- There is a nonidentity element lying in no conjugate of a Frobenius complement. -/
theorem exists_ne_one_mem_frobeniusKernel (hH : IsFrobeniusComplement H) :
    ∃ x, x ∈ frobeniusKernel H ∧ x ≠ 1 :=
  hH.isTISubgroup.exists_ne_one_mem_frobeniusKernel hH.ne_top

end IsFrobeniusComplement

end TauCeti
