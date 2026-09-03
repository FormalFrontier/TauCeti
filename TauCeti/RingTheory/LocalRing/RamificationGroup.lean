/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The ramification filtration of a group acting on a local ring

Let `G` act by ring automorphisms on a local ring `S`. The **ramification groups** of the action
are the decreasing family of subgroups

`ramificationGroup G S i = {σ | ∀ x : S, σ • x - x ∈ 𝔪 ^ (i + 1)}`,

indexed by `i : ℤ` with the convention that `𝔪 ^ 0 = ⊤`, so that the family is total and equals
`⊤` below `0`. This is Serre's lower-numbering filtration `G_i`, written here for the pair
`(G, S)` rather than for an extension of local fields: nothing in the definition, and nothing in
the results below, uses a valuation on a fraction field. The filtration of a finite Galois
extension of nonarchimedean local fields is the case `G = L ≃ₐ[K] L`, `S = 𝒪[L]`.

Mathlib's `Ideal.inertia` already names `{σ | ∀ x, σ • x - x ∈ I}` for an ideal `I`; the content
here is the family it forms as `I` runs through the powers of the maximal ideal, together with the
integer indexing that Herbrand theory uses.

## Main definitions

* `TauCeti.IsLocalRing.ramificationGroup G S i`: the `i`-th ramification group, for `i : ℤ`.
* `TauCeti.IsLocalRing.ramificationGroupReal G S u`: the same family reindexed by a real number
  through `⌈·⌉`, the convention under which the step function is constant on `(i - 1, i]`.

## Main results

* `TauCeti.IsLocalRing.ramificationGroup_eq_top_of_le_neg_one` and
  `TauCeti.IsLocalRing.ramificationGroup_antitone`: the filtration starts at `⊤` and decreases.
* `TauCeti.IsLocalRing.ramificationGroup_zero`: `G_0` is the kernel of the action on the residue
  field, and `TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertiaSubgroup` identifies it with
  Mathlib's `ValuationSubring.inertiaSubgroup` for a valuation subring of a field.
* `TauCeti.IsLocalRing.instNormalRamificationGroup`: each `G_i` is normal in `G`.
* `TauCeti.IsLocalRing.iInf_ramificationGroup` and
  `TauCeti.IsLocalRing.exists_ramificationGroup_eq_bot`: for a faithful action on a Noetherian
  local ring the filtration separates points, and it is trivial from some index on when `G` is
  finite.
* `TauCeti.IsLocalRing.mem_ramificationGroup_iff_of_adjoin_eq_top`: when `S` is monogenic over a
  base ring `R` whose elements `G` fixes, membership in `G_i` is decided at the generator alone.
* `TauCeti.IsLocalRing.mem_ramificationGroup_iff_le_addVal`: over a discrete valuation ring the
  defining condition is the valuation inequality `v (σ x - x) ≥ i + 1`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968corpslocaux], Chapter IV, §1.
-/

public section

open IsLocalRing

namespace TauCeti

namespace IsLocalRing

section Defs

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The `i`-th **ramification group**, in the lower numbering, of a group `G` acting by ring
automorphisms on a local ring `S`: the subgroup of elements acting trivially on `S ⧸ 𝔪 ^ (i + 1)`.
The index is an integer, and `𝔪 ^ (i + 1)` is read as `𝔪 ^ (i + 1).toNat`, so that the family is
total and constantly `⊤` for `i ≤ -1`. -/
def ramificationGroup (i : ℤ) : Subgroup G :=
  Ideal.inertia G (maximalIdeal S ^ (i + 1).toNat)

variable {G S}

/-- The defining membership criterion of the ramification groups. -/
theorem mem_ramificationGroup_iff {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S ^ (i + 1).toNat :=
  Ideal.mem_inertia

/-- At a nonnegative index the truncation disappears from the membership criterion. -/
theorem mem_ramificationGroup_natCast_iff {n : ℕ} {σ : G} :
    σ ∈ ramificationGroup G S n ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S ^ (n + 1) := by
  have h : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [mem_ramificationGroup_iff, h]

/-- Membership in `G_i` says that `σ` acts trivially on `S ⧸ 𝔪 ^ (i + 1)`. -/
theorem mem_ramificationGroup_iff_quotient_mk_smul_eq {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ∀ x : S,
      Ideal.Quotient.mk (maximalIdeal S ^ (i + 1).toNat) (σ • x) =
        Ideal.Quotient.mk (maximalIdeal S ^ (i + 1).toNat) x := by
  simp [mem_ramificationGroup_iff, Ideal.Quotient.eq]

variable (G S)

/-- Below the index `0` the filtration is the whole group. -/
theorem ramificationGroup_eq_top_of_le_neg_one {i : ℤ} (hi : i ≤ -1) :
    ramificationGroup G S i = ⊤ := by
  have h : (i + 1).toNat = 0 := by omega
  ext σ
  simp [mem_ramificationGroup_iff, h]

/-- The ramification filtration is decreasing. -/
theorem ramificationGroup_antitone : Antitone (ramificationGroup G S) := by
  intro i j hij σ hσ
  rw [mem_ramificationGroup_iff] at hσ ⊢
  exact fun x ↦ Ideal.pow_le_pow_right (by omega) (hσ x)

end Defs

section Adjoin

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
variable {R : Type*} [CommRing R] [Algebra R S] [SMulCommClass G R S]

/-- **Serre's criterion.** When `S` is generated over `R` by a single element `ξ` and `G` acts by
`R`-algebra automorphisms, membership in `G_i` is decided at `ξ` alone: the elements moved into
`𝔪 ^ (i + 1)` form an `R`-subalgebra. This is what makes the filtration computable, and it applies
to the integer ring of a finite separable extension of local fields through local monogenicity. -/
theorem mem_ramificationGroup_iff_of_adjoin_eq_top {ξ : S} (hξ : Algebra.adjoin R {ξ} = ⊤)
    {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ σ • ξ - ξ ∈ maximalIdeal S ^ (i + 1).toNat := by
  rw [mem_ramificationGroup_iff]
  refine ⟨fun h ↦ h ξ, fun h x ↦ ?_⟩
  have hx : x ∈ Algebra.adjoin R {ξ} := hξ ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap r =>
      have hr : σ • algebraMap R S r = algebraMap R S r := by simp
      rw [hr, sub_self]
      exact zero_mem _
  | add y z _ _ hy hz =>
      have hyz : σ • (y + z) - (y + z) = (σ • y - y) + (σ • z - z) := by
        rw [smul_add]; ring
      rw [hyz]
      exact add_mem hy hz
  | mul y z _ _ hy hz =>
      have hyz : σ • (y * z) - y * z = σ • y * (σ • z - z) + (σ • y - y) * z := by
        rw [smul_mul']; ring
      rw [hyz]
      exact add_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ hy)

end Adjoin

section Normal

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- A group acting by ring automorphisms on a local ring preserves the powers of the maximal
ideal. -/
theorem smul_mem_maximalIdeal_pow (σ : G) {n : ℕ} {x : S} (hx : x ∈ maximalIdeal S ^ n) :
    σ • x ∈ maximalIdeal S ^ n := by
  have hsurj : Function.Surjective (MulSemiringAction.toRingHom G S σ) :=
    fun y ↦ ⟨σ⁻¹ • y, smul_inv_smul σ y⟩
  have hmap : (maximalIdeal S ^ n).map (MulSemiringAction.toRingHom G S σ) =
      maximalIdeal S ^ n := by
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective _ hsurj]
  exact hmap ▸ Ideal.mem_map_of_mem (MulSemiringAction.toRingHom G S σ) hx

/-- Every ramification group is normal, because the action preserves the powers of the maximal
ideal. -/
instance instNormalRamificationGroup (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] (i : ℤ) : (ramificationGroup G S i).Normal where
  conj_mem σ hσ τ := by
    rw [mem_ramificationGroup_iff] at hσ ⊢
    intro x
    have h : (τ * σ * τ⁻¹) • x - x = τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) := by
      simp [mul_smul, smul_sub]
    rw [h]
    exact smul_mem_maximalIdeal_pow τ (hσ _)

end Normal

section ResidueField

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

private theorem mem_ker_toRingAut_iff {k : Type*} [Ring k] [MulSemiringAction G k] {σ : G} :
    σ ∈ MonoidHom.ker (MulSemiringAction.toRingAut G k) ↔ ∀ y : k, σ • y = y := by
  simp [MonoidHom.mem_ker, RingEquiv.ext_iff]

/-- The zeroth ramification group is the inertia group: the kernel of the induced action on the
residue field. -/
theorem ramificationGroup_zero :
    ramificationGroup G S 0 = MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField S)) := by
  ext σ
  rw [mem_ramificationGroup_iff, mem_ker_toRingAut_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have hx : residue S (σ • x - x) = 0 := by
      rw [residue_eq_zero_iff]
      simpa using h x
    rwa [map_sub, ResidueField.residue_smul, sub_eq_zero] at hx
  · intro h x
    have hx : residue S (σ • x - x) = 0 := by
      rw [map_sub, ResidueField.residue_smul, sub_eq_zero]
      exact h (residue S x)
    rw [residue_eq_zero_iff] at hx
    simpa using hx

/-- For a valuation subring of a field, the zeroth ramification group of the decomposition
subgroup is Mathlib's `ValuationSubring.inertiaSubgroup`. -/
theorem ramificationGroup_zero_eq_inertiaSubgroup (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) :
    ramificationGroup (A.decompositionSubgroup K) A 0 = A.inertiaSubgroup K :=
  ramificationGroup_zero _ _

end ResidueField

section Separated

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
variable [IsNoetherianRing S] [FaithfulSMul G S]

/-- A faithful action on a Noetherian local ring is separated by its ramification filtration. -/
theorem iInf_ramificationGroup : ⨅ i : ℤ, ramificationGroup G S i = ⊥ := by
  refine le_antisymm (fun σ hσ ↦ ?_) bot_le
  rw [Subgroup.mem_iInf] at hσ
  refine Subgroup.mem_bot.2 (eq_of_smul_eq_smul fun x : S ↦ ?_)
  have hmem : σ • x - x ∈ ⨅ n : ℕ, maximalIdeal S ^ n := by
    refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
    have h : (((n : ℤ) - 1) + 1).toNat = n := by omega
    have := mem_ramificationGroup_iff.1 (hσ ((n : ℤ) - 1)) x
    rwa [h] at this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal S).ne_top,
    Ideal.mem_bot, sub_eq_zero] at hmem
  rw [hmem, one_smul]

/-- For a faithful action of a finite group on a Noetherian local ring the ramification groups
vanish from some index on. -/
theorem exists_ramificationGroup_eq_bot [Finite G] :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i → ramificationGroup G S i = ⊥ := by
  classical
  have key : ∀ σ : G, σ ≠ 1 → ∃ i : ℤ, σ ∉ ramificationGroup G S i := by
    intro σ hσ
    by_contra hcon
    push Not at hcon
    refine hσ ?_
    have hmem : σ ∈ ⨅ i : ℤ, ramificationGroup G S i := Subgroup.mem_iInf.2 hcon
    rw [iInf_ramificationGroup] at hmem
    exact hmem
  choose! f hf using key
  obtain ⟨N, hN⟩ := (Set.finite_range f).bddAbove
  refine ⟨N, fun i hi ↦ eq_bot_iff.2 fun σ hσi ↦ ?_⟩
  by_contra hσ
  rw [Subgroup.mem_bot] at hσ
  exact hf σ hσ
    (ramificationGroup_antitone G S ((hN (Set.mem_range_self σ)).trans hi) hσi)

end Separated

section DiscreteValuationRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [MulSemiringAction G S]

/-- Membership in a power of the maximal ideal of a discrete valuation ring, read on the additive
valuation. -/
theorem mem_maximalIdeal_pow_iff_le_addVal {n : ℕ} {x : S} :
    x ∈ maximalIdeal S ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal S x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow]

/-- Over a discrete valuation ring the ramification groups are cut out by the valuation
inequality `v (σ x - x) ≥ i + 1`, which is Serre's definition. -/
theorem mem_ramificationGroup_iff_le_addVal {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔
      ∀ x : S, ((i + 1).toNat : ℕ∞) ≤ IsDiscreteValuationRing.addVal S (σ • x - x) := by
  simp only [mem_ramificationGroup_iff, mem_maximalIdeal_pow_iff_le_addVal]

end DiscreteValuationRing

section Subgroup

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The ramification filtration of a subgroup is the trace on it of the ramification filtration of
the ambient group. -/
theorem subgroupOf_ramificationGroup (H : Subgroup G) (i : ℤ) :
    (ramificationGroup G S i).subgroupOf H = ramificationGroup H S i :=
  AddSubgroup.subgroupOf_inertia _ H

end Subgroup

section Real

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The ramification filtration reindexed by a real number, through the ceiling. This is the
indexing convention of Herbrand theory: the resulting step function is constant on `(i - 1, i]`. -/
noncomputable def ramificationGroupReal (u : ℝ) : Subgroup G :=
  ramificationGroup G S ⌈u⌉

@[simp]
theorem ramificationGroupReal_intCast (i : ℤ) :
    ramificationGroupReal G S (i : ℝ) = ramificationGroup G S i := by
  rw [ramificationGroupReal, Int.ceil_intCast]

/-- The real indexing is constant on the interval `(i - 1, i]`. -/
theorem ramificationGroupReal_eq_of_sub_one_lt_of_le {i : ℤ} {u : ℝ} (hleft : (i : ℝ) - 1 < u)
    (hright : u ≤ i) : ramificationGroupReal G S u = ramificationGroup G S i := by
  rw [ramificationGroupReal, Int.ceil_eq_iff.2 ⟨hleft, hright⟩]

end Real

end IsLocalRing

end TauCeti
