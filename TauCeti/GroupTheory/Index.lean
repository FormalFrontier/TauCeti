/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Consequences of the index formula

The preimage `H.comap f` of a finite-index subgroup along a group homomorphism again has finite
index: its index is the relative index of `H` in the range of `f`, which is finite. Adjoining
the centre to a finite-index subgroup also keeps the index finite, since it only enlarges the
subgroup.

Because the order of a subgroup divides the order of the group -- with the index as cofactor --
invertibility of the order of a finite group in a semiring passes to every subgroup.

Adjoining a two-element subgroup `N ⊄ Γ` normalised by `Γ` is also quantified: `Γ` then has
relative index exactly `2` in `Γ ⊔ N`, so `Γ.index = 2 * (Γ ⊔ N).index`. Taking `N` to be the
centre gives the `Γ.withCenter` readings.

## Main results

* `Subgroup.mem_withCenter_iff`: an element of `Γ·Z(G)` is one of `Γ` times a central one.
* `Subgroup.withCenter_le_iff`: the universal property — containing `Γ·Z(G)` is containing both.
* `Subgroup.withCenter_eq_self_iff`: adjoining the centre changes nothing exactly when the
  centre already lies inside `Γ`.
* `Subgroup.relIndex_sup_eq_two`, `Subgroup.index_eq_two_mul_index_sup`: the relative index `2`
  and the index doubling, for an `N` normalised by `Γ` whose elements are `1` and `a ∉ Γ`.
* `Subgroup.relIndex_withCenter_eq_two`, `Subgroup.index_eq_two_mul_index_withCenter`: the same
  two facts on `Γ.withCenter`, when the centre is `{1, a}`.
-/

public section

namespace Subgroup

/-- The preimage of a finite-index subgroup under a group homomorphism has finite index. -/
@[to_additive]
instance instFiniteIndexComap {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) [H.FiniteIndex]
    (f : G' →* G) : (H.comap f).FiniteIndex :=
  ⟨by rw [index_comap]; exact FiniteIndex.index_ne_zero⟩

/-- `Γ` with the centre of the ambient group adjoined. For `Γ ≤ SL(2, ℤ)` the centre is
`{±I}`, which acts trivially on `ℍ`; it is the cosets of `Γ·{±I}` — not those of `Γ` itself —
that name the distinct translates of `𝒟` tiling a `Γ` fundamental domain, since `q` and `-q`
would otherwise be counted as two cosets carrying the same translate. The two subgroups agree
exactly when `-I ∈ Γ`. -/
def withCenter {G : Type*} [Group G] (Γ : Subgroup G) : Subgroup G :=
  Γ ⊔ Subgroup.center G

/-- Unfolding: `Γ.withCenter` is the supremum of `Γ` with the centre. -/
theorem withCenter_def {G : Type*} [Group G] (Γ : Subgroup G) :
    Γ.withCenter = Γ ⊔ Subgroup.center G := (rfl)

/-- `Γ` sits inside `Γ` with the centre adjoined. -/
lemma le_withCenter {G : Type*} [Group G] (Γ : Subgroup G) : Γ ≤ Γ.withCenter :=
  le_sup_left

/-- The centre sits inside `Γ` with the centre adjoined — the other half of the supremum. -/
lemma center_le_withCenter {G : Type*} [Group G] (Γ : Subgroup G) :
    Subgroup.center G ≤ Γ.withCenter :=
  le_sup_right

/-- **The universal property of `withCenter`**: a subgroup contains `Γ·Z(G)` exactly when it
contains both `Γ` and the centre. -/
@[simp]
theorem withCenter_le_iff {G : Type*} [Group G] {Γ H : Subgroup G} :
    Γ.withCenter ≤ H ↔ Γ ≤ H ∧ Subgroup.center G ≤ H :=
  sup_le_iff

/-- **Characteristic membership for `withCenter`**: an element of `Γ·Z(G)` is one of `Γ` times a
central one. -/
-- The product is oriented `γ * c = g` to match `Subgroup.mem_sup_of_normal_right` -- which is
-- what proves it -- and the rest of mathlib's `mem_sup` family.
--
-- Not `@[simp]`, tested: its left-hand side `g ∈ Γ.withCenter` is the same shape as that of the
-- `SL(2, ℤ)`-specific `Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg`, which *is* `@[simp]` and
-- resolves the centre to `{±1}`. Tagging this one too takes that lemma's left-hand side out of
-- simp-normal form -- `simpNF` rejects it -- and would pre-empt the sharper rewrite everywhere
-- the group is `SL(2, ℤ)`.
theorem mem_withCenter_iff {G : Type*} [Group G] {Γ : Subgroup G} {g : G} :
    g ∈ Γ.withCenter ↔ ∃ γ ∈ Γ, ∃ c ∈ Subgroup.center G, γ * c = g :=
  Subgroup.mem_sup_of_normal_right

/-- **Adjoining the centre changes nothing exactly when the centre is already inside `Γ`** —
the other half of the dichotomy `Subgroup.withCenter` describes. -/
@[simp]
theorem withCenter_eq_self_iff {G : Type*} [Group G] {Γ : Subgroup G} :
    Γ.withCenter = Γ ↔ Subgroup.center G ≤ Γ :=
  sup_eq_left

instance instFiniteIndexWithCenter {G : Type*} [Group G] (Γ : Subgroup G)
    [Γ.FiniteIndex] : Γ.withCenter.FiniteIndex :=
  Subgroup.finiteIndex_of_le Γ.le_withCenter

variable {G : Type*} [Group G] {Γ : Subgroup G} {a : G}

/-- **A two-element subgroup normalised by `Γ` and not already inside it has relative index
`2`.** If every element of `N` is `1` or `a`, and `a ∉ Γ`, then `Γ ⊔ N` splits into the two
cosets `Γ` and `Γ * a`.

Only normalisation by `Γ` is asked for, not normality of `N` in the whole group, so a
two-element subgroup normalised by `Γ` alone is covered. A globally normal `N` is the special
case `Subgroup.le_normalizer_of_normal`.

Stated for an arbitrary `N` rather than for the centre, because the centre is often larger than
two elements — in `GL (Fin 2) ℝ` it is every scalar — while the two-element subgroup one actually
wants there is `Subgroup.zpowers (-1)`. A caller supplies whichever `N` is in hand.

`a` is not assumed to be an involution; it follows from the hypotheses that it is one.

Generalises Mathlib's `Subgroup.relindex_adjoinNegOne_eq_two`
(`Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean`) from `𝒢 ≤ GL n R` with `a = -1` to
an arbitrary group. -/
theorem relIndex_sup_eq_two (N : Subgroup G) (hnorm : Γ ≤ Subgroup.normalizer N) (ha : a ∈ N)
    (haΓ : a ∉ Γ) (hN : ∀ c ∈ N, c = 1 ∨ c = a) : Γ.relIndex (Γ ⊔ N) = 2 := by
  have ha2 : a * a = 1 := by
    rcases hN _ (N.mul_mem ha ha) with h | h
    · exact h
    · exact absurd (mul_eq_left.mp h ▸ Γ.one_mem) haΓ
  refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
    ⟨a, Subgroup.mem_sup_right ha, haΓ, fun b hb ↦ ?_⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Γ N hnorm] at hb
  obtain ⟨g, hg, c, hc, rfl⟩ := hb
  rcases hN c hc with rfl | rfl
  · exact Or.inr (by simpa using hg)
  · exact Or.inl (by simpa [mul_assoc, ha2] using hg)

/-- **The index doubles on adjoining a two-element subgroup normalised by `Γ` and not inside
it.** The counting form of `Subgroup.relIndex_sup_eq_two`. -/
theorem index_eq_two_mul_index_sup (N : Subgroup G) (hnorm : Γ ≤ Subgroup.normalizer N)
    (ha : a ∈ N) (haΓ : a ∉ Γ) (hN : ∀ c ∈ N, c = 1 ∨ c = a) :
    Γ.index = 2 * (Γ ⊔ N).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_left : Γ ≤ Γ ⊔ N),
    relIndex_sup_eq_two N hnorm ha haΓ hN]

/-- **When the centre is `{1, a}` and `a ∉ Γ`, `Γ` has relative index exactly `2` in
`Γ.withCenter`.** The centre reading of `Subgroup.relIndex_sup_eq_two`. This is the branch in
which the two subgroups genuinely differ; they coincide exactly when the centre already lies
inside `Γ`.

For `Γ ≤ SL(2, ℤ)` the centre is `{±I}` and `a = -I`, so this is the quantitative form of the
dichotomy recorded on `Subgroup.withCenter`: cosets of `Γ` count each translate of `𝒟` twice
unless `-I ∈ Γ` already. -/
theorem relIndex_withCenter_eq_two (ha : a ∈ Subgroup.center G) (haΓ : a ∉ Γ)
    (hcenter : ∀ c ∈ Subgroup.center G, c = 1 ∨ c = a) : Γ.relIndex Γ.withCenter = 2 :=
  Subgroup.withCenter_def Γ ▸
    relIndex_sup_eq_two _ Subgroup.le_normalizer_of_normal ha haΓ hcenter

/-- **When the centre is `{1, a}` and `a ∉ Γ`, the index of `Γ` is twice that of
`Γ.withCenter`.** The counting form of `Subgroup.relIndex_withCenter_eq_two`: it is
`Γ.withCenter`, not `Γ`, whose cosets index the distinct translates, so a count over `Γ`-cosets is
twice the geometric one. -/
theorem index_eq_two_mul_index_withCenter (ha : a ∈ Subgroup.center G) (haΓ : a ∉ Γ)
    (hcenter : ∀ c ∈ Subgroup.center G, c = 1 ∨ c = a) : Γ.index = 2 * Γ.withCenter.index :=
  Subgroup.withCenter_def Γ ▸
    index_eq_two_mul_index_sup _ Subgroup.le_normalizer_of_normal ha haΓ hcenter

end Subgroup

namespace TauCeti

/-- If the order of a finite group is invertible in `k`, then so is the order of any subgroup,
because the two differ by the index. -/
theorem isUnit_natCard_subgroup {k : Type*} {G : Type*} [Semiring k] [Group G]
    (S : Subgroup G) (hG : IsUnit (Nat.card G : k)) : IsUnit (Nat.card S : k) := by
  have h : IsUnit ((Nat.card S : k) * (S.index : k)) := by
    rwa [← Nat.cast_mul, S.card_mul_index]
  exact ((Nat.cast_commute _ _).isUnit_mul_iff.mp h).1

end TauCeti
