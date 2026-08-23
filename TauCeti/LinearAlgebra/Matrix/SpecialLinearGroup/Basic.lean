/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.ZMod.Units

/-!
# Special linear groups: reduction, the centre, and coordinate descriptions

The natural reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective (strong approximation for
`SL₂`; Shimura §1.6, Serre Ch. VII), and the base-change map `SL(n, R) → GL(n, S)` sends
`-I` to `-I`. Basic coordinate descriptions for `SL₂` and its image under `mapGL` are also
recorded here for downstream matrix computations, together with what the determinant says about
a matrix with a prescribed bottom row `(N, p)`: it is the Bézout relation `m p - n N = 1`.

`mem_center_iff_eq_one_or_eq_neg_one` pins down `±I` itself, which is what the base-change
statement moves around:
over a commutative ring without zero divisors the centre of `SL₂` is exactly `{±I}`, the
scalar form Mathlib gives having no other square roots of `1` to offer.

The surjectivity is ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/SL2Surjection.lean`, Chris Birkbeck). Prerequisite for the
diamond operators of the ModularForms roadmap (Layer 0), where it realizes every unit of
`ZMod N` as the lower-right entry of a matrix in `Γ₀(N)`.

## Main results

* `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`: strong approximation for `SL₂`.
* `Matrix.SpecialLinearGroup.mapGL_neg_one`: `mapGL S (-1) = -1`.
* `Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one`: the determinant-one identity in
  coordinates.
* `Matrix.SpecialLinearGroup.coe_mapGL_fin_two`: the entrywise matrix of `mapGL S` on `SL₂(R)`,
  with `coe_mapGL_int_rat_fin_two` its `ℤ`-to-`ℚ` specialization.
* `Matrix.SpecialLinearGroup.mul_sub_mul_eq_one_of_lowerRow`: a bottom row `(N, p)` gives the
  Bézout relation `m p - n N = 1`.
* `Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one`: the centre of `SL₂` is
  `{±I}` when `R` has no zero divisors.
* `Matrix.SpecialLinearGroup.finite_center` and
  `Matrix.SpecialLinearGroup.card_center_le_two`: that centre is finite, of order at most two.
* `Matrix.SpecialLinearGroup.disjoint_center_iff_neg_one_notMem`: the simp-normal form of the
  `= 1` case, `Disjoint (center _) Γ ↔ -I ∉ Γ`.
* `Matrix.SpecialLinearGroup.card_center_subgroupOf_eq_two_iff` and
  `Matrix.SpecialLinearGroup.card_center_subgroupOf_eq_one_iff`: for a subgroup `Γ ≤ SL₂`, the
  part of the centre that `Γ` contains has order `2` exactly when `-I ∈ Γ` and `1` exactly when
  it does not — both under `-1 ≠ 1`, which fails exactly when `(2 : R) = 0`.
* `Matrix.SpecialLinearGroup.card_center_subgroupOf_eq_one_or_two`: that order is `1` or `2`,
  needing no hypothesis beyond `NoZeroDivisors R`.

## References

* Shimura, *Introduction to the arithmetic theory of automorphic functions*, §1.6
* Serre, *A course in arithmetic*, Ch. VII
-/

public section

open Matrix

open scoped MatrixGroups

variable {d : ℕ}

namespace Matrix.SpecialLinearGroup

/-- The determinant-one identity for an element of `SL₂(R)`, written in coordinates. -/
lemma fin_two_mul_sub_mul_eq_one {R : Type*} [CommRing R] (g : SL(2, R)) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using g.det_coe

/-- The matrix of `mapGL S σ`, written entrywise for `σ ∈ SL₂(R)`. -/
lemma coe_mapGL_fin_two {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (σ : SL(2, R)) :
    (↑(mapGL S σ) : Matrix (Fin 2) (Fin 2) S) =
      !![algebraMap R S (σ 0 0), algebraMap R S (σ 0 1);
        algebraMap R S (σ 1 0), algebraMap R S (σ 1 1)] := by
  rw [mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The rational matrix of `mapGL ℚ σ`, written entrywise for `σ ∈ SL₂(ℤ)`. -/
lemma coe_mapGL_int_rat_fin_two (σ : SL(2, ℤ)) :
    (↑(mapGL ℚ σ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![((σ 0 0 : ℤ) : ℚ), ((σ 0 1 : ℤ) : ℚ);
        ((σ 1 0 : ℤ) : ℚ), ((σ 1 1 : ℤ) : ℚ)] := by
  simpa only [eq_intCast] using coe_mapGL_fin_two (S := ℚ) σ

/-- **The bottom row of an `SL₂(ℤ)` matrix is a Bézout relation.** If it is `(N, p)`, then the
top row `(m, n)` satisfies `m p - n N = 1`. -/
lemma mul_sub_mul_eq_one_of_lowerRow {N p : ℕ} {σ : SL(2, ℤ)} (hσ10 : σ 1 0 = (N : ℤ))
    (hσ11 : σ 1 1 = (p : ℤ)) : σ 0 0 * (p : ℤ) - σ 0 1 * (N : ℤ) = 1 := by
  simpa only [hσ10, hσ11] using fin_two_mul_sub_mul_eq_one σ

/-- `-I` maps to `-I` under `SL(n, R) → GL(n, S)`. -/
@[simp]
lemma mapGL_neg_one {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    [Algebra R S] [Fact (Even (Fintype.card n))] :
    mapGL S (-1 : SpecialLinearGroup n R) = -1 := by
  ext i j
  rcases eq_or_ne i j with h | h <;> simp [mapGL, h]

variable {R : Type*} [CommRing R]

/-- **The centre of `SL₂` is `{±I}`** over any commutative ring without zero divisors.

`Matrix.SpecialLinearGroup.mem_center_iff` puts a central element in scalar form `r • I` with
`r ^ 2 = 1`; without zero divisors the only such scalars are `±1`, which turns that existential
into an alternative. The hypothesis is needed, not incidental — over `ZMod 8` the scalar `3`
also squares to `1`, so the centre is strictly larger than `{±I}` there.

`@[simp]` because the rewrite terminates: it takes a structured membership to a disjunction of
equalities, and nothing rewrites `γ ∈ Subgroup.center _` first — Mathlib's general
`Subgroup.mem_center_iff` is `@[to_additive]` but carries no `simp` attribute. -/
@[simp]
theorem mem_center_iff_eq_one_or_eq_neg_one [NoZeroDivisors R] {γ : SpecialLinearGroup (Fin 2) R} :
    γ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) R) ↔ γ = 1 ∨ γ = -1 := by
  refine ⟨fun hγ ↦ ?_, ?_⟩
  · obtain ⟨r, hr, hscal⟩ := mem_center_iff.mp hγ
    -- `r ^ 2 = 1` has only the two roots because `R` has no zero divisors.
    rcases mul_self_eq_one_iff.mp (by simpa [pow_two] using hr) with rfl | rfl <;> [left; right] <;>
      exact Subtype.ext (by simpa [map_neg, map_one] using hscal.symm)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_center_iff.mpr fun g ↦ by rw [neg_one_mul, mul_neg_one]

/-- The centre of `SL₂` is finite: by `mem_center_iff_eq_one_or_eq_neg_one` it is the set `{±I}`,
which has at most two elements — exactly two unless `1 = -1` in `R`, where it is a singleton. -/
theorem finite_center [NoZeroDivisors R] :
    Finite (Subgroup.center (SpecialLinearGroup (Fin 2) R)) := by
  have hf : Finite ({1, -1} : Set (SpecialLinearGroup (Fin 2) R)) := Set.toFinite _
  -- the type ascription on `e` is load-bearing: without it instance search is asked for
  -- `Finite { x // x = 1 ∨ x = -1 }` and fails, since that subtype is definitionally
  -- `↥({1, -1} : Set _)` but resolution does not see through the membership unfolding
  have e : (Subgroup.center (SpecialLinearGroup (Fin 2) R)) ≃
      ({1, -1} : Set (SpecialLinearGroup (Fin 2) R)) :=
    Equiv.subtypeEquivRight fun _ ↦ mem_center_iff_eq_one_or_eq_neg_one
  exact Finite.of_equiv _ e.symm

/-- **The centre of `SL₂` has at most two elements.** Stated as a bound rather than an equality
because `1 = -1` when `R` has characteristic `2`, where the centre is trivial.

This is a strictly weaker statement than finiteness: `Nat.card` is `0` on an infinite type, so
`≤ 2` alone would also hold for an infinite centre. Callers that need both take `finite_center`
as well. -/
theorem card_center_le_two [NoZeroDivisors R] :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) R)) ≤ 2 := by
  have h : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) R)) =
      Nat.card ({1, -1} : Set (SpecialLinearGroup (Fin 2) R)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_center_iff_eq_one_or_eq_neg_one)
  rw [h, Nat.card_coe_set_eq]
  exact (Set.ncard_insert_le _ _).trans (by simp)

/-- `-I ≠ I` in `SL₂` is exactly `(2 : R) ≠ 0`, read off the `(0,0)` entry. Stated as a helper so
the `@[simp]` lemmas below can take `[NeZero (2 : R)]`, which simp's discharger can settle by
typeclass synthesis, rather than an explicit hypothesis, which it cannot. -/
private theorem neg_one_ne_one_of_neZero_two [NeZero (2 : R)] :
    (-1 : SpecialLinearGroup (Fin 2) R) ≠ 1 := fun h ↦ by
  have h00 := congrArg (fun g : SpecialLinearGroup (Fin 2) R ↦
    (g : Matrix (Fin 2) (Fin 2) R) 0 0) h
  simp only [Fin.isValue, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one,
    Matrix.neg_apply, one_apply_eq] at h00
  exact NeZero.ne (2 : R) (by linear_combination -h00)

/-- **The centre of `SL₂` has exactly two elements** once `-I ≠ I`. `card_center_le_two` is the
unconditional bound; this is the value, and it is what a consumer evaluating the centre factor of
a stabiliser splitting needs. In characteristic `2` the hypothesis fails and the centre is the
singleton `{I}`. -/
theorem card_center_eq_two [NoZeroDivisors R]
    (hne : (-1 : SpecialLinearGroup (Fin 2) R) ≠ 1) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) R)) = 2 := by
  have h : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) R)) =
      Nat.card ({1, -1} : Set (SpecialLinearGroup (Fin 2) R)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_center_iff_eq_one_or_eq_neg_one)
  rw [h, Nat.card_coe_set_eq]
  exact Set.ncard_pair (Ne.symm hne)

-- the count is between one and two, and the name says both halves: the identity is always
-- there, and the inclusion of `Γ ⊓ {±I}` into `{±I}` caps it by `card_center_le_two`
private theorem card_center_subgroupOf_pos_and_le_two [NoZeroDivisors R]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) R)) :
    0 < Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) ∧
      Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) ≤ 2 := by
  have : Finite (Subgroup.center (SpecialLinearGroup (Fin 2) R)) := finite_center
  -- `subgroupOf` is `comap` along `Γ.subtype`, so the order divides the centre's outright; the
  -- ascription states the divisibility in `subgroupOf` form rather than `comap` form
  have hdvd : Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) ∣
      Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) R)) :=
    Subgroup.card_comap_dvd_of_injective _ Γ.subtype Γ.subtype_injective
  have hne : Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdvd
    exact Nat.card_pos.ne' hdvd
  have : Finite ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) :=
    Nat.finite_of_card_ne_zero hne
  exact ⟨Nat.card_pos, (Nat.le_of_dvd Nat.card_pos hdvd).trans card_center_le_two⟩

/-- **The complementary case**: the factor is `1` exactly when `-I ∉ Γ`, i.e. when the matrix and
projective stabiliser orders agree. -/
-- Not `@[simp]`, tested: `simpNF` rejects it because the left-hand side is already reducible —
-- `Subgroup.card_eq_one` then `Subgroup.subgroupOf_eq_bot` rewrite
-- `Nat.card (center.subgroupOf Γ) = 1` to `Disjoint (center _) Γ`, so it is not in simp-normal
-- form. The `= 2` companion below has no such reduction and does carry the attribute.
-- `disjoint_center_iff_neg_one_notMem` is the simp-reachable form: it states the same fact at the
-- normal form this one reduces to, so a goal that simp has already rewritten to `Disjoint` is
-- still closed.
theorem card_center_subgroupOf_eq_one_iff [NoZeroDivisors R] [NeZero (2 : R)]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) R)) :
    Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) = 1 ↔
      (-1 : SpecialLinearGroup (Fin 2) R) ∉ Γ := by
  rw [Subgroup.card_eq_one]
  constructor
  · intro h hneg
    -- `-I` would be a second element, so triviality forces it out of `Γ`
    have hx := (Subgroup.eq_bot_iff_forall _).mp h (⟨-1, hneg⟩ : Γ)
      (Subgroup.mem_subgroupOf.mpr (mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)))
    exact neg_one_ne_one_of_neZero_two (by simpa using Subtype.ext_iff.mp hx)
  · intro hneg
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx ↦ ?_
    rcases mem_center_iff_eq_one_or_eq_neg_one.mp (Subgroup.mem_subgroupOf.mp hx) with hx1 | hx1
    · exact Subtype.ext hx1
    · -- `x.2 : ↑x ∈ Γ`, and `hx1` identifies `↑x` with `-I`, so the membership transports
      have hm : (-1 : SpecialLinearGroup (Fin 2) R) ∈ Γ := hx1 ▸ x.2
      exact absurd hm hneg

/-- **`Γ` meets the centre only in the identity exactly when it does not contain `-I`.**
`Disjoint` of subgroups is triviality of the intersection, not emptiness — `1` lies in both
however `Γ` is chosen — so the content is that `-I` is the only other candidate. This is
`card_center_subgroupOf_eq_one_iff` restated at its simp-normal form: `simp` rewrites
`Nat.card (center.subgroupOf Γ) = 1` through `Subgroup.card_eq_one` and
`Subgroup.subgroupOf_eq_bot` into `Disjoint (center _) Γ`, and this is the rule that then
finishes the job. Stating it separately is what makes the `= 1` case simp-reachable at all,
since the cardinality form cannot itself carry `@[simp]`.

Needs `(2 : R) ≠ 0` for the same reason as the `= 2` companion: in characteristic `2` the centre
is the singleton `{I}`, so it is disjoint from every `Γ` — while `-I = I ∈ Γ` for *every* `Γ`,
including `⊥`, since `I` always lies in a subgroup. Without the hypothesis the equivalence fails
for all `Γ`, not merely for nontrivial ones. -/
@[simp]
theorem disjoint_center_iff_neg_one_notMem [NoZeroDivisors R] [NeZero (2 : R)]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) R)) :
    Disjoint (Subgroup.center (SpecialLinearGroup (Fin 2) R)) Γ ↔
      (-1 : SpecialLinearGroup (Fin 2) R) ∉ Γ := by
  rw [← Subgroup.subgroupOf_eq_bot, ← Subgroup.card_eq_one]
  exact card_center_subgroupOf_eq_one_iff Γ

/-- **The `±I` factor is `2` exactly when `-I ∈ Γ`.** The part of the centre that `Γ` contains is
`{I}` or `{±I}` according to whether `Γ` contains `-I`, so the centre factor in the stabiliser
splitting for a subgroup of `SL₂` is decided by that single membership.

Needs `-1 ≠ 1`: in characteristic `2` the centre is the singleton `{I}` and the count is always
`1`. The unindexed `card_center_subgroupOf_eq_one_or_two` needs no such hypothesis. -/
@[simp]
theorem card_center_subgroupOf_eq_two_iff [NoZeroDivisors R] [NeZero (2 : R)]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) R)) :
    Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) = 2 ↔
      (-1 : SpecialLinearGroup (Fin 2) R) ∈ Γ := by
  obtain ⟨hpos, hle⟩ := card_center_subgroupOf_pos_and_le_two Γ
  constructor
  · intro h
    by_contra hneg
    have h1 := (card_center_subgroupOf_eq_one_iff Γ).mpr hneg
    omega
  · intro hneg
    have h1 : Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) ≠ 1 :=
      fun h ↦ (card_center_subgroupOf_eq_one_iff Γ).mp h hneg
    omega

/-- **The `±I` factor is always `1` or `2`**, with no hypothesis on `R` beyond `NoZeroDivisors`:
the `= 1` case is what characteristic `2` gives, where `-I = I` and the centre is the singleton
`{I}`. This is the form for a consumer that needs only the two-way split and not the `-I ∈ Γ`
membership that decides between them. -/
theorem card_center_subgroupOf_eq_one_or_two [NoZeroDivisors R]
    (Γ : Subgroup (SpecialLinearGroup (Fin 2) R)) :
    Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) = 1 ∨
      Nat.card ((Subgroup.center (SpecialLinearGroup (Fin 2) R)).subgroupOf Γ) = 2 := by
  -- no `-1 ≠ 1` hypothesis: the disjunction is exactly `0 < n ≤ 2`, and when `1 = -1` the
  -- centre is a singleton so the first branch holds
  obtain ⟨hpos, hle⟩ := card_center_subgroupOf_pos_and_le_two Γ
  omega

/-- The `(1,0)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
@[simp]
lemma inv_apply_one_zero (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 1 0 = -(M 1 0) := by
  rw [SL2_inv_expl]
  rfl

/-- The `(1,1)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
@[simp]
lemma inv_apply_one_one (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 1 1 = M 0 0 := by
  rw [SL2_inv_expl]
  rfl

/-- The `(0,0)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
@[simp]
lemma inv_apply_zero_zero (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 0 0 = M 1 1 := by
  rw [SL2_inv_expl]
  rfl

/-- The `(0,1)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
@[simp]
lemma inv_apply_zero_one (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 0 1 = -(M 0 1) := by
  rw [SL2_inv_expl]
  rfl

private lemma mul_apply_one_zero (M g : SpecialLinearGroup (Fin 2) R) :
    (M * g) 1 0 = M 1 0 * g 0 0 + M 1 1 * g 1 0 := by
  simp [coe_mul, mul_apply, Fin.sum_univ_two]

private lemma mul_apply_zero_zero (M g : SpecialLinearGroup (Fin 2) R) :
    (M * g) 0 0 = M 0 0 * g 0 0 + M 0 1 * g 1 0 := by
  simp [coe_mul, mul_apply, Fin.sum_univ_two]

private lemma inv_mul_one_zero_eq_zero
    (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) : (M⁻¹ * g) 1 0 = 0 := by
  rw [mul_apply_one_zero, inv_apply_one_zero, inv_apply_one_one, ← h0, ← h1]
  ring

private lemma inv_mul_zero_zero_eq_one
    (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) : (M⁻¹ * g) 0 0 = 1 := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 :=
    fin_two_mul_sub_mul_eq_one M
  rw [mul_apply_zero_zero, inv_apply_zero_zero, inv_apply_zero_one, ← h0, ← h1]
  linear_combination hdet

/-- An element of `SL₂(ℤ/dℤ)` with first column `(1, 0)` is upper unitriangular, and lifts
to `SL₂(ℤ)` as a transvection, by lifting its upper-right entry. -/
private lemma exists_map_eq_of_col_eq (h : SpecialLinearGroup (Fin 2) (ZMod d))
    (h00 : h 0 0 = 1) (h10 : h 1 0 = 0) :
    ∃ τ : SpecialLinearGroup (Fin 2) ℤ,
      SpecialLinearGroup.map (Int.castRingHom (ZMod d)) τ = h := by
  obtain ⟨t₀, ht₀⟩ := ZMod.intCast_surjective (h 0 1)
  have h11 : h 1 1 = 1 := by
    have hdet := fin_two_mul_sub_mul_eq_one h
    rw [h00, h10] at hdet
    linear_combination hdet
  refine ⟨transvection (by decide : (0 : Fin 2) ≠ 1) t₀, ?_⟩
  ext i j
  simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
    transvection_coe]
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, ht₀]

/-- **Strong approximation for `SL₂` over `ℤ`**: the reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is
surjective. -/
theorem map_intCast_zmod_surjective :
    Function.Surjective (SpecialLinearGroup.map (Int.castRingHom (ZMod d)) :
      SpecialLinearGroup (Fin 2) ℤ →* SpecialLinearGroup (Fin 2) (ZMod d)) := by
  intro g
  obtain ⟨a₀, c₀, ha₀, hc₀, hcop⟩ := (g.isCoprime_col 0).exists_int_lifts
  obtain ⟨σ, hσ0, hσ1⟩ := hcop.exists_SL2_col (0 : Fin 2)
  set M := SpecialLinearGroup.map (Int.castRingHom (ZMod d)) σ with hMdef
  have hentry : ∀ i j, M i j = ((σ i j : ℤ) : ZMod d) := fun i j => by
    rw [hMdef]
    simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]
  have hcol0 : M 0 0 = g 0 0 := by rw [hentry, hσ0, ha₀]
  have hcol1 : M 1 0 = g 1 0 := by rw [hentry, hσ1, hc₀]
  obtain ⟨τ, hτ⟩ := exists_map_eq_of_col_eq (M⁻¹ * g)
    (inv_mul_zero_zero_eq_one M g hcol0 hcol1) (inv_mul_one_zero_eq_zero M g hcol0 hcol1)
  exact ⟨σ * τ, by rw [map_mul, ← hMdef, hτ, mul_inv_cancel_left]⟩

end Matrix.SpecialLinearGroup
