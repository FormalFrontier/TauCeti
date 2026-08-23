/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

import Mathlib.Algebra.Field.ZMod
import TauCeti.Data.ZMod.Divisibility

/-!
# Congruence subgroups: the pair `Γ₁(N) ⊴ Γ₀(N)`, the index of `Γ₀(pᵏ)`, and the level

Foundational results about the pair `Γ₁(N) ≤ Γ₀(N)` beyond Mathlib's
`Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`: `Γ₀(N)` normalizes `Γ₁(N)` (also
after mapping to `GL₂(ℝ)`), the ratio of two `Γ₀(N)`-elements with equal lower-right entry
lies in `Γ₁(N)`, the lower-right-entry map `Γ₀(N) →* (ZMod N)ˣ` is surjective, and the
location of `-I`: it always lies in `Γ₀(N)`, with lower-right entry the unit `-1`, and it
lies in `Γ₁(N)` exactly when `N ∣ 2`; and every power of the translation matrix `T` lies in
`Γ₁(N)`, at every level.  The file then computes the index of `Γ₀` at
prime-power levels — the degree count of Shimura, Theorem 3.24 — which lives here because it
is congruence-subgroup arithmetic consumed by, but independent of, the Hecke-ring layer.

A final section records how the *principal* congruence subgroups compose with the arithmetic
of the level: `Γ` is antitone in the level like the other two families, and the join of two
of them is the principal congruence subgroup of the gcd, `Γ(gcd a b) = Γ(a) ⊔ Γ(b)`. That
identity is Shimura's Lemma 3.28; it is the Chinese remainder theorem for `SL₂`, and it is
what lets a Hecke operator at level `ab` be analysed one prime at a time.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`, for the index section
`LeanModularForms/HeckeRIngs/GL2/CongruenceIndex.lean`, for the level-antitonicity
lemmas `LeanModularForms/HeckeRIngs/GL2/LevelEmbed.lean`, and for the gcd decomposition
`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Foundation.lean`, all Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), extracted from
`TauCeti/NumberTheory/ModularForms/DiamondOperators.lean` as congruence-subgroup
infrastructure independent of the diamond operators.

## Main results

* `CongruenceSubgroup.Gamma1_le_Gamma1_of_dvd`, `CongruenceSubgroup.Gamma0_le_Gamma0_of_dvd`,
  `CongruenceSubgroup.Gamma_le_Gamma_of_dvd`: all three families are antitone in the level,
  `Γ(N) ≤ Γ(M)` whenever `M ∣ N`.
* `CongruenceSubgroup.mem_Gamma1_iff`: `Γ₁(N)` is cut out inside `Γ₀(N)` by the
  single congruence `d ≡ 1`.
* `CongruenceSubgroup.isUnit_intCast_apply_zero_zero_of_mem_Gamma0`: a `Γ₀(N)` matrix has
  unit upper-left entry modulo `N`.
* `CongruenceSubgroup.intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0`: modulo its
  level, a `Γ₀(N)` matrix has mutually inverse diagonal entries.
* `CongruenceSubgroup.Gamma0_normalizes_Gamma1` and
  `CongruenceSubgroup.Gamma0_le_normalizer_Gamma1`: conjugation by `Γ₀(N)` preserves `Γ₁(N)`.
* `CongruenceSubgroup.Gamma1_map_le_Gamma0_map`: the inclusion `Γ₁(N) ≤ Γ₀(N)` after mapping to
  `GL₂(ℝ)`.
* `CongruenceSubgroup.Gamma1_map_inv_conjAct_eq`: `(Gamma1 N).map (mapGL ℝ)` is invariant
  under conjugation by `Γ₀(N)` elements in `GL₂(ℝ)`.
* `CongruenceSubgroup.Gamma0Map_toHomUnits_surjective`: every unit of `ZMod N` is the
  lower-right entry of a matrix in `Γ₀(N)` (via strong approximation for `SL₂`).
* `CongruenceSubgroup.gamma0Twist`: an explicit `Γ₀(N)` element whose lower-right entry is any
  natural number coprime to `N`.
* `CongruenceSubgroup.neg_one_mem_Gamma0` and
  `CongruenceSubgroup.Gamma0Map_toHomUnits_negOne`: `-I ∈ Γ₀(N)`, with lower-right entry the
  unit `-1`; `CongruenceSubgroup.neg_one_mem_Gamma1_iff`: `-I ∈ Γ₁(N) ↔ N ∣ 2`.
* `CongruenceSubgroup.Gamma0_prime_index`: `[SL₂(ℤ) : Γ₀(p)] = p + 1` for prime `p`.
* `CongruenceSubgroup.Gamma0_relIndex_pow_succ`: `[Γ₀(pᵏ) : Γ₀(p^(k+1))] = p` for `0 < p`
  and `0 < k`.
* `CongruenceSubgroup.Gamma0_prime_power_index`: `[SL₂(ℤ) : Γ₀(pᵏ)] = p^(k-1) * (p + 1)` for
  prime `p` and `k ≥ 1`.
* `CongruenceSubgroup.Gamma_gcd_eq_sup`: `Γ(gcd a b) = Γ(a) ⊔ Γ(b)` — Shimura's Lemma 3.28,
  the Chinese remainder theorem for `SL₂`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Lemma 3.28 and Theorem 3.24.
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups Pointwise

variable {N : ℕ}

namespace CongruenceSubgroup

/-- `Γ₁` is antitone in the level: if `M ∣ N` then `Γ₁(N) ≤ Γ₁(M)`, since reducing the
congruences `a ≡ d ≡ 1`, `c ≡ 0` modulo `N` along `ZMod N → ZMod M` gives them modulo `M`. -/
theorem Gamma1_le_Gamma1_of_dvd {M N : ℕ} (h : M ∣ N) : Gamma1 N ≤ Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  exact ⟨by simpa [map_intCast, map_one, map_zero] using congr_arg (ZMod.castHom h (ZMod M)) hA.1,
    by simpa [map_intCast, map_one, map_zero] using congr_arg (ZMod.castHom h (ZMod M)) hA.2.1,
    by simpa [map_intCast, map_one, map_zero] using congr_arg (ZMod.castHom h (ZMod M)) hA.2.2⟩

/-- `Γ` is antitone in the level: if `M ∣ N` then `Γ(N) ≤ Γ(M)`, by reducing the four
congruences along `ZMod N → ZMod M`. The `Γ₀`/`Γ₁` cases are below and above. -/
theorem Gamma_le_Gamma_of_dvd {M N : ℕ} (h : M ∣ N) : Gamma N ≤ Gamma M := by
  intro A hA
  rw [Gamma_mem] at hA ⊢
  exact ⟨by simpa [map_intCast, map_one, map_zero] using congr_arg (ZMod.castHom h (ZMod M)) hA.1,
    by simpa [map_intCast, map_one, map_zero] using congr_arg (ZMod.castHom h (ZMod M)) hA.2.1,
    by simpa [map_intCast, map_one, map_zero] using
      congr_arg (ZMod.castHom h (ZMod M)) hA.2.2.1,
    by simpa [map_intCast, map_one, map_zero] using
      congr_arg (ZMod.castHom h (ZMod M)) hA.2.2.2⟩

/-- `Γ(N) ≤ Γ₀(N)`: the principal congruence subgroup sits inside `Γ₀(N)`, since `c ≡ 0` is
one of the four congruences it imposes. -/
theorem Gamma_le_Gamma0 (N : ℕ) : Gamma N ≤ Gamma0 N := fun _ hA ↦
  Gamma0_mem.mpr (Gamma_mem.mp hA).2.2.1

/-- `Γ₀` is antitone in the level: if `M ∣ N` then `Γ₀(N) ≤ Γ₀(M)`. -/
theorem Gamma0_le_Gamma0_of_dvd {M N : ℕ} (h : M ∣ N) : Gamma0 N ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  simpa [map_intCast, map_one, map_zero] using congr_arg (ZMod.castHom h (ZMod M)) hA

/-- **`Γ₁(N)` is the fibre of `Gamma0Map` over `1`.** A matrix lies in `Γ₁(N)` exactly when it
lies in `Γ₀(N)` and its lower-right entry is `1` modulo `N`; the congruence `a ≡ 1` that
`CongruenceSubgroup.Gamma1_mem` also asks for is then forced by the determinant. This is the
form in which membership is checked whenever a construction produces a `Γ₀(N)` matrix and
controls only its lower-right entry. -/
theorem mem_Gamma1_iff {γ : SL(2, ℤ)} :
    γ ∈ Gamma1 N ↔ γ ∈ Gamma0 N ∧ ((γ 1 1 : ℤ) : ZMod N) = 1 :=
  ⟨fun h ↦ ⟨Gamma1_in_Gamma0 N h, (Gamma1_mem N γ).mp h |>.2.1⟩,
    fun ⟨h₀, h₁⟩ ↦ (Gamma1_mem N γ).mpr ((Gamma1_to_Gamma0_mem ⟨γ, h₀⟩).mp h₁)⟩

/-- **The diagonal entries of a `Γ₀(M)` matrix are mutually inverse modulo `M`**: the determinant
identity `ad - bc = 1` with the `bc` term killed by `M ∣ c`. It refines
`CongruenceSubgroup.isUnit_intCast_apply_zero_zero_of_mem_Gamma0` by naming the inverse. -/
theorem intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 {M : ℕ}
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  have h := congrArg (Int.cast : ℤ → ZMod M) hdet
  push_cast at h
  rw [Gamma0_mem.mp hγ] at h
  linear_combination h

/-- The upper-left entry of a `Γ₀(N)` matrix is a unit modulo `N`: the determinant is one
and the lower-left entry vanishes modulo `N`, so `ad ≡ 1`. -/
theorem isUnit_intCast_apply_zero_zero_of_mem_Gamma0 {N : ℕ} {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N) :
    IsUnit ((σ.1 0 0 : ℤ) : ZMod N) := by
  have h10 : ((σ.1 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hσ
  have hdet : σ.1 0 0 * σ.1 1 1 - σ.1 0 1 * σ.1 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one σ
  have hcast := congrArg (fun z : ℤ ↦ (z : ZMod N)) hdet
  push_cast at hcast
  rw [h10, mul_zero, sub_zero] at hcast
  exact IsUnit.of_mul_eq_one _ hcast

/-- Conjugation by a `Gamma0 N` element preserves `Gamma1 N`.
This is the foundation for the diamond operator `⟨d⟩` on modular forms. -/
theorem Gamma0_normalizes_Gamma1 (g : ↥(Gamma0 N)) (h : SL(2, ℤ)) (hh : h ∈ Gamma1 N) :
    (g : SL(2, ℤ)) * h * (g : SL(2, ℤ))⁻¹ ∈ Gamma1 N :=
  (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp <|
    (Gamma0Map N).normal_ker.conj_mem ⟨h, Gamma1_in_Gamma0 N hh⟩
      ((Gamma1_to_Gamma0_mem _).mpr ((Gamma1_mem _ _).mp hh)) g

/-- `Γ₀(N)` lies in the normaliser of `Γ₁(N)`: the statement of `Gamma0_normalizes_Gamma1` in
the form the coset combinatorics of the Petersson product consumes. -/
theorem Gamma0_le_normalizer_Gamma1 (N : ℕ) :
    Gamma0 N ≤ Subgroup.normalizer (Gamma1 N : Set SL(2, ℤ)) := fun g hg ↦
  Subgroup.mem_normalizer_iff.mpr fun h ↦
    ⟨Gamma0_normalizes_Gamma1 ⟨g, hg⟩ h, fun hh ↦ by
      simpa [mul_assoc] using
        Gamma0_normalizes_Gamma1 ⟨g⁻¹, (Gamma0 N).inv_mem hg⟩ _ hh⟩

/-- The inclusion `Γ₁(N) ≤ Γ₀(N)`, transported to `GL₂(ℝ)`. -/
theorem Gamma1_map_le_Gamma0_map (N : ℕ) :
    (Gamma1 N).map (mapGL ℝ) ≤ (Gamma0 N).map (mapGL ℝ) :=
  Subgroup.map_mono (Gamma1_in_Gamma0 N)

/-- `(Gamma1 N).map (mapGL ℝ)` is invariant under conjugation by `Gamma0 N` elements
in `GL₂(ℝ)`. -/
theorem Gamma1_map_inv_conjAct_eq (g : ↥(Gamma0 N)) :
    ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ)))⁻¹ •
    (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, hσy⟩
    have hmem : (g : SL(2, ℤ))⁻¹ * σ * (g : SL(2, ℤ)) ∈ Gamma1 N := by
      simpa [inv_inv] using Gamma0_normalizes_Gamma1
        ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩ σ hσ
    exact ⟨_, hmem, by
      simp only [map_mul, map_inv, hσy]
      group⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨(g : SL(2, ℤ)) * σ * (g : SL(2, ℤ))⁻¹,
      Gamma0_normalizes_Gamma1 g σ hσ, by simp [map_mul, map_inv]⟩

/-- If two `Γ₀(N)` elements have equal image under `Gamma0Map`, their ratio
`g₁ · g₂⁻¹` lies in `Γ₁(N)` (as an `SL₂(ℤ)` element). -/
lemma mul_inv_mem_Gamma1_of_Gamma0Map_eq (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) ∈ Gamma1 N := by
  have hker : g₁ * g₂⁻¹ ∈ (Gamma0Map N).ker := by
    rw [← div_eq_mul_inv]
    exact (MonoidHom.div_mem_ker_iff (Gamma0Map N)).mpr heq
  exact (Gamma1_mem _ _).mpr <| (Gamma1_to_Gamma0_mem _).mp hker

/-- The diagonal matrix `!![u⁻¹, 0; 0, u]` as an element of `SL₂(ZMod N)`. -/
private def diagUnit (u : (ZMod N)ˣ) : SpecialLinearGroup (Fin 2) (ZMod N) :=
  ⟨!![(↑u⁻¹ : ZMod N), 0; 0, ↑u], by simp [det_fin_two_of]⟩

private lemma coe_diagUnit (u : (ZMod N)ˣ) :
    (diagUnit u : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![(↑u⁻¹ : ZMod N), 0; 0, ↑u] := rfl

/-- `(Gamma0Map N).toHomUnits` is surjective: every unit `u ∈ (ZMod N)ˣ` is realized as the
lower-right entry of some `g ∈ Gamma0 N`, by strong approximation for `SL₂`. -/
theorem Gamma0Map_toHomUnits_surjective :
    Function.Surjective ((Gamma0Map N).toHomUnits) := fun u ↦ by
  obtain ⟨g, hg⟩ := map_intCast_zmod_surjective (diagUnit u)
  have hentry : ∀ i j, ((g i j : ℤ) : ZMod N) =
      (!![(↑u⁻¹ : ZMod N), 0; 0, ↑u] : Matrix (Fin 2) (Fin 2) (ZMod N)) i j := fun i j => by
    have h := congrArg
      (fun A : SpecialLinearGroup (Fin 2) (ZMod N) => (A : Matrix (Fin 2) (Fin 2) (ZMod N)) i j)
      hg
    simpa only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
      coe_diagUnit] using h
  have h10 : ((g 1 0 : ℤ) : ZMod N) = 0 := by rw [hentry]; simp
  have h11 : ((g 1 1 : ℤ) : ZMod N) = u := by rw [hentry]; simp
  exact ⟨⟨g, Gamma0_mem.mpr h10⟩, Units.ext (by simpa [Gamma0Map] using h11)⟩

/-- A Bézout matrix with bottom row `(N, p)`, for `p` coprime to `N`. -/
noncomputable def gamma0Twist (N p : ℕ) (h : Nat.Coprime p N) : SL(2, ℤ) :=
  ((Nat.isCoprime_iff_coprime.mpr h.symm : IsCoprime (N : ℤ) (p : ℤ)).exists_SL2_row 1).choose

/-- The lower-left entry of the Bézout twist is `N`. -/
@[simp] lemma gamma0Twist_apply_one_zero {p : ℕ} (h : Nat.Coprime p N) :
    gamma0Twist N p h 1 0 = (N : ℤ) := by
  exact ((Nat.isCoprime_iff_coprime.mpr h.symm :
    IsCoprime (N : ℤ) (p : ℤ)).exists_SL2_row 1).choose_spec.1

/-- The lower-right entry of the Bézout twist is `p`. -/
@[simp] lemma gamma0Twist_apply_one_one {p : ℕ} (h : Nat.Coprime p N) :
    gamma0Twist N p h 1 1 = (p : ℤ) := by
  exact ((Nat.isCoprime_iff_coprime.mpr h.symm :
    IsCoprime (N : ℤ) (p : ℤ)).exists_SL2_row 1).choose_spec.2

/-- The Bézout twist lies in `Γ₀(N)`. -/
lemma gamma0Twist_mem_Gamma0 {p : ℕ} (h : Nat.Coprime p N) : gamma0Twist N p h ∈ Gamma0 N := by
  rw [Gamma0_mem, gamma0Twist_apply_one_zero h]
  simp

/-- The unit-valued lower-right entry of the Bézout twist is the residue class of `p`. -/
lemma Gamma0Map_toHomUnits_gamma0Twist {p : ℕ} (h : Nat.Coprime p N) :
    (Gamma0Map N).toHomUnits ⟨gamma0Twist N p h, gamma0Twist_mem_Gamma0 h⟩ =
      ZMod.unitOfCoprime p h :=
  Units.ext (by simp [Gamma0Map, gamma0Twist_apply_one_one h])

/-- `-I` lies in `Γ₀(N)`: its lower-left entry is `0`. -/
theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  simp

/-- `-I ∈ Γ₀(N)`, packaged as an element of the subgroup. It is the representative through
which the diamond operator at `-1` is computed. -/
def Gamma0.negOne (N : ℕ) : ↥(Gamma0 N) := ⟨-1, neg_one_mem_Gamma0⟩

@[simp]
lemma Gamma0.coe_negOne (N : ℕ) : (Gamma0.negOne N : SL(2, ℤ)) = -1 := (rfl)

/-- The lower-right entry of `-I ∈ Γ₀(N)` is `-1`. -/
@[simp]
theorem Gamma0Map_negOne : Gamma0Map N (Gamma0.negOne N) = -1 := by
  simp [Gamma0Map, Gamma0.coe_negOne]

/-- The unit-valued lower-right entry of `-I ∈ Γ₀(N)` is the unit `-1`. -/
@[simp]
theorem Gamma0Map_toHomUnits_negOne :
    (Gamma0Map N).toHomUnits (Gamma0.negOne N) = -1 :=
  Units.ext (by simp)

/-- `-I` lies in `Γ₁(N)` exactly when `N ∣ 2`, i.e. for `N ∈ {1, 2}`. This is the degenerate
range in which `Γ₁(N)` contains `-I`, so that all odd-weight forms for it vanish. -/
theorem neg_one_mem_Gamma1_iff : (-1 : SL(2, ℤ)) ∈ Gamma1 N ↔ N ∣ 2 := by
  have h : (-1 : ZMod N) = 1 ↔ N ∣ 2 := by
    rw [neg_eq_iff_add_eq_zero, ← ZMod.natCast_eq_zero_iff 2 N]
    norm_num
  simp [Gamma1_mem, h]

/-- **Every power of the translation matrix lies in `Γ₁(N)`, at every level.** `Tⁿ` has diagonal
`(1, 1)` and vanishing lower-left entry, so the three congruences of `Gamma1_mem` hold with no
condition on `n` or `N`. (In particular the width of the cusp `∞` for `Γ₁(N)` is `1`.) -/
theorem T_zpow_mem_Gamma1 (N : ℕ) (n : ℤ) : ModularGroup.T ^ n ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.coe_T_zpow]

/-! ## The index of `Γ₀(pᵏ)`

The coset representatives of `Γ₀(p)` in `SL₂(ℤ)` are `TʲS` for `0 ≤ j < p` together with the
identity, giving `[SL₂(ℤ) : Γ₀(p)] = p + 1`; the relative index of `Γ₀(p^(k+1))` in `Γ₀(pᵏ)`
is `p` via lower-unitriangular representatives, and the tower multiplies to
`[SL₂(ℤ) : Γ₀(pᵏ)] = p^(k-1)(p + 1)` for prime `p` and `k ≥ 1` — the degree count of
Shimura, Theorem 3.24. -/

section BaseCase

open ModularGroup

private lemma TjS_00 (j : ℤ) : (T ^ j * S).1 0 0 = j := by
  simp [coe_T_zpow, coe_S]

private lemma TjS_10 (j : ℤ) : (T ^ j * S).1 1 0 = 1 := by
  simp [coe_S]

private lemma TjS_inv_10 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 0 = -1 := by
  rw [inv_apply_one_zero, TjS_10]

private lemma TjS_inv_11 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 1 = j := by
  rw [inv_apply_one_one, TjS_00]


private lemma TjS_inv_mul_10 (j : ℤ) (σ : SL(2, ℤ)) :
    ((T ^ j * S)⁻¹ * σ).1 1 0 = j * σ.1 1 0 - σ.1 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [TjS_inv_10, TjS_inv_11]
  ring

private lemma rep_diff_10 (i j : ℤ) :
    ((T ^ j * S)⁻¹ * (T ^ i * S)).1 1 0 = j - i := by
  rw [TjS_inv_mul_10, TjS_10, TjS_00]
  ring

variable (p : ℕ) (hp : Nat.Prime p)
include hp

private def Gamma0Rep (j : Fin (p + 1)) : SL(2, ℤ) :=
  if j.val < p then T ^ (j.val : ℤ) * S else 1

private lemma Gamma0_prime_index_inj :
    Function.Injective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ hf
  rw [QuotientGroup.eq, Gamma0_mem] at hf
  simp only [Gamma0Rep] at hf
  split_ifs at hf with h1 h2
  · rw [rep_diff_10, ZMod.intCast_zmod_eq_zero_iff_dvd] at hf
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hf (by omega)
    exact Fin.mk_eq_mk.mpr (by omega)
  · rw [mul_one, TjS_inv_10] at hf
    exact absurd hf (by norm_num)
  · rw [inv_one, one_mul, TjS_10] at hf
    exact absurd hf (by norm_num)
  · exact Fin.mk_eq_mk.mpr (by omega)

private lemma Gamma0_prime_index_surj :
    Function.Surjective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  by_cases h : ((σ.1 1 0 : ℤ) : ZMod p) = 0
  · refine ⟨⟨p, p.lt_succ_self⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simpa [Gamma0Rep] using h
  · have hunit : IsUnit ((σ.1 1 0 : ℤ) : ZMod p) := by
      have : Fact (Nat.Prime p) := ⟨hp⟩
      obtain ⟨j, hj⟩ : ∃ j : ZMod p, j * ((σ.1 1 0 : ℤ) : ZMod p) = 1 :=
        Finite.surjective_of_injective (mul_left_injective₀ h) 1
      exact IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at hj)
    obtain ⟨j₀, hj₀⟩ := ZMod.exists_dvd_sub_val_mul p (σ.1 0 0) (σ.1 1 0) hunit
    refine ⟨⟨j₀.val, Nat.lt_succ_of_lt (ZMod.val_lt j₀)⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simp only [Gamma0Rep, ZMod.val_lt j₀, ite_true]
    rwa [TjS_inv_mul_10, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_sub_comm]

/-- `[SL₂(ℤ) : Γ₀(p)] = p + 1` for prime `p`. -/
theorem Gamma0_prime_index : (Gamma0 p).index = p + 1 :=
  Nat.card_eq_of_equiv_fin (Equiv.ofBijective _
    ⟨Gamma0_prime_index_inj p hp, Gamma0_prime_index_surj p hp⟩).symm

end BaseCase

section InductiveStep

variable (p : ℕ)

private def lowerTriRep (k : ℕ) (c : Fin p) : SL(2, ℤ) :=
  ⟨!![1, 0; (c : ℤ) * (p : ℤ) ^ k, 1], by simp [det_fin_two_of]⟩

private lemma lowerTriRep_mem_Gamma0 (k : ℕ) (c : Fin p) :
    lowerTriRep p k c ∈ Gamma0 (p ^ k) := by
  rw [Gamma0_mem]
  simp [lowerTriRep, ← Nat.cast_pow, -Int.natCast_pow]

private lemma lowerTriRep_diff_entry (k : ℕ) (c₁ c₂ : Fin p) :
    ((lowerTriRep p k c₁)⁻¹ * lowerTriRep p k c₂).1 1 0 =
    ((c₂ : ℤ) - (c₁ : ℤ)) * (p : ℤ) ^ k := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [inv_apply_one_zero, inv_apply_one_one]
  simp [lowerTriRep]
  ring

private lemma lowerTriRep_inv_mul_10 (k : ℕ) (c : Fin p) (σ : SL(2, ℤ)) :
    ((lowerTriRep p k c)⁻¹ * σ).1 1 0 = σ.1 1 0 - (c : ℤ) * (p : ℤ) ^ k * σ.1 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [inv_apply_one_zero, inv_apply_one_one]
  simp [lowerTriRep]
  ring

private def relindexRep (k : ℕ) (c : Fin p) : ↥(Gamma0 (p ^ k)) :=
  ⟨lowerTriRep p k c, lowerTriRep_mem_Gamma0 p k c⟩

variable (hp : 0 < p)
include hp

private lemma Gamma0_relindex_step_inj (k : ℕ) :
    Function.Injective (fun c : Fin p ↦
      (QuotientGroup.mk (relindexRep p k c) :
        ↥(Gamma0 (p ^ k)) ⧸ (Gamma0 (p ^ (k + 1))).subgroupOf (Gamma0 (p ^ k)))) := by
  intro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ hf
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Gamma0_mem] at hf
  simp only [relindexRep, InvMemClass.coe_inv, MulMemClass.coe_mul] at hf
  rw [lowerTriRep_diff_entry p, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, pow_succ,
    mul_comm ((↑c₂ : ℤ) - ↑c₁) ((p : ℤ) ^ k),
    mul_dvd_mul_iff_left (pow_ne_zero k (Int.natCast_ne_zero.mpr hp.ne'))] at hf
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hf (by omega)
  exact Fin.mk_eq_mk.mpr (by omega)

private lemma Gamma0_relindex_step_surj (k : ℕ) (hk : 0 < k) :
    Function.Surjective (fun c : Fin p ↦
      (QuotientGroup.mk (relindexRep p k c) :
        ↥(Gamma0 (p ^ k)) ⧸ (Gamma0 (p ^ (k + 1))).subgroupOf (Gamma0 (p ^ k)))) := by
  have : NeZero p := ⟨hp.ne'⟩
  intro x
  obtain ⟨⟨σ, hσ_K⟩, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨q, hq⟩ : (↑(p ^ k) : ℤ) ∣ σ.1 1 0 := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← Gamma0_mem]
  push_cast at hq
  have h00_unit : IsUnit ((σ.1 0 0 : ℤ) : ZMod p) :=
    isUnit_intCast_apply_zero_zero_of_mem_Gamma0 (Gamma0_mem.mpr (by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hq ▸ dvd_mul_of_dvd_left (dvd_pow_self _ hk.ne') q))
  obtain ⟨c₀, hc₀⟩ := ZMod.exists_dvd_sub_val_mul p q (σ.1 0 0) h00_unit
  refine ⟨⟨c₀.val, ZMod.val_lt c₀⟩, ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [relindexRep, InvMemClass.coe_inv, MulMemClass.coe_mul]
  rw [Gamma0_mem, lowerTriRep_inv_mul_10, hq, ZMod.intCast_zmod_eq_zero_iff_dvd, pow_succ]
  push_cast
  calc (p : ℤ) ^ k * (p : ℤ)
      ∣ (p : ℤ) ^ k * (q - ↑c₀.val * σ.1 0 0) := mul_dvd_mul_left _ hc₀
    _ = (p : ℤ) ^ k * q - ↑c₀.val * (p : ℤ) ^ k * σ.1 0 0 := by ring

/-- `[Γ₀(pᵏ) : Γ₀(p^(k+1))] = p` for any positive base `p` and `k ≥ 1`. -/
theorem Gamma0_relIndex_pow_succ (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ (k + 1))).relIndex (Gamma0 (p ^ k)) = p :=
  Nat.card_eq_of_equiv_fin (Equiv.ofBijective _
    ⟨Gamma0_relindex_step_inj p hp k, Gamma0_relindex_step_surj p hp k hk⟩).symm

end InductiveStep

/-- `[SL₂(ℤ) : Γ₀(pᵏ)] = p^(k-1) * (p + 1)` for prime `p` and `k ≥ 1`. -/
theorem Gamma0_prime_power_index (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ k)).index = p ^ (k - 1) * (p + 1) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using Gamma0_prime_index p hp
  | succ m hm ih =>
    rw [Nat.add_sub_cancel,
      ← Subgroup.relIndex_mul_index (Gamma0_le_Gamma0_of_dvd (pow_dvd_pow p m.le_succ)),
      Gamma0_relIndex_pow_succ p hp.pos m hm, ih, ← mul_assoc, ← pow_succ',
      Nat.sub_add_cancel hm]

/-! ### The Chinese-remainder decomposition `Γ(gcd a b) = Γ(a) ⊔ Γ(b)` -/

/-- Two integers agreeing modulo `gcd m n` are simultaneously congruent to a single lift,
modulo `m` and modulo `n`: the Bézout coefficients give the lift explicitly. -/
private lemma exists_int_modEq_of_modEq_gcd {m n x y : ℤ} (h : x ≡ y [ZMOD ↑(Int.gcd m n)]) :
    ∃ z : ℤ, z ≡ x [ZMOD m] ∧ z ≡ y [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  have hbez := Int.gcd_eq_gcd_ab m n
  refine ⟨x + m * (Int.gcdA m n * k), ?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-(Int.gcdA m n * k), by ring⟩
  · refine Int.modEq_iff_dvd.mpr ⟨Int.gcdB m n * k, ?_⟩
    -- `hk : y - x = gcd m n * k` is the divisibility witness; solved for `y` it is the shape
    -- `hbez` can be substituted into.
    have hy : y = x + (↑(Int.gcd m n) : ℤ) * k := by linarith
    rw [hy, hbez]
    ring

/-- Entries of a `Γ(N)` matrix agree with the identity's modulo `N`. -/
private lemma intCast_apply_modEq_one_of_mem_Gamma (N : ℕ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma N) (i j : Fin 2) :
    ((1 : SL(2, ℤ)) i j : ℤ) ≡ (γ i j : ℤ) [ZMOD (N : ℤ)] := by
  rw [Gamma_mem'] at hγ
  have h := congr_fun₂ (congr_arg Subtype.val hγ) i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one, Int.coe_castRingHom] at h
  rw [← ZMod.intCast_eq_intCast_iff]
  simpa [Matrix.one_apply] using h.symm

/-- A lift chosen modulo `lcm a b` reduces correctly modulo any divisor of it. -/
private lemma map_apply_of_dvd_lcm {a b : ℕ}
    (M : Matrix (Fin 2) (Fin 2) ℤ) (β : SL(2, ℤ))
    (hβ : (↑(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (Nat.lcm a b))) β) :
        Matrix (Fin 2) (Fin 2) (ZMod (Nat.lcm a b))) =
      M.map (Int.castRingHom (ZMod (Nat.lcm a b))))
    {m : ℕ} (hm : m ∣ Nat.lcm a b) (i j : Fin 2) :
    (↑(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) β) :
        Matrix (Fin 2) (Fin 2) (ZMod m)) i j = ((M i j : ℤ) : ZMod m) := by
  have hentry : (((β : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (Nat.lcm a b)) =
      ((M i j : ℤ) : ZMod (Nat.lcm a b)) := by
    have := congr_fun₂ hβ i j
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Int.coe_castRingHom] using this
  have := congr_arg (ZMod.castHom hm (ZMod m)) hentry
  simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Int.coe_castRingHom, map_intCast] using this

/-- **A `2 × 2` integer matrix congruent to the identity modulo `a` and to a matrix of
`SL(2, ℤ)` modulo `b` has determinant congruent to `1` modulo `lcm a b`.** -/
private lemma det_fin_two_modEq_one_lcm {a b : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ} {γ : SL(2, ℤ)}
    (hMa : ∀ i j, M i j ≡ ((1 : SL(2, ℤ)) i j : ℤ) [ZMOD (a : ℤ)])
    (hMb : ∀ i j, M i j ≡ (γ i j : ℤ) [ZMOD (b : ℤ)]) :
    M 0 0 * M 1 1 - M 0 1 * M 1 0 ≡ 1 [ZMOD ↑(Nat.lcm a b)] := by
  -- reduction is a ring map, so it carries determinants to determinants (`RingHom.map_det`),
  -- and every matrix of `SL(2, ℤ)` has determinant `1`; the two moduli then differ only in
  -- which matrix `M` is compared against
  have key : ∀ (n : ℕ) (g : SL(2, ℤ)), (∀ i j, M i j ≡ (g i j : ℤ) [ZMOD (n : ℤ)]) →
      M 0 0 * M 1 1 - M 0 1 * M 1 0 ≡ 1 [ZMOD (n : ℤ)] := by
    intro n g hM
    have hmap : (Int.castRingHom (ZMod n)).mapMatrix M =
        (Int.castRingHom (ZMod n)).mapMatrix (g : Matrix (Fin 2) (Fin 2) ℤ) := by
      ext i j
      exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hM i j)
    have hdet := congr_arg Matrix.det hmap
    rw [← RingHom.map_det, ← RingHom.map_det, g.prop] at hdet
    rw [← ZMod.intCast_eq_intCast_iff, ← Matrix.det_fin_two]
    simpa using hdet
  -- `Int.modEq_and_modEq_iff_modEq_lcm` is stated for `Int.lcm`, so the `Nat.lcm` modulus
  -- has to be renamed before it applies.
  have hlcm : (↑(Nat.lcm a b) : ℤ) = ↑(Int.lcm (a : ℤ) (b : ℤ)) := by simp [Int.lcm, Nat.lcm]
  rw [hlcm, ← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨key a 1 hMa, key b γ hMb⟩

/-- **A lift realising `M` modulo `lcm a b` splits `γ` across the two levels.** If `β` reduces
to `M` modulo `lcm a b`, and `M` is congruent to the identity modulo `a` and to `γ` modulo `b`,
then `β ∈ Γ(a)` and `β⁻¹γ ∈ Γ(b)`. -/
private lemma mem_Gamma_and_inv_mul_mem_Gamma_of_map_eq {a b : ℕ}
    {M : Matrix (Fin 2) (Fin 2) ℤ} {β γ : SL(2, ℤ)}
    (hβ : (↑(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (Nat.lcm a b))) β) :
        Matrix (Fin 2) (Fin 2) (ZMod (Nat.lcm a b))) =
      M.map (Int.castRingHom (ZMod (Nat.lcm a b))))
    (hMa : ∀ i j, M i j ≡ ((1 : SL(2, ℤ)) i j : ℤ) [ZMOD (a : ℤ)])
    (hMb : ∀ i j, M i j ≡ (γ i j : ℤ) [ZMOD (b : ℤ)]) :
    β ∈ Gamma a ∧ β⁻¹ * γ ∈ Gamma b := by
  have hzM : ∀ i j : Fin 2,
      (M i j : ZMod a) = ((1 : SL(2, ℤ)) i j : ZMod a) ∧
      (M i j : ZMod b) = (γ i j : ZMod b) := fun i j =>
    ⟨(ZMod.intCast_eq_intCast_iff _ _ _).mpr (hMa i j),
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hMb i j)⟩
  refine ⟨?_, ?_⟩
  · rw [Gamma_mem']
    ext i j
    rw [map_apply_of_dvd_lcm M β hβ (Nat.dvd_lcm_left a b) i j, (hzM i j).1]
    simp [Matrix.one_apply]
  · rw [Gamma_mem', map_mul, map_inv]
    have hβ_b : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod b)) β =
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod b)) γ := by
      ext i j
      rw [map_apply_of_dvd_lcm M β hβ (Nat.dvd_lcm_right a b) i j, (hzM i j).2]
      simp
    rw [hβ_b]
    exact inv_mul_cancel _

/-- **The Chinese remainder theorem lifts a matrix of `Γ(gcd a b)` simultaneously.** For
`γ ∈ Γ(gcd a b)` there is an integer matrix congruent to the identity modulo `a` and to `γ`
modulo `b`. -/
private lemma exists_matrix_modEq_one_modEq_of_mem_Gamma_gcd {a b : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma (Nat.gcd a b)) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      (∀ i j, M i j ≡ ((1 : SL(2, ℤ)) i j : ℤ) [ZMOD (a : ℤ)]) ∧
        ∀ i j, M i j ≡ (γ i j : ℤ) [ZMOD (b : ℤ)] := by
  have hcompat : ∀ i j : Fin 2,
      ((1 : SL(2, ℤ)) i j : ℤ) ≡ (γ i j : ℤ) [ZMOD ↑(Int.gcd (a : ℤ) (b : ℤ))] := by
    -- `Int.gcd` of two casts is the `Nat.gcd` of the naturals; the two spellings of the
    -- modulus are equal but not syntactically interchangeable.
    have hgcd : (↑(Int.gcd (a : ℤ) (b : ℤ)) : ℤ) = ↑(Nat.gcd a b) := by simp [Int.gcd]
    rw [hgcd]
    exact intCast_apply_modEq_one_of_mem_Gamma _ γ hγ
  choose z hza hzb using fun i j => exists_int_modEq_of_modEq_gcd (hcompat i j)
  exact ⟨Matrix.of z, hza, hzb⟩

/-- **Shimura, Lemma 3.28.** `Γ(gcd a b) = Γ(a) ⊔ Γ(b)`: the join of two principal congruence
subgroups is the principal congruence subgroup of the gcd.

The inclusion `⊇` is antitonicity. For `⊆`, lift `γ ∈ Γ(gcd a b)` entrywise: its entries agree
with the identity's modulo `gcd a b`, so the Chinese remainder theorem supplies a matrix `M`
congruent to `1` modulo `a` and to `γ` modulo `b`. Strong approximation
(`map_intCast_zmod_surjective`) realises `M mod lcm a b` by an actual `β ∈ SL₂(ℤ)`, and then
`β ∈ Γ(a)` while `β⁻¹γ ∈ Γ(b)`, so `γ = β · (β⁻¹γ)`. -/
theorem Gamma_gcd_eq_sup (a b : ℕ) : Gamma (Nat.gcd a b) = Gamma a ⊔ Gamma b := by
  -- a zero level contributes `Γ(0) = ⊥` and drops out of both sides
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [Gamma_zero_bot]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [Gamma_zero_bot]
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  have : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  refine le_antisymm ?_ (sup_le (Gamma_le_Gamma_of_dvd (Nat.gcd_dvd_left a b))
    (Gamma_le_Gamma_of_dvd (Nat.gcd_dvd_right a b)))
  have : (Gamma a).Normal := Gamma_normal a
  intro γ hγ
  rw [Subgroup.mem_sup_of_normal_left]
  obtain ⟨M, hMa, hMb⟩ := exists_matrix_modEq_one_modEq_of_mem_Gamma_gcd hγ
  have hM_det : (M.map (Int.castRingHom (ZMod (Nat.lcm a b)))).det = 1 := by
    simp only [Matrix.det_fin_two, Matrix.map_apply, Int.coe_castRingHom]
    have h := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (det_fin_two_modEq_one_lcm hMa hMb)
    push_cast at h ⊢
    exact_mod_cast h
  obtain ⟨β, hβ⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective
    ⟨M.map (Int.castRingHom (ZMod (Nat.lcm a b))), hM_det⟩
  obtain ⟨hβ_a, hβ_b⟩ :=
    mem_Gamma_and_inv_mul_mem_Gamma_of_map_eq (congr_arg Subtype.val hβ) hMa hMb
  exact ⟨β, hβ_a, β⁻¹ * γ, hβ_b, by group⟩

end CongruenceSubgroup
