/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DiagonalCoset
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The double coset `Γ₁(N) · diag(1, p) · Γ₁(N)` at `p ∣ N`

`GL2/CosetDecomposition.lean` supplies the `p` upper-triangular matrices
`upperTriRep p b = !![1, b; 0, p]`, and `HeckeSlash/UpperTri/` builds an operator on
`M_k(Γ₁(N))` by slashing against them and summing. Nothing so far says that this family *is* the
double coset of `diag(1, p)`, and without that the classical operator and the abstract Hecke
ring's operator are two unrelated objects. This file proves the missing statement, for `p ∣ N`:

`Γ₁(N) · diag(1, p) · Γ₁(N) = ⋃_{b < p} Γ₁(N) · !![1, b; 0, p]`,

a disjoint union of **right** cosets — the handedness Shimura's slash sum needs
(`HeckeSlash/Basic.lean`).

## Why `p ∣ N`, and where it enters

Only the inclusion `⊆` uses it. An element of the double coset is `γ₁ · diag(1, p) · γ₂`, and
since the left factor is absorbed by the coset, the content is that `diag(1, p) · γ₂` lies in one
of the `p` right cosets. Writing `γ₂ = !![a, b; c, d]`, the candidate is

`diag(1, p) · γ₂ = !![a, m; p c, d - c j] · !![1, j; 0, p]`,

which asks for `p ∣ b - a j` — solvable for `j` because `a` is invertible modulo `p`. That is
where the level enters: `γ₂ ∈ Γ₁(N)` gives `a ≡ 1 (mod N)`, and `p ∣ N` promotes it to
`a ≡ 1 (mod p)`, so `j ≡ b` works. The new left factor lands back in `Γ₁(N)` because `N ∣ c`
makes both `p c ≡ 0` and `d - c j ≡ d ≡ 1` modulo `N`.

⚠ For `p ∤ N` the statement is false: when `p` is prime the double coset then has `p + 1` right
cosets, the extra one represented by `!![m, n; N, p] · diag(p, 1)` for any `m p − n N = 1`
(Diamond–Shurman, Proposition 5.2.1). That case is proved in `Gamma1/CoprimeCosets.lean` by
`doubleCoset_natDiagGL_eq_iUnion_rightCosets_of_prime`.

The reverse inclusion needs no divisibility: `!![1, b; 0, p] = diag(1, p) · Tᵇ` and every power
of `T = !![1, 1; 0, 1]` lies in `Γ₁(N)`.

## Main definitions

* `HeckeRing.GL2.diagCosetGamma1`: the double coset of `diag(1, p)` in the Hecke triple of
  `Γ₁(N)`, an element of `HeckeCoset (Δ₀(N)) (Γ₁(N)) (Γ₁(N))`.

## Main results

* `HeckeRing.GL2.natDiagGL_one_mem_Delta0`, `HeckeRing.GL2.coe_natDiagGL_one`: `diag(1, p)` lies
  in `Δ₀(N)` at every level, and its matrix.
* `HeckeRing.GL2.natDiagGL_mul_mapGL_T_zpow`: `diag(1, p) · Tᵇ = !![1, b; 0, p]`, the
  reverse inclusion in one line.
* `HeckeRing.GL2.exists_mem_Gamma1_natDiagGL_mul_of_dvd`: the factorisation
  `diag(1, p) · γ = δ · !![1, j; 0, p]` with `δ ∈ Γ₁(N)`, at any offset `j` with `p ∣ b − a j`;
  `HeckeRing.GL2.exists_mem_Gamma1_natDiagGL_mul` chooses such an offset from `p ∣ N`, and is
  the forward inclusion.
* `HeckeRing.GL2.op_upperTriRep_smul_injective`: the `p` right cosets are pairwise distinct,
  so the union is disjoint. Stated for an arbitrary subgroup of `SL₂(ℤ)`, since only
  integrality is used.
* `DoubleCoset.doubleCoset_eq_iUnion_rightCosets_of_forall_exists`: the general criterion
  turning forward factorizations and reverse witnesses into a right-coset decomposition.
* `HeckeRing.GL2.doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL`: the chosen
  representative of `diagCosetGamma1 N p` has the canonical double coset.
* `HeckeRing.GL2.doubleCoset_natDiagGL_eq_iUnion_rightCosets`: the decomposition itself, and
  `HeckeRing.GL2.doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets` the same statement read
  at the chosen representative of `diagCosetGamma1 N p`, which is the shape the slash sum of
  `ModularForms/HeckeSlash/Independence.lean` consumes.

## Provenance

No code is transcribed. The statement is Diamond–Shurman Proposition 5.2.1 in the case `p ∣ N`,
proved here directly for this repository's own representative families `natDiagGL` and
`upperTriRep` rather than for transcribed matrices. The AINTLIB `LeanModularForms` project
(Chris Birkbeck, Apache-2.0) organises the same case as its `heckeT_p_divN` branch of
`heckeT_p_all` (`LeanModularForms/HeckeRIngs/GL2/HeckeT_n.lean`), on the operator rather than
the coset side; the coset statement below is what identifies the two, and is proved from the
group law here.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.2.1.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable {N p : ℕ}

/-- `diag(1, p) ∈ Δ₀(N)`, for every level `N`: the upper-left entry is `1`, a unit modulo
anything. This is `natDiagGL_mem_Delta0_of_coprime` with its hypothesis discharged. -/
lemma natDiagGL_one_mem_Delta0 (N p : ℕ) : natDiagGL 2 ![1, p] ∈ Delta0 N :=
  natDiagGL_mem_Delta0_of_coprime N ![1, p] fun _ ↦ by simp

/-- The matrix of `diag(1, p)`, for `0 < p`. -/
lemma coe_natDiagGL_one (hp : 0 < p) :
    (↑(natDiagGL 2 ![1, p]) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (p : ℚ)] := by
  rw [natDiagGL_coe 2 ![1, p] fun i ↦ by fin_cases i <;> simp [hp]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The Hecke double coset of `diag(1, p)` at level `Γ₁(N)`.** For `p ∣ N` this is the coset
whose slash sum is the classical `Tₚ = Uₚ`; the identification is
`doubleCoset_natDiagGL_eq_iUnion_rightCosets`, and its operator form lives in
`ModularForms/HeckeSlash/UpperTri/DoubleCoset.lean`. -/
noncomputable def diagCosetGamma1 (N p : ℕ) :
    HeckeCoset (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) :=
  HeckeCoset.mk _ _ ⟨natDiagGL 2 ![1, p], natDiagGL_one_mem_Delta0 N p⟩

/-- Defining equation for the sealed definition `diagCosetGamma1`. -/
lemma diagCosetGamma1_def (N p : ℕ) :
    diagCosetGamma1 N p = HeckeCoset.mk ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      ⟨natDiagGL 2 ![1, p], natDiagGL_one_mem_Delta0 N p⟩ := (rfl)

/-- The underlying set of `diagCosetGamma1 N p` is the double coset of `diag(1, p)`. -/
@[simp] lemma diagCosetGamma1_toSet (N p : ℕ) :
    (diagCosetGamma1 N p).toSet =
      doubleCoset (natDiagGL 2 ![1, p]) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) :=
  HeckeCoset.toSet_mk _

/-- The rational matrix of a power of the translation matrix `T`. -/
private lemma coe_mapGL_T_zpow (n : ℤ) :
    (↑(mapGL ℚ (ModularGroup.T ^ n)) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (n : ℚ); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mapGL_coe_matrix, ModularGroup.coe_T_zpow, -map_zpow]

/-- **`diag(1, p) · Tᵇ = !![1, b; 0, p]`.** Right multiplication by the `b`-th power of the
translation matrix moves `diag(1, p)` onto the `b`-th upper-triangular representative; this is
the reverse inclusion of the coset decomposition below. -/
lemma natDiagGL_mul_mapGL_T_zpow (hp : 0 < p) (b : Fin p) :
    natDiagGL 2 ![1, p] * mapGL ℚ (ModularGroup.T ^ (b : ℤ)) = upperTriRep p b := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_natDiagGL_one hp, coe_mapGL_T_zpow, coe_upperTriRep,
    Matrix.mul_fin_two]
  norm_num

/-- **The forward factorisation, at a prescribed offset.** If `γ ∈ Γ₁(N)` and the offset
`j < p` satisfies `p ∣ b − a j` for `γ = !![a, b; c, d]`, then `diag(1, p) · γ` lies in the
right coset `Γ₁(N) · !![1, j; 0, p]`: explicitly

`diag(1, p) · γ = !![a, m; p c, d − c j] · !![1, j; 0, p]`,  `b − a j = p m`,

whose left factor has determinant `a d − b c = 1` and stays in `Γ₁(N)` because `N ∣ c`.

The divisibility on the offset is the only arithmetic input, and it is where the two branches
of Diamond–Shurman's Proposition 5.2.1 differ: at `p ∣ N` every `γ ∈ Γ₁(N)` admits such a `j`
(below), while at a prime `p ∤ N` only those with `p ∤ a` do, the rest needing the further coset
of `Gamma1/CoprimeCosets.lean`. -/
lemma exists_mem_Gamma1_natDiagGL_mul_of_dvd (hp : 0 < p) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N)
    {j : ℕ} (hjlt : j < p) (hj : (p : ℤ) ∣ γ 0 1 - γ 0 0 * j) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 N ∧
      natDiagGL 2 ![1, p] * mapGL ℚ γ = mapGL ℚ δ * upperTriRep p ⟨j, hjlt⟩ := by
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N γ).mp hγ
  obtain ⟨m, hm⟩ := hj
  -- the new left factor
  have hdet : (!![γ 0 0, m; (p : ℤ) * γ 1 0, γ 1 1 - γ 1 0 * j] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have hγdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
      Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
    rw [Matrix.det_fin_two_of]
    linear_combination hγdet + γ 1 0 * hm
  obtain ⟨δ, hδmat⟩ : ∃ δ : SL(2, ℤ), (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0, m; (p : ℤ) * γ 1 0, γ 1 1 - γ 1 0 * j] := ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨δ, ?_, ?_⟩
  · refine (Gamma1_mem N δ).mpr ⟨?_, ?_, ?_⟩
    · simpa [hδmat] using ha
    · have h : ((γ 1 1 - γ 1 0 * j : ℤ) : ZMod N) = 1 := by push_cast; rw [hd, hc]; ring
      simpa [hδmat] using h
    · have h : (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0 := by push_cast; rw [hc]; ring
      simpa [hδmat] using h
  · refine Units.ext ?_
    have hmZ : (γ 0 1 : ℤ) = γ 0 0 * j + m * p := by linarith
    have e00 : (δ 0 0 : ℤ) = γ 0 0 := by rw [hδmat]; simp
    have e01 : (δ 0 1 : ℤ) = m := by rw [hδmat]; simp
    have e10 : (δ 1 0 : ℤ) = (p : ℤ) * γ 1 0 := by rw [hδmat]; simp
    have e11 : (δ 1 1 : ℤ) = γ 1 1 - γ 1 0 * j := by rw [hδmat]; simp
    rw [Units.val_mul, Units.val_mul, coe_natDiagGL_one hp, coe_upperTriRep,
      coe_mapGL_int_rat_fin_two γ, coe_mapGL_int_rat_fin_two δ, e00, e01, e10, e11,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_]
    · ring1
    · rw [hmZ]; push_cast; ring1
    · push_cast; ring1
    · push_cast; ring1

/-- **The forward factorisation at `p ∣ N`.** For `p ∣ N` and `γ ∈ Γ₁(N)`, the product
`diag(1, p) · γ` lies in one of the `p` right cosets `Γ₁(N) · !![1, j; 0, p]`.

The offset is `j ≡ b (mod p)` for `γ = !![a, b; c, d]`, which works because `p ∣ N` makes
`a ≡ 1 (mod p)`; the factorisation itself is
`exists_mem_Gamma1_natDiagGL_mul_of_dvd`. -/
lemma exists_mem_Gamma1_natDiagGL_mul (hp : 0 < p) (hpN : p ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 N) :
    ∃ (j : Fin p) (δ : SL(2, ℤ)), δ ∈ Gamma1 N ∧
      natDiagGL 2 ![1, p] * mapGL ℚ γ = mapGL ℚ δ * upperTriRep p j := by
  obtain ⟨ha, -, -⟩ := (Gamma1_mem N γ).mp hγ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  -- the level divisibility, read in `ℤ`
  have haN : (N : ℤ) ∣ γ 0 0 - 1 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    rw [ha, sub_self]
  -- the offset `j ≡ b (mod p)`, taken opaquely: only its size and its residue matter
  obtain ⟨j, hjlt, hpj⟩ : ∃ j : ℕ, j < p ∧ (p : ℤ) ∣ γ 0 1 - j := by
    have hj0 : (0 : ℤ) ≤ γ 0 1 % p := Int.emod_nonneg _ hp'.ne'
    refine ⟨(γ 0 1 % p).toNat, ?_, ?_⟩
    · have := Int.emod_lt_of_pos (γ 0 1) hp'
      omega
    · rw [Int.toNat_of_nonneg hj0, Int.emod_def]
      exact ⟨γ 0 1 / p, by ring⟩
  have hpa : (p : ℤ) ∣ γ 0 0 - 1 := dvd_trans (Int.natCast_dvd_natCast.mpr hpN) haN
  have hj : (p : ℤ) ∣ γ 0 1 - γ 0 0 * j := by
    have h : γ 0 1 - γ 0 0 * j = (γ 0 1 - j) - (γ 0 0 - 1) * j := by ring
    rw [h]
    exact dvd_sub hpj (Dvd.dvd.mul_right hpa _)
  obtain ⟨δ, hδ, heq⟩ := exists_mem_Gamma1_natDiagGL_mul_of_dvd hp hγ hjlt hj
  exact ⟨⟨j, hjlt⟩, δ, hδ, heq⟩

/-- **The `p` right cosets are pairwise distinct.** If `Γ · !![1, j₁; 0, p] = Γ · !![1, j₂; 0, p]`
for a subgroup `Γ` of `SL₂(ℤ)`, then `j₁ = j₂`: the comparison matrix has upper-left entry `1`
and upper-right entry `(j₂ − j₁)/p`, and integrality forces `p ∣ j₂ − j₁`, which two offsets
below `p` can only satisfy by being equal.

Only integrality of `Γ` is used, so no congruence condition and no divisibility appear. -/
theorem op_upperTriRep_smul_injective {G : Subgroup SL(2, ℤ)} :
    Function.Injective fun j : Fin p ↦
      MulOpposite.op (upperTriRep p j) • ((G.map (mapGL ℚ)) : Set (GL (Fin 2) ℚ)) := by
  intro j₁ j₂ h
  obtain ⟨σ, -, hσ⟩ := Subgroup.mem_map.mp ((rightCoset_eq_iff _).mp h)
  have hmul : (mapGL ℚ σ : GL (Fin 2) ℚ) * upperTriRep p j₁ = upperTriRep p j₂ := by
    rw [hσ, inv_mul_cancel_right]
  have hmat : (↑(mapGL ℚ σ) : Matrix (Fin 2) (Fin 2) ℚ) * !![1, (j₁ : ℚ); 0, (p : ℚ)] =
      !![1, (j₂ : ℚ); 0, (p : ℚ)] := by
    rw [← coe_upperTriRep, ← coe_upperTriRep, ← Units.val_mul, hmul]
  rw [coe_mapGL_int_rat_fin_two, Matrix.mul_fin_two] at hmat
  have h00 : (σ 0 0 : ℤ) = 1 := by simpa using congrFun (congrFun hmat 0) 0
  have h01 : ((σ 0 0 : ℤ) : ℚ) * (j₁ : ℚ) + ((σ 0 1 : ℤ) : ℚ) * (p : ℚ) = (j₂ : ℚ) := by
    simpa using congrFun (congrFun hmat 0) 1
  rw [h00] at h01
  have key : (j₂ : ℤ) - (j₁ : ℤ) = σ 0 1 * p := by
    have hQ : ((j₂ : ℤ) : ℚ) - ((j₁ : ℤ) : ℚ) = ((σ 0 1 * p : ℤ) : ℚ) := by
      push_cast at h01 ⊢
      linarith
    exact_mod_cast hQ
  have hdvd : (p : ℤ) ∣ (j₂ : ℤ) - (j₁ : ℤ) := ⟨σ 0 1, by rw [key]; ring⟩
  have habs : |(j₂ : ℤ) - (j₁ : ℤ)| < (p : ℤ) := by
    have h1 := j₁.isLt
    have h2 := j₂.isLt
    rw [abs_lt]
    omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  exact Fin.ext (by omega)

/-- **The `Tₚ` double coset at `p ∣ N` is the union of the `p` upper-triangular right cosets.**
`Γ₁(N) · diag(1, p) · Γ₁(N) = ⋃_{j < p} Γ₁(N) · !![1, j; 0, p]`, Diamond–Shurman's
Proposition 5.2.1 in the case `p ∣ N`.

The inclusion `⊇` is `natDiagGL_mul_mapGL_T_zpow` and needs no divisibility; the inclusion `⊆`
is `exists_mem_Gamma1_natDiagGL_mul` and is where `p ∣ N` enters. That the union is disjoint is
`op_upperTriRep_smul_injective`. -/
theorem doubleCoset_natDiagGL_eq_iUnion_rightCosets (hp : 0 < p) (hpN : p ∣ N) :
    doubleCoset (natDiagGL 2 ![1, p]) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
      ⋃ j : Fin p, MulOpposite.op (upperTriRep p j) •
        ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  apply doubleCoset_eq_iUnion_rightCosets_of_forall_exists
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      (natDiagGL 2 ![1, p]) (upperTriRep p)
  · intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨j, δ, hδ, heq⟩ := exists_mem_Gamma1_natDiagGL_mul hp hpN hγ
    exact ⟨j, mapGL ℚ δ, Subgroup.mem_map_of_mem _ hδ, heq⟩
  · intro j
    exact ⟨mapGL ℚ (ModularGroup.T ^ (j : ℤ)),
      Subgroup.mem_map_of_mem _ (T_zpow_mem_Gamma1 N _),
      natDiagGL_mul_mapGL_T_zpow hp j⟩

/-- The chosen representative of `diagCosetGamma1 N p` has the same double coset as the
canonical matrix `diag(1, p)`. -/
theorem doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL :
    doubleCoset ((diagCosetGamma1 N p).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
      doubleCoset (natDiagGL 2 ![1, p]) ((Gamma1 N).map (mapGL ℚ))
        ((Gamma1 N).map (mapGL ℚ)) := by
  have hout : HeckeCoset.mk ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      (diagCosetGamma1 N p).out = diagCosetGamma1 N p := Quotient.out_eq _
  rw [HeckeCoset.eq_iff.mp (hout.trans (diagCosetGamma1_def N p))]

/-- The decomposition of `doubleCoset_natDiagGL_eq_iUnion_rightCosets`, read at the chosen
representative `D.out` of `diagCosetGamma1 N p` — the shape the slash-sum machinery of
`HeckeSlash/Independence.lean` consumes. -/
theorem doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets (hp : 0 < p) (hpN : p ∣ N) :
    doubleCoset ((diagCosetGamma1 N p).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
      ⋃ j : Fin p, MulOpposite.op (upperTriRep p j) •
        ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL,
    doubleCoset_natDiagGL_eq_iUnion_rightCosets hp hpN]

end HeckeRing.GL2

end
