/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The degree of a rank-two diagonal double coset

The degree of a double coset is the relative index of the conjugated copy of `SL₂(ℤ)`. For a
diagonal representative `a = (a₀, a₁)` with `a₀ ∣ a₁` whose ratio `N = a₁ / a₀` is positive,
conjugating `SL₂(ℤ)` by `natDiagGL 2 a` carves out exactly `Γ₀(N)`, so

`deg T(a₀, a₁) = [SL₂(ℤ) : Γ₀(N)]`,

and specializing to `N = pᵏ` with the index computed in
`TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic` gives Shimura's `pᵏ⁻¹(p + 1)`.

Positivity of the ratio is needed: it forces both entries positive, and so rules out the
tuples on which `natDiagGL` takes its junk value `1` (for `a = (0, 0)` the ratio is `0`).

Note that the degree is not the number of diagonal representatives: for `a = (1, p)` that
count is `p`, while the true degree is `p + 1` — the double coset also contains
representatives with permuted diagonals.

## Main results

* `degree_diagCoset_eq_Gamma0_index`: `deg T(a₀, a₁) = [SL₂(ℤ) : Γ₀(N)]` for a divisibility
  chain `a` whose ratio `N = a₁ / a₀` is positive.
* `degree_diagCoset_of_ratio_eq_prime_pow`: `deg T(a₀, a₁) = pᵏ⁻¹(p + 1)` for a divisibility
  chain `a` whose ratio is `pᵏ`, with `p` prime and `k ≥ 1`.

The rank-general constant case `deg T(c, ..., c) = 1` is in
`TauCeti/NumberTheory/HeckeRing/GLn/Degree.lean`.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/Degree.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), split out of the rank-general material of that file, since
the Γ₀-index computation is specific to rank two.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Propositions 3.14, 3.18 and Theorem 3.24.
-/

public section

open HeckeRing HeckeRing.GLn Finset CongruenceSubgroup Matrix.SpecialLinearGroup Matrix
open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

private lemma a1_eq_a0_mul_ratio {N : ℕ} {a : Fin 2 → ℕ}
    (h_ratio : a 1 / a 0 = N) (h_dvd_a : a 0 ∣ a 1) :
    (a 1 : ℚ) = (a 0 : ℚ) * (N : ℚ) := by
  have h1 := Nat.div_mul_cancel h_dvd_a
  rw [h_ratio] at h1
  push_cast [← h1]; ring

private lemma conj_natDiagGL_mem_of_dvd (N : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (h_ratio : a 1 / a 0 = N) (h_dvd_a : a 0 ∣ a 1) (σ : SL(2, ℤ))
    (hσ : (N : ℤ) ∣ σ.1 1 0) :
    (natDiagGL 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * natDiagGL 2 a ∈ SLnZ 2 := by
  obtain ⟨c, hc⟩ := hσ
  let τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![σ.1 0 0, (N : ℤ) * σ.1 0 1; c, σ.1 1 1]
  have h_det : τ_mat.det = 1 := by
    simp only [τ_mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hσ_det := σ.prop; simp only [Matrix.det_fin_two] at hσ_det
    rw [hc] at hσ_det; linarith
  let τ : SL(2, ℤ) := ⟨τ_mat, h_det⟩
  refine (mem_SLnZ_iff 2).mpr ⟨τ, ?_⟩
  have ha1 := a1_eq_a0_mul_ratio h_ratio h_dvd_a
  have hcQ : (σ.1 1 0 : ℚ) = (N : ℚ) * (c : ℚ) := by exact_mod_cast hc
  suffices h : natDiagGL 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * natDiagGL 2 a by
    have h' := congr_arg ((natDiagGL 2 a)⁻¹ * ·) h
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h'; exact h'
  apply Units.ext
  have hval : ∀ μ : SL(2, ℤ), (↑(mapGL ℚ μ) : Matrix _ _ ℚ) = μ.val.map (Int.cast) :=
    fun μ ↦ by simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
  simp only [Units.val_mul, hval]
  ext i j
  simp only [natDiagGL_coe 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [τ, τ_mat, Matrix.of_apply, Matrix.cons_val', Fin.isValue] <;>
    push_cast <;> (try rw [hcQ]) <;> (try rw [ha1]) <;> ring

private lemma dvd_of_conj_natDiagGL_mem (N : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (h_ratio : a 1 / a 0 = N) (h_dvd_a : a 0 ∣ a 1) (σ : SL(2, ℤ))
    (hmem : (natDiagGL 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * natDiagGL 2 a ∈ SLnZ 2) :
    (N : ℤ) ∣ σ.1 1 0 := by
  obtain ⟨τ, hτ⟩ := (mem_SLnZ_iff 2).mp hmem
  have ha1 := a1_eq_a0_mul_ratio h_ratio h_dvd_a
  have ha0_ne : (a 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha 0).ne'
  have h_mul : natDiagGL 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * natDiagGL 2 a := by
    have := congr_arg (natDiagGL 2 a * ·) hτ
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at this; exact this
  have h_entry : (a 1 : ℚ) * (τ.1 1 0 : ℚ) = (σ.1 1 0 : ℚ) * (a 0 : ℚ) := by
    have h10 := Units.ext_iff.mp h_mul
    have := congr_arg (fun M ↦ M 1 0) h10
    simpa only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
      natDiagGL_coe 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.map_apply, algebraMap_int_eq, eq_intCast] using this
  have h_σ₁₀ : (σ.1 1 0 : ℚ) = (N : ℚ) * (τ.1 1 0 : ℚ) := by
    rw [ha1] at h_entry; field_simp at h_entry ⊢; linarith
  exact ⟨τ.1 1 0, by exact_mod_cast h_σ₁₀⟩

private lemma natDiagGL_conj_relIndex_eq_Gamma0_index (N : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (h_ratio : a 1 / a 0 = N) (h_dvd_a : a 0 ∣ a 1) :
    (ConjAct.toConjAct (natDiagGL 2 a) • SLnZ 2).relIndex (SLnZ 2) =
    (Gamma0 N).index := by
  set H := SLnZ 2
  set α := natDiagGL 2 a
  set f := (mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ)
  have h_inj : Function.Injective f := mapGL_injective
  have h_H_eq : H = Subgroup.map f ⊤ := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    exact (mem_SLnZ_iff 2).trans (by simp [f])
  have h_gamma0_iff : ∀ σ : SL(2, ℤ),
      σ ∈ Gamma0 N ↔ α⁻¹ * f σ * α ∈ H := by
    intro σ
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨conj_natDiagGL_mem_of_dvd N a ha h_ratio h_dvd_a σ,
           dvd_of_conj_natDiagGL_mem N a ha h_ratio h_dvd_a σ⟩
  have h_inf_eq : (ConjAct.toConjAct α • H) ⊓ H = Subgroup.map f (Gamma0 N) := by
    ext g; simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨h_smul, h_mem⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_smul
      obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff 2).mp h_mem
      exact ⟨σ, (h_gamma0_iff σ).mpr h_smul, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨?_, coe_mem_SLnZ 2 σ⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      exact (h_gamma0_iff σ).mp hσ
  calc (ConjAct.toConjAct α • H).relIndex H
      = ((ConjAct.toConjAct α • H) ⊓ H).relIndex H :=
        (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.map f (Gamma0 N)).relIndex (Subgroup.map f ⊤) := by
        rw [h_inf_eq, h_H_eq]
    _ = (Gamma0 N).relIndex ⊤ :=
        Subgroup.relIndex_map_map_of_injective _ _ h_inj
    _ = (Gamma0 N).index := (Gamma0 N).relIndex_top_right

/-- **The degree of a rank-two diagonal double coset is an index of `Γ₀`**: if `a` is a
divisibility chain whose entries are in ratio `N > 0`, then
`deg T(a₀, a₁) = [SL₂(ℤ) : Γ₀(N)]`. Conjugating `SL₂(ℤ)` by the diagonal matrix `a` carves out
exactly `Γ₀(N)`, so the relative index computing the degree is the index of `Γ₀(N)`. -/
theorem degree_diagCoset_eq_Gamma0_index (N : ℕ) (hN : 0 < N) (a : Fin 2 → ℕ)
    (hdiv : IsDvdChain a) (h_ratio : a 1 / a 0 = N) :
    (diagCoset a).degree = (Gamma0 N).index := by
  -- positivity is forced by the ratio: in `ℕ`, a vanishing numerator or denominator would
  -- make `a 1 / a 0` zero, but `N` is not
  have ha : ∀ i, 0 < a i := by
    have h0 : 0 < a 0 := by
      rcases Nat.eq_zero_or_pos (a 0) with h | h
      · rw [h, Nat.div_zero] at h_ratio; omega
      · exact h
    have h1 : 0 < a 1 := by
      rcases Nat.eq_zero_or_pos (a 1) with h | h
      · rw [h, Nat.zero_div] at h_ratio; omega
      · exact h
    intro i
    fin_cases i <;> assumption
  -- `degree_mk` already computes the degree from an explicit representative, so only the
  -- relative index at `natDiagGL` is left to identify
  rw [diagCoset_def, HeckeCoset.degree_mk,
    natDiagGL_conj_relIndex_eq_Gamma0_index N a ha h_ratio (isDvdChain_iff.mp hdiv (Fin.zero_le 1))]

/-- **The prime-power degree** (Shimura, Theorem 3.24, degree count): for prime `p` and
`k ≥ 1`, a divisibility chain `a` of ratio `a₁ / a₀ = pᵏ` has `deg T(a₀, a₁) = pᵏ⁻¹ (p + 1)`.
The archetype is `a = (pⁱ, pⁱ⁺ᵏ)`. -/
theorem degree_diagCoset_of_ratio_eq_prime_pow (p : ℕ) (hp : Nat.Prime p) (a : Fin 2 → ℕ)
    (hdiv : IsDvdChain a) (k : ℕ) (hk : 0 < k) (h_ratio : a 1 / a 0 = p ^ k) :
    (diagCoset a).degree = p ^ (k - 1) * (p + 1) := by
  rw [degree_diagCoset_eq_Gamma0_index (p ^ k) (pow_pos hp.pos k) a hdiv h_ratio,
    Gamma0_prime_power_index p hp k hk]

end HeckeRing.GL2
