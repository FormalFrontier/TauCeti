/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic

-- the gcd decomposition and `Γ(N) ≤ Γ₀(N)` are used only inside proofs here
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The `Γ₀(N)` double coset of a coprime-determinant element

**Shimura, Lemma 3.29(3).** For `α ∈ Δ₀(N)` whose determinant is coprime to `N`,

`SL₂(ℤ) α SL₂(ℤ) ∩ Δ₀(N) = Γ₀(N) α Γ₀(N)`.

The right-hand side is always contained in the left, because `Γ₀(N) ≤ SL₂(ℤ)` and `Δ₀(N)` is a
submonoid containing both `Γ₀(N)` and `α`. The content is the other inclusion: an element
`σ₁ α σ₂` of the level-one double coset that happens to lie in `Δ₀(N)` can be rewritten with
`σ₁, σ₂` taken from `Γ₀(N)`.

The mechanism is the Chinese-remainder decomposition
`CongruenceSubgroup.Gamma_gcd_eq_sup`: coprimality of `det α` with `N` makes
`Γ(N) ⊔ Γ(det α) = ⊤`, so `σ₁` factors as `τ_N · τ_a` with `τ_N ∈ Γ(N) ≤ Γ₀(N)` and
`τ_a ∈ Γ(det α)`. The second factor is absorbed on the other side: `HeckeRing.GLn`'s
`inv_conjugate_mem_SLnZ_of_mem_ker` says `α⁻¹ τ_a α` is again integral, so
`τ_a α = α · (α⁻¹ τ_a α)`, and the new right factor is forced into `Γ₀(N)` by reading off the
lower-left entry of the product —
which is where `gcd(det α, N) = 1` is used a second time, through the lower-right entry.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Foundation.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).

## Main results

* `HeckeRing.GL2.Gamma0Image_le_SLnZ`: `Γ₀(N) ≤ SL₂(ℤ)` inside `GL₂(ℚ)`.
* `HeckeRing.GL2.doubleCoset_Gamma0Image_le_doubleCoset_SLnZ`: `Γ₀(N) α Γ₀(N) ⊆ Γ α Γ`.
* `HeckeRing.GL2.doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image`: the equality above.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Lemma 3.29(3).
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- `Γ₀(N) ≤ SL₂(ℤ)` as subgroups of `GL₂(ℚ)`: the image of any integral matrix of determinant
one lies in the range of `mapGL`. -/
lemma Gamma0Image_le_SLnZ : Gamma0Image N ≤ SLnZ 2 := by
  intro g hg
  obtain ⟨σ, -, rfl⟩ := (mem_Gamma0Image_iff N).mp hg
  exact (mem_SLnZ_iff 2).mpr ⟨σ, rfl⟩

/-- `Γ₀(N) α Γ₀(N) ⊆ Γ α Γ`: immediate from `Γ₀(N) ≤ SL₂(ℤ)`. -/
lemma doubleCoset_Gamma0Image_le_doubleCoset_SLnZ (α : GL (Fin 2) ℚ) :
    DoubleCoset.doubleCoset α (Gamma0Image N) (Gamma0Image N) ⊆
      DoubleCoset.doubleCoset α (SLnZ 2) (SLnZ 2) := fun _ hx ↦ by
  rw [DoubleCoset.mem_doubleCoset] at hx ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx
  exact ⟨γ₁, Gamma0Image_le_SLnZ N hγ₁, γ₂, Gamma0Image_le_SLnZ N hγ₂, hx_eq⟩

/-- If `N ∣ c` and `det` is coprime to `N`, then so is the lower-right entry: modulo `N` the
determinant is `a * d`, so `d` divides a unit. -/
private lemma gcd_apply_one_one_eq_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hAN : (N : ℤ) ∣ A 1 0)
    (hdet : Int.gcd A.det N = 1) : Int.gcd (A 1 1) N = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hdet ⊢
  obtain ⟨k, hk⟩ := hAN
  have hmul : A 0 0 * A 1 1 = A.det + A 0 1 * k * (N : ℤ) := by
    rw [Matrix.det_fin_two A, hk]; ring
  exact (IsCoprime.mul_left_iff.mp (hmul ▸ hdet.add_mul_right_left _)).2

/-- Cancel a left factor from a lower-left divisibility: if `N ∣ (P * Q) 1 0` and `N ∣ P 1 0`
with `P 1 1` coprime to `N`, then `N ∣ Q 1 0`. -/
private lemma dvd_apply_one_zero_of_dvd_mul (P Q : Matrix (Fin 2) (Fin 2) ℤ)
    (hPQ : (N : ℤ) ∣ (P * Q) 1 0) (hP10 : (N : ℤ) ∣ P 1 0)
    (hP11 : Int.gcd (P 1 1) N = 1) : (N : ℤ) ∣ Q 1 0 := by
  have key : (P * Q) 1 0 = P 1 0 * Q 0 0 + P 1 1 * Q 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [key] at hPQ
  have h2 : (N : ℤ) ∣ Q 1 0 * P 1 1 := by
    have h := Int.dvd_sub hPQ (dvd_mul_of_dvd_left hP10 (Q 0 0))
    rw [add_sub_cancel_left, mul_comm] at h
    exact h
  exact (Int.isCoprime_iff_gcd_eq_one.mpr hP11).symm.dvd_of_dvd_mul_right h2

/-- Multiplying on the left by a `Γ(N)`-matrix preserves both "lower-left divisible by `N`" and
"lower-right coprime to `N`". -/
private lemma dvd_and_gcd_of_Gamma_mul (τ A : Matrix (Fin 2) (Fin 2) ℤ)
    (hτ10 : (N : ℤ) ∣ τ 1 0) (hτ11 : (N : ℤ) ∣ (τ 1 1 - 1))
    (hAN : (N : ℤ) ∣ A 1 0) (hA11 : Int.gcd (A 1 1) N = 1) :
    (N : ℤ) ∣ (τ * A) 1 0 ∧ Int.gcd ((τ * A) 1 1) N = 1 := by
  refine ⟨?_, ?_⟩
  · have h : (τ * A) 1 0 = τ 1 0 * A 0 0 + τ 1 1 * A 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    exact h ▸ dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_right hAN _)
  · rw [← Int.isCoprime_iff_gcd_eq_one]
    have hmod : (N : ℤ) ∣ ((τ * A) 1 1 - A 1 1) := by
      have h : (τ * A) 1 1 - A 1 1 = τ 1 0 * A 0 1 + (τ 1 1 - 1) * A 1 1 := by
        simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
      exact h ▸ dvd_add (dvd_mul_of_dvd_left hτ10 _) (dvd_mul_of_dvd_left hτ11 _)
    obtain ⟨k, hk⟩ := hmod
    have hshift : (τ * A) 1 1 = A 1 1 + k * (N : ℤ) := by linarith
    exact hshift ▸ (Int.isCoprime_iff_gcd_eq_one.mpr hA11).add_mul_right_left k

/-- The integral matrix of `τ α δ` is the product of the three integral matrices. -/
private lemma mapGL_mul_coe_eq_intMatrix (τ δ : SpecialLinearGroup (Fin 2) ℤ)
    (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    (↑(mapGL ℚ τ * g * mapGL ℚ δ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((τ : Matrix (Fin 2) (Fin 2) ℤ) * A * (δ : Matrix (Fin 2) (Fin 2) ℤ)).map
        (Int.cast : ℤ → ℚ) := by
  -- multiplicativity of the entrywise cast is `map_mul` for `(Int.castRingHom ℚ).mapMatrix`
  have h₁ := map_mul (Int.castRingHom ℚ).mapMatrix
    ((τ : Matrix (Fin 2) (Fin 2) ℤ) * A) (δ : Matrix (Fin 2) (Fin 2) ℤ)
  have h₂ := map_mul (Int.castRingHom ℚ).mapMatrix (τ : Matrix (Fin 2) (Fin 2) ℤ) A
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at h₁ h₂
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, map_apply_coe,
    RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom, hA]
  rw [h₁, h₂]

/-- The hard inclusion of Lemma 3.29(3): an element `σ₁ α σ₂` of the level-one double coset
that lies in `Δ₀(N)` already lies in the `Γ₀(N)`-double coset. -/
private lemma mem_doubleCoset_Gamma0Image_of_mem_Delta0
    (α : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hA11 : Int.gcd (A 1 1) N = 1) (hdet : Int.gcd A.det N = 1)
    (σ₁ σ₂ : SpecialLinearGroup (Fin 2) ℤ)
    (hmem : mapGL ℚ σ₁ * α * mapGL ℚ σ₂ ∈ Delta0 N) :
    mapGL ℚ σ₁ * α * mapGL ℚ σ₂ ∈
      DoubleCoset.doubleCoset α (Gamma0Image N) (Gamma0Image N) := by
  have : (Gamma N).Normal := Gamma_normal N
  -- coprimality of `det α` with `N` makes the two principal congruence subgroups fill `SL₂(ℤ)`
  have h_top : Gamma N ⊔ Gamma A.det.natAbs = ⊤ := by
    -- `Int.gcd` is *defined* as `Nat.gcd` on the `natAbs`, but the two spellings are not
    -- interchangeable for `rw`, so the bridge is named.
    have hgcd : Nat.gcd A.det.natAbs N = Int.gcd A.det N := by simp [Int.gcd]
    have h := Gamma_gcd_eq_sup A.det.natAbs N
    rw [hgcd, hdet, Gamma_one_top] at h
    rw [sup_comm]
    exact h.symm
  obtain ⟨τ_N, hτ_N, τ_a, hτ_a, hσ₁_eq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (h_top ▸ Subgroup.mem_top σ₁)
  have hτ_N_Gamma0 : τ_N ∈ Gamma0 N := Gamma_le_Gamma0 N hτ_N
  have hτ10 : (N : ℤ) ∣ (τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rwa [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ_N_Gamma0
  have hτ11 : (N : ℤ) ∣ ((τ_N : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1) := by
    rw [Gamma_mem] at hτ_N
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    simp [hτ_N.2.2.2]
  -- the `Γ(det α)` factor crosses `α` and lands back in `SL₂(ℤ)`
  have hτ_ker : τ_a ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker := by
    rw [MonoidHom.mem_ker]
    rwa [Gamma_mem'] at hτ_a
  obtain ⟨h_sl, hh_sl⟩ :=
    (mem_SLnZ_iff 2).mp (inv_conjugate_mem_SLnZ_of_mem_ker 2 α A hA τ_a hτ_ker)
  set γ₂' := h_sl * σ₂ with hγ₂'
  have hx_eq : mapGL ℚ σ₁ * α * mapGL ℚ σ₂ = mapGL ℚ τ_N * α * mapGL ℚ γ₂' := by
    have hcross : mapGL ℚ τ_a * α = α * mapGL ℚ h_sl := by
      rw [hh_sl]; group
    rw [← hσ₁_eq, map_mul, hγ₂', map_mul, mul_assoc, mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, hcross, mul_assoc]
  -- the new right factor is in `Γ₀(N)`: read off the lower-left entry of the whole product
  have hγ₂'_mem : γ₂' ∈ Gamma0 N := by
    obtain ⟨B, hB, -, hBN, -⟩ := (mem_Delta0_iff N).mp hmem
    obtain ⟨hCN, hC11⟩ := dvd_and_gcd_of_Gamma_mul N (τ_N : Matrix (Fin 2) (Fin 2) ℤ) A
      hτ10 hτ11 hAN hA11
    have hB_eq : B = (τ_N : Matrix (Fin 2) (Fin 2) ℤ) * A * (γ₂' : Matrix (Fin 2) (Fin 2) ℤ) :=
      Matrix.map_injective Int.cast_injective
        (hB.symm.trans (hx_eq ▸ mapGL_mul_coe_eq_intMatrix τ_N γ₂' α A hA))
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_apply_one_zero_of_dvd_mul N _ (γ₂' : Matrix (Fin 2) (Fin 2) ℤ)
      (hB_eq ▸ hBN) hCN hC11
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨mapGL ℚ τ_N, (mem_Gamma0Image_iff N).mpr ⟨τ_N, hτ_N_Gamma0, rfl⟩,
    mapGL ℚ γ₂', (mem_Gamma0Image_iff N).mpr ⟨γ₂', hγ₂'_mem, rfl⟩, hx_eq⟩

/-- **Shimura, Lemma 3.29(3).** For `α ∈ Δ₀(N)` with `gcd(det α, N) = 1`, cutting the level-one
double coset down to `Δ₀(N)` leaves exactly the `Γ₀(N)`-double coset:
`SL₂(ℤ) α SL₂(ℤ) ∩ Δ₀(N) = Γ₀(N) α Γ₀(N)`.

This is the prerequisite for comparing the level-one and `Γ₀(N)` Hecke operators at an index
coprime to the level, and so for the later multiplicativity of `T_n` on `M_k(Γ₀(N))`; neither
comparison nor multiplicativity is proved here — this identifies the two double cosets. -/
theorem doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0Image
    (α : GL (Fin 2) ℚ) (hα : α ∈ Delta0 N) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hdet : Int.gcd A.det N = 1) :
    DoubleCoset.doubleCoset α (SLnZ 2) (SLnZ 2) ∩ (Delta0 N : Set (GL (Fin 2) ℚ)) =
      DoubleCoset.doubleCoset α (Gamma0Image N) (Gamma0Image N) := by
  obtain ⟨B, hB, -, hBN, -⟩ := (mem_Delta0_iff N).mp hα
  -- `Δ₀(N)` already supplies an integral representative with `N ∣ c`, and `hA` identifies it
  -- with `A`, so the divisibility need not be assumed
  have hBA : B = A := Matrix.map_injective Int.cast_injective (hB.symm.trans hA)
  have hAN : (N : ℤ) ∣ A 1 0 := hBA ▸ hBN
  have hA11 : Int.gcd (A 1 1) N = 1 := gcd_apply_one_one_eq_one N A hAN hdet
  ext x
  constructor
  · rintro ⟨hx_dc, hx_delta⟩
    rw [DoubleCoset.mem_doubleCoset] at hx_dc
    obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := hx_dc
    obtain ⟨σ₁, rfl⟩ := (mem_SLnZ_iff 2).mp hγ₁
    obtain ⟨σ₂, rfl⟩ := (mem_SLnZ_iff 2).mp hγ₂
    exact mem_doubleCoset_Gamma0Image_of_mem_Delta0 N α A hA hAN hA11 hdet σ₁ σ₂ hx_delta
  · intro hx
    refine ⟨doubleCoset_Gamma0Image_le_doubleCoset_SLnZ N α hx, ?_⟩
    rw [DoubleCoset.mem_doubleCoset] at hx
    obtain ⟨δ₁, hδ₁, δ₂, hδ₂, rfl⟩ := hx
    exact (Delta0 N).mul_mem ((Delta0 N).mul_mem (Gamma0Image_le_Delta0 N hδ₁) hα)
      (Gamma0Image_le_Delta0 N hδ₂)

end HeckeRing.GL2
