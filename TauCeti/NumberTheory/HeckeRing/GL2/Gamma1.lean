/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

-- only the Γ₀ unit-entry lemma is needed, and only inside a proof
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The Hecke triple of `Γ₁(N)`

The submonoid `Δ₀(N) ⊆ GL₂(ℚ)` of integral matrices with positive determinant that are
upper-triangular modulo `N` with unit upper-left entry, and the Hecke triple it forms with
the image of the congruence subgroup `Γ₁(N)`. This is the level-`N` counterpart of the
arithmetic triple `(Δₙ, SL_n(ℤ))`, and the setting in which the Hecke operators on
`M_k(Γ₁(N))` live.

`Δ₀(N)` is the classical semigroup of Miyake, *Modular Forms*, §4.5: integral, of positive
determinant, with `c ≡ 0` and `a` coprime to `N`, the coprimality spelled here as
`IsUnit (a : ZMod N)`. Asking the upper-left entry to be a *unit* rather than `≡ 1` is what
makes `Γ₀(N) ≤ Δ₀(N)`, so that the resulting Hecke ring carries the diamond operators
alongside the `T_p`: an element of `Γ₀(N)` has `ad ≡ 1` modulo `N`, hence unit `a`, but
`a ≡ 1` only for the elements of `Γ₁(N)` itself. The smaller classical semigroup `Δ₁(N)`,
cut out by `a ≡ 1`, is the sub-semigroup carrying the `T_p` alone.

Determinants divisible by `N` are deliberately admitted: `diag(1, p)` lies in `Δ₀(N)` even
when `p ∣ N`, where it gives the bad-prime operator `U_p`. Because of this, the whole
determinant-`n` part of `Δ₀(N)` is the full diamond orbit of the classical `T_n`, not `T_n`
itself; an operator defined downstream must be cut out of the `a ≡ 1` part rather than taken
as that entire fibre.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GL2.Delta0`: the submonoid `Δ₀(N)`.
* `HeckeRing.GL2.Gamma1Image`: the image of `Γ₁(N)` in `GL₂(ℚ)`.

## Main results

* `HeckeRing.GL2.Gamma1Image_le_Delta0`: `Γ₁(N) ≤ Δ₀(N)`.
* `HeckeRing.GL2.Gamma0_map_le_Delta0`: `Γ₀(N) ≤ Δ₀(N)`, so the diamond operators live in
  the same Hecke ring.
* `HeckeRing.GL2.Delta0_le_commensurator`: `Δ₀(N)` lies in the commensurator of `Γ₁(N)`.
* the `IsHeckeTriple (Delta0 N) (Gamma1Image N) (Gamma1Image N)` instance.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup
  Subgroup.Commensurable HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- The image of `Γ₁(N)` in `GL₂(ℚ)`. -/
noncomputable def Gamma1Image : Subgroup (GL (Fin 2) ℚ) :=
  (Gamma1 N).map (mapGL ℚ)

/-- Membership in the image of `Γ₁(N)`, by an integral witness. -/
@[simp] lemma mem_Gamma1Image_iff {g : GL (Fin 2) ℚ} :
    g ∈ Gamma1Image N ↔ ∃ σ ∈ Gamma1 N, mapGL ℚ σ = g := by
  rw [Gamma1Image, Subgroup.mem_map]

/-- `Δ₀(N)`: integral matrices of positive determinant that are upper-triangular modulo `N`
with unit upper-left entry, i.e. `c ≡ 0 (mod N)` and `a` a unit in `ZMod N`. The unit
condition (rather than `a ≡ 1`) is what makes `Γ₀(N) ≤ Δ₀(N)`. -/
noncomputable def Delta0 : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ (N : ℤ) ∣ A 1 0 ∧ IsUnit (A 0 0 : ZMod N)}
  one_mem' := ⟨1, by simp, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨A, hA, hda, hAN, hAunit⟩ ⟨B, hB, hdb, hBN, hBunit⟩
    refine ⟨A * B, ?_, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · simpa [Matrix.det_mul] using mul_pos hda hdb
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · -- the upper-left entry of the product is `a₁a₂` modulo `N`, since `c₂ ≡ 0`
      have hentry : ((A * B) 0 0 : ZMod N) = (A 0 0 : ZMod N) * (B 0 0 : ZMod N) := by
        simp [Matrix.mul_apply, Fin.sum_univ_two,
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hBN]
      rw [hentry]
      exact hAunit.mul hBunit

/-- Membership in `Δ₀(N)`, unfolded. -/
@[simp] lemma mem_Delta0_iff {g : GL (Fin 2) ℚ} :
    g ∈ Delta0 N ↔ ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
        0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ (N : ℤ) ∣ A 1 0 ∧
          IsUnit (A 0 0 : ZMod N) :=
  Iff.rfl

/-- `Γ₁(N) ≤ Δ₀(N)`: the congruence subgroup embeds in the submonoid. -/
lemma Gamma1Image_le_Delta0 : (Gamma1Image N).toSubmonoid ≤ Delta0 N := by
  intro g hg
  obtain ⟨σ, hσ, rfl⟩ := (mem_Gamma1Image_iff N).mp hg
  obtain ⟨ha, -, hc⟩ := (Gamma1_mem _ _).mp hσ
  refine (mem_Delta0_iff N).mpr ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ), ?_, ?_, ?_, ha ▸ isUnit_one⟩
  · simp [mapGL_coe_matrix, algebraMap_int_eq]
  · rw [mapGL_coe_matrix, (SpecialLinearGroup.map (algebraMap ℤ ℚ) σ).prop]
    exact one_pos
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

/-- `Γ₀(N) ≤ Δ₀(N)`: an element of `Γ₀(N)` has `ad ≡ 1` modulo `N`, since `c ≡ 0` and the
determinant is one, so its upper-left entry is a unit. This containment is what puts the
diamond operators into the Hecke ring of `Γ₁(N)`. -/
lemma Gamma0_map_le_Delta0 :
    ((Gamma0 N).map (mapGL ℚ)).toSubmonoid ≤ Delta0 N := by
  intro g hg
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
  refine (mem_Delta0_iff N).mpr ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ), ?_, ?_, ?_,
    isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hσ⟩
  · simp [mapGL_coe_matrix, algebraMap_int_eq]
  · rw [mapGL_coe_matrix, (SpecialLinearGroup.map (algebraMap ℤ ℚ) σ).prop]
    exact one_pos
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hσ)

/-- `Δ₀(N)` consists of integral matrices with positive determinant. -/
lemma Delta0_le_posDetInt : Delta0 N ≤ posDetInt 2 := by
  intro g hg
  obtain ⟨A, hA, hdet, -, -⟩ := (mem_Delta0_iff N).mp hg
  exact (mem_posDetInt_iff 2).mpr ⟨(hasIntEntries_iff 2).mpr ⟨A, hA⟩, hdet⟩

variable [NeZero N]

/-- `Γ₁(N)` is commensurable with `SL₂(ℤ)`: it has finite index in it. -/
lemma commensurable_Gamma1Image_SLnZ : Commensurable (Gamma1Image N) (SLnZ 2) := by
  have hSL : SLnZ 2 =
      Subgroup.map (mapGL ℚ : SpecialLinearGroup (Fin 2) ℤ →* GL (Fin 2) ℚ) ⊤ := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    exact (mem_SLnZ_iff 2).trans (by simp)
  constructor
  · rw [Gamma1Image, hSL,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Gamma1Image, hSL,
      Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective, Subgroup.relIndex_top_left]
    exact one_ne_zero

/-- `Δ₀(N)` lies in the commensurator of `Γ₁(N)`: it lies in that of `SL₂(ℤ)`, and the two
groups are commensurable. -/
lemma Delta0_le_commensurator : Delta0 N ≤ (commensurator (Gamma1Image N)).toSubmonoid := by
  rw [Subgroup.Commensurable.eq (commensurable_Gamma1Image_SLnZ N)]
  exact (Delta0_le_posDetInt N).trans (posDetInt_le_commensurator 2)

/-- **The Hecke triple of `Γ₁(N)`**: `Γ₁(N) ≤ Δ₀(N) ≤ commensurator(Γ₁(N))` inside
`GL₂(ℚ)` — the setting of the Hecke operators on modular forms of level `N`. -/
instance : IsHeckeTriple (Delta0 N) (Gamma1Image N) (Gamma1Image N) :=
  IsHeckeTriple.of_diagonal (Gamma1Image_le_Delta0 N) (Delta0_le_commensurator N)

end HeckeRing.GL2
