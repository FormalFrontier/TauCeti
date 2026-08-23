/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.Basic

/-!
# The semigroup `Δ₀(N)`

The submonoid `Δ₀(N) ⊆ GL₂(ℚ)` of integral matrices with positive determinant that are
upper-triangular modulo `N` with unit upper-left entry. It is the `Δ` of the Hecke triples of
both `Γ₀(N)` and `Γ₁(N)`, and nothing about it refers to either group, so it lives here rather
than inside one of the two triple modules.

`Δ₀(N)` is the classical semigroup of Miyake, *Modular Forms*, §4.5: integral, of positive
determinant, with `c ≡ 0` and `a` coprime to `N`, the coprimality spelled here as
`IsUnit (a : ZMod N)`. Asking the upper-left entry to be a *unit* rather than `≡ 1` is what
makes `Γ₀(N) ≤ Δ₀(N)`, so that the Hecke ring of `Γ₁(N)` carries the diamond operators
alongside the `T_p`. The smaller classical semigroup `Δ₁(N)`, cut out by `a ≡ 1`, is the
sub-semigroup carrying the `T_p` alone.

Determinants divisible by `N` are deliberately admitted: `diag(1, p)` lies in `Δ₀(N)` even
when `p ∣ N`, where it gives the bad-prime operator `U_p`. Because of this, the whole
determinant-`n` part of `Δ₀(N)` is the full diamond orbit of the classical `T_n`, not `T_n`
itself; an operator defined downstream must be cut out of the `a ≡ 1` part rather than taken
as that entire fibre.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), with `CoprimeDet` and `coprimeDet_iff` from the `CoprimeDet` section of
`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, and
`exists_primitive_content_quotient` from `Gamma0_content_quotient` of
`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean` (all Chris Birkbeck).

## Main definitions

* `HeckeRing.GL2.Delta0`: the submonoid `Δ₀(N)`.

## Main results

* `HeckeRing.GL2.mem_Delta0_iff`: membership, unfolded.
* `HeckeRing.GL2.CoprimeDet`, `HeckeRing.GL2.coprimeDet_iff`: the elements whose integral
  representative has determinant coprime to `N`, and the fact that one witness decides it.
* `HeckeRing.GL2.Delta0_le_posDetInt`: `Δ₀(N)` consists of integral matrices of positive
  determinant, which is what puts it in the commensurator of `SL₂(ℤ)`.
* `HeckeRing.GL2.exists_primitive_content_quotient`: dividing a matrix of the `Δ₀(N)` shape by
  the gcd of its entries leaves a primitive matrix of the same shape.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

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

/-- An element of `Δ₀(N)` has **coprime determinant** when every integral matrix representing
it has determinant coprime to `N`.

Quantifying over all representatives rather than choosing one keeps the predicate free of a
choice; the representative is unique anyway, since `ℤ → ℚ` is injective. -/
def CoprimeDet (g : Delta0 N) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
      Int.gcd A.det N = 1

/-- `CoprimeDet` is decided by any single integral witness: the witness is unique, because the
entrywise cast `ℤ → ℚ` is injective. This is the introduction rule for the definition, whose
universal quantifier only eliminates. -/
lemma coprimeDet_iff {g : Delta0 N} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    CoprimeDet N g ↔ Int.gcd A.det N = 1 := by
  refine ⟨fun h ↦ h A hA, fun h A' hA' ↦ ?_⟩
  have : A' = A := Matrix.map_injective Int.cast_injective (hA'.symm.trans hA)
  exact this ▸ h

/-- `Δ₀(N)` consists of integral matrices with positive determinant. -/
lemma Delta0_le_posDetInt : Delta0 N ≤ posDetInt 2 := by
  intro g hg
  obtain ⟨A, hA, hdet, -, -⟩ := (mem_Delta0_iff N).mp hg
  exact (mem_posDetInt_iff 2).mpr ⟨(hasIntEntries_iff 2).mpr ⟨A, hA⟩, hdet⟩

/-- The gcd of the four entries, as a natural number. -/
private def entryGCD (A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs) (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs)

/-- The gcd of the entries divides each of them. -/
private lemma entryGCD_dvd (A : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    ((entryGCD A : ℕ) : ℤ) ∣ A i j := by
  refine Int.natAbs_dvd_natAbs.mp ?_
  rw [Int.natAbs_natCast]
  fin_cases i <;> fin_cases j
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

/-- A matrix with nonzero determinant has a nonzero entry, so its entry gcd is positive. -/
private lemma entryGCD_pos {A : Matrix (Fin 2) (Fin 2) ℤ} (hA_det_pos : 0 < A.det) :
    0 < entryGCD A := by
  refine Nat.pos_of_ne_zero fun h ↦ hA_det_pos.ne' ?_
  simp only [entryGCD, Nat.gcd_eq_zero_iff, Int.natAbs_eq_zero] at h
  rw [Matrix.det_fin_two, h.1.1, h.1.2, h.2.1, h.2.2]
  ring

/-- If `d` is the gcd of the entries of `A` and `A = d • A₀`, no prime divides every entry of
`A₀`: such a prime `q` would make `q * d` a common divisor of `A`'s entries, exceeding `d`. -/
private lemma not_prime_dvd_entries_of_isGCD {A A₀ : Matrix (Fin 2) (Fin 2) ℤ} {d : ℕ}
    (hd_pos : 0 < d) (hA_eq : ∀ i j, A i j = (d : ℤ) * A₀ i j)
    (hd_is_gcd : d = Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
      (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs)) (q : ℕ) (hq : q.Prime) :
    ¬((q : ℤ) ∣ A₀ 0 0 ∧ (q : ℤ) ∣ A₀ 0 1 ∧ (q : ℤ) ∣ A₀ 1 0 ∧ (q : ℤ) ∣ A₀ 1 1) := by
  rintro ⟨hq00, hq01, hq10, hq11⟩
  have hqd_nat : ∀ i j : Fin 2, q * d ∣ (A i j).natAbs := fun i j ↦ by
    have h : (q : ℤ) ∣ A₀ i j := by fin_cases i <;> fin_cases j <;> assumption
    rw [hA_eq i j, Int.natAbs_mul, Int.natAbs_natCast, mul_comm]
    exact Nat.mul_dvd_mul_left d (Int.natAbs_dvd_natAbs.mpr h)
  have hqd_dvd_d : q * d ∣ d := by
    conv_rhs => rw [hd_is_gcd]
    exact Nat.dvd_gcd (Nat.dvd_gcd (hqd_nat 0 0) (hqd_nat 0 1))
      (Nat.dvd_gcd (hqd_nat 1 0) (hqd_nat 1 1))
  have hq_le : q ≤ 1 :=
    Nat.le_of_mul_le_mul_right (by linarith [Nat.le_of_dvd hd_pos hqd_dvd_d]) hd_pos
  exact absurd hq.two_le (by omega)

/-- **Content factorisation for the `Δ₀(N)` shape.** Dividing an integral matrix by the gcd `d`
of its entries leaves a *primitive* matrix — one no prime divides entrywise — that still has
positive determinant, `N ∣ c`, and upper-left entry coprime to `N`.

The `Δ₀(N)` conditions survive the division because `d` is coprime to `N`: it divides `A 0 0`,
which is coprime to `N` by hypothesis. This is the reduction step that lets a statement about
`Δ₀(N)` double cosets be proved for primitive representatives first.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB>), where it is `Gamma0_content_quotient`. -/
lemma exists_primitive_content_quotient (A : Matrix (Fin 2) (Fin 2) ℤ) (hA_det_pos : 0 < A.det)
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1) (d : ℕ)
    (hd_is_gcd : d = Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
      (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs)) :
    ∃ A₀ : Matrix (Fin 2) (Fin 2) ℤ, (∀ i j, A i j = (d : ℤ) * A₀ i j) ∧ 0 < A₀.det ∧
      (N : ℤ) ∣ A₀ 1 0 ∧ Int.gcd (A₀ 0 0) N = 1 ∧
      ∀ q : ℕ, q.Prime → ¬((q : ℤ) ∣ A₀ 0 0 ∧ (q : ℤ) ∣ A₀ 0 1 ∧ (q : ℤ) ∣ A₀ 1 0 ∧
        (q : ℤ) ∣ A₀ 1 1) := by
  -- both facts the caller might have supplied are consequences of `hd_is_gcd`
  have hd_dvd : ∀ i j : Fin 2, (d : ℤ) ∣ A i j := fun i j ↦ hd_is_gcd ▸ entryGCD_dvd A i j
  have hd_pos : 0 < d := hd_is_gcd ▸ entryGCD_pos hA_det_pos
  set A₀ : Matrix (Fin 2) (Fin 2) ℤ := fun i j ↦ A i j / d with hA₀
  have hA_eq : ∀ i j, A i j = (d : ℤ) * A₀ i j := fun i j ↦ by
    simp only [hA₀]; rw [mul_comm]; exact (Int.ediv_mul_cancel (hd_dvd i j)).symm
  -- `d` divides the upper-left entry, which is coprime to `N`, so `d` is too
  have hd_Nco : Int.gcd (d : ℤ) N = 1 := by
    refine Nat.eq_one_of_dvd_one (hAco ▸ Nat.dvd_gcd ?_ ?_)
    · exact Int.natAbs_dvd_natAbs.mpr ((Int.gcd_dvd_left (d : ℤ) N).trans (hd_dvd 0 0))
    · exact Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_right (d : ℤ) N)
  -- the entrywise equation, repackaged as a scalar multiple so that `Matrix.det_smul` applies
  have hA_smul : A = (d : ℤ) • A₀ := Matrix.ext fun i j ↦ hA_eq i j
  -- the scaling is `Matrix.det_smul` at `Fintype.card (Fin 2) = 2`
  have hdet : A.det = (d : ℤ) ^ 2 * A₀.det := by
    rw [hA_smul, Matrix.det_smul, Fintype.card_fin]
  refine ⟨A₀, hA_eq, ?_, ?_, ?_, not_prime_dvd_entries_of_isGCD hd_pos hA_eq hd_is_gcd⟩
  · exact (mul_pos_iff.mp (hdet ▸ hA_det_pos)).elim (fun h ↦ h.2)
      fun h ↦ absurd h.1 (not_lt.mpr (sq_nonneg (d : ℤ)))
  · exact (Int.isCoprime_iff_gcd_eq_one.mpr hd_Nco).symm.dvd_of_dvd_mul_left (hA_eq 1 0 ▸ hAN)
  · exact Int.isCoprime_iff_gcd_eq_one.mp
      ((Int.isCoprime_iff_gcd_eq_one.mpr (hA_eq 0 0 ▸ hAco)).of_isCoprime_of_dvd_left
        (dvd_mul_left (A₀ 0 0) (d : ℤ)))

end HeckeRing.GL2
