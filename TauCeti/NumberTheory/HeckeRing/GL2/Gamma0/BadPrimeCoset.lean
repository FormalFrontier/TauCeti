/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

-- `ZMod.coe_int_isUnit_iff_isCoprime` is used only inside a proof, so this stays private.
import Mathlib.Data.ZMod.Units
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset
public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

/-!
# The `N`-supported determinant case of `Δ₀(N)`

`Gamma0/DoubleCoset.lean` settles the **coprime** case: when `gcd(det α, N) = 1`, the
`SL₂(ℤ)`-double coset of `α` meets `Δ₀(N)` in exactly the `Γ₀(N)`-double coset. This file
handles the opposite extreme, Shimura Proposition 3.33: an element of `Δ₀(N)` whose determinant
`m` **divides a power of `N`** lies in the `Γ₀(N)`-double coset of `diag(1, m)`.

⚠ These two cases do **not** exhaust the determinants a `Δ₀(N)` element can have. A determinant
may be neither coprime to `N` nor a divisor of a power of it: `natDiagGL 2 ![1, 6]` lies in
`Δ₀(2)` with determinant `6`, and `gcd(6, 2) = 2 ≠ 1` while `6 ∤ 2 ^ k` for every `k`. The
mixed case is not treated here or in `Gamma0/DoubleCoset.lean`.

The proof is a column reduction. Coprimality of the upper-left entry to the determinant lets
one column operation clear the upper row modulo `m`; the determinant identity then forces the
lower-right entry to clear as well, leaving `A` in the left `Γ₀(N)`-coset of `!![1, r; 0, m]`
for a reduced `0 ≤ r < m`. Splitting that representative as `diag(1, m) · !![1, r; 0, 1]` moves
the remaining parameter into a second `Γ₀(N)` factor, which is what makes the conclusion a
*double* coset.

## Main results

* `HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_dvd_pow`: Shimura 3.33 — an element of `Δ₀(N)`
  whose determinant `m` divides a power of the level lies in the `Γ₀(N)`-double coset of
  `diag(1, m)`.
* `HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_intWitness`: the same conclusion drawn from an
  integral witness directly, with no `Δ₀(N)` hypothesis.
* `HeckeRing.GL2.exists_unimodular_mul_upperTriangular`: the column reduction, stated on its
  own.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.33.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, declarations
  `exists_mod_clearing`, `dvd_lowerRight_witness`, `shimura_prop_3_33_gen` and
  `shimura_prop_3_33`.

  Four source declarations are deliberately **not** ported. `diagMat_one_mem_Delta0` and
  `diagMat_mem_Delta0_of_gcd` are already on main as `natDiagGL_one_mem_Delta0` and
  `natDiagGL_mem_Delta0_of_coprime`. `fin2_col_scale` exists only to drive the source's
  entrywise `fin_cases`/`linarith` verification of the final matrix identity, which is done
  here by factoring `!![1, r; 0, m]` and reusing `HeckeRing.GLn.mapGL_mul_coe_eq_intMatrix`.
  `coprime_of_gcd_one_dvd_pow` is `Nat.Coprime.pow_right` composed with
  `Nat.Coprime.coprime_dvd_right` and is used inline instead.

  The source's `diagMat`/`Delta0_submonoid`/`(Gamma0_pair N).H` vocabulary is
  `natDiagGL`/`Delta0`/`(Gamma0 N).map (mapGL ℚ)` here; the source's `[NeZero N]` instance,
  its `β ∈ Δ₀(N)` hypothesis on the general form, and its `0 < m` hypothesis on both forms are
  dropped as unused or derivable.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

/-- **Bézout, in the shape a row operation needs.** If `a` is coprime to `p` then the residue
of `c` can be cleared by adding a multiple of `a`: some `t` has `p ∣ t * a + c`.

Stated over `ℤ` with `p : ℕ` because the modulus arrives as a natural determinant. -/
lemma exists_mod_clearing (a c : ℤ) (p : ℕ) (hap : Int.gcd a p = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ (t * a + c) := by
  refine ⟨-c * Int.gcdA a p, ⟨c * Int.gcdB a p, ?_⟩⟩
  have bez := Int.gcd_eq_gcd_ab a p
  rw [hap] at bez
  linear_combination c * bez

/-- **Clearing the upper row clears the lower-right entry too.** For an integral matrix whose
lower-left entry is `N * c₀` and whose determinant is `m`, with the upper-left entry coprime to
`m`: if `m` divides `A 0 0 * r - A 0 1` then it divides `A 1 1 - N * c₀ * r`.

This is the bookkeeping that lets one column operation put a `Δ₀(N)` representative into the
shape `diag(1, m)` sits in. The determinant identity does the work; coprimality of `A 0 0` with
`m` is what lets it be cancelled. -/
private lemma dvd_lowerRight_witness (A : Matrix (Fin 2) (Fin 2) ℤ) (N m : ℕ) (c₀ r : ℤ)
    (hc₀ : A 1 0 = (N : ℤ) * c₀) (hdet : A.det = m) (ham : Int.gcd (A 0 0) m = 1)
    (hm_ar_b : (m : ℤ) ∣ (A 0 0 * r - A 0 1)) :
    (m : ℤ) ∣ (A 1 1 - (N : ℤ) * c₀ * r) := by
  have h_key : A 0 0 * (A 1 1 - (N : ℤ) * c₀ * r)
      = (m : ℤ) + (A 0 1 - A 0 0 * r) * ((N : ℤ) * c₀) := by
    have h_det := Matrix.det_fin_two A
    rw [hc₀, hdet] at h_det
    linarith
  have hm_ba : (m : ℤ) ∣ (A 0 1 - A 0 0 * r) := by
    obtain ⟨w, hw⟩ := hm_ar_b
    exact ⟨-w, by linarith⟩
  exact ((Int.isCoprime_iff_gcd_eq_one.mpr ham).symm).dvd_of_dvd_mul_left
    (h_key ▸ dvd_add (dvd_refl _) (dvd_mul_of_dvd_left hm_ba _))

/-- **The reduced shear parameter.** With `A 0 0` coprime to `m` there is an `r` in `[0, m)`
clearing the upper row modulo `m`: `m ∣ A 0 0 * r - A 0 1`.

Split out of `exists_unimodular_mul_upperTriangular` below: it is the arithmetic half, and
isolating it keeps that lemma's matrix bookkeeping readable. -/
private lemma exists_reduced_shear (A : Matrix (Fin 2) (Fin 2) ℤ) (m : ℕ) (hm_pos : 0 < m)
    (ham : Int.gcd (A 0 0) m = 1) :
    ∃ r : ℤ, 0 ≤ r ∧ r < m ∧ (m : ℤ) ∣ (A 0 0 * r - A 0 1) := by
  obtain ⟨t_inv, ht⟩ := exists_mod_clearing (A 0 0) (-A 0 1) m ham
  refine ⟨t_inv % (m : ℤ), Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), ?_⟩
  -- `t_inv` differs from its residue by a multiple of `m`, so subtracting that multiple of
  -- `A 0 0` from Bézout's combination leaves the divisibility intact.
  have hquot : t_inv - t_inv % (m : ℤ) = (m : ℤ) * (t_inv / (m : ℤ)) := by
    linarith [Int.mul_ediv_add_emod t_inv ((m : ℤ))]
  have hm_tr : (m : ℤ) ∣ (t_inv - t_inv % (m : ℤ)) := hquot ▸ dvd_mul_right _ _
  have h := dvd_sub ht (dvd_mul_of_dvd_left hm_tr (A 0 0))
  have hcollapse : t_inv * A 0 0 + -A 0 1 - (t_inv - t_inv % (m : ℤ)) * A 0 0
      = A 0 0 * (t_inv % (m : ℤ)) - A 0 1 := by ring
  rwa [hcollapse] at h

/-- **The determinant of an integral witness.** If `A` represents `g ∈ GL₂(ℚ)` entrywise over
`ℤ` and `g` has determinant `m`, then `A` has determinant `m` over `ℤ`.

The `Δ₀(N)` membership predicate states the determinant on the `ℚ`-side while the column
reduction works on the `ℤ`-side, so this cast bridge is needed to move between them. -/
lemma det_eq_of_coe_eq_map_intCast (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) (m : ℕ)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    A.det = (m : ℤ) := by
  have h : ((A.det : ℤ) : ℚ) = (m : ℚ) := by
    rw [← hdet, hA, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [Matrix.map_apply]
    push_cast
    ring
  exact_mod_cast h

/-- **The cofactor pair is unimodular.** Given the two divisibility witnesses `q₁, q₂` produced
by the column reduction, the matrix `!![A 0 0, -q₁; N * c₀, q₂]` has determinant one.

The identity holds after multiplying by `m` — that is just `det A = m` rearranged — and `m ≠ 0`
cancels it. Split out of `exists_unimodular_mul_upperTriangular` to keep that proof under the
decomposition threshold. -/
private lemma cofactor_pair_unimodular (A : Matrix (Fin 2) (Fin 2) ℤ) (N m : ℕ) (hm_pos : 0 < m)
    (c₀ r q₁ q₂ : ℤ) (hc₀ : A 1 0 = (N : ℤ) * c₀) (hdet : A.det = m)
    (hq₁ : A 0 0 * r - A 0 1 = (m : ℤ) * q₁)
    (hq₂ : A 1 1 - (N : ℤ) * c₀ * r = (m : ℤ) * q₂) :
    A 0 0 * q₂ + q₁ * ((N : ℤ) * c₀) = 1 := by
  have hdet' : A 0 0 * A 1 1 - A 0 1 * ((N : ℤ) * c₀) = (m : ℤ) := by
    rw [← hdet, Matrix.det_fin_two, hc₀]
  have h1 : (A 0 0 * q₂ + q₁ * ((N : ℤ) * c₀)) * (m : ℤ) = 1 * (m : ℤ) := by
    rw [one_mul]
    calc (A 0 0 * q₂ + q₁ * ((N : ℤ) * c₀)) * (m : ℤ)
        = A 0 0 * ((m : ℤ) * q₂) + ((m : ℤ) * q₁) * ((N : ℤ) * c₀) := by ring
      _ = A 0 0 * (A 1 1 - (N : ℤ) * c₀ * r) + (A 0 0 * r - A 0 1) * ((N : ℤ) * c₀) := by
            rw [← hq₂, ← hq₁]
      _ = (m : ℤ) := by linarith [hdet']
  have hm_ne : (m : ℤ) ≠ 0 := by omega
  exact mul_right_cancel₀ hm_ne h1

/-- **The upper-triangular normal form of the column reduction.** An integral matrix with
lower-left entry divisible by `N`, determinant `m`, and upper-left entry coprime to `m`,
factors as `L * !![1, r; 0, m]` with `L` again of that `Γ₀`-shape — determinant one and
lower-left entry divisible by `N` — and `r` reduced into `[0, m)`.

This is the column reduction behind Shimura 3.33: it exhibits `A` in the left `Γ₀(N)`-coset of
the upper-triangular representative `!![1, r; 0, m]`. No separate positivity hypothesis on
`det A` is required beyond `hm_pos` and `hdet`, which already pin the determinant down; the
source carries such a hypothesis as well and never uses it. -/
lemma exists_unimodular_mul_upperTriangular (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hAN : (N : ℤ) ∣ A 1 0) (m : ℕ) (hm_pos : 0 < m) (hdet : A.det = m)
    (ham : Int.gcd (A 0 0) m = 1) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ), L.det = 1 ∧ (N : ℤ) ∣ L 1 0 ∧ 0 ≤ r ∧ r < m ∧
      A = L * (Matrix.of ![![(1 : ℤ), r], ![0, (m : ℤ)]]) := by
  obtain ⟨c₀, hc₀⟩ := hAN
  obtain ⟨r, hr_nonneg, hr_lt, hm_ar_b⟩ := exists_reduced_shear A m hm_pos ham
  obtain ⟨q₂, hq₂⟩ := dvd_lowerRight_witness A N m c₀ r hc₀ hdet ham hm_ar_b
  obtain ⟨q₁, hq₁⟩ := hm_ar_b
  refine ⟨Matrix.of ![![A 0 0, -q₁], ![(N : ℤ) * c₀, q₂]], r, ?_, ?_, hr_nonneg, hr_lt, ?_⟩
  · simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val']
    linarith [cofactor_pair_unimodular A N m hm_pos c₀ r q₁ q₂ hc₀ hdet hq₁ hq₂]
  · norm_num [Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val',
      Matrix.cons_val_zero]
  · have h00 : A 0 0 = A 0 0 * 1 + (-q₁) * 0 := by ring
    have h01 : A 0 1 = A 0 0 * r + (-q₁) * (m : ℤ) := by linarith [hq₁]
    have h10 : A 1 0 = (N : ℤ) * c₀ * 1 + q₂ * 0 := by linarith [hc₀]
    have h11 : A 1 1 = (N : ℤ) * c₀ * r + q₂ * (m : ℤ) := by linarith [hq₂]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val'] <;>
      first | exact h00 | exact h01 | exact h10 | exact h11

/-- **The reduced representative splits off its shear.** `!![1, r; 0, m]` is `diag(1, m)`
followed by the unipotent `!![1, r; 0, 1]`.

This one identity is what upgrades the column reduction from a *left*-coset statement to a
double-coset one. `exists_unimodular_mul_upperTriangular` puts `A` in the left `Γ₀(N)`-coset of
`!![1, r; 0, m]`, which still mentions `r`; splitting the shear off on the right moves `r` into
a second `Γ₀(N)` factor, where it is harmless, a unipotent upper-triangular matrix having
lower-left entry `0` and so lying in `Γ₀(N)` for every level. -/
private lemma upperTriangular_eq_diagonal_mul_unipotent (m : ℕ) (r : ℤ) :
    (Matrix.of ![![(1 : ℤ), r], ![0, (m : ℤ)]]) =
      Matrix.diagonal (fun i ↦ ((![1, m] : Fin 2 → ℕ) i : ℤ)) *
        Matrix.of ![![(1 : ℤ), r], ![0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- A `GL₂(ℚ)` element whose determinant equals a natural number forces that number to be
positive: an invertible matrix has nonzero determinant, and a nonzero natural is positive.

Kept separate so the two main results can drop `0 < m` from their hypotheses without carrying
the derivation inline. -/
private lemma pos_of_det_eq_natCast (β : GL (Fin 2) ℚ) (m : ℕ)
    (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) : 0 < m :=
  Nat.pos_of_ne_zero (by
    have hne := Matrix.GeneralLinearGroup.det_ne_zero β
    rw [hdet] at hne
    exact_mod_cast hne)

/-- **Shimura 3.33, from an integral witness.** An element of `GL₂(ℚ)` with an integral matrix
`A` whose lower-left entry is divisible by `N`, whose determinant is `m`, and whose upper-left
entry is coprime to `m`, lies in the `Γ₀(N)`-double coset of `diag(1, m)`.

Membership of `Δ₀(N)` is deliberately **not** assumed: the proof uses exactly the three facts
about `A` that `mem_Delta0_iff` would hand over. Positivity of `m` is likewise not assumed —
`β` is invertible, so its determinant is nonzero. -/
theorem mem_doubleCoset_natDiagGL_of_intWitness (N m : ℕ) (β : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (β : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ))
    (ham : Int.gcd (A 0 0) m = 1) :
    β ∈ DoubleCoset.doubleCoset (natDiagGL 2 ![1, m])
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  have hm_pos : 0 < m := pos_of_det_eq_natCast β m hdet
  obtain ⟨L, r, hL_det, hL_N, -, -, hA_eq⟩ :=
    exists_unimodular_mul_upperTriangular N A hAN m hm_pos
      (det_eq_of_coe_eq_map_intCast β A hA m hdet) ham
  have hR_det : (Matrix.of ![![(1 : ℤ), r], ![0, 1]]).det = 1 := by
    simp [Matrix.det_fin_two]
  -- `SL(2, ℤ)` is reducibly the subtype `{A // A.det = 1}`, so an ascribed
  -- `(⟨L, hL_det⟩ : SL(2, ℤ))` elaborates to the *subtype's* constructor and leaves the goal
  -- ill-typed at `implicit` transparency, where the coercion lemmas can no longer fire. Naming
  -- the factors as genuine `SL(2, ℤ)` variables is what avoids that.
  obtain ⟨L_sl, hL_sl⟩ : ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) = L := ⟨⟨L, hL_det⟩, rfl⟩
  obtain ⟨R_sl, hR_sl⟩ : ∃ g : SL(2, ℤ),
      (g : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.of ![![(1 : ℤ), r], ![0, 1]] := ⟨⟨_, hR_det⟩, rfl⟩
  have hDiag := natDiagGL_coe_eq_map_intCast 2 ![1, m] fun i ↦ by fin_cases i <;> simp [hm_pos]
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨mapGL ℚ L_sl, Subgroup.mem_map_of_mem _ (Gamma0_mem.mpr ?_),
    mapGL ℚ R_sl, Subgroup.mem_map_of_mem _ (Gamma0_mem.mpr ?_), Units.ext ?_⟩
  · exact hL_sl ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL_N
  · simp [hR_sl]
  · rw [mapGL_mul_coe_eq_intMatrix 2 L_sl R_sl _ _ hDiag, hL_sl, hR_sl, hA, hA_eq,
      upperTriangular_eq_diagonal_mul_unipotent, ← mul_assoc]

/-- **Shimura, Proposition 3.33.** An element of `Δ₀(N)` whose determinant `m` divides a power
of the level lies in the `Γ₀(N)`-double coset of `diag(1, m)`.

This is the `N`-supported determinant case. `Gamma0/DoubleCoset.lean` settles the coprime case
`gcd(m, N) = 1`; a determinant of neither kind is treated by neither file, as the
module docstring records. -/
theorem mem_doubleCoset_natDiagGL_of_dvd_pow (N m : ℕ) (k : ℕ) (hm_dvd : m ∣ N ^ k)
    (β : GL (Fin 2) ℚ) (hβ : β ∈ Delta0 N)
    (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    β ∈ DoubleCoset.doubleCoset (natDiagGL 2 ![1, m])
      ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A, hA, -, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hβ
  have hAcop : Int.gcd (A 0 0) N = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp
      (isCoprime_comm.mp ((ZMod.coe_int_isUnit_iff_isCoprime _ _).mp hAunit))
  exact mem_doubleCoset_natDiagGL_of_intWitness N m β A hA hAN hdet
    (Nat.Coprime.coprime_dvd_right hm_dvd (Nat.Coprime.pow_right k hAcop))

end HeckeRing.GL2

end
