/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.CoprimeMul
public import TauCeti.NumberTheory.HeckeRing.GLn.ScalarMul

import Mathlib.Data.Finset.NatDivisors

/-!
# The `GL₂` Hecke operators `T(a, d)` and `T(m)`

The specialization of the `GL_n` Hecke ring to `n = 2`: the basis operators `T(a, d)` for
divisor pairs `a ∣ d`, the scalar operators `T(c, c)`, and Shimura's summed operator
`T(m) = ∑_{a ∣ m} T(a, m / a)`.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Basic.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GL2.heckeTDiag`: `T(a, d)`, zero unless `0 < a`, `0 < d`, `a ∣ d`.
* `HeckeRing.GL2.heckeTScalar`: the scalar operator `T(c, c)`.
* `HeckeRing.GL2.heckeT`: Shimura's `T(m) = ∑_{a ∣ m} T(a, m / a)`.

## Main results

* `HeckeRing.GL2.heckeTDiag_one_one`: `T(1, 1) = 1`, with `heckeTScalar_one` its scalar form.
* `HeckeRing.GL2.heckeT_one`: `T(1) = 1`.
* `HeckeRing.GL2.heckeT_prime`: `T(p) = T(1, p)` for prime `p`.
* `HeckeRing.GL2.heckeTDiag_mul_of_coprime`: `T(a,da) · T(b,db) = T(ab, da·db)` for
  coprime determinants — coprimality alone, the zero-extension covering the rest.
* `HeckeRing.GL2.heckeT_mul_of_coprime`: `T(m) · T(n) = T(mn)` for coprime `m`, `n`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Theorem 3.24.
-/

public section

open Matrix HeckeRing DoubleCoset Finset HeckeRing.GLn

namespace HeckeRing.GL2

/-- `T(a, d)`: the diagonal Hecke basis element of the pair `(a, d)`, zero unless
`0 < a`, `0 < d` and `a ∣ d`. -/
noncomputable def heckeTDiag (a d : ℕ) : IntegralHeckeRing 2 :=
  if 0 < a ∧ 0 < d ∧ a ∣ d then diagElem ![a, d] else 0

/-- Defining equation for the sealed `heckeTDiag`. -/
lemma heckeTDiag_def (a d : ℕ) :
    heckeTDiag a d = if 0 < a ∧ 0 < d ∧ a ∣ d then diagElem ![a, d] else 0 := (rfl)

/-- `T(a, d)` is the diagonal Hecke element when the divisor-pair conditions hold.

All three hypotheses are needed. `0 < d` does not follow from `0 < a` and `a ∣ d`: in `ℕ`
every number divides `0`, so `a = 1, d = 0` satisfies both while `0 < d` fails — and that is
exactly the tuple on which `natDiagGL` takes its junk value, which the `0 < d` branch of
`heckeTDiag` exists to exclude. -/
-- Deliberately not `@[simp]`: it rewrites *past* `heckeTDiag_one_one`. With this tagged,
-- `heckeTDiag 1 1` normalises to `diagElem ![1, 1]` rather than to `1`, and it stops there —
-- `diagElem_one` is stated for `fun _ ↦ 1`, which `![1, 1]` does not match syntactically. The
-- identity normal form `T(1, 1) = 1` is the more useful one, so this stays a cited lemma.
lemma heckeTDiag_eq_diagElem {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (h : a ∣ d) :
    heckeTDiag a d = diagElem ![a, d] :=
  ite_eq_left ⟨ha, hd, h⟩

/-- `T(a, d)` is zero when the divisor-pair conditions fail. -/
@[simp]
lemma heckeTDiag_eq_zero {a d : ℕ} (h : ¬(0 < a ∧ 0 < d ∧ a ∣ d)) : heckeTDiag a d = 0 :=
  ite_eq_right h

/-- `T(c, c)`: the scalar Hecke operator. -/
noncomputable def heckeTScalar (c : ℕ) : IntegralHeckeRing 2 :=
  heckeTDiag c c

/-- The defining equation of `heckeTScalar`. -/
-- Deliberately not `@[simp]`: unfolding `heckeTScalar c` to `heckeTDiag c c` would leave the
-- left-hand side of `heckeTScalar_of_pos` in non-normal form, which `simpNF` rejects. Only one
-- of the two can carry the attribute, and `heckeTScalar_of_pos` is the one that reduces to a
-- diagonal element.
lemma heckeTScalar_def (c : ℕ) : heckeTScalar c = heckeTDiag c c := (rfl)

/-- `T(0, 0) = 0`: the scalar operator of `0` is zero, since the divisor-pair conditions fail.

Together with `heckeTScalar_of_pos` this covers the whole `ℕ`-valued interface, so consumers
never need to unfold through `heckeTScalar_def`. -/
@[simp]
lemma heckeTScalar_zero : heckeTScalar 0 = 0 := by
  rw [heckeTScalar_def]
  exact heckeTDiag_eq_zero (by simp)

/-- The scalar operator of a positive `c` is the constant diagonal element. -/
-- Deliberately not `@[simp]`, although an earlier api-design round asked for it. Tagging this
-- unfolds every `heckeTScalar p` to `diagElem (fun _ ↦ p)`, which leaves the left-hand side of
-- `heckeTScalar_mul_heckeTDiag_prime_pow` non-normal — `simpNF` rejects that, and the index
-- shift is the rule worth keeping: it collapses `T(p,p) · T(pʲ, p^d)` to a single
-- `heckeTDiag`, the normal form the GL₂ multiplication table works in.
lemma heckeTScalar_of_pos {c : ℕ} (hc : 0 < c) :
    heckeTScalar c = diagElem (fun _ : Fin 2 ↦ c) := by
  rw [heckeTScalar, heckeTDiag_eq_diagElem hc hc dvd_rfl]
  exact congrArg diagElem (funext fun i ↦ by fin_cases i <;> rfl)

/-- `T(1, 1)` is the identity. -/
@[simp] lemma heckeTDiag_one_one : heckeTDiag 1 1 = 1 := by
  rw [heckeTDiag_eq_diagElem one_pos one_pos dvd_rfl,
    show ![1, 1] = (fun _ : Fin 2 ↦ 1) from funext fun i ↦ by fin_cases i <;> rfl]
  exact diagElem_one

/-- `T(1, 1) = 1` in scalar form: the scalar operator of `1` is the identity. Together with
`heckeTScalar_zero` and `heckeTScalar_of_pos` this closes the `ℕ`-valued interface at its
canonical input. -/
@[simp] lemma heckeTScalar_one : heckeTScalar 1 = 1 := by
  rw [heckeTScalar_def]
  exact heckeTDiag_one_one

/-- Shimura's summed Hecke operator: `T(m) = ∑_{a ∣ m} T(a, m / a)`. -/
noncomputable def heckeT (m : ℕ+) : IntegralHeckeRing 2 :=
  ∑ a ∈ (m : ℕ).divisors, heckeTDiag a ((m : ℕ) / a)

/-- The defining equation of `heckeT`. -/
lemma heckeT_def (m : ℕ+) :
    heckeT m = ∑ a ∈ (m : ℕ).divisors, heckeTDiag a ((m : ℕ) / a) := (rfl)

/-- `T(1) = 1`: the only divisor pair of `1` is `(1,1)`. -/
@[simp] lemma heckeT_one : heckeT 1 = 1 := by
  rw [heckeT_def]
  simp only [PNat.one_coe, Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  exact heckeTDiag_one_one

/-- For a prime `p`, the summed operator collapses: `T(p) = T(1, p)`. -/
@[simp]
lemma heckeT_prime (p : ℕ) (hp : p.Prime) : heckeT ⟨p, hp.pos⟩ = heckeTDiag 1 p := by
  -- `heckeT` is sealed (`public section`, no `@[expose]`), so `rw`/`simp` cannot unfold it;
  -- `change` states the defeq divisor-pair sum directly
  change ∑ a ∈ p.divisors, heckeTDiag a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one,
    heckeTDiag_eq_zero (fun ⟨_, _, hdvd⟩ ↦ hp.ne_one (Nat.dvd_one.mp hdvd)), zero_add]

section Structural

variable (p : ℕ)

/-- Powers of the scalar operator: `T(p,p) ^ i = T(pⁱ,...,pⁱ)`. -/
lemma heckeTScalar_pow (hp : 0 < p) (i : ℕ) :
    heckeTScalar p ^ i = diagElem (fun _ : Fin 2 ↦ p ^ i) := by
  induction i with
  | zero =>
    rw [pow_zero]
    exact ((congrArg diagElem (funext fun _ ↦ by simp)).trans diagElem_one).symm
  | succ i ih =>
    rw [pow_succ', ih, heckeTScalar_of_pos hp,
      diagElem_const_mul 2 p hp (fun _ ↦ p ^ i) (fun _ ↦ pow_pos hp i)]
    exact congrArg diagElem (funext fun _ ↦ by simp [Pi.mul_apply, pow_succ, mul_comm])

/-- Expansion of `T(pᵏ)`: only the divisor pairs `(pⁱ, p^(k-i))` with `i ≤ k - i`
contribute. -/
lemma heckeT_prime_pow_expansion (hp : p.Prime) (k : ℕ) :
    heckeT ⟨p ^ k, pow_pos hp.pos k⟩ =
      ∑ i ∈ Finset.range (k / 2 + 1), heckeTDiag (p ^ i) (p ^ (k - i)) := by
  -- `heckeT` is sealed (`public section`, no `@[expose]`), so `rw`/`simp` cannot unfold it;
  -- `change` states the defeq divisor-pair sum directly
  change ∑ a ∈ (p ^ k).divisors, heckeTDiag a (p ^ k / a) = _
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_congr rfl
    (g := fun j ↦ heckeTDiag (p ^ j) (p ^ (k - j))) fun j hj ↦ by
      rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]]
  refine (Finset.sum_subset (Finset.range_mono (by omega)) fun j hj hnj ↦ ?_).symm
  simp only [Finset.mem_range] at hj hnj
  exact heckeTDiag_eq_zero fun ⟨_, _, hdvd⟩ ↦ absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd)
    (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (by omega)))

/-- **Coprime multiplicativity** (Shimura, Proposition 3.16 in the `GL₂` notation):
`T(a, da) · T(b, db) = T(ab, da·db)` when the determinants `a·da` and `b·db` are coprime.

Coprimality is the *only* hypothesis. No positivity or divisor-pair condition is needed,
because `heckeTDiag` is zero-extended and coprimality propagates that zero: if `T(a, da)`
fails to be a basis element then so does `T(ab, da·db)`, since `a` is coprime to `db`, so
`a ∣ ab ∣ da·db` would force `a ∣ da`. Both sides are then `0`. -/
lemma heckeTDiag_mul_of_coprime (a b da db : ℕ)
    (hcop : Nat.Coprime (a * da) (b * db)) :
    heckeTDiag a da * heckeTDiag b db = heckeTDiag (a * b) (da * db) := by
  -- Coprimality alone suffices: if either factor fails to be a basis element it is zero, and
  -- coprimality then forces the product to be zero too (see `hzero`).
  have hzero : ∀ x y u v : ℕ, Nat.Coprime (x * u) (y * v) →
      ¬(0 < x ∧ 0 < u ∧ x ∣ u) → ¬(0 < x * y ∧ 0 < u * v ∧ x * y ∣ u * v) := by
    rintro x y u v hc hbad ⟨hxy, huv, hdvd⟩
    refine hbad ⟨Nat.pos_of_ne_zero fun h ↦ by simp [h] at hxy,
      Nat.pos_of_ne_zero fun h ↦ by simp [h] at huv, ?_⟩
    -- `x` is coprime to `v`, and `x ∣ x * y ∣ u * v`, so `x ∣ u`
    exact (Nat.Coprime.dvd_of_dvd_mul_right
      ((hc.coprime_dvd_left (dvd_mul_right x u)).coprime_dvd_right (dvd_mul_left v y))
      ((dvd_mul_right x y).trans hdvd))
  by_cases h1 : 0 < a ∧ 0 < da ∧ a ∣ da
  swap
  · rw [heckeTDiag_eq_zero h1, zero_mul, heckeTDiag_eq_zero (hzero a b da db hcop h1)]
  by_cases h2 : 0 < b ∧ 0 < db ∧ b ∣ db
  swap
  · rw [heckeTDiag_eq_zero h2, mul_zero,
      heckeTDiag_eq_zero (by simpa [Nat.mul_comm] using hzero b a db da hcop.symm h2)]
  obtain ⟨ha, hda, hdva⟩ := h1
  obtain ⟨hb, hdb, hdvb⟩ := h2
  have hb : 0 < b := Nat.pos_of_dvd_of_pos hdvb hdb
  rw [heckeTDiag_eq_diagElem ha hda hdva, heckeTDiag_eq_diagElem hb hdb hdvb,
    heckeTDiag_eq_diagElem (Nat.mul_pos ha hb) (Nat.mul_pos hda hdb) (Nat.mul_dvd_mul hdva hdvb)]
  have hprod : diagElem ((![a, da] : Fin 2 → ℕ) * ![b, db]) =
      diagElem (![a * b, da * db] : Fin 2 → ℕ) :=
    congrArg diagElem (funext fun i ↦ by fin_cases i <;> simp [Pi.mul_apply])
  rw [← hprod]
  exact diagElem_mul_of_coprime 2 ![a, da] ![b, db]
    (by simpa [Fin.prod_univ_two] using hcop)

open scoped Pointwise in
/-- **Shimura, Theorem 3.24(3a)** — coprime multiplicativity: `T(m) · T(n) = T(mn)` when
`m` and `n` are coprime. -/
theorem heckeT_mul_of_coprime (m n : ℕ+) (hcop : Nat.Coprime (m : ℕ) (n : ℕ)) :
    heckeT m * heckeT n = heckeT (m * n) := by
  simp only [heckeT_def, PNat.mul_coe]
  -- `Finset` pointwise multiplication is by definition the image of the product set,
  -- so the divisor-set product can be reindexed as a sum over pairs
  rw [Finset.sum_mul_sum, Nat.divisors_mul,
    show ((m : ℕ).divisors * (n : ℕ).divisors) =
      ((m : ℕ).divisors ×ˢ (n : ℕ).divisors).image (fun q ↦ q.1 * q.2) from rfl,
    Finset.sum_image hcop.mul_injOn_divisors, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  obtain ⟨a, b⟩ := q
  simp only [Finset.mem_product, Nat.mem_divisors] at hq
  rw [(Nat.div_mul_div_comm hq.1.1 hq.2.1).symm]
  refine heckeTDiag_mul_of_coprime a b _ _ ?_
  rwa [Nat.mul_div_cancel' hq.1.1, Nat.mul_div_cancel' hq.2.1]

end Structural

end HeckeRing.GL2
