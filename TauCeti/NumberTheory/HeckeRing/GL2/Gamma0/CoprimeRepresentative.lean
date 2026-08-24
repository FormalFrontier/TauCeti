/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.RingTheory.Int.Basic

/-!
# Coprime representatives under the two-sided `Γ₀(N)` action

An element of `Δ₀(N)` whose integral matrix is **primitive** — no prime divides all four
entries — can be moved by the two-sided `Γ₀(N)` action to a representative whose upper-left
entry is coprime to a prescribed modulus `c`, provided `c` is coprime to `N`. The `Δ₀(N)`
shape is preserved: the translate is still integral, its lower-left entry is still divisible
by `N`, and its upper-left entry is still coprime to `N` — now coprime to `c` as well. (Coprime
to `N`, not a unit in `ℤ`: nothing here proves the entry is `±1`.)

The mechanism is local-to-global. For a single prime `p ∤ N` not dividing all of `A`, one of
the four choices `(l, t) ∈ {0,1}²` already makes `A₀₀ + l·A₁₀ + N·t·(A₀₁ + l·A₁₁)` prime to
`p`; primitivity is exactly what guarantees such a choice exists. Those independent local
choices are then glued by the Chinese remainder theorem over `c.primeFactors`, and the entry
depends on `l` and `t` only modulo `p`, so the glued pair inherits every local choice at once.
The resulting `l₀, t₀` are read off as the unipotent matrices `!![1, l₀; 0, 1]` and
`!![1, 0; N·t₀, 1]`, both of determinant `1` and both in `Γ₀(N)`.

Together with `exists_primitive_content_quotient`, which divides out the content so that
primitivity may be assumed, this is the reduction behind Shimura's Proposition 3.8 at level
`Γ₀(N)`: it is what lets a statement about `Δ₀(N)` double cosets be proved for coprime
representatives first.

Ported from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
[`HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`](https://github.com/CBirkbeck/AINTLIB),
declaration `Gamma0_two_sided_coprime_rep_prim`. Two hypotheses the source carries but never
uses — membership of `g` in `Δ₀(N)`, and `c ∣ det A` — are dropped here.

## Main results

* `HeckeRing.GL2.exists_gamma0_mul_mul_coprime_upperLeft`: the two-sided clearing.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-! ### The arithmetic core -/

/-- **Avoiding one prime.** If `p` divides neither the modulus `M` nor all four entries of `A`,
some `l, t` make `A₀₀ + l·A₁₀ + M·t·(A₀₁ + l·A₁₁)` prime to `p`. -/
private lemma entry_clear_prime (A : Matrix (Fin 2) (Fin 2) ℤ) (M : ℤ)
    (p : ℕ) (hp : p.Prime) (hpM : ¬((p : ℤ) ∣ M))
    (hprim : ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)) :
    ∃ l t : ℤ, ¬((p : ℤ) ∣ (A 0 0 + l * A 1 0 + M * t * (A 0 1 + l * A 1 1))) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases ha : (p : ℤ) ∣ A 0 0
  · by_cases hc : (p : ℤ) ∣ A 1 0
    · by_cases hb : (p : ℤ) ∣ A 0 1
      · have hd : ¬((p : ℤ) ∣ A 1 1) := fun hd ↦ hprim ⟨ha, hb, hc, hd⟩
        refine ⟨1, 1, fun h ↦ hd ?_⟩
        have h1 : (p : ℤ) ∣ A 0 0 + A 1 0 + M * A 0 1 :=
          dvd_add (dvd_add ha hc) (dvd_mul_of_dvd_right hb _)
        -- what is left after removing the three divisible summands is `M * A 1 1`
        have hgap : A 0 0 + 1 * A 1 0 + M * 1 * (A 0 1 + 1 * A 1 1) -
            (A 0 0 + A 1 0 + M * A 0 1) = M * A 1 1 := by ring
        have h2 : (p : ℤ) ∣ M * A 1 1 := hgap ▸ dvd_sub h h1
        exact (hp'.dvd_mul.mp h2).resolve_left hpM
      · refine ⟨0, 1, fun h ↦ hb ?_⟩
        have hgap : A 0 0 + 0 * A 1 0 + M * 1 * (A 0 1 + 0 * A 1 1) - A 0 0 = M * A 0 1 := by
          ring
        have h1 : (p : ℤ) ∣ M * A 0 1 := hgap ▸ dvd_sub h ha
        exact (hp'.dvd_mul.mp h1).resolve_left hpM
    · refine ⟨1, 0, fun h ↦ hc ?_⟩
      have hgap : A 0 0 + 1 * A 1 0 + M * 0 * (A 0 1 + 1 * A 1 1) - A 0 0 = A 1 0 := by ring
      exact hgap ▸ dvd_sub h ha
  · -- `l = t = 0` leaves the upper-left entry untouched
    have hgap : A 0 0 + 0 * A 1 0 + M * 0 * (A 0 1 + 0 * A 1 1) = A 0 0 := by ring
    exact ⟨0, 0, by rw [hgap]; exact ha⟩

/-- **Congruence transport.** The entry expression depends on `l` and `t` only modulo `n`:
it is built from them by addition and multiplication, and `Int.ModEq` is a ring congruence. -/
private lemma entry_congr_mod (n l l' t t' a b c d M : ℤ)
    (hl : l ≡ l' [ZMOD n]) (ht : t ≡ t' [ZMOD n]) :
    (a + l * c + M * t * (b + l * d)) ≡ (a + l' * c + M * t' * (b + l' * d)) [ZMOD n] :=
  ((Int.ModEq.refl a).add (hl.mul_right c)).add
    (((Int.ModEq.refl M).mul ht).mul ((Int.ModEq.refl b).add (hl.mul_right d)))

/-- **From `Nat.ModEq` at the reduced representative to `Int.ModEq`.** -/
private lemma intCast_modEq_of_modEq_toNat (m p : ℕ) (x : ℤ) (hp : (p : ℤ) ≠ 0)
    (h : Nat.ModEq p m (x % (p : ℤ)).toNat) : x ≡ (m : ℤ) [ZMOD (p : ℤ)] := by
  refine Int.modEq_iff_dvd.mpr ?_
  obtain ⟨a', ha'⟩ := Nat.modEq_iff_dvd.mp h
  obtain ⟨b', hb'⟩ : (p : ℤ) ∣ ((x % (p : ℤ)).toNat : ℤ) - x := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp)]
    exact ⟨-(x / p), by rw [Int.emod_def]; ring⟩
  exact ⟨-a' + b', by linear_combination -ha' + hb'⟩

/-- **Simultaneous solution across the prime factors.** Any prescription of residues at the
primes dividing `c` is realised by a single natural number, because distinct primes are
coprime. This is the only place the Chinese remainder theorem enters, and the clearing
argument below applies it twice — once for `l`, once for `t`. -/
private lemma exists_modEq_forall_primeFactors (a : ℕ → ℕ) (c : ℕ) :
    ∃ x : ℕ, ∀ p ∈ c.primeFactors, Nat.ModEq p x (a p) := by
  have hpw : (c.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact ((Nat.mem_primeFactors.mp hp).1).coprime_iff_not_dvd.mpr
      (fun h ↦ hpq (((Nat.mem_primeFactors.mp hq).1).eq_one_or_self_of_dvd p h |>.resolve_left
        ((Nat.mem_primeFactors.mp hp).1).one_lt.ne'))
  have hpnz : ∀ p ∈ c.primeFactors, (id p : ℕ) ≠ 0 :=
    fun p hp ↦ ((Nat.mem_primeFactors.mp hp).1).ne_zero
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset a id c.primeFactors hpnz hpw
  exact ⟨x, fun p hp ↦ by simpa using hx p hp⟩

/-- **Coprimality from prime-wise non-divisibility**, in the `ℤ`-against-`ℕ` spelling the
clearing argument produces. The content is `Nat.coprime_of_dvd`; only the coercions are new. -/
private lemma gcd_eq_one_of_forall_prime_not_dvd (x : ℤ) (c : ℕ)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (c : ℤ) → ¬((p : ℤ) ∣ x)) : Int.gcd x c = 1 :=
  Nat.coprime_of_dvd fun p hp hpx hpc ↦
    h p hp (Int.natCast_dvd_natCast.mpr hpc) (Int.natCast_dvd.mpr hpx)

/-- **Avoiding every prime of `c` at once.** The per-prime choices of `entry_clear_prime` are
glued by the Chinese remainder theorem over `c.primeFactors`; `entry_congr_mod` is what makes
the glued `l, t` inherit each local choice. -/
private lemma exists_coprime_entry (A : Matrix (Fin 2) (Fin 2) ℤ) (M : ℤ)
    (c : ℕ) (hc : 0 < c)
    (hprim : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (c : ℤ) → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1))
    (hcM : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (c : ℤ) → ¬((p : ℤ) ∣ M)) :
    ∃ l t : ℤ, Int.gcd (A 0 0 + l * A 1 0 + M * t * (A 0 1 + l * A 1 1)) c = 1 := by
  have havoid : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (c : ℤ) →
      ∃ l t : ℤ, ¬((p : ℤ) ∣ (A 0 0 + l * A 1 0 + M * t * (A 0 1 + l * A 1 1))) :=
    fun p hp hpc ↦ entry_clear_prime A M p hp (hcM p hp hpc)
      (fun ⟨h1, h2, h3, h4⟩ ↦ hprim p hp hpc ⟨h1, h2, h3, h4⟩)
  classical
  set wit : ℕ → ℤ × ℤ := fun p ↦
    if h : p.Prime ∧ (p : ℤ) ∣ (c : ℤ)
    then ⟨(havoid p h.1 h.2).choose, (havoid p h.1 h.2).choose_spec.choose⟩
    else ⟨0, 0⟩
  obtain ⟨l₀, hl₀⟩ := exists_modEq_forall_primeFactors (fun p ↦ ((wit p).1 % (p : ℤ)).toNat) c
  obtain ⟨t₀, ht₀⟩ := exists_modEq_forall_primeFactors (fun p ↦ ((wit p).2 % (p : ℤ)).toNat) c
  refine ⟨(l₀ : ℤ), (t₀ : ℤ), gcd_eq_one_of_forall_prime_not_dvd _ _ fun p hp hpc hpe ↦ ?_⟩
  have hp_mem : p ∈ c.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, Int.natCast_dvd_natCast.mp hpc, by omega⟩
  have hwit : wit p = ⟨(havoid p hp hpc).choose, (havoid p hp hpc).choose_spec.choose⟩ :=
    dite_eq_left_of_eq_true (eq_true ⟨hp, hpc⟩)
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hcongr := (entry_congr_mod (p : ℤ) (wit p).1 (l₀ : ℤ) (wit p).2 (t₀ : ℤ)
    (A 0 0) (A 0 1) (A 1 0) (A 1 1) M
    (intCast_modEq_of_modEq_toNat l₀ p (wit p).1 hp_ne (hl₀ p hp_mem))
    (intCast_modEq_of_modEq_toNat t₀ p (wit p).2 hp_ne (ht₀ p hp_mem))).dvd
  have hwit_fst : (wit p).1 = (havoid p hp hpc).choose := by rw [hwit]
  have hwit_snd : (wit p).2 = (havoid p hp hpc).choose_spec.choose := by rw [hwit]
  rw [hwit_fst, hwit_snd] at hcongr
  apply (havoid p hp hpc).choose_spec.choose_spec
  obtain ⟨k, hk⟩ := hcongr
  obtain ⟨m, hm⟩ := hpe
  exact ⟨m - k, by linear_combination hm - hk⟩

/-- A prime dividing `c` cannot divide `N` when `c` and `N` are coprime. -/
private lemma not_intCast_dvd_of_coprime (c p : ℕ) (hp : p.Prime)
    (hc : Nat.Coprime c N) (hpc : (p : ℤ) ∣ (c : ℤ)) : ¬((p : ℤ) ∣ (N : ℤ)) := by
  intro hpN
  have h1 := (hc.coprime_dvd_right (Int.natCast_dvd_natCast.mp hpN)).coprime_dvd_left
    (Int.natCast_dvd_natCast.mp hpc)
  rw [Nat.Coprime, Nat.gcd_self] at h1
  exact absurd h1 hp.one_lt.ne'

/-! ### The clearing lemma -/

/-- The two entries of a two-sided unipotent translate that the `Δ₀(N)` conditions read: the
upper-left one, carrying the coprimality, and the lower-left one, carrying the divisibility. -/
private lemma unipotent_translate_entries (A : Matrix (Fin 2) (Fin 2) ℤ) (l m : ℤ) :
    (Matrix.of ![![1, l], ![0, 1]] * A * Matrix.of ![![1, 0], ![m, 1]]) 0 0 =
        A 0 0 + l * A 1 0 + (A 0 1 + l * A 1 1) * m ∧
      (Matrix.of ![![1, l], ![0, 1]] * A * Matrix.of ![![1, 0], ![m, 1]]) 1 0 =
        A 1 0 + A 1 1 * m := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- **Two-sided `Γ₀(N)` clearing.** Let `c` be positive and coprime to `N`, and let `A` be an
integral representative of `g` with `N ∣ A₁₀` and `gcd(A₀₀, N) = 1` which no prime dividing `c`
divides entrywise. Then there are `γL, γR ∈ Γ₀(N)` whose two-sided translate `γL · g · γR` has
an integral representative `A'` with the same two properties — `N ∣ A'₁₀` and
`gcd(A'₀₀, N) = 1` — and in addition `gcd(A'₀₀, c) = 1`.

Primitivity is only assumed at primes dividing `c`, which is all the local-to-global argument
consumes; a globally primitive `A` satisfies it a fortiori. -/
theorem exists_gamma0_mul_mul_coprime_upperLeft
    (g : GL (Fin 2) ℚ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0) (hAco : Int.gcd (A 0 0) N = 1)
    (c : ℕ) (hc : 0 < c) (hcN : Nat.Coprime c N)
    (hprim : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (c : ℤ) → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧
      (p : ℤ) ∣ A 1 0 ∧ (p : ℤ) ∣ A 1 1)) :
    ∃ γL γR : ((Gamma0 N).map (mapGL ℚ)),
      ∃ A' : Matrix (Fin 2) (Fin 2) ℤ,
        (((γL : GL (Fin 2) ℚ) * g * (γR : GL (Fin 2) ℚ) : GL (Fin 2) ℚ) :
            Matrix (Fin 2) (Fin 2) ℚ) = A'.map (Int.cast : ℤ → ℚ) ∧
          (N : ℤ) ∣ A' 1 0 ∧ Int.gcd (A' 0 0) N = 1 ∧ Int.gcd (A' 0 0) c = 1 := by
  obtain ⟨l₀, t₀, hlt⟩ := exists_coprime_entry A (N : ℤ) c hc hprim
    (fun p hp hpc ↦ not_intCast_dvd_of_coprime N c p hp hcN hpc)
  set L : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, l₀], ![0, 1]] with hL
  have hL_det : L.det = 1 := by
    simp [hL, Matrix.det_fin_two]
  set R : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, 0], ![(N : ℤ) * t₀, 1]] with hR
  have hR_det : R.det = 1 := by
    simp [hR, Matrix.det_fin_two]
  have hL_Gamma0 : (⟨L, hL_det⟩ : SpecialLinearGroup (Fin 2) ℤ) ∈ Gamma0 N :=
    Gamma0_mem.mpr (by simp [hL])
  have hR_Gamma0 : (⟨R, hR_det⟩ : SpecialLinearGroup (Fin 2) ℤ) ∈ Gamma0 N :=
    Gamma0_mem.mpr (by simp [hR])
  obtain ⟨h00, h10⟩ := unipotent_translate_entries A l₀ ((N : ℤ) * t₀)
  rw [← hL, ← hR] at h00 h10
  refine ⟨⟨mapGL ℚ ⟨L, hL_det⟩, Subgroup.mem_map_of_mem _ hL_Gamma0⟩,
    ⟨mapGL ℚ ⟨R, hR_det⟩, Subgroup.mem_map_of_mem _ hR_Gamma0⟩, L * A * R, ?_, ?_, ?_, ?_⟩
  · exact mapGL_mul_coe_eq_intMatrix 2 ⟨L, hL_det⟩ ⟨R, hR_det⟩ g A hA
  · -- the translate adds a multiple of `N` to the lower-left entry
    have hlow : A 1 0 + A 1 1 * ((N : ℤ) * t₀) = A 1 0 + (N : ℤ) * (A 1 1 * t₀) := by ring
    rw [h10, hlow]
    exact dvd_add hAN (dvd_mul_right _ _)
  · obtain ⟨k, hk⟩ := hAN
    -- collecting the `N` lets `Int.gcd_add_mul_left_left` discard the whole correction
    have hup : A 0 0 + l₀ * ((N : ℤ) * k) + (A 0 1 + l₀ * A 1 1) * ((N : ℤ) * t₀) =
        A 0 0 + (N : ℤ) * (l₀ * k + (A 0 1 + l₀ * A 1 1) * t₀) := by ring
    rw [h00, hk, hup, Int.gcd_add_mul_left_left]
    exact hAco
  · -- the same entry, written in the shape `entry_clear_prime` produced it
    have hshape : A 0 0 + l₀ * A 1 0 + (A 0 1 + l₀ * A 1 1) * ((N : ℤ) * t₀) =
        A 0 0 + l₀ * A 1 0 + (N : ℤ) * t₀ * (A 0 1 + l₀ * A 1 1) := by ring
    rw [h00, hshape]
    exact hlt

end HeckeRing.GL2
