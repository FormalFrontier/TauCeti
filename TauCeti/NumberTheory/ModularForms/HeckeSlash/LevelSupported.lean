/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The Hecke operators at an index supported on the level

Call a positive integer `n` *supported on the level* `N` when every prime factor of `n` divides
`N`, that is `n.primeFactors ⊆ N.primeFactors`. These are the indices at which the decomposition
of `HeckeRing/GL2/Gamma1/UpperTriCosets.lean` writes the double coset
`Γ₁(N) · diag(1, n) · Γ₁(N)` as `n` upper-triangular right cosets
`Γ₁(N) · !![1, b; 0, n]` — no further coset appears, as it does at a prime `p ∤ N`. The prime
powers `p ^ r` with `p ∣ N` are supported on the level whether or not they divide it, and they
are the reason this regime is worth naming: `p ∣ N` alone does not reach `T_{p²}`.

Consequently `T_n` is the plain upper-triangular sum there, and — this is the point — these
operators **multiply**: composing the `m`-term and the `n`-term sums enumerates the `(n·m)`-term
sum exactly once each, so

`T_n T_m = T_{n m}`  for `n` and `m` supported on the level,

with **`T_{p^r} = T_p ^ r` at `p ∣ N`** as the special case the ModularForms roadmap names. In
the vocabulary of modern papers the operator at `p ∣ N` is `U_p`
(`heckeUNat`, an alias of `T_p` by `heckeUNat_eq_heckeTNat`), so the same statement reads
`T_{p^r} = U_p ^ r`; no second operator is introduced.

⚠ This does not supply multiplicativity for arbitrary coprime indices: it applies when each
index is supported on the level, whether or not the two indices are coprime. An index with a
prime factor outside the level needs the whole coset decomposition of
`Gamma1/CoprimeCosets.lean`. In the level-supported case the identity degenerates the
prime-power recurrence
`T_{p^{r+2}} = T_p T_{p^{r+1}} − p^{k−1}⟨p⟩ T_{p^r}` to `T_{p^r} = T_p ^ r`, the zero-extended
diamond `⟨p⟩` vanishing at `p ∣ N`.

Two consequences are recorded alongside: `T_n` preserves each nebentypus space `M_k(N, χ)` and
`S_k(N, χ)` there, and its effect on `q`-expansions is `aₘ(T_n f) = a_{n m}(f)`, proved from
the function-level recurrence in `UpperTri/QExpansion.lean`.

## Main results

* `HeckeRing.GL2.coe_heckeTNat_of_primeFactors_subset` and
  `HeckeRing.GL2.coe_heckeTCuspNat_of_primeFactors_subset`: at an index supported on the level,
  `T_n` is the upper-triangular sum.
* `HeckeRing.GL2.heckeTNat_mul_of_primeFactors_subset` and its cusp-form counterpart:
  `T_{n m} = T_n ∘ T_m` for two indices supported on the level, with
  `HeckeRing.GL2.commute_heckeTNat_of_primeFactors_subset` recording that such operators
  commute.
* `HeckeRing.GL2.heckeTNat_pow_of_primeFactors_subset`: `T_{n^r} = T_n ^ r` at every
  level-supported index, with its cusp-form counterpart.
* `HeckeRing.GL2.heckeTNat_pow_of_dvd`: **`T_{p^r} = T_p ^ r` at `p ∣ N`**, with its
  cusp-form counterpart.
* `HeckeRing.GL2.heckeTNat_mem_modFormCharSpace_of_primeFactors_subset` with its
  cusp-form counterpart: the operator preserves `M_k(N, χ)` and `S_k(N, χ)`.
* `HeckeRing.GL2.qExpansion_coeff_heckeTNat_of_primeFactors_subset` and its cusp-form
  counterpart: `aₘ(T_n f) = a_{n m}(f)`.

## Provenance

No code is transcribed. The prime-power statement is the ModularForms roadmap's Layer 2(b)
milestone, carried in the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0) as
`heckeT_ppow_eq_pow_of_not_coprime` (`LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`);
there it is a statement about a family of operators assembled prime by prime, while here it
falls out of the composition law for the coset representatives, which holds at every pair of
level-supported indices and not only at powers of one prime.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Propositions 5.2.1--5.2.2 and equations (5.3)--(5.4).
* T. Miyake, *Modular forms*, §4.5, Lemma 4.5.7.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] (k : ℤ)

/-- **At an index supported on the level, `T_n` is the upper-triangular sum**
`∑_{b < n} f ∣[k] !![1, b; 0, n]`. This is the normalisation lemma of
`UpperTri/DoubleCoset.lean` at every such index, not only at the divisors of `N`. -/
theorem coe_heckeTNat_of_primeFactors_subset (n : ℕ) [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeTNat (N := N) k n f) = heckeSlashUpperTri k n ⇑f := by
  rw [coe_heckeTNat]
  exact heckeSlashSum_diagCosetGamma1 k (Nat.pos_of_ne_zero (NeZero.ne n)) hn f

/-- **At an index supported on the level, the cusp-form `T_n` is the upper-triangular sum.** -/
theorem coe_heckeTCuspNat_of_primeFactors_subset (n : ℕ) [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(heckeTCuspNat (N := N) k n f) = heckeSlashUpperTri k n ⇑f := by
  rw [coe_heckeTCuspNat]
  exact heckeSlashSum_diagCosetGamma1 k (Nat.pos_of_ne_zero (NeZero.ne n)) hn f

omit [NeZero N] in
/-- A product of two indices supported on the level is supported on the level. -/
private lemma primeFactors_mul_subset {n m : ℕ} [NeZero n] [NeZero m]
    (hn : n.primeFactors ⊆ N.primeFactors) (hm : m.primeFactors ⊆ N.primeFactors) :
    (n * m).primeFactors ⊆ N.primeFactors := by
  rw [Nat.primeFactors_mul (NeZero.ne n) (NeZero.ne m)]
  exact Finset.union_subset hn hm

/-- **The Hecke operators at indices supported on the level multiply**: `T_{n m} = T_n ∘ T_m`
on `M_k(Γ₁(N))`.

Both sides are upper-triangular sums, and `upperTriRep_mul_upperTriRep` matches the pairs of
representatives with the representatives at index `n · m` bijectively. Nothing here is a
coprimality statement: each of `n` and `m` is supported on the level, and the identity holds
whether or not they are coprime (in particular, for `n = m`). -/
theorem heckeTNat_mul_of_primeFactors_subset {n m : ℕ} [NeZero n] [NeZero m]
    (hn : n.primeFactors ⊆ N.primeFactors) (hm : m.primeFactors ⊆ N.primeFactors) :
    heckeTNat (N := N) k (n * m) = heckeTNat (N := N) k n * heckeTNat (N := N) k m :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeTNat_of_primeFactors_subset k _ (primeFactors_mul_subset hn hm),
      Module.End.mul_apply, coe_heckeTNat_of_primeFactors_subset k n hn,
      coe_heckeTNat_of_primeFactors_subset k m hm, heckeSlashUpperTri_heckeSlashUpperTri,
      mul_comm m n]

/-- **The cusp-form Hecke operators at indices supported on the level multiply**:
`T_{n m} = T_n ∘ T_m` on `S_k(Γ₁(N))`. -/
theorem heckeTCuspNat_mul_of_primeFactors_subset {n m : ℕ} [NeZero n] [NeZero m]
    (hn : n.primeFactors ⊆ N.primeFactors) (hm : m.primeFactors ⊆ N.primeFactors) :
    heckeTCuspNat (N := N) k (n * m) = heckeTCuspNat (N := N) k n * heckeTCuspNat (N := N) k m :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeTCuspNat_of_primeFactors_subset k _ (primeFactors_mul_subset hn hm),
      Module.End.mul_apply, coe_heckeTCuspNat_of_primeFactors_subset k n hn,
      coe_heckeTCuspNat_of_primeFactors_subset k m hm, heckeSlashUpperTri_heckeSlashUpperTri,
      mul_comm m n]

/-- **The Hecke operators at indices supported on the level commute.** Both orders compute the
operator at the product index, and the product of indices is commutative. This is the
commuting family the simultaneous-diagonalisation arguments consume at the bad primes. -/
theorem commute_heckeTNat_of_primeFactors_subset {n m : ℕ} [NeZero n] [NeZero m]
    (hn : n.primeFactors ⊆ N.primeFactors) (hm : m.primeFactors ⊆ N.primeFactors) :
    Commute (heckeTNat (N := N) k n) (heckeTNat (N := N) k m) := by
  rw [commute_iff_eq, ← heckeTNat_mul_of_primeFactors_subset k hn hm,
    ← heckeTNat_mul_of_primeFactors_subset k hm hn]
  exact heckeTNat_congr k (mul_comm n m)

/-- **The cusp-form Hecke operators at indices supported on the level commute.** -/
theorem commute_heckeTCuspNat_of_primeFactors_subset {n m : ℕ} [NeZero n] [NeZero m]
    (hn : n.primeFactors ⊆ N.primeFactors) (hm : m.primeFactors ⊆ N.primeFactors) :
    Commute (heckeTCuspNat (N := N) k n) (heckeTCuspNat (N := N) k m) := by
  rw [commute_iff_eq, ← heckeTCuspNat_mul_of_primeFactors_subset k hn hm,
    ← heckeTCuspNat_mul_of_primeFactors_subset k hm hn]
  exact heckeTCuspNat_congr k (mul_comm n m)

omit [NeZero N] in
/-- A power of an index supported on the level is supported on the level. -/
private lemma primeFactors_pow_subset {n : ℕ} (hn : n.primeFactors ⊆ N.primeFactors) (r : ℕ) :
    (n ^ r).primeFactors ⊆ N.primeFactors := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · rw [Nat.primeFactors_pow n hr.ne']
    exact hn

/-- **`T_{n^r} = T_n ^ r` at an index supported on the level.** -/
theorem heckeTNat_pow_of_primeFactors_subset {n : ℕ} [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors) (r : ℕ) :
    heckeTNat (N := N) k (n ^ r) = heckeTNat (N := N) k n ^ r := by
  induction r with
  | zero => rw [heckeTNat_congr k (pow_zero n), heckeTNat_one, pow_zero]
  | succ r ih =>
      rw [heckeTNat_congr k (pow_succ n r),
        heckeTNat_mul_of_primeFactors_subset k (primeFactors_pow_subset hn r) hn, ih, pow_succ]

/-- **`T_{n^r} = T_n ^ r` on cusp forms, at an index supported on the level.** -/
theorem heckeTCuspNat_pow_of_primeFactors_subset {n : ℕ} [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors) (r : ℕ) :
    heckeTCuspNat (N := N) k (n ^ r) = heckeTCuspNat (N := N) k n ^ r := by
  induction r with
  | zero => rw [heckeTCuspNat_congr k (pow_zero n), heckeTCuspNat_one, pow_zero]
  | succ r ih =>
      rw [heckeTCuspNat_congr k (pow_succ n r),
        heckeTCuspNat_mul_of_primeFactors_subset k (primeFactors_pow_subset hn r) hn, ih,
        pow_succ]

/-- **`T_{p^r} = T_p ^ r` at a divisor `p ∣ N`**, on `M_k(Γ₁(N))`.

The roadmap's prime case is the degenerate case of the prime-power recurrence
`T_{p^{r+2}} = T_p T_{p^{r+1}} − p^{k−1} ⟨p⟩ T_{p^r}`: the zero-extended diamond `⟨p⟩` vanishes
at a prime `p ∣ N`, leaving `T_{p^{r+1}} = T_p T_{p^r}`. In that case, read through
`heckeUNat_eq_heckeTNat`, the statement is `T_{p^r} = U_p ^ r`; there is no second operator. -/
theorem heckeTNat_pow_of_dvd (hpN : p ∣ N) (r : ℕ) :
    heckeTNat (N := N) k (p ^ r)
        (_hn := haveI := NeZero.of_dvd hpN; NeZero.pow)
      = heckeTNat (N := N) k p
          (_hn := NeZero.of_dvd hpN) ^ r :=
  let _ : NeZero p := NeZero.of_dvd hpN
  heckeTNat_pow_of_primeFactors_subset k (Nat.primeFactors_mono hpN (NeZero.ne N)) r

/-- **`T_{p^r} = T_p ^ r` at a divisor `p ∣ N`**, on `S_k(Γ₁(N))`. -/
theorem heckeTCuspNat_pow_of_dvd (hpN : p ∣ N) (r : ℕ) :
    heckeTCuspNat (N := N) k (p ^ r)
        (_hn := haveI := NeZero.of_dvd hpN; NeZero.pow)
      = heckeTCuspNat (N := N) k p
          (_hn := NeZero.of_dvd hpN) ^ r :=
  let _ : NeZero p := NeZero.of_dvd hpN
  heckeTCuspNat_pow_of_primeFactors_subset k (Nat.primeFactors_mono hpN (NeZero.ne N)) r

section Nebentypus

variable (χ : (ZMod N)ˣ →* ℂˣ)

/-- **`T_n` preserves the nebentypus at every index supported on the level**: it maps
`M_k(N, χ)` into itself. Not an assumption but a theorem, as the ModularForms roadmap asks of
the Hecke action. -/
theorem heckeTNat_mem_modFormCharSpace_of_primeFactors_subset (n : ℕ) [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeTNat (N := N) k n f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [coe_heckeTNat_of_primeFactors_subset k n hn, ← ModularForm.rat_slash_mapGL]
  exact heckeSlashUpperTri_slash_mapGL_of_nebentypus_of_primeFactors_subset k χ n
    (NeZero.ne n) hn g fun δ ↦ by rw [ModularForm.rat_slash_mapGL]; exact hf δ

/-- **`T_n` preserves the nebentypus on cusp forms**: it maps `S_k(N, χ)` into itself, at every
index supported on the level. -/
theorem heckeTCuspNat_mem_cuspFormCharSpace_of_primeFactors_subset (n : ℕ) [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeTCuspNat (N := N) k n f ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  rw [coe_heckeTCuspNat_of_primeFactors_subset k n hn, ← ModularForm.rat_slash_mapGL]
  exact heckeSlashUpperTri_slash_mapGL_of_nebentypus_of_primeFactors_subset k χ n
    (NeZero.ne n) hn g fun δ ↦ by rw [ModularForm.rat_slash_mapGL]; exact hf δ

end Nebentypus

/-- **The `q`-expansion recurrence at an index supported on the level**:
`aₘ(T_n f) = a_{n m}(f)`. When `f` lies in a nebentypus-`χ` space, at a prime `p ∣ N`
this is the Diamond–Shurman recurrence
`aₘ(Tₚ f) = a_{m p}(f) + χ(p) p^{k-1} a_{m/p}(f)` with its second term killed by `χ(p) = 0`;
at `n = p ^ r` it is the `r`-fold iterate of that. -/
theorem qExpansion_coeff_heckeTNat_of_primeFactors_subset (n : ℕ) [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeTNat (N := N) k n f)).coeff m = (qExpansion 1 f).coeff (n * m) := by
  rw [coe_heckeTNat_of_primeFactors_subset k n hn f]
  exact qExpansion_coeff_heckeSlashUpperTri' k n
    (TauCeti.one_mem_strictPeriods_Gamma1_map _) (Nat.pos_of_ne_zero (NeZero.ne n)) f m

/-- **The `q`-expansion recurrence on cusp forms**: `aₘ(T_n f) = a_{n m}(f)` at an index
supported on the level. -/
theorem qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset (n : ℕ) [NeZero n]
    (hn : n.primeFactors ⊆ N.primeFactors)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion 1 (heckeTCuspNat (N := N) k n f)).coeff m = (qExpansion 1 f).coeff (n * m) := by
  rw [coe_heckeTCuspNat_of_primeFactors_subset k n hn f]
  exact qExpansion_coeff_heckeSlashUpperTri' k n
    (TauCeti.one_mem_strictPeriods_Gamma1_map _) (Nat.pos_of_ne_zero (NeZero.ne n)) f m

end HeckeRing.GL2

end
