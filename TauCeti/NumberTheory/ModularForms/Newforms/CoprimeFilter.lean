/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Nat.Squarefree
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.LevelSupported

/-!
# The coprime-index filter on `S_k(Γ₁(N), χ)`

Miyake's Lemma 4.6.5: a cusp form `f ∈ S_k(Γ₁(N), χ)` can be *filtered* at a divisor of the
level. For a nonzero `L` all of whose primes already divide `N`, there is a cusp form `g` at a
raised level, again with nebentypus `χ` read there, whose `q`-expansion keeps exactly the
coefficients at indices coprime to `L`:

`aₙ(g) = aₙ(f)` when `(n, L) = 1`, and `aₙ(g) = 0` otherwise.

Only the *primes* of `L` do any filtering, so the level `g` lives at is `∏ L.primeFactors`
times `N`. For squarefree `L` that product is `L` itself, which is the level `L * N` at which
Miyake states the lemma.

## Main results

* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`: the filter, for an
  arbitrary nonzero `L`, at level `∏ L.primeFactors * N`.
* `TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_squarefree`:
  Miyake's Lemma 4.6.5 as stated, at level `L * N`.

## Implementation notes

The construction is one prime at a time. At a single `p` the witness is `f - V_p (T_p f)`, read
at level `p * N`; the `q`-expansion identities `TauCeti.CuspForm.qExpansion_levelRaise_coeff_Gamma1`
and `HeckeRing.GL2.qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset` make the two
contributions cancel at exactly the indices divisible by `p`. Neither of those needs `p` to be
prime, only that its prime factors already divide the level, so the single-`p` step is stated
at that generality; primality is used only to compose the filters, where
`Nat.Coprime n (q * m)` has to split as `¬ q ∣ n` and `Nat.Coprime n m`.

Iterating over `L.primeFactors` raises the level by one prime per step, so the induction is on
the number of primes left to peel and the level it lands at is existentially quantified, with
the equation `M' = ∏ S * M` recorded alongside. That keeps the recursion free of any transport
along an equality of levels: the caller substitutes the equation once, at a concrete level.

## Provenance

Adapted from AINTLIB's `StrongMultiplicityOne/LevelChangeCharSpace.lean` (see References): the
declarations `miyake_4_6_5_single_prime_dvd_N` and `miyake_4_6_5_iterated_L` with their two
`q`-expansion and `ite`-composition helpers. Deliberate differences from the source: the
source's `hp : p.Prime` is dropped from the single-`p` step and from the `q`-expansion
cancellation, neither proof using it; the `Squarefree (∏ S)` hypothesis the source threads
through the recursion only to feed itself disappears once the conclusion is stated at the level
`∏ S * M`; and the nonzero-`L` statement is exposed here, the source stating only the
squarefree form at this stage (its `_general` variant generalizes the target level, not `L`).

`coprime_prod_primeFactors_iff` is AINTLIB's `coprime_prod_primeFactors_iff_coprime`, which
lives one file up in `StrongMultiplicityOne.lean`. It is restated here for an arbitrary nonzero
`L` rather than for the ambient level, and proved from `Nat.dvd_prod_primeFactors_pow_self`
instead of by contradiction on a common prime divisor.

## References

* [Miyake, *Modular forms*][miyake1989], Lemma 4.6.5.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, files
  `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/LevelChangeCharSpace.lean`
  and `projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne.lean`.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

open HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The `q`-expansion of `f - V_p (T_p f)`.** Read at level `p * N`, the level-raise of
`T_p f` reproduces exactly the coefficients of `f` at the indices divisible by `p`, so the
difference is `f` with those indices deleted. Primality of `p` is not needed: what makes
`T_p` act by `aₘ(T_p f) = a_{p m}(f)` is that `p`'s prime factors already divide `N`. -/
private theorem qExpansion_coeff_ofLe_sub_levelRaise_heckeTCuspNat {p : ℕ} [NeZero p]
    (hpN : p.primeFactors ⊆ N.primeFactors) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
          CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p)
            (heckeTCuspNat (N := N) k p f))).coeff n =
      if p ∣ n then 0 else (qExpansion 1 f).coeff n := by
  rw [_root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
    CuspForm.qExpansion_levelRaise_coeff_Gamma1 N _ n,
    qExpansion_coeff_heckeTCuspNat_of_primeFactors_subset k p hpN f (n / p),
    CuspForm.coe_ofLe]
  by_cases hpn : p ∣ n <;> simp [hpn, Nat.mul_div_cancel']

/-- **Composing a coprimality filter with a prime one.** Deleting the indices divisible by a
prime `q` from the indices coprime to `m` leaves exactly the indices coprime to `q * m`. -/
private theorem ite_coprime_ite_dvd_eq_ite_coprime_mul {α : Type*} [Zero α] {q : ℕ}
    (hq : q.Prime) (n m : ℕ) (a : α) :
    (if Nat.Coprime n m then (if q ∣ n then 0 else a) else 0) =
      if Nat.Coprime n (q * m) then a else 0 := by
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_comm, hq.coprime_iff_not_dvd, ite_and]
  split_ifs <;> rfl

/-- **Coprimality only sees the primes.** For nonzero `L`, an `n` is coprime to `L` exactly
when it is coprime to the product of `L`'s prime factors. -/
private theorem coprime_prod_primeFactors_iff {n L : ℕ} (hL : L ≠ 0) :
    Nat.Coprime n (L.primeFactors.prod id) ↔ Nat.Coprime n L :=
  ⟨fun h ↦ (h.pow_right L).coprime_dvd_right (Nat.dvd_prod_primeFactors_pow_self hL),
    fun h ↦ h.coprime_dvd_right (Nat.prod_primeFactors_dvd L)⟩

/-- **The filter at a single level-supported `p`.** From `f ∈ S_k(Γ₁(N), χ)` and a nonzero `p`
whose prime factors all divide `N`, the form `f - V_p (T_p f)` lies in `S_k(Γ₁(p * N), χ)` and
carries the coefficients of `f` at the indices *not* divisible by `p`, the rest deleted. `p`
need be neither prime nor a prime power; only its prime support is constrained. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {p : ℕ} [NeZero p]
    (hpN : p.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if p ∣ n then 0 else (qExpansion 1 f).coeff n :=
  ⟨CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
      CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p) (heckeTCuspNat (N := N) k p f),
    Submodule.sub_mem _ (CuspForm.ofLe_mem_cuspFormCharSpace χ _ hf)
      (CuspForm.levelRaise_mem_cuspFormCharSpace N p χ
        (heckeTCuspNat_mem_cuspFormCharSpace_of_primeFactors_subset k χ p hpN hf)),
    qExpansion_coeff_ofLe_sub_levelRaise_heckeTCuspNat hpN f⟩

/-- The iterated filter, by induction on the number of primes still to be peeled off. The level
it lands at is existentially quantified together with the equation naming it, so that no step of
the recursion has to transport a cusp form along an equality of levels. -/
private theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_prod (m : ℕ) :
    ∀ {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
      {g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}, g ∈ cuspFormCharSpace k χ →
      ∀ S : Finset ℕ, S ⊆ M.primeFactors → S.card = m → ∃ (M' : ℕ) (hMM' : M ∣ M'),
        M' = S.prod id * M ∧ ∃ g' : CuspForm ((Gamma1 M').map (mapGL ℝ)) k,
          g' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hMM')) ∧
          ∀ n, (qExpansion 1 g').coeff n =
            if Nat.Coprime n (S.prod id) then (qExpansion 1 g).coeff n else 0 := by
  induction m with
  | zero =>
    intro M _ k χ g hg S _ hScard
    obtain rfl := Finset.card_eq_zero.mp hScard
    exact ⟨M, dvd_rfl, by simp, g, by simpa [ZMod.unitsMap_self] using hg,
      fun _ ↦ by simp [Nat.Coprime]⟩
  | succ m ih =>
    intro M _ k χ g hg S hS hScard
    obtain ⟨q, hqS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hqM : q ∈ M.primeFactors := hS hqS
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqM
    have : NeZero q := ⟨hq.ne_zero⟩
    have hMqM : M ∣ q * M := Nat.dvd_mul_left M q
    have : NeZero (q * M) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M)⟩
    obtain ⟨g₁, hg₁, hg₁q⟩ :=
      exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd χ hg
        (Nat.primeFactors_mono (Nat.dvd_of_mem_primeFactors hqM) (NeZero.ne M))
    have hprod : S.prod id = q * (S.erase q).prod id := (Finset.mul_prod_erase _ _ hqS).symm
    obtain ⟨M', hM'dvd, hM'eq, g', hg', hg'q⟩ :=
      ih _ hg₁ (S.erase q)
        (fun _ hr ↦ Nat.primeFactors_mono hMqM (NeZero.ne _) (hS (Finset.mem_of_mem_erase hr)))
        (by rw [Finset.card_erase_of_mem hqS, hScard]; omega)
    refine ⟨M', hMqM.trans hM'dvd, by rw [hM'eq, hprod]; ring, g', ?_, fun n ↦ ?_⟩
    · simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hg'
    · rw [hg'q n, hg₁q n, hprod]
      exact ite_coprime_ite_dvd_eq_ite_coprime_mul hq n _ _

/-- **The coprime-index filter.** For `f ∈ S_k(Γ₁(N), χ)` and a nonzero `L` whose primes all
divide `N`, there is a cusp form `g` of level `∏ L.primeFactors * N`, with the nebentypus `χ`
read at that level, whose `q`-expansion is that of `f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

Only the primes of `L` matter, both to the filter and to the level: `Nat.Coprime n L` depends
only on `L`'s prime support, and the construction peels off one prime of `L` at a time. The
squarefree case, where the level is `L * N`, is
`exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_squarefree`. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ}
    [NeZero L] (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (L.primeFactors.prod id * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k
        (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N (L.primeFactors.prod id)))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  obtain ⟨M', hM'dvd, hM'eq, g, hg, hgq⟩ :=
    exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_prod L.primeFactors.card χ hf
      L.primeFactors hLN rfl
  subst hM'eq
  exact ⟨g, hg, fun n ↦ by simp only [hgq n, coprime_prod_primeFactors_iff (NeZero.ne L)]⟩

/-- **Miyake's Lemma 4.6.5, the coprime-index filter at squarefree `L`.** For
`f ∈ S_k(Γ₁(N), χ)` and a squarefree `L` whose primes all divide `N`, there is a cusp form `g`
of level `L * N`, with the nebentypus `χ` read at that level, whose `q`-expansion is that of
`f` restricted to the indices coprime to `L`:

`aₙ(g) = if (n, L) = 1 then aₙ(f) else 0`.

This is `exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime` at a squarefree `L`,
where `∏ L.primeFactors` is `L` itself. -/
theorem exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_of_squarefree
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) {L : ℕ} (hL : Squarefree L)
    (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : CuspForm ((Gamma1 (L * N)).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N L))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  have : NeZero L := ⟨hL.ne_zero⟩
  have hprod : L.primeFactors.prod id = L := by
    simpa using Nat.prod_primeFactors_of_squarefree hL
  have key := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime χ hf hLN
  rwa [hprod] at key

end TauCeti
