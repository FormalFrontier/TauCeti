/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
public import TauCeti.NumberTheory.NumberField.SplitsCompletely
import TauCeti.RingTheory.Ideal.LiesOver
import TauCeti.NumberTheory.NumberField.IntegralSqrt

/-!
# The prime-splitting law for a multiquadratic field

For a multiquadratic number field `K = ℚ(√d₁, …, √dₙ)` and an odd prime `p` dividing none of the
radicands, `p` splits completely in `K` if and only if every `dᵢ` is a quadratic residue mod `p`.

This is the general (compositum) case; the base case `n = 1` is `ncard_primesOver_quadratic_iff`.

## Main results

* `TauCeti.NumberField.ncard_primesOver_multiquadratic_iff`: the multiquadratic prime-splitting
  law — `p` splits completely in `K = ℚ(√d₁, …, √dₙ)` iff every `dᵢ` is a quadratic residue
  mod `p`.
-/

open Polynomial NumberField Ideal Module MulAction
open scoped Pointwise

namespace TauCeti.NumberField

public section

variable {K : Type*} [Field K] [NumberField K]

/-- Forward direction (pointwise): for `K` Galois over `ℚ`, if `p` splits completely
(`#{primes over p} = [K : ℚ]`) and `p ∤ d i`, then `d i` is a quadratic residue mod `p`. -/
private theorem legendreSym_eq_one_of_ncard_primesOver_eq_finrank {ι : Type*} (d : ι → ℤ)
    (r : ι → K) (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i)) [IsGalois ℚ K]
    {p : ℕ} [Fact p.Prime] {i : ι} (hcop_i : ¬ (p : ℤ) ∣ d i)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (hsplit : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K) :
    legendreSym p (d i) = 1 := by
  -- Complete splitting forces residue degree `1`, so `𝓞 K ⧸ Q` is the prime field `ℤ ⧸ (p)`;
  -- lifting the residue of `r i` to an integer `a` gives `a² ≡ d i (mod p)`.
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp Fact.out))
      (by simpa [Ideal.span_singleton_eq_bot] using hpne)
  haveI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (span {(p : ℤ)})
  let R : 𝓞 K := integralSqrt (hr i)
  rw [ncard_primesOver_eq_finrank_iff K p] at hsplit
  have hfQ : finrank (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q) = 1 := by
    rw [← Ideal.inertiaDeg'_algebraMap (p := span {(p : ℤ)}) (P := Q),
      Ideal.inertiaDeg'_eq_inertiaDeg,
      ← Ideal.inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) Q (K ≃ₐ[ℚ] K)]
    exact hsplit.2
  letI fld : Field (ℤ ⧸ span {(p : ℤ)}) := Ideal.Quotient.field _
  -- A one-dimensional algebra over a field is free, so `finrank = 1 ⟹ algebraMap` is bijective.
  haveI : Module.Free (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q) :=
    @Module.Free.of_divisionRing _ _ fld.toDivisionRing _ _
  have hbij := (Algebra.finrank_eq_one_iff_bijective_algebraMap
    (F := ℤ ⧸ span {(p : ℤ)}) (E := 𝓞 K ⧸ Q)).mp hfQ
  -- Lift the residue of `R` to an integer `a`, so `R ≡ a (mod Q)`.
  obtain ⟨c, hc⟩ := hbij.surjective (Ideal.Quotient.mk Q R)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  -- The algebra map `ℤ ⧸ (p) → 𝓞 K ⧸ Q` is `Ideal.quotientMap`, which sends `mk a` to
  -- `mk (algebraMap ℤ (𝓞 K) a)`.
  have hcompat : algebraMap (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q) (Ideal.Quotient.mk _ a)
      = Ideal.Quotient.mk Q (algebraMap ℤ (𝓞 K) a) := Ideal.quotientMap_mk
  rw [hcompat] at hc
  have hdiff : algebraMap ℤ (𝓞 K) a - R ∈ Q := Ideal.Quotient.eq.mp hc
  -- `(algebraMap a - R)(algebraMap a + R) = algebraMap (a² - d i) ∈ Q`, so `p ∣ a² - d i`.
  have hpd : (p : ℤ) ∣ a ^ 2 - d i := by
    rw [← algebraMap_int_mem_iff_dvd_of_liesOver Q]
    have hfac : algebraMap ℤ (𝓞 K) (a ^ 2 - d i) =
        (algebraMap ℤ (𝓞 K) a - R) * (algebraMap ℤ (𝓞 K) a + R) := by
      rw [map_sub, map_pow, ← integralSqrt_sq (hr i)]; ring
    rw [hfac]
    exact Ideal.mul_mem_right _ _ hdiff
  rw [legendreSym.eq_one_iff p (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop_i)]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hpd
  push_cast at hpd
  exact ⟨(a : ZMod p), by linear_combination -hpd⟩

/-- A nonzero quadratic residue `d` mod a prime `p` (`legendreSym p d = 1`, `p ∤ d`) has an integer
square root modulo `p`: some `a` with `p ∣ a² - d` and `p ∤ a`. -/
private theorem exists_dvd_sq_sub_and_not_dvd_of_legendreSym_eq_one (p : ℕ) [Fact p.Prime]
    {d : ℤ} (hqr : legendreSym p d = 1) :
    ∃ a : ℤ, (p : ℤ) ∣ a ^ 2 - d ∧ ¬ (p : ℤ) ∣ a := by
  -- `legendreSym p d = 1 ≠ 0`, and `legendreSym p d = 0 ↔ p ∣ d`, so `p ∤ d`.
  have hcop : ¬ (p : ℤ) ∣ d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← legendreSym.eq_zero_iff p d, hqr]
    exact one_ne_zero
  obtain ⟨b, hb⟩ := (legendreSym.eq_one_iff p (by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hcop)).mp hqr
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective b
  have hpa : (p : ℤ) ∣ a ^ 2 - d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hb]; ring
  refine ⟨a, hpa, fun hd => hcop ?_⟩
  -- `a² - (a² - d) = d`, so `p ∣ d` follows from `p ∣ a²` and `p ∣ a² - d`.
  have hsub : a ^ 2 - (a ^ 2 - d) = d := by ring
  rw [← hsub]
  exact dvd_sub (dvd_pow hd (by norm_num)) hpa

/-- If `d` is a quadratic residue mod the odd prime `p` (with `p ∤ d`), no element `σ` of the
decomposition group of a prime `Q` above `p` sends the generator `r` to its negation. -/
private theorem map_ne_neg_of_legendreSym_eq_one (d : ℤ) (r : K)
    (hr : r ^ 2 = algebraMap ℤ K d)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hqr : legendreSym p d = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ stabilizer (K ≃ₐ[ℚ] K) Q) : σ r ≠ - r := by
  intro hflip
  obtain ⟨a, hpa, hpa'⟩ := exists_dvd_sq_sub_and_not_dvd_of_legendreSym_eq_one p hqr
  let R : 𝓞 K := integralSqrt hr
  -- `algebraMap` intertwines the Galois action on `𝓞 K` with that on `K` (used for `hsR`/`hsA`).
  have hbridge (x : 𝓞 K) : algebraMap (𝓞 K) K (σ • x) = σ (algebraMap (𝓞 K) K x) := by
    have hcoe : algebraMap (𝓞 K) K (σ • x) = σ • algebraMap (𝓞 K) K x :=
      integralClosure.coe_smul σ x
    rw [hcoe, AlgEquiv.smul_def]
  have hmapQ : ∀ x ∈ Q, σ • x ∈ Q := by
    intro x hx; rw [← mem_stabilizer_iff.mp hσ]; exact Ideal.smul_mem_pointwise_smul σ x Q hx
  set A : 𝓞 K := algebraMap ℤ (𝓞 K) a with hAdef
  -- `(R - A)(R + A) = d - a² ∈ Q`, so one factor lies in the prime `Q`.
  have hAsq : A ^ 2 = algebraMap ℤ (𝓞 K) (a ^ 2) := by rw [hAdef, ← map_pow]
  have heq : (R - A) * (R + A) = algebraMap ℤ (𝓞 K) (d - a ^ 2) := by
    have h1 : (R - A) * (R + A) = R ^ 2 - A ^ 2 := by ring
    rw [h1, integralSqrt_sq hr, hAsq, ← map_sub]
  have hfacQ : (R - A) * (R + A) ∈ Q := by
    rw [heq]; exact (algebraMap_int_mem_iff_dvd_of_liesOver Q _).mpr (dvd_sub_comm.mp hpa)
  -- `σ` sends `R ↦ -R` and fixes the integer `A`.
  have hsR : σ • R = - R := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [hbridge R, map_neg, algebraMap_integralSqrt, hflip]
  have hsA : σ • A = A := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [hbridge A, hAdef, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K,
      IsScalarTower.algebraMap_apply ℤ ℚ K, AlgEquiv.commutes]
  -- Applying `σ` to whichever factor lies in `Q` and adding the two gives `2 A ∈ Q`.
  have h2A : (2 : 𝓞 K) * A ∈ Q := by
    rcases (‹Q.IsPrime›).mem_or_mem hfacQ with hca | hca
    · have h1 : σ • (R - A) ∈ Q := hmapQ _ hca
      rw [smul_sub, hsR, hsA] at h1
      have hs := Q.add_mem hca h1
      have hsum : (R - A) + (-R - A) = -(2 * A) := by ring
      rw [hsum] at hs
      exact neg_mem_iff.mp hs
    · have h1 : σ • (R + A) ∈ Q := hmapQ _ hca
      rw [smul_add, hsR, hsA] at h1
      have hs := Q.add_mem hca h1
      have hsum : (R + A) + (-R + A) = 2 * A := by ring
      rw [hsum] at hs
      exact hs
  -- `2 A = algebraMap (2 a) ∈ Q` forces `p ∣ 2 a`, hence (as `p` is odd) `p ∣ a` — absurd.
  have h2a : algebraMap ℤ (𝓞 K) (2 * a) ∈ Q := by
    have halg_two : algebraMap ℤ (𝓞 K) 2 = 2 := by norm_num
    rw [map_mul, halg_two, ← hAdef]
    exact h2A
  have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  rcases hpint.dvd_mul.mp ((algebraMap_int_mem_iff_dvd_of_liesOver Q _).mp h2a) with h2 | ha
  · exact hodd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h2))
  · exact hpa' ha

/-- Backward core (pointwise): if `p` is odd and `d` is a quadratic residue mod `p`, then every
`σ` in the decomposition group of `Q` fixes the generator `r`. -/
private theorem decompositionGroup_fixes_gen (d : ℤ) (r : K)
    (hr : r ^ 2 = algebraMap ℤ K d)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hqr : legendreSym p d = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : σ ∈ stabilizer (K ≃ₐ[ℚ] K) Q) : σ r = r := by
  -- From `σ r² = r²`, `σ r = ± r`; the `+` case is immediate and the `-` case is
  -- excluded by `map_ne_neg_of_legendreSym_eq_one`.
  have hr' : r ^ 2 = algebraMap ℚ K ((d : ℚ)) := by rw [hr]; simp
  have h2 : σ r ^ 2 = r ^ 2 := by rw [← map_pow, hr', AlgEquiv.commutes]
  rcases eq_or_eq_neg_of_sq_eq_sq (σ r) r h2 with h | h
  · exact h
  · exact absurd h (map_ne_neg_of_legendreSym_eq_one d r hr hodd hqr Q hσ)

/-- Backward wrapper: for `K` generated over `ℚ` by the `r i` (`ℚ(rᵢ) = K`), if `p` is odd and
every `d i` is a quadratic residue mod `p`, then the decomposition group of `Q` is trivial. -/
private theorem stabilizer_eq_bot_of_forall_legendreSym_eq_one {ι : Type*} (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (hqr : ∀ i, legendreSym p (d i) = 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    stabilizer (K ≃ₐ[ℚ] K) Q = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  -- Each `σ` in the stabilizer fixes every generator `r i`, and these generate `K = ℚ(rᵢ)`,
  -- so `σ = 1` by an adjoin induction.
  have hfix : ∀ i, σ (r i) = r i :=
    fun i => decompositionGroup_fixes_gen (d i) (r i) (hr i) hodd (hqr i) Q hσ
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  have hx : x ∈ (⊤ : IntermediateField ℚ K) := IntermediateField.mem_top
  rw [← htop] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hfix i
  | algebraMap q => exact AlgEquiv.commutes σ q
  | add a b _ _ ha hb => rw [map_add, ha, hb]
  | inv a _ ha => rw [map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]

/-- **The multiquadratic splitting law.** For `K = ℚ(√d₁, …, √dₙ)` generated over `ℚ` by square
roots `r i` of integers `d i`, and an odd prime `p` dividing none of the `d i`, `p` splits
completely in `K` iff every `d i` is a quadratic residue mod `p`. -/
theorem ncard_primesOver_multiquadratic_iff {ι : Type*} [Finite ι] (d : ι → ℤ) (r : ι → K)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ K (d i))
    (htop : IntermediateField.adjoin ℚ (Set.range r) = ⊤)
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hcop : ∀ i, ¬ (p : ℤ) ∣ d i) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔
      ∀ i, legendreSym p (d i) = 1 := by
  -- `K` is Galois over `ℚ`: transport the multiquadratic `isGalois` along `htop`.
  have hr' : ∀ i, r i ^ 2 = algebraMap ℚ K ((d i : ℚ)) := by
    intro i; rw [hr i]; simp
  haveI : IsGalois ℚ K := by
    have hg := TauCeti.Multiquadratic.isGalois (K := ℚ) (L := K) (d := fun i => (d i : ℚ)) hr'
    rw [htop] at hg
    exact isGalois_iff_isGalois_top.mp hg
  -- Fix a prime `Q` of `𝓞 K` above `p`.
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp Fact.out))
      (by simpa [Ideal.span_singleton_eq_bot] using hpne)
  obtain ⟨Q, hQp, hQo⟩ : ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧ Q.LiesOver (span {(p : ℤ)}) := by
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty (primesOver (span {(p : ℤ)}) (𝓞 K)))
    exact ⟨Q, hQ⟩
  haveI := hQp
  haveI := hQo
  refine ⟨fun hsplit i =>
    legendreSym_eq_one_of_ncard_primesOver_eq_finrank d r hr (hcop i) Q hsplit, fun hqr => ?_⟩
  rw [ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot K Q]
  exact stabilizer_eq_bot_of_forall_legendreSym_eq_one d r hr htop hodd hqr Q

end

end TauCeti.NumberField
