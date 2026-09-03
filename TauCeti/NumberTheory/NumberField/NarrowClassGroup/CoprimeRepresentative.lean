/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Coprime representatives of narrow ideal classes

Every narrow ideal class of a number field has an integral representative coprime to any prescribed
nonzero ideal. This is the finite-place approximation input needed to evaluate genus characters on
narrow ideal classes in Layer 3 of the multiquadratic roadmap.

The proof starts with the Dedekind-domain approximation
`IsDedekindDomain.exists_sup_span_eq`, applied to `I * M ≤ I`. It gives an element `a ∈ I` such
that `I * M + (a) = I`; consequently the quotient `(a) / I` is coprime to `M`. Adding a sufficiently
large positive rational integer from `I * M` makes `a` totally positive without changing this ideal
identity. Thus `(a) / I` represents the inverse narrow class of `I`.

This is the usual finite-prime form of strong approximation for ideal classes. See J. W. S. Cassels
and A. Fröhlich, *Algebraic Number Theory*, Chapter II.

## Main results

* `NumberField.exists_isTotallyPositive_span_eq_mul_isCoprime`: a totally positive principal
  multiple of a nonzero ideal whose quotient is coprime to a prescribed ideal.
* `NumberField.NarrowClassGroup.exists_mk0_eq_and_isCoprime`: every narrow ideal class has a
  nonzero integral representative coprime to a prescribed nonzero ideal.
* `NumberField.NarrowClassGroup.exists_mk0_eq_and_isCoprime_absNorm`: the representative may be
  chosen with absolute norm coprime to a prescribed nonzero integer.
-/

public section

open scoped nonZeroDivisors

open NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Shifting a generator by an element of `H` preserves the ideal generated together with `H`. -/
private theorem sup_span_singleton_eq_of_sub_mem {R : Type*} [CommRing R] {H : Ideal R} {a b : R}
    (hba : b - a ∈ H) : H ⊔ Ideal.span {b} = H ⊔ Ideal.span {a} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Ideal.span_singleton_le_iff_mem, ← sub_add_cancel b a]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hba)
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  · refine sup_le le_sup_left ?_
    rw [Ideal.span_singleton_le_iff_mem]
    have hab : a = b - (b - a) := by abel
    rw [hab]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
      (Ideal.mem_sup_left hba)

/-- **A totally positive coprime quotient of an ideal.** Given nonzero integral ideals `I` and `M`,
there are a nonzero totally positive algebraic integer `a` and a nonzero ideal `J`, coprime to `M`,
such that `(a) = I * J`.

Equivalently, `J = (a) / I`. The element `a` may be chosen totally positive while retaining the
finite-place coprimality because one may add a sufficiently large positive integer lying in
`I * M`. -/
theorem exists_isTotallyPositive_span_eq_mul_isCoprime (I M : (Ideal (𝓞 K))⁰) :
    ∃ (a : 𝓞 K) (J : (Ideal (𝓞 K))⁰), a ≠ 0 ∧ IsTotallyPositive (a : K) ∧
      Ideal.span {a} = (I : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)) ∧
      IsCoprime (J : Ideal (𝓞 K)) (M : Ideal (𝓞 K)) := by
  classical
  let H : Ideal (𝓞 K) := (I : Ideal (𝓞 K)) * (M : Ideal (𝓞 K))
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hM0 : (M : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp M.2
  have hH0 : H ≠ 0 := mul_ne_zero hI0 hM0
  have hHI : H ≤ (I : Ideal (𝓞 K)) := by
    exact Ideal.mul_le_left
  -- Dedekind approximation supplies an initial generator with the required ideal identity.
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hHI hH0
  let q : 𝓞 K := Ideal.absNorm H
  have hqH : q ∈ H := by
    simpa [q] using Ideal.absNorm_mem H
  have hq0 : q ≠ 0 := by
    simpa [q, Ideal.absNorm_eq_zero_iff] using hH0
  have hqpos : 0 < Ideal.absNorm H := Nat.pos_of_ne_zero <| by
    simpa [Ideal.absNorm_eq_zero_iff] using hH0
  let B : ℝ := ∑ w : {w : InfinitePlace K // w.IsReal},
    |embedding_of_isReal w.2 (a : K)|
  -- The norm bound and positivity shift the generator by a large positive multiple of `q`.
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let b : 𝓞 K := a + n * q
  have hbsub : b - a ∈ H := by
    simpa [b] using H.mul_mem_left (n : 𝓞 K) hqH
  have hbpos : IsTotallyPositive (b : K) := by
    rw [isTotallyPositive_iff]
    intro w hw
    let w' : {w : InfinitePlace K // w.IsReal} := ⟨w, hw⟩
    have habs : |embedding_of_isReal hw (a : K)| ≤ B := by
      exact Finset.single_le_sum (f := fun v : {w : InfinitePlace K // w.IsReal} =>
        |embedding_of_isReal v.2 (a : K)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w')
    have hqone : (1 : ℝ) ≤ Ideal.absNorm H := by exact_mod_cast hqpos
    have hnq : (n : ℝ) ≤ (n : ℝ) * Ideal.absNorm H := by nlinarith
    have hbmap : embedding_of_isReal hw (b : K) =
        embedding_of_isReal hw (a : K) + (n : ℝ) * Ideal.absNorm H := by
      simp [b, q]
    rw [hbmap]
    have halower : -B ≤ embedding_of_isReal hw (a : K) := (abs_le.mp habs).1
    linarith
  -- The shift lies in `H`, so the span identity is preserved.
  have hsupb : H ⊔ Ideal.span {b} = (I : Ideal (𝓞 K)) := by
    exact (sup_span_singleton_eq_of_sub_mem hbsub).trans ha
  -- If the shifted generator vanishes, fall back to the positive norm element `q`.
  let c : 𝓞 K := if b = 0 then q else b
  have hc0 : c ≠ 0 := by
    by_cases hb0 : b = 0
    · simp only [c, hb0, ↓reduceIte]
      exact hq0
    · simp only [c, hb0, ↓reduceIte]
      exact hb0
  have hcpos : IsTotallyPositive (c : K) := by
    by_cases hb0 : b = 0
    · simp only [c, hb0, ↓reduceIte]
      simpa [q] using (isTotallyPositive_ratCast (K := K) (q := (Ideal.absNorm H : ℚ))
        (by exact_mod_cast hqpos))
    · simpa [c, hb0] using hbpos
  have hsupc : H ⊔ Ideal.span {c} = (I : Ideal (𝓞 K)) := by
    by_cases hb0 : b = 0
    · have hHIeq : H = (I : Ideal (𝓞 K)) := by simpa [hb0] using hsupb
      simp only [c, hb0, ↓reduceIte]
      rw [hHIeq, sup_eq_left]
      rw [Ideal.span_singleton_le_iff_mem]
      exact hHIeq ▸ hqH
    · simpa [c, hb0] using hsupb
  have hcI : Ideal.span {c} ≤ (I : Ideal (𝓞 K)) := le_sup_right.trans_eq hsupc
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hcI
  have hJ0 : J ≠ 0 := by
    intro hJ0
    rw [hJ0, mul_zero] at hJ
    have hcspan : Ideal.span {c} = ⊥ := hJ
    exact hc0 ((Ideal.span_singleton_eq_bot).mp hcspan)
  have hcop : IsCoprime J (M : Ideal (𝓞 K)) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    have hsupc' : (I : Ideal (𝓞 K)) * (M : Ideal (𝓞 K)) ⊔ Ideal.span {c} =
        (I : Ideal (𝓞 K)) := by
      simpa only [H] using hsupc
    have hmulEq : (I : Ideal (𝓞 K)) * ((M : Ideal (𝓞 K)) ⊔ J) =
        (I : Ideal (𝓞 K)) * ⊤ := by
      rw [Ideal.mul_sup, Ideal.mul_top, ← hJ, hsupc']
    -- Cancel the nonzero ideal `I` to obtain coprimality of `J` and `M`.
    exact mul_left_cancel₀ hI0 hmulEq
  exact ⟨c, ⟨J, by simpa using hJ0⟩, hc0, hcpos, hJ, hcop⟩

namespace NarrowClassGroup

/-- Ideal coprimality to the ideal generated by `n` forces numerical coprimality of the absolute
norm with `n`. This is the finite-prime bridge used by the integer-modulus corollary below. -/
private theorem absNorm_coprime_of_isCoprime_span_natCast {I : Ideal (𝓞 K)} {n : ℕ}
    (hcop : IsCoprime I (Ideal.span {(n : 𝓞 K)})) : (Ideal.absNorm I).Coprime n := by
  by_contra h
  obtain ⟨p, hp, hpI, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  obtain ⟨P, hPmax, hPunder, hPI⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hpI
  have hIle : I ≤ P := Ideal.dvd_iff_le.mp hPI
  have hnmem : (n : 𝓞 K) ∈ P := by
    have hnunder : (n : ℤ) ∈ P.under ℤ := by
      rw [hPunder, Ideal.mem_span_singleton]
      exact_mod_cast hpn
    have hnmap : algebraMap ℤ (𝓞 K) (n : ℤ) ∈ P := by
      rw [← Ideal.mem_under]
      exact hnunder
    simpa using hnmap
  have hnle : Ideal.span {(n : 𝓞 K)} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hnmem
  have htop : (⊤ : Ideal (𝓞 K)) ≤ P := by
    rw [← hcop.sup_eq]
    exact sup_le hIle hnle
  exact hPmax.ne_top (top_unique htop)

/-- **Every narrow ideal class has a coprime integral representative.** For every class `C` and
nonzero integral ideal `M`, there is a nonzero integral ideal `J`, coprime to `M`, whose narrow
class is `C`.

This is the strong-approximation input used to define ideal-class characters from arithmetic
functions that are only multiplicative away from a fixed modulus. -/
theorem exists_mk0_eq_and_isCoprime (C : NarrowClassGroup K) (M : (Ideal (𝓞 K))⁰) :
    ∃ J : (Ideal (𝓞 K))⁰, mk0 J = C ∧
      IsCoprime (J : Ideal (𝓞 K)) (M : Ideal (𝓞 K)) := by
  obtain ⟨I, hI⟩ := mk0_surjective C⁻¹
  obtain ⟨a, J, ha0, hapos, haIJ, hcop⟩ :=
    exists_isTotallyPositive_span_eq_mul_isCoprime I M
  have hspan0 : Ideal.span {a} ∈ (Ideal (𝓞 K))⁰ :=
    Ideal.span_singleton_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ha0)
  have hone : mk0 ⟨Ideal.span {a}, hspan0⟩ = 1 :=
    mk0_eq_one_of_isTotallyPositive ha0 hapos rfl
  have hmul := congrArg mk0
    (Subtype.ext haIJ : (⟨Ideal.span {a}, hspan0⟩ : (Ideal (𝓞 K))⁰) = I * J)
  rw [map_mul, hI, hone] at hmul
  have hJC : mk0 J = C := by
    apply mul_left_cancel (a := C⁻¹)
    simpa using hmul.symm
  exact ⟨J, hJC, hcop⟩

/-- **Every narrow ideal class has a representative of norm coprime to a modulus.** For a nonzero
integer `m`, every narrow ideal class is represented by a nonzero integral ideal `J` whose absolute
norm is coprime to `m`.

This is the integer-modulus form consumed by genus characters, whose value on `J` is evaluated at
`Ideal.absNorm J`. -/
theorem exists_mk0_eq_and_isCoprime_absNorm (C : NarrowClassGroup K) {m : ℤ} (hm : m ≠ 0) :
    ∃ J : (Ideal (𝓞 K))⁰, mk0 J = C ∧ IsCoprime (Ideal.absNorm (J : Ideal (𝓞 K)) : ℤ) m := by
  have hmabs : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hmcast : (m.natAbs : 𝓞 K) ≠ 0 := by exact_mod_cast hmabs
  have hM : Ideal.span {(m.natAbs : 𝓞 K)} ∈ (Ideal (𝓞 K))⁰ :=
    Ideal.span_singleton_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hmcast)
  obtain ⟨J, hJC, hcop⟩ := exists_mk0_eq_and_isCoprime C ⟨_, hM⟩
  refine ⟨J, hJC, ?_⟩
  rw [Int.isCoprime_iff_nat_coprime]
  simpa using absNorm_coprime_of_isCoprime_span_natCast hcop

end NarrowClassGroup

end NumberField
