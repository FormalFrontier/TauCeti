/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets

import Mathlib.Algebra.CharP.Invertible
import TauCeti.Data.ZMod.Divisibility

/-!
# The double coset `Γ₁(N) · diag(1, p) · Γ₁(N)` at a prime `p ∤ N`

`Gamma1/UpperTriCosets.lean` decomposes this double coset at `p ∣ N`, where the `p`
representatives `!![1, b; 0, p]` exhaust it. At a prime `p ∤ N` they do not: there is exactly one
further right coset, and this file produces it, giving Diamond–Shurman's Proposition 5.2.1 in its
remaining case,

`Γ₁(N) · diag(1, p) · Γ₁(N) = (⋃_{b < p} Γ₁(N) · !![1, b; 0, p])  ∪  Γ₁(N) · σ · diag(p, 1)`,

a disjoint union of `p + 1` **right** cosets. Here `σ = !![m, n; N, p]` is any integral matrix
with `m p − n N = 1`: an element of `Γ₀(N)`, *not* of `Γ₁(N)`, and it is that twist which later
supplies the factor `χ(p)` in the Hecke recurrence at a good prime.

## Where the hypotheses enter

The whole statement is carried by the bottom row of `σ`. Its two entries `N` and `p` together
with `det σ = 1` say exactly `m p − n N = 1`
(`mul_sub_mul_eq_one_of_lowerRow`), so such a `σ` exists precisely when `p` and `N` are coprime,
as also follows from `Matrix.SpecialLinearGroup.isCoprime_row`. Everything below is stated for
an arbitrary such `σ`, which
keeps the coprimality implicit in the data rather than as a side hypothesis, and lets the caller
supply whichever Bézout witness it already has.

The field property supplied by primality is used only in the forward inclusion: writing
`γ = !![a, b; c, d]` for an element of `Γ₁(N)`, the product `diag(1, p) · γ` lands in an
upper-triangular coset as soon as the congruence `a j ≡ b (mod p)` is solvable, which for `p ∤ a`
needs `a` invertible modulo `p`. The complementary case `p ∣ a` is where the twisted coset is
used, and it needs no primality:

`diag(1, p) · γ = !![a − b N, b m − a′ n; p(c − d N), p d m − c n] · σ · diag(p, 1)`,  `a = p a′`,

whose left factor has determinant `(a d − b c)(m p − n N) = 1` and lies in `Γ₁(N)` because
`N ∣ c` and `m p ≡ 1 (mod N)`. (For composite `p ∤ N` neither branch covers a `γ` with
`1 < gcd(a, p) < p`, and indeed the coset count is then not `p + 1`.)

Disjointness of the last coset from the others uses only `1 < p` and integrality: comparing
`σ · diag(p, 1)` with `!![1, b; 0, p]` forces `p ∣ n`, which `m p − n N = 1` forbids.

## Main definitions

* `HeckeRing.GL2.primeRep`: the `p + 1` right-coset representatives, indexed by `Option (Fin p)`
  — `some b` the upper-triangular `!![1, b; 0, p]`, `none` the twisted `σ · diag(p, 1)`.

## Main results

* `HeckeRing.GL2.exists_mem_Gamma1_natDiagGL_mul_primeRep_none_of_dvd`: the factorisation of
  `diag(1, p) · γ` through the twisted representative, for `p ∣ a`.
* `HeckeRing.GL2.exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none`:
  `diag(1, p) · !![m p, n; N, 1] = σ · diag(p, 1)` with `!![m p, n; N, 1] ∈ Γ₁(N)` — the reverse
  inclusion for the twisted coset.
* `HeckeRing.GL2.exists_mem_Gamma1_natDiagGL_mul_primeRep`: for prime `p`, every
  `diag(1, p) · γ` with `γ ∈ Γ₁(N)` lies in one of the `p + 1` right cosets.
* `HeckeRing.GL2.op_primeRep_smul_injective`: the `p + 1` right cosets are pairwise distinct.
* `HeckeRing.GL2.doubleCoset_natDiagGL_eq_iUnion_rightCosets_of_prime`: **the decomposition**,
  and `HeckeRing.GL2.doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets_of_prime` the same
  statement read at the chosen representative of `diagCosetGamma1 N p`, which is the shape the
  slash sum of `ModularForms/HeckeSlash/Independence.lean` consumes.

## Provenance

No code is transcribed. The statement is Diamond–Shurman Proposition 5.2.1 in the case `p ∤ N`,
proved here for this repository's own representative families `natDiagGL`, `upperTriRep` and
`scaleRep`. The AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0) organises the same
case as the `heckeT_p_coprime` branch of `heckeT_p_all`
(`LeanModularForms/HeckeRIngs/GL2/HeckeT_n.lean`), on the operator rather than the coset side;
the coset statement below is what identifies the two, and is proved from the group law here.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.2.1.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4–3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups Pointwise

namespace HeckeRing.GL2

variable {N p : ℕ} {σ : SL(2, ℤ)}

/-- **The family of `p + 1` matrices out of which the good-prime `Tₚ` is built.** The `p`
upper-triangular matrices `!![1, b; 0, p]`, indexed by `some b`, together with the twisted
diagonal `σ · diag(p, 1)`, indexed by `none`; the definition makes no assumption on `p` or `σ`.
They are the right-coset representatives of `Γ₁(N) · diag(1, p) · Γ₁(N)` exactly under the
hypotheses of `doubleCoset_natDiagGL_eq_iUnion_rightCosets_of_prime`, namely for `p` prime and
`σ` with bottom row `(N, p)`. The index type `Option (Fin p)` is what the slash-sum machinery of
`HeckeSlash/Independence.lean` sums over. -/
noncomputable def primeRep (σ : SL(2, ℤ)) (p : ℕ) : Option (Fin p) → GL (Fin 2) ℚ
  | some b => upperTriRep p b
  | none => mapGL ℚ σ * scaleRep p

/-- The representative indexed by `some b` is the `b`-th upper-triangular matrix. -/
@[simp] lemma primeRep_some (σ : SL(2, ℤ)) (p : ℕ) (b : Fin p) :
    primeRep σ p (some b) = upperTriRep p b := (rfl)

/-- The representative indexed by `none` is the twisted diagonal `σ · diag(p, 1)`. -/
@[simp] lemma primeRep_none (σ : SL(2, ℤ)) (p : ℕ) :
    primeRep σ p none = mapGL ℚ σ * scaleRep p := (rfl)

/-- The matrix of the twisted representative: multiplying by `diag(p, 1)` on the right scales the
first column of `σ` by `p`, so `!![a, b; c, d] · diag(p, 1) = !![a p, b; c p, d]`. At the bottom
row `(N, p)` the decomposition uses, this reads `σ · diag(p, 1) = !![m p, n; N p, p]`. -/
lemma coe_primeRep_none (hp : 0 < p) :
    (↑(primeRep σ p none) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![((σ 0 0 : ℤ) : ℚ) * (p : ℚ), ((σ 0 1 : ℤ) : ℚ);
        ((σ 1 0 : ℤ) : ℚ) * (p : ℚ), ((σ 1 1 : ℤ) : ℚ)] := by
  rw [primeRep_none, Units.val_mul, coe_mapGL_int_rat_fin_two, coe_scaleRep p hp,
    Matrix.mul_fin_two]
  congrm !![?_, ?_; ?_, ?_] <;> ring1

-- Kept separate so that the repeated rational matrix computation runs on entrywise atoms.
-- The first use supplies the nontrivial left factor in the forward inclusion; the second
-- specializes that factor to `1` for the reverse witness.
private lemma natDiagGL_mul_mapGL_eq_mapGL_mul_primeRep_none_of_entries (hp : 0 < p)
    (hσ10 : σ 1 0 = (N : ℤ)) (hσ11 : σ 1 1 = (p : ℤ))
    {γ δ : SL(2, ℤ)} {a' : ℤ} (ha' : γ 0 0 = (p : ℤ) * a')
    (e00 : δ 0 0 = γ 0 0 - γ 0 1 * (N : ℤ))
    (e01 : δ 0 1 = γ 0 1 * σ 0 0 - a' * σ 0 1)
    (e10 : δ 1 0 = (p : ℤ) * (γ 1 0 - γ 1 1 * (N : ℤ)))
    (e11 : δ 1 1 = (p : ℤ) * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1) :
    natDiagGL 2 ![1, p] * mapGL ℚ γ = mapGL ℚ δ * primeRep σ p none := by
  refine Units.ext ?_
  have hσdet : σ 0 0 * (p : ℤ) - σ 0 1 * (N : ℤ) = 1 :=
    mul_sub_mul_eq_one_of_lowerRow hσ10 hσ11
  have hσdetQ : ((σ 0 0 : ℤ) : ℚ) * (p : ℚ) -
      ((σ 0 1 : ℤ) : ℚ) * (N : ℚ) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hσdet
  have haQ : ((γ 0 0 : ℤ) : ℚ) = (p : ℚ) * ((a' : ℤ) : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) ha'
  rw [Units.val_mul, Units.val_mul, coe_natDiagGL_one hp, coe_primeRep_none hp,
    coe_mapGL_int_rat_fin_two γ, coe_mapGL_int_rat_fin_two δ, e00, e01, e10, e11, hσ10, hσ11,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  push_cast
  congrm !![?_, ?_; ?_, ?_]
  · linear_combination (-(p : ℚ) * ((a' : ℤ) : ℚ)) * hσdetQ +
      (1 - ((σ 0 0 : ℤ) : ℚ) * (p : ℚ)) * haQ
  · linear_combination (-((γ 0 1 : ℤ) : ℚ)) * hσdetQ - ((σ 0 1 : ℤ) : ℚ) * haQ
  · linear_combination (-(p : ℚ) * ((γ 1 0 : ℤ) : ℚ)) * hσdetQ
  · linear_combination (-(p : ℚ) * ((γ 1 1 : ℤ) : ℚ)) * hσdetQ

/-- **The forward factorisation through the twisted coset.** For `γ = !![a, b; c, d] ∈ Γ₁(N)`
with `p ∣ a`, the product `diag(1, p) · γ` lies in the right coset `Γ₁(N) · σ · diag(p, 1)`:

`diag(1, p) · γ = !![a − b N, b m − a′ n; p(c − d N), p d m − c n] · σ · diag(p, 1)`,  `a = p a′`.

No primality is used, and the divisibility `p ∣ a` is what makes the upper-right entry of the
left factor integral. -/
lemma exists_mem_Gamma1_natDiagGL_mul_primeRep_none_of_dvd (hp : 0 < p)
    (hσ10 : σ 1 0 = (N : ℤ))
    (hσ11 : σ 1 1 = (p : ℤ)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) (hpa : (p : ℤ) ∣ γ 0 0) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 N ∧
      natDiagGL 2 ![1, p] * mapGL ℚ γ = mapGL ℚ δ * primeRep σ p none := by
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N γ).mp hγ
  obtain ⟨a', ha'⟩ := hpa
  have hσdet : σ 0 0 * (p : ℤ) - σ 0 1 * (N : ℤ) = 1 :=
    mul_sub_mul_eq_one_of_lowerRow hσ10 hσ11
  have hγdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  -- the new left factor
  have hdet : (!![γ 0 0 - γ 0 1 * (N : ℤ), γ 0 1 * σ 0 0 - a' * σ 0 1;
      (p : ℤ) * (γ 1 0 - γ 1 1 * (N : ℤ)), (p : ℤ) * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hγdet + (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) * hσdet +
      (σ 0 1 * (γ 1 1 * (N : ℤ) - γ 1 0)) * ha'
  obtain ⟨δ, hδmat⟩ : ∃ δ : SL(2, ℤ), (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0 - γ 0 1 * (N : ℤ), γ 0 1 * σ 0 0 - a' * σ 0 1;
        (p : ℤ) * (γ 1 0 - γ 1 1 * (N : ℤ)), (p : ℤ) * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1] :=
    ⟨⟨_, hdet⟩, rfl⟩
  -- `m p ≡ 1 (mod N)`, the congruence that puts the left factor in `Γ₁(N)`
  have hmp : ((σ 0 0 * (p : ℤ) : ℤ) : ZMod N) = 1 := by
    have hσΓ0 : σ ∈ Gamma0 N := Gamma0_mem.mpr (by rw [hσ10]; simp)
    simpa [hσ11] using intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hσΓ0
  refine ⟨δ, ?_, ?_⟩
  · refine (Gamma1_mem N δ).mpr ⟨?_, ?_, ?_⟩
    · have h : ((γ 0 0 - γ 0 1 * (N : ℤ) : ℤ) : ZMod N) = 1 := by
        push_cast
        rw [ha, ZMod.natCast_self]
        ring
      simpa [hδmat] using h
    · have h : (((p : ℤ) * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1 : ℤ) : ZMod N) = 1 := by
        push_cast at hmp ⊢
        rw [hc]
        linear_combination (((γ 1 1 : ℤ) : ZMod N)) * hmp + hd
      simpa [hδmat] using h
    · have h : (((p : ℤ) * (γ 1 0 - γ 1 1 * (N : ℤ)) : ℤ) : ZMod N) = 0 := by
        push_cast
        rw [hc, ZMod.natCast_self]
        ring
      simpa [hδmat] using h
  · have e00 : (δ 0 0 : ℤ) = γ 0 0 - γ 0 1 * (N : ℤ) := by rw [hδmat]; simp
    have e01 : (δ 0 1 : ℤ) = γ 0 1 * σ 0 0 - a' * σ 0 1 := by rw [hδmat]; simp
    have e10 : (δ 1 0 : ℤ) = (p : ℤ) * (γ 1 0 - γ 1 1 * (N : ℤ)) := by rw [hδmat]; simp
    have e11 : (δ 1 1 : ℤ) = (p : ℤ) * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1 := by rw [hδmat]; simp
    exact natDiagGL_mul_mapGL_eq_mapGL_mul_primeRep_none_of_entries hp hσ10 hσ11 ha'
      e00 e01 e10 e11

/-- **The witness for the reverse inclusion.** The matrix `!![m p, n; N, 1]` lies in `Γ₁(N)` —
its determinant is the Bézout relation and `m p ≡ 1 (mod N)` — and moving it across
`diag(1, p)` produces exactly the twisted representative. -/
lemma exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none (hp : 0 < p) (hσ10 : σ 1 0 = (N : ℤ))
    (hσ11 : σ 1 1 = (p : ℤ)) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma1 N ∧
      natDiagGL 2 ![1, p] * mapGL ℚ γ = primeRep σ p none := by
  have hσdet : σ 0 0 * (p : ℤ) - σ 0 1 * (N : ℤ) = 1 :=
    mul_sub_mul_eq_one_of_lowerRow hσ10 hσ11
  have hdet : (!![σ 0 0 * (p : ℤ), σ 0 1; (N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hσdet
  obtain ⟨γ, hγmat⟩ : ∃ γ : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![σ 0 0 * (p : ℤ), σ 0 1; (N : ℤ), 1] := ⟨⟨_, hdet⟩, rfl⟩
  have hmp : ((σ 0 0 * (p : ℤ) : ℤ) : ZMod N) = 1 := by
    have hσΓ0 : σ ∈ Gamma0 N := Gamma0_mem.mpr (by rw [hσ10]; simp)
    simpa [hσ11] using intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hσΓ0
  refine ⟨γ, (Gamma1_mem N γ).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [hγmat] using hmp
  · simp [hγmat]
  · simp [hγmat]
  · have e00 : (γ 0 0 : ℤ) = σ 0 0 * (p : ℤ) := by rw [hγmat]; simp
    have e01 : (γ 0 1 : ℤ) = σ 0 1 := by rw [hγmat]; simp
    have e10 : (γ 1 0 : ℤ) = (N : ℤ) := by rw [hγmat]; simp
    have e11 : (γ 1 1 : ℤ) = 1 := by rw [hγmat]; simp
    have ha' : γ 0 0 = (p : ℤ) * σ 0 0 := by rw [e00]; ring
    have h00 : (1 : SL(2, ℤ)) 0 0 = γ 0 0 - γ 0 1 * (N : ℤ) := by
      rw [e00, e01]
      simpa using hσdet.symm
    have h01 : (1 : SL(2, ℤ)) 0 1 = γ 0 1 * σ 0 0 - σ 0 0 * σ 0 1 := by
      rw [e01]
      simp [mul_comm]
    have h10 : (1 : SL(2, ℤ)) 1 0 = (p : ℤ) * (γ 1 0 - γ 1 1 * (N : ℤ)) := by
      rw [e10, e11]
      simp
    have h11 : (1 : SL(2, ℤ)) 1 1 =
        (p : ℤ) * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1 := by
      rw [e10, e11]
      simpa [mul_comm] using hσdet.symm
    simpa using
      natDiagGL_mul_mapGL_eq_mapGL_mul_primeRep_none_of_entries (σ := σ) hp hσ10 hσ11
        (δ := (1 : SL(2, ℤ))) (a' := σ 0 0) ha' h00 h01 h10 h11

/-- **The forward inclusion.** For a prime `p` and `γ ∈ Γ₁(N)`, the product `diag(1, p) · γ` lies
in one of the `p + 1` right cosets: an upper-triangular one when `p ∤ a`, where the congruence
`a j ≡ b (mod p)` is solvable because `a` is then invertible modulo the prime `p`, and the
twisted one when `p ∣ a`. -/
lemma exists_mem_Gamma1_natDiagGL_mul_primeRep (hp : p.Prime) (hσ10 : σ 1 0 = (N : ℤ))
    (hσ11 : σ 1 1 = (p : ℤ)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    ∃ (i : Option (Fin p)) (δ : SL(2, ℤ)), δ ∈ Gamma1 N ∧
      natDiagGL 2 ![1, p] * mapGL ℚ γ = mapGL ℚ δ * primeRep σ p i := by
  by_cases hpa : (p : ℤ) ∣ γ 0 0
  · obtain ⟨δ, hδ, heq⟩ :=
      exists_mem_Gamma1_natDiagGL_mul_primeRep_none_of_dvd hp.pos hσ10 hσ11 hγ hpa
    exact ⟨none, δ, hδ, heq⟩
  · have hunit : IsUnit ((γ 0 0 : ℤ) : ZMod p) :=
      (CharP.isUnit_intCast_iff (R := ZMod p) hp).mpr hpa
    have : NeZero p := ⟨hp.pos.ne'⟩
    obtain ⟨j, hdvd⟩ := ZMod.exists_dvd_sub_val_mul p (γ 0 1) (γ 0 0) hunit
    have hjlt : j.val < p := ZMod.val_lt j
    obtain ⟨δ, hδ, heq⟩ := exists_mem_Gamma1_natDiagGL_mul_of_dvd hp.pos hγ hjlt
      (by simpa [mul_comm] using hdvd)
    exact ⟨some ⟨j.val, hjlt⟩, δ, hδ, by rw [primeRep_some]; exact heq⟩

/-- **The `p + 1` right cosets are pairwise distinct for any integral subgroup when `1 < p`.**
The `p` upper-triangular ones are separated by `op_upperTriRep_smul_injective`; separating the
twisted one from them is integrality. If
`G · !![1, b; 0, p] = G · σ · diag(p, 1)`, comparing the top rows gives
`n = p (m b + σ'₀₁)` for some `σ' ∈ G`, so `p ∣ n`, and then `m p − n N = 1` makes `p` a
divisor of `1`. -/
theorem op_primeRep_smul_injective {G : Subgroup SL(2, ℤ)} (hp : 1 < p)
    (hσ10 : σ 1 0 = (N : ℤ))
    (hσ11 : σ 1 1 = (p : ℤ)) :
    Function.Injective fun i : Option (Fin p) ↦
      MulOpposite.op (primeRep σ p i) • ((G.map (mapGL ℚ)) : Set (GL (Fin 2) ℚ)) := by
  have hp0 : 0 < p := by omega
  have hσdet : σ 0 0 * (p : ℤ) - σ 0 1 * (N : ℤ) = 1 :=
    mul_sub_mul_eq_one_of_lowerRow hσ10 hσ11
  -- the twisted coset is not one of the upper-triangular ones
  have hne : ∀ b : Fin p,
      MulOpposite.op (primeRep σ p (some b)) • ((G.map (mapGL ℚ)) :
          Set (GL (Fin 2) ℚ)) ≠
        MulOpposite.op (primeRep σ p none) • ((G.map (mapGL ℚ)) :
          Set (GL (Fin 2) ℚ)) := by
    intro b heq
    obtain ⟨τ, -, hτeq⟩ := Subgroup.mem_map.mp ((rightCoset_eq_iff _).mp heq)
    have hmul : (mapGL ℚ τ : GL (Fin 2) ℚ) * upperTriRep p b = primeRep σ p none := by
      rw [hτeq, ← primeRep_some σ p b, inv_mul_cancel_right]
    have hmat : (↑(mapGL ℚ τ) : Matrix (Fin 2) (Fin 2) ℚ) * !![1, (b : ℚ); 0, (p : ℚ)] =
        (↑(primeRep σ p none) : Matrix (Fin 2) (Fin 2) ℚ) := by
      rw [← coe_upperTriRep, ← Units.val_mul, hmul]
    rw [coe_mapGL_int_rat_fin_two, coe_primeRep_none hp0, Matrix.mul_fin_two] at hmat
    have h00 : ((τ 0 0 : ℤ) : ℚ) = ((σ 0 0 : ℤ) : ℚ) * (p : ℚ) := by
      simpa using congrFun (congrFun hmat 0) 0
    have h01 : ((τ 0 0 : ℤ) : ℚ) * (b : ℚ) + ((τ 0 1 : ℤ) : ℚ) * (p : ℚ) = ((σ 0 1 : ℤ) : ℚ) := by
      simpa using congrFun (congrFun hmat 0) 1
    rw [h00] at h01
    have hn : (σ 0 1 : ℤ) = (p : ℤ) * (σ 0 0 * (b : ℕ) + τ 0 1) := by
      have hQ : ((σ 0 1 : ℤ) : ℚ) = (((p : ℤ) * (σ 0 0 * (b : ℕ) + τ 0 1) : ℤ) : ℚ) := by
        push_cast at h01 ⊢
        linarith
      exact_mod_cast hQ
    have hdvd : (p : ℤ) ∣ 1 :=
      ⟨σ 0 0 - (σ 0 0 * (b : ℕ) + τ 0 1) * (N : ℤ), by linear_combination -hσdet - (N : ℤ) * hn⟩
    have hle := Int.le_of_dvd one_pos hdvd
    have htwo : 2 ≤ (p : ℤ) := by exact_mod_cast hp
    omega
  rintro (_ | b₁) (_ | b₂) h
  · rfl
  · exact absurd h.symm (hne b₂)
  · exact absurd h (hne b₁)
  · simpa using op_upperTriRep_smul_injective (G := G) (by simpa using h)

/-- **The `Tₚ` double coset at a prime `p ∤ N` is the union of `p + 1` right cosets.**
`Γ₁(N) · diag(1, p) · Γ₁(N) = ⋃_{j < p} Γ₁(N) · !![1, j; 0, p]  ∪  Γ₁(N) · σ · diag(p, 1)`,
Diamond–Shurman's Proposition 5.2.1 in the case `p ∤ N` — the coprimality being carried by the
existence of the twist `σ` rather than stated separately (equivalently, by
`Matrix.SpecialLinearGroup.isCoprime_row`, the bottom-row entries are coprime).

The inclusion `⊆` is `exists_mem_Gamma1_natDiagGL_mul_primeRep` and is where primality enters;
`⊇` is `natDiagGL_mul_mapGL_T_zpow` on the upper-triangular cosets and
`exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none` on the twisted one. That the union is disjoint
is `op_primeRep_smul_injective`, which only needs `1 < p`. -/
theorem doubleCoset_natDiagGL_eq_iUnion_rightCosets_of_prime (hp : p.Prime)
    (hσ10 : σ 1 0 = (N : ℤ)) (hσ11 : σ 1 1 = (p : ℤ)) :
    doubleCoset (natDiagGL 2 ![1, p]) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
      ⋃ i : Option (Fin p), MulOpposite.op (primeRep σ p i) •
        ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  apply doubleCoset_eq_iUnion_rightCosets_of_forall_exists
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))
      (natDiagGL 2 ![1, p]) (primeRep σ p)
  · intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨i, δ, hδ, heq⟩ :=
      exists_mem_Gamma1_natDiagGL_mul_primeRep hp hσ10 hσ11 hγ
    exact ⟨i, mapGL ℚ δ, Subgroup.mem_map_of_mem _ hδ, heq⟩
  · intro i
    cases i with
    | none =>
      obtain ⟨γ, hγ, heq⟩ :=
        exists_mem_Gamma1_natDiagGL_mul_eq_primeRep_none hp.pos hσ10 hσ11
      exact ⟨mapGL ℚ γ, Subgroup.mem_map_of_mem _ hγ, heq⟩
    | some b =>
      exact ⟨mapGL ℚ (ModularGroup.T ^ (b : ℤ)),
        Subgroup.mem_map_of_mem _ (T_zpow_mem_Gamma1 N _), by
        rw [primeRep_some, natDiagGL_mul_mapGL_T_zpow hp.pos b]⟩

/-- The decomposition of `doubleCoset_natDiagGL_eq_iUnion_rightCosets_of_prime`, read at the
chosen representative `D.out` of `diagCosetGamma1 N p` — the shape the slash-sum machinery of
`HeckeSlash/Independence.lean` consumes. -/
theorem doubleCoset_out_diagCosetGamma1_eq_iUnion_rightCosets_of_prime (hp : p.Prime)
    (hσ10 : σ 1 0 = (N : ℤ)) (hσ11 : σ 1 1 = (p : ℤ)) :
    doubleCoset ((diagCosetGamma1 N p).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) =
      ⋃ i : Option (Fin p), MulOpposite.op (primeRep σ p i) •
        ((Gamma1 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL,
    doubleCoset_natDiagGL_eq_iUnion_rightCosets_of_prime hp hσ10 hσ11]

end HeckeRing.GL2

end
