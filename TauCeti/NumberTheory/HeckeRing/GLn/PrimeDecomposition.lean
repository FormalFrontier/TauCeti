/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.CoprimeMul
-- supplies the `Ring (IntegralHeckeRing n)` instance that `Subring` needs for `pLocalSubring`
public import TauCeti.NumberTheory.HeckeRing.Associativity

import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime decomposition of diagonal Hecke operators

The `p`-adic decomposition of the diagonal Hecke operators: every `T(a₁,...,aₙ)` with
entrywise nonzero `a` splits off its `p`-power part,
`T(a) = T(p-part) · T(p-free part)`, by the coprime product theorem. Nonvanishing is what is
required throughout — it is all `Nat.factorization` and `ordCompl` ask for, and it is exactly
what keeps `natDiagGL` off its junk value, which it takes on a tuple with a zero entry.

The `p`-power operators whose exponent vector is *monotone* generate the `p`-local Hecke
subring `R_p` (Shimura's `R_p`). For `1 < p`, monotonicity is exactly what makes the exponent
vector a divisibility chain, hence a canonical diagonal. `p` itself is left unrestricted, so
the definition carries no hypothesis, and the two degenerate values fail that reading in
opposite ways: at `p = 0` a positive exponent gives `0 ^ e i = 0`, so the generator is
`natDiagGL`'s junk value rather than a coset, while at `p = 1` every exponent vector gives the
constant-one chain, so monotonicity is not necessary. In practice `p` is prime.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/PrimeDecomposition.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GLn.primePowDiag`: the `p`-power diagonal `i ↦ p ^ e i`.
* `HeckeRing.GLn.diagFactorizationAt`: the entrywise `p`-adic valuation of a diagonal — the
  full `Nat.factorization` evaluated at the single prime `p` in each coordinate, hence the
  `At` suffix; it is a `Fin n → ℕ`, not a finitely supported factorization.
* `HeckeRing.GLn.diagOrdCompl`: the entrywise `p`-free part of a diagonal, i.e. `ordCompl[p]`
  applied in each coordinate.
* `HeckeRing.GLn.pLocalSubring`: the `p`-local Hecke subring `R_p`.

## Main results

* `HeckeRing.GLn.diagElem_eq_primePowDiag_mul_diagOrdCompl`: `T(a) = T(p-part) · T(p-free part)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.2.
-/

public section

open Matrix HeckeRing DoubleCoset Finset

namespace HeckeRing.GLn

variable (n : ℕ)

section PPow

/-- The `p`-power diagonal: entries are `p ^ e i`. -/
def primePowDiag (p : ℕ) (e : Fin n → ℕ) : Fin n → ℕ :=
  fun i ↦ p ^ e i

/-- Defining equation for the sealed definition `primePowDiag`. -/
@[simp]
lemma primePowDiag_apply (p : ℕ) (e : Fin n → ℕ) (i : Fin n) :
    primePowDiag n p e i = p ^ e i := (rfl)

/-- Every entry of a `p`-power diagonal is positive when `p` is. -/
lemma primePowDiag_pos (p : ℕ) (hp : 0 < p) (e : Fin n → ℕ) :
    ∀ i, 0 < primePowDiag n p e i :=
  fun _ ↦ pow_pos hp _

/-- The `p`-power diagonal turns a sum of exponent vectors into the entrywise product. -/
@[simp]
lemma primePowDiag_add (p : ℕ) (e f : Fin n → ℕ) :
    primePowDiag n p (e + f) = primePowDiag n p e * primePowDiag n p f := by
  ext i
  simp [pow_add]

/-- Monotone exponents give a divisibility chain of `p`-power diagonals. -/
lemma isDvdChain_primePowDiag (p : ℕ) (e : Fin n → ℕ) (hmono : Monotone e) :
    IsDvdChain (primePowDiag n p e) :=
  isDvdChain_iff.mpr fun _ _ hij ↦ Nat.pow_dvd_pow p (hmono hij)

/-- The entrywise `p`-adic valuation of a diagonal. -/
def diagFactorizationAt (p : ℕ) (a : Fin n → ℕ) : Fin n → ℕ :=
  fun i ↦ (a i).factorization p

/-- Defining equation for the sealed `diagFactorizationAt`. -/
@[simp]
lemma diagFactorizationAt_apply (p : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    diagFactorizationAt n p a i = (a i).factorization p := (rfl)

/-- The `p`-component of a divisibility chain is monotone. -/
lemma diagFactorizationAt_monotone (a : Fin n → ℕ)
    (ha_ne : ∀ i, a i ≠ 0) (ha : IsDvdChain a) (p : ℕ) :
    Monotone (diagFactorizationAt n p a) := fun i j hij ↦
  (Nat.factorization_le_iff_dvd (ha_ne i) (ha_ne j)).mpr
    (isDvdChain_iff.mp ha hij) p

end PPow

section DiagOrdCompl

/-- The entrywise `p`-free part of a diagonal: `a i ↦ a i / p ^ (v_p (a i))`. -/
noncomputable def diagOrdCompl (p : ℕ) (a : Fin n → ℕ) : Fin n → ℕ :=
  fun i ↦ ordCompl[p] (a i)

/-- Defining equation for the sealed `diagOrdCompl`. -/
@[simp]
lemma diagOrdCompl_apply (p : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    diagOrdCompl n p a i = ordCompl[p] (a i) := (rfl)

/-- Removing the `p`-part preserves positivity of every entry. -/
lemma diagOrdCompl_pos (p : ℕ) (a : Fin n → ℕ) (ha_ne : ∀ i, a i ≠ 0) :
    ∀ i, 0 < diagOrdCompl n p a i :=
  fun i ↦ Nat.ordCompl_pos p (ha_ne i)

/-- The `p`-free part preserves divisibility chains. -/
lemma isDvdChain_diagOrdCompl (p : ℕ) (a : Fin n → ℕ) (ha : IsDvdChain a) :
    IsDvdChain (diagOrdCompl n p a) :=
  isDvdChain_iff.mpr fun _ _ hij ↦
    Nat.ordCompl_dvd_ordCompl_of_dvd (isDvdChain_iff.mp ha hij) p

/-- The pointwise product of the `p`-part and the `p`-free part recovers the diagonal. -/
@[simp]
lemma primePowDiag_mul_diagOrdCompl (p : ℕ) (a : Fin n → ℕ) :
    primePowDiag n p (diagFactorizationAt n p a) * diagOrdCompl n p a = a :=
  funext fun i ↦ Nat.ordProj_mul_ordCompl_eq_self (a i) p

/-- The `p`-part and `p`-free-part determinants are coprime. -/
lemma coprime_prod_primePowDiag_diagOrdCompl (p : ℕ) (hp : p.Prime)
    (a : Fin n → ℕ) (ha_ne : ∀ i, a i ≠ 0) :
    Nat.Coprime (∏ i, primePowDiag n p (diagFactorizationAt n p a) i)
      (∏ i, diagOrdCompl n p a i) := by
  -- the `p`-part determinant is a single power of `p`; `primePowDiag_apply` exposes the
  -- entries as `p ^ e i`, after which the product-to-power identity applies verbatim
  have hprod : (∏ i, primePowDiag n p (diagFactorizationAt n p a) i)
      = p ^ ∑ i, diagFactorizationAt n p a i := by
    simpa only [primePowDiag_apply] using
      Finset.prod_pow_eq_pow_sum Finset.univ (diagFactorizationAt n p a) p
  rw [hprod]
  exact (Nat.Coprime.prod_right fun i _ ↦ Nat.coprime_ordCompl hp (ha_ne i)).pow_left _

end DiagOrdCompl

variable [NeZero n]

/-- **Binary prime splitting** (Shimura, §3.2): every diagonal Hecke operator with entrywise
nonzero entries factors into its `p`-power component and its `p`-free component, for any
prime `p`. The hypothesis is essential, not cosmetic: on a tuple with a zero entry `natDiagGL`
takes its junk value and the two factors need not multiply back to `T(a)`. Callers holding
positivity discharge it with `.ne'`. -/
theorem diagElem_eq_primePowDiag_mul_diagOrdCompl (a : Fin n → ℕ) (ha_ne : ∀ i, a i ≠ 0) (p : ℕ)
    (hp : p.Prime) :
    diagElem a =
      diagElem (primePowDiag n p (diagFactorizationAt n p a)) * diagElem (diagOrdCompl n p a) := by
  conv_lhs => rw [← primePowDiag_mul_diagOrdCompl n p a]
  exact (diagElem_mul_of_coprime n _ _
    (coprime_prod_primePowDiag_diagOrdCompl n p hp a ha_ne)).symm

/-- The `p`-local Hecke subring `R_p`: generated by the diagonal Hecke operators
`T(p^e₁,...,p^eₙ)` whose exponent vector `e` is **monotone** (Shimura's `R_p`). Monotonicity
is part of the generating set, not an afterthought: for `1 < p` it is exactly the condition
making the entries a divisibility chain, so each generator names a canonical double coset.

`p` is unrestricted, so no hypothesis is needed to form the subring, but that
canonical-double-coset reading needs `1 < p` (in practice `p` prime). At `p = 0` a positive
exponent gives a zero entry, so the generator is `natDiagGL`'s junk value rather than a
diagonal coset; at `p = 1` every exponent vector gives the constant-one chain, so monotonicity
is not necessary. -/
noncomputable def pLocalSubring (p : ℕ) : Subring (IntegralHeckeRing n) :=
  Subring.closure
    {f | ∃ (e : Fin n → ℕ) (_ : Monotone e), f = diagElem (primePowDiag n p e)}

/-- Defining equation for the sealed definition `pLocalSubring`. -/
lemma pLocalSubring_def (p : ℕ) :
    pLocalSubring n p = Subring.closure
      {f | ∃ (e : Fin n → ℕ) (_ : Monotone e), f = diagElem (primePowDiag n p e)} := (rfl)

/-- A diagonal Hecke operator with `p`-power entries lies in `R_p`, provided its exponent
vector is monotone — that is the generating set of `pLocalSubring`. -/
@[simp]
lemma diagElem_primePowDiag_mem_pLocalSubring (p : ℕ) (e : Fin n → ℕ)
    (hmono : Monotone e) : diagElem (primePowDiag n p e) ∈ pLocalSubring n p :=
  Subring.subset_closure ⟨e, hmono, rfl⟩

/-- **The universal property of `R_p`**: a subring contains `R_p` exactly when it contains
every monotone `p`-power generator. This is the elimination form — `pLocalSubring` is a
`Subring.closure`, so proving a map or an inclusion out of it should go through this rather
than unfolding the closure and manipulating the generating set by hand. -/
@[simp]
lemma pLocalSubring_le_iff (p : ℕ) (S : Subring (IntegralHeckeRing n)) :
    pLocalSubring n p ≤ S ↔
      ∀ e : Fin n → ℕ, Monotone e → diagElem (primePowDiag n p e) ∈ S := by
  rw [pLocalSubring_def, Subring.closure_le]
  exact ⟨fun h e he ↦ h ⟨e, he, rfl⟩, fun h _ ⟨e, he, hf⟩ ↦ hf ▸ h e he⟩

end HeckeRing.GLn
