/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Finiteness of `MvPolynomial.expand`

The polynomial ring `R[X_i]` is a finite module over its image under `MvPolynomial.expand n`
(the subring `R[X_i ^ n]`), spanned by the monomials whose exponents are all below `n`.

Composed with the finiteness of `MvPolynomial.map f` — a separate result, proved in
`TauCeti/RingTheory/MvPolynomial/Basic.lean` and not imported here — this gives that
`k'[X_1, …, X_r]` is a finite module over `k[X_1 ^ q, …, X_r ^ q]` for a finite extension
`k' / k`, the finiteness that Stacks 10.161.13 (tag 032O) records as "`R'[x^{1/q}]` is finite
over `R[x]`" and that the purely inseparable half of normalization-finiteness rests on.

Also here is the coefficient-level Frobenius computation behind Stacks' "some details omitted":
if every coefficient of `g` acquires a `q`-th root in `S`, then `g(X ^ q)` becomes a `q`-th power
in `S[X_i]`.

## Main results

* `TauCeti.MvPolynomial.span_monomial_lt_eq_top`: over the image of `expand n`, the monomials
  with all exponents below `n` span the polynomial ring.
* `TauCeti.MvPolynomial.finite_expand`: `expand n` is a finite ring map for `0 < n`.
* `TauCeti.MvPolynomial.exists_pow_eq_map_expand`: `(map f) (expand (p ^ n) g)` is a
  `p ^ n`-th power once the coefficients of `g` have `p ^ n`-th roots in `S`.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`.

All three results are the multivariate form of the univariate argument in Stacks, Lemma 10.161.13
(tag 032O), whose proof records only "`R′[x^{1/q}]` is finite over `R[x]`" for the first two. The
third is the coefficient half of the details that lemma omits: "There exists a finite purely
inseparable field extension `L′/K` and `q = p^e` such that `L ⊂ L′(x^{1/q})`; some details
omitted". Concretely, with `h = ∑ d_α X ^ α` for `d_α ^ (p ^ n) = f (coeff α g)`, Frobenius gives
`h ^ (p ^ n) = ∑ f (coeff α g) X ^ (p ^ n • α)`. The multivariate forms are not claimed as source
material.

The argument is the finiteness sentence of Stacks 10.161.13 (tag 032O). **That lemma is
univariate**: it is stated for the rings `R[x]` and `R'[x^{1/q}]` in a single variable. What is
formalized here is its multivariate form, over a finite variable type `σ`, which is what the
`n`-variable Noether normalization downstream needs. The mathematical content of each step is
Stacks'; the passage to several variables at once is not, and is not claimed as such below.
-/

public section

namespace TauCeti

/-- Every monomial lies in the span, over the image of `MvPolynomial.expand n`, of the monomials
with all exponents below `n`: write each exponent as `n * γ + β` with `β < n`, so that
`X ^ (n • γ + β) = expand n (X ^ γ) * X ^ β`. -/
private theorem MvPolynomial.monomial_mem_span_monomial_lt {σ R : Type*} [CommSemiring R]
    [Finite σ]
    {n : ℕ} (hn : 0 < n) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.monomial d r ∈
      Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
        (Set.range fun β : σ → Fin n =>
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) := by
  classical
  -- the exponent `d i` splits as `n * (d i / n) + d i % n`
  have hexp :
      n • (Finsupp.equivFunOnFinite.symm fun i => d i / n)
        + (Finsupp.equivFunOnFinite.symm fun i =>
            ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) = d := by
    ext i
    simp [Nat.div_add_mod]
  -- the sub-`n` part is one of the generators
  have hmem :
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i =>
          ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) (1 : R) ∈
        Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
          (Set.range fun β : σ → Fin n =>
            MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) :=
    Submodule.subset_span ⟨fun i => ⟨d i % n, Nat.mod_lt _ hn⟩, rfl⟩
  -- name the scalar, so that the `•`/`*` defeq check stays cheap
  obtain ⟨a, ha⟩ : ∃ a : (MvPolynomial.expand (σ := σ) (R := R) n).range,
      (a : MvPolynomial σ R)
        = (MvPolynomial.expand (σ := σ) (R := R) n)
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => d i / n) r) :=
    ⟨⟨_, AlgHom.mem_range_self _ _⟩, rfl⟩
  have key : (MvPolynomial.monomial d r : MvPolynomial σ R)
      = (MvPolynomial.expand (σ := σ) (R := R) n)
            (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => d i / n) r) *
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i =>
            ((⟨d i % n, Nat.mod_lt _ hn⟩ : Fin n) : ℕ)) (1 : R) := by
    rw [MvPolynomial.expand_monomial, MvPolynomial.monomial_mul_monomial, mul_one, hexp]
  rw [key, ← ha]
  exact Submodule.smul_mem _ a hmem

/-- Over the image of `MvPolynomial.expand n`, the finitely many monomials with all exponents
below `n` span the whole polynomial ring. -/
theorem MvPolynomial.span_monomial_lt_eq_top {σ R : Type*} [CommSemiring R] [Finite σ] {n : ℕ}
    (hn : 0 < n) :
    Submodule.span (MvPolynomial.expand (σ := σ) (R := R) n).range
      (Set.range fun β : σ → Fin n =>
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (β i : ℕ)) (1 : R)) = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  exact MvPolynomial.induction_on' f (fun d r => MvPolynomial.monomial_mem_span_monomial_lt hn d r)
    (fun p q hp hq => Submodule.add_mem _ hp hq)

/-- `MvPolynomial.expand n` is a finite ring map for `0 < n`: the polynomial ring is spanned over
`R[X_i ^ n]` by the monomials with exponents below `n`. -/
theorem MvPolynomial.finite_expand {σ R : Type*} [CommRing R] [Finite σ] {n : ℕ} (hn : 0 < n) :
    (MvPolynomial.expand (σ := σ) (R := R) n).toRingHom.Finite := by
  classical
  -- `MvPolynomial σ R` is a finite module over the subalgebra `R[X_i ^ n]`
  have hfin : Module.Finite (MvPolynomial.expand (σ := σ) (R := R) n).range
      (MvPolynomial σ R) :=
    Module.Finite.of_fg_top (Submodule.fg_def.2 ⟨_, Set.finite_range _,
      MvPolynomial.span_monomial_lt_eq_top hn⟩)
  -- Factor `expand n` as `R[X_i] ↠ R[X_i ^ n] ↪ R[X_i]`. Going through the range keeps the
  -- `Module (MvPolynomial σ R) (MvPolynomial σ R)` diamond out of the way: instance search
  -- picks `Semiring.toModule` (plain multiplication), not the `expand`-algebra the statement
  -- means, and the two are not defeq.
  have h₁ : ((MvPolynomial.expand (σ := σ) (R := R) n).rangeRestrict.toRingHom).Finite :=
    RingHom.Finite.of_surjective _ (AlgHom.rangeRestrict_surjective _)
  have h₂ : ((MvPolynomial.expand (σ := σ) (R := R) n).range.val.toRingHom).Finite := hfin
  -- from Mathlib's `(Subalgebra.val _).comp φ.rangeRestrict = φ`, rather than by `rfl`, so the
  -- factorisation does not depend on how bundled-hom composition happens to be implemented
  have hfac : (MvPolynomial.expand (σ := σ) (R := R) n).toRingHom
      = ((MvPolynomial.expand (σ := σ) (R := R) n).range.val.toRingHom).comp
        ((MvPolynomial.expand (σ := σ) (R := R) n).rangeRestrict.toRingHom) :=
    congrArg AlgHom.toRingHom
      (MvPolynomial.expand (σ := σ) (R := R) n).val_comp_rangeRestrict.symm
  rw [hfac]
  exact RingHom.Finite.comp h₂ h₁

/-- If every coefficient of `g` has a `p ^ n`-th root in `S`, then `g(X ^ (p ^ n))`, read in
`S[X_i]`, is a `p ^ n`-th power. -/
theorem MvPolynomial.exists_pow_eq_map_expand {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : ℕ) [ExpChar S p] (n : ℕ) {g : MvPolynomial σ R}
    (hg : ∀ i ∈ g.support, ∃ d : S, d ^ p ^ n = f (g.coeff i)) :
    ∃ h : MvPolynomial σ S, h ^ p ^ n = MvPolynomial.map f (MvPolynomial.expand (p ^ n) g) := by
  classical
  -- total-ise the choice of roots, so the witness is a plain sum over `g.support`
  have hg' : ∀ i : σ →₀ ℕ, ∃ d : S, i ∈ g.support → d ^ p ^ n = f (g.coeff i) := by
    intro i
    by_cases hi : i ∈ g.support
    · obtain ⟨d, hd⟩ := hg i hi
      exact ⟨d, fun _ ↦ hd⟩
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose d hd using hg'
  refine ⟨∑ α ∈ g.support, MvPolynomial.monomial α (d α), ?_⟩
  -- the chosen-root polynomial maps under the iterated Frobenius to `map f g`
  have hmap : MvPolynomial.map (iterateFrobenius S p n)
      (∑ α ∈ g.support, MvPolynomial.monomial α (d α)) = MvPolynomial.map f g := by
    rw [map_sum]
    conv_rhs => rw [MvPolynomial.as_sum g]
    rw [map_sum]
    refine Finset.sum_congr rfl fun α hα ↦ ?_
    rw [MvPolynomial.map_monomial, MvPolynomial.map_monomial, iterateFrobenius_def, hd α hα]
  -- so Mathlib's Frobenius/expand identity supplies the power, with `map_expand` moving `map`
  -- past `expand` on each side
  rw [← MvPolynomial.map_iterateFrobenius_expand (p := p) _ n, MvPolynomial.map_expand, hmap,
    ← MvPolynomial.map_expand]

end TauCeti
