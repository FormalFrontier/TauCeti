/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Radical.Basic

/-!
# The monic irreducible factors of a polynomial over a field

For a polynomial `f` over a field `K`, `Polynomial.Factors f` is the type of its distinct monic
irreducible factors: the subtype of `K[X]` cut out by `Irreducible p ∧ p.Monic ∧ p ∣ f`. Working
with this subtype rather than with `normalizedFactors f` keeps `DecidableEq K` out of the
statements; the two are compared by Mathlib's `Polynomial.mem_normalizedFactors_iff`, whose
conjunct order the predicate above follows.

The factors are pairwise coprime, and when `f` is nonzero and squarefree their product is
associated to `f`, so the ideal `(f)` is the intersection of the ideals `(p)`. That is the input
for the Chinese Remainder decomposition of `K[X] ⧸ (f)` into the fields `K[X] ⧸ (p)`.

## Main definitions

* `Polynomial.Factors`: the distinct monic irreducible factors of `f`, as a type.
* `Polynomial.Factors.linearEquivRoots`: the linear factors correspond to the roots of `f`, with
  `linearEquivRoots_apply` and `linearEquivRoots_symm_apply` computing both directions.

## Main results

* `Polynomial.Factors.finite`: a nonzero polynomial has finitely many factors.
* `Polynomial.Factors.isCoprime`: distinct factors are coprime.
* `Polynomial.Factors.span_eq_iInf_span`: for `f` nonzero and squarefree,
  `(f) = ⨅ p, (p)`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil): the `2`-descent of the weak
Mordell–Weil theorem works with the étale algebra `K[X] ⧸ (f)` of a Weierstrass cubic `f`, which it
splits into fields along the monic irreducible factors of `f`; this file is that index type and the
coprimality that makes the splitting a Chinese Remainder decomposition. Nothing here mentions a
curve, so it is stated for an arbitrary polynomial over a field.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `EtaleDecomposition`. The source is written against
Lean `v4.32.0`; this is a forward port.
-/

public section

namespace Polynomial

open UniqueFactorizationMonoid

variable {K : Type*} [Field K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

This is *not* defined via `normalizedFactors` (which would require `DecidableEq K`); the
predicate is spelled in the order of `Polynomial.mem_normalizedFactors_iff`, which is therefore
the characterization of membership in `normalizedFactors f`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // Irreducible p ∧ p.Monic ∧ p ∣ f}

namespace Factors

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.1

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2

lemma ne_zero (p : f.Factors) : (p : K[X]) ≠ 0 := p.irreducible.ne_zero

lemma prime (p : f.Factors) : Prime (p : K[X]) := p.irreducible.prime

lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd

lemma finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact .of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (Polynomial.mem_normalizedFactors_iff hf).mpr hp).injective

lemma nonempty (hu : ¬ IsUnit f) : Nonempty f.Factors :=
  let ⟨p, hmonic, hirr, hdvd⟩ := f.exists_monic_irreducible_factor hu
  ⟨⟨p, hirr, hmonic, hdvd⟩⟩

/-- The monic linear factors of `f` correspond to the roots of `f`. -/
noncomputable def linearEquivRoots :
    {p : f.Factors // (p : K[X]).natDegree = 1} ≃ {x : K // f.eval x = 0} where
  toFun p := ⟨-((p : f.Factors) : K[X]).coeff 0,
    eval_eq_zero_of_dvd_of_eval_eq_zero (p : f.Factors).dvd <| by
      conv_lhs => rw [(p : f.Factors).monic.eq_X_add_C p.2]
      simp⟩
  invFun x := ⟨⟨X - C (x : K), irreducible_X_sub_C _, monic_X_sub_C _,
    dvd_iff_isRoot.mpr x.2⟩, natDegree_X_sub_C _⟩
  left_inv p := by
    refine Subtype.ext (Subtype.ext ?_)
    -- `invFun (toFun p)` is the monic linear polynomial with the recorded root; the `change`
    -- only replaces it by that polynomial, which is how `invFun` is defined.
    change X - C (-((p : f.Factors) : K[X]).coeff 0) = _
    conv_rhs => rw [(p : f.Factors).monic.eq_X_add_C p.2]
    rw [map_neg, sub_neg_eq_add]
  right_inv x := by
    refine Subtype.ext ?_
    -- likewise `toFun (invFun x)` is by definition the negated constant coefficient of
    -- `X - C x`, which is what the `change` displays.
    change -(X - C (x : K)).coeff 0 = _
    simp

/-- `linearEquivRoots` sends a monic linear factor to the root it records, the negated constant
coefficient. -/
@[simp]
lemma linearEquivRoots_apply (p : {p : f.Factors // (p : K[X]).natDegree = 1}) :
    (linearEquivRoots p : K) = -((p : f.Factors) : K[X]).coeff 0 :=
  (rfl)

/-- `linearEquivRoots.symm` sends a root `x` to the monic linear factor `X - C x`. -/
@[simp]
lemma linearEquivRoots_symm_apply (x : {x : K // f.eval x = 0}) :
    ((linearEquivRoots.symm x : f.Factors) : K[X]) = X - C (x : K) :=
  (rfl)

/-- Distinct monic irreducible factors of `f` are coprime: each spans a maximal ideal, and the
two ideals differ because a monic polynomial is determined by the ideal it spans. -/
lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
    Ideal.IsMaximal.coprime_of_ne
      (PrincipalIdealRing.isMaximal_of_irreducible p.irreducible)
      (PrincipalIdealRing.isMaximal_of_irreducible q.irreducible)
      fun h ↦ hne <| Subtype.ext <| eq_of_monic_of_associated p.monic q.monic <|
        Ideal.span_singleton_eq_span_singleton.mp h

lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

/-- A nonzero squarefree polynomial is associated to the product of its distinct monic
irreducible factors. -/
lemma associated_prod [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  -- identify `f.Factors` with the subtype of the `Finset` of normalized factors
  have hprod : ∏ p : f.Factors, (p : K[X]) =
      ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun p ↦ by
        rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hf]) _ _
      fun x ↦ by rw [Equiv.subtypeEquivRight_apply]
  have hcoe : ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) =
      ∏ p ∈ (normalizedFactors f).toFinset, p :=
    Finset.prod_coe_sort _ fun x ↦ x
  rw [hprod, hcoe, toFinset_normalizedFactors]
  exact radical_associated hsq.isRadical hf

/-- The degrees of the distinct monic irreducible factors of `f ≠ 0` sum to at most the
degree of `f`. -/
lemma sum_natDegree_le [Fintype f.Factors] (hf : f ≠ 0) :
    ∑ p : f.Factors, (p : K[X]).natDegree ≤ f.natDegree := by
  rw [← natDegree_prod _ _ fun p _ ↦ p.ne_zero]
  exact natDegree_le_of_dvd
    (Fintype.prod_dvd_of_coprime (fun p q hpq ↦ isCoprime hpq) fun p ↦ p.dvd) hf

/-- For `f` nonzero and squarefree, the ideal `(f)` is the intersection of the ideals `(p)` over
the monic irreducible factors `p` of `f`. This is the input for the Chinese Remainder
decomposition of `K[X] ⧸ (f)`. -/
lemma span_eq_iInf_span (hf : f ≠ 0) (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have : Fintype f.Factors := @Fintype.ofFinite _ (finite hf)
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hf hsq)).symm

end Factors

end Polynomial

end
