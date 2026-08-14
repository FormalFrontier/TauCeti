/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Endomorphisms of finite order

An endomorphism `f` of a vector space with `f ^ n = 1` is annihilated by `X ^ n - 1`. Two
consequences are recorded here: every root of its characteristic polynomial is an `n`-th root of
unity, and if `n` is invertible in the coefficient field then `f` is semisimple, because `X ^ n - 1`
is then squarefree.

The roots of unity are algebraic integers, so as soon as the characteristic polynomial splits the
trace, being the sum of those roots, is one too. Splitting is not a real hypothesis: base change to
an algebraic closure leaves the trace alone beyond transporting it along the field embedding
(`LinearMap.trace_baseChange`), and an element of the base field whose image is integral over `ℤ`
was already integral over `ℤ`. So the trace of an endomorphism of finite order is an algebraic
integer over **any** field.

Over an algebraically closed field semisimplicity is diagonalizability, so the eigenspaces of such
an `f` decompose the space. Every power of `f` acts on the `μ`-eigenspace as the scalar `μ ^ m`,
which turns the trace of `f ^ m` into the sum `∑ μ, dim(V_μ) * μ ^ m` over the eigenvalues.

That sum is what makes the trace transform predictably under a ring endomorphism `σ` of the
coefficient field: the dimensions are natural numbers and so are fixed by `σ`, so if `σ` raises
every `n`-th root of unity to the `j`-th power then `σ (tr f) = tr (f ^ j)`. Over `ℂ` complex
conjugation is such a `σ`, with `j = n - 1`, since it sends a root of unity `μ` to
`μ⁻¹ = μ ^ (n - 1)`; that instance is the source of `conj (χ g) = χ g⁻¹` for characters of complex
representations.

All the results are stated of `Module.End`, so they sit in the `End` namespace under `open Module`.

## Main results

* `TauCeti.End.pow_eq_one_of_isRoot_charpoly`: the roots of the characteristic polynomial of
  an endomorphism of finite order `n` are `n`-th roots of unity.
* `TauCeti.End.isSemisimple_of_pow_eq_one`: an endomorphism of finite order `n`, with `n`
  invertible in the field, is semisimple.
* `TauCeti.End.isIntegral_trace_of_pow_eq_one`: over any field, the trace of an endomorphism of
  finite order is integral over `ℤ`.
* `TauCeti.End.trace_pow_eq_sum_eigenvalue_pow`: over an algebraically closed field, the trace of
  `f ^ m` is the sum of the `m`-th powers of the eigenvalues of `f`, weighted by the dimensions of
  the eigenspaces.
* `TauCeti.End.map_trace_eq_trace_pow`: a ring endomorphism raising every `n`-th root of unity to
  the `j`-th power sends the trace of an endomorphism of finite order `n` to the trace of its
  `j`-th power.
* `TauCeti.End.conj_trace_eq_trace_pow_sub_one`: over `ℂ`, the conjugate of the trace of an
  endomorphism of finite order `n` is the trace of its inverse `f ^ (n - 1)`.
-/

public section

namespace TauCeti

open Module Polynomial

universe u w

variable {k : Type u} {V : Type w} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

namespace End

/-- Every root of the characteristic polynomial of an endomorphism `f` with `f ^ n = 1` is an
`n`-th root of unity. -/
theorem pow_eq_one_of_isRoot_charpoly {f : End k V} {n : ℕ} (hf : f ^ n = 1) {μ : k}
    (hμ : f.charpoly.IsRoot μ) : μ ^ n = 1 := by
  have hspec : μ ∈ spectrum k f := (End.mem_spectrum_iff_isRoot_charpoly f μ).2 hμ
  rcases subsingleton_or_nontrivial (End k V) with _ | _
  · exact absurd (isUnit_of_subsingleton _) (spectrum.mem_iff.mp hspec)
  · have hpow := spectrum.pow_mem_pow f n hspec
    rw [hf, spectrum.one_eq] at hpow
    simpa using hpow

/-- The trace of an endomorphism of finite order is an algebraic integer once its characteristic
polynomial splits: the trace is then the sum of the roots, and each of those is an `n`-th root of
unity. This is the splitting case of `TauCeti.End.isIntegral_trace_of_pow_eq_one`, which subsumes
it, so it stays private. -/
private theorem isIntegral_trace_of_pow_eq_one_of_splits {f : End k V} {n : ℕ} (hn : n ≠ 0)
    (hf : f ^ n = 1) (hsplits : f.charpoly.Splits) : IsIntegral ℤ (LinearMap.trace k V f) := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits]
  refine IsIntegral.multiset_sum fun μ hμ => IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
  rw [pow_eq_one_of_isRoot_charpoly hf (isRoot_of_mem_roots hμ)]
  exact isIntegral_one

/-- **The trace of an endomorphism of finite order is an algebraic integer**, over an arbitrary
field. When the characteristic polynomial splits the trace is a sum of roots of unity; that
splitting hypothesis is removed by base change to an algebraic closure, which preserves both the
order of `f` and, up to the field embedding, its trace, and an element of `k` whose image in the
closure is integral over `ℤ` is itself integral over `ℤ`. -/
theorem isIntegral_trace_of_pow_eq_one {f : End k V} {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace k V f) := by
  have hbase : f.baseChange (AlgebraicClosure k) ^ n = 1 := by
    rw [← LinearMap.baseChange_pow, hf, LinearMap.baseChange_one]
  have hint := isIntegral_trace_of_pow_eq_one_of_splits (k := AlgebraicClosure k) hn hbase
    (IsAlgClosed.splits _)
  rw [LinearMap.trace_baseChange] at hint
  exact hint.tower_bot (algebraMap k (AlgebraicClosure k)).injective

omit [FiniteDimensional k V] in
/-- An endomorphism `f` with `f ^ n = 1` for some `n` invertible in `k` is semisimple, because it
is annihilated by the squarefree polynomial `X ^ n - 1`. -/
theorem isSemisimple_of_pow_eq_one {f : End k V} {n : ℕ} (hn : (n : k) ≠ 0) (hf : f ^ n = 1) :
    f.IsSemisimple := by
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ n - 1) ?_ ?_
  · simpa using (Polynomial.separable_X_pow_sub_C (1 : k) hn one_ne_zero).squarefree
  · simp [hf]

section Eigenspace

variable {f : End k V} {n : ℕ}

omit [FiniteDimensional k V] in
/-- Every power of `f` maps each eigenspace of `f` to itself, acting there as the scalar `μ ^ m`. -/
theorem mapsTo_pow_eigenspace (f : End k V) (μ : k) (m : ℕ) :
    Set.MapsTo (f ^ m) (f.eigenspace μ) (f.eigenspace μ) := fun x hx => by
  have hx' : (f ^ m) x = μ ^ m • x := by
    simpa using End.aeval_apply_of_mem_apply_eq_smul (p := X ^ m) (End.mem_eigenspace_iff.1 hx)
  rw [SetLike.mem_coe, hx']
  exact Submodule.smul_mem _ _ hx

/-- The trace of `f ^ m` on the `μ`-eigenspace of `f` is `dim(V_μ) * μ ^ m`, because `f ^ m` acts
there as the scalar `μ ^ m`. -/
theorem trace_restrict_eigenspace (f : End k V) (μ : k) (m : ℕ) :
    LinearMap.trace k _ ((f ^ m).restrict (mapsTo_pow_eigenspace f μ m)) =
      (finrank k (f.eigenspace μ) : k) * μ ^ m := by
  have hrestrict : (f ^ m).restrict (mapsTo_pow_eigenspace f μ m) = μ ^ m • LinearMap.id := by
    ext x
    refine (LinearMap.coe_restrict_apply _ x).trans ?_
    simpa using End.aeval_apply_of_mem_apply_eq_smul (p := X ^ m) (End.mem_eigenspace_iff.1 x.2)
  rw [hrestrict, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

/-- Every eigenvalue of an endomorphism of finite order `n` is an `n`-th root of unity. -/
theorem pow_eq_one_of_hasEigenvalue (hf : f ^ n = 1) {μ : k} (hμ : f.HasEigenvalue μ) :
    μ ^ n = 1 :=
  pow_eq_one_of_isRoot_charpoly hf
    ((End.mem_spectrum_iff_isRoot_charpoly f μ).1 (End.hasEigenvalue_iff_mem_spectrum.1 hμ))

variable [IsAlgClosed k]

open scoped Classical in
/-- **The eigenspaces of an endomorphism of finite order decompose the space**, `n` being invertible
in the algebraically closed field `k`: such an `f` is semisimple, hence diagonalizable. -/
theorem isInternal_eigenspace_of_pow_eq_one (hn : (n : k) ≠ 0) (hf : f ^ n = 1) :
    DirectSum.IsInternal f.eigenspace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep
    (isSemisimple_of_pow_eq_one hn hf).iSup_eigenspace_eq_top

/-- **The trace of a power of an endomorphism of finite order is the weighted sum of the powers of
its eigenvalues**: `tr (f ^ m) = ∑ μ, dim(V_μ) * μ ^ m`, the sum being over the eigenvalues of `f`.
The hypothesis `(n : k) ≠ 0` makes `f` diagonalizable, so that the eigenspaces already exhaust the
space. -/
theorem trace_pow_eq_sum_eigenvalue_pow (hn : (n : k) ≠ 0) (hf : f ^ n = 1) (m : ℕ) :
    LinearMap.trace k V (f ^ m) =
      ∑ μ ∈ (End.finite_hasEigenvalue f).toFinset, (finrank k (f.eigenspace μ) : k) * μ ^ m := by
  classical
  rw [LinearMap.trace_eq_sum_trace_restrict' (isInternal_eigenspace_of_pow_eq_one hn hf)
    (End.finite_hasEigenvalue f) (mapsTo_pow_eigenspace f · m)]
  exact Finset.sum_congr rfl fun μ _ => trace_restrict_eigenspace f μ m

/-- **A ring endomorphism raising the roots of unity to the `j`-th power raises an endomorphism of
finite order to the `j`-th power, as far as the trace can see**: if `f ^ n = 1` and `σ μ = μ ^ j`
for every `n`-th root of unity `μ`, then `σ (tr f) = tr (f ^ j)`. Both sides are the sum
`∑ μ, dim(V_μ) · μ ^ j` over the eigenvalues, since a ring homomorphism fixes the dimensions,
which enter as natural numbers. -/
theorem map_trace_eq_trace_pow {j : ℕ} (hn : (n : k) ≠ 0) (hf : f ^ n = 1) (σ : k →+* k)
    (hσ : ∀ μ : k, μ ^ n = 1 → σ μ = μ ^ j) :
    σ (LinearMap.trace k V f) = LinearMap.trace k V (f ^ j) := by
  conv_lhs => rw [← pow_one f]
  rw [trace_pow_eq_sum_eigenvalue_pow hn hf 1, trace_pow_eq_sum_eigenvalue_pow hn hf j, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [map_mul, map_natCast, pow_one,
    hσ μ (pow_eq_one_of_hasEigenvalue hf ((End.finite_hasEigenvalue f).mem_toFinset.1 hμ))]

end Eigenspace

section Complex

variable {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Complex conjugation of the trace inverts the endomorphism.** If `f ^ n = 1` with `n ≠ 0`, then
the conjugate of the trace of `f` is the trace of its inverse `f ^ (n - 1)`: the eigenvalues of `f`
are `n`-th roots of unity, and conjugation inverts those. -/
theorem conj_trace_eq_trace_pow_sub_one {f : End ℂ V} {n : ℕ} (hn : n ≠ 0) (hf : f ^ n = 1) :
    (starRingEnd ℂ) (LinearMap.trace ℂ V f) = LinearMap.trace ℂ V (f ^ (n - 1)) :=
  map_trace_eq_trace_pow (Nat.cast_ne_zero.2 hn) hf (starRingEnd ℂ) fun μ hμ => by
    rw [← Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hμ hn)]
    exact inv_eq_of_mul_eq_one_right
      (by rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn), hμ])

end Complex

end End

end TauCeti
