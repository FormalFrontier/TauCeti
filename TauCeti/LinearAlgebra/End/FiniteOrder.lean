/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Semisimple

/-!
# Endomorphisms of finite order

An endomorphism `f` of a vector space with `f ^ n = 1` is annihilated by `X ^ n - 1`. Two
consequences are recorded here: every root of its characteristic polynomial is an `n`-th root of
unity, and if `n` is invertible in the coefficient field then `f` is semisimple, because `X ^ n - 1`
is then squarefree.

## Main results

* `TauCeti.pow_eq_one_of_isRoot_charpoly`: the roots of the characteristic polynomial of an
  endomorphism of finite order `n` are `n`-th roots of unity.
* `TauCeti.isSemisimple_of_pow_eq_one`: an endomorphism of finite order `n`, with `n` invertible in
  the field, is semisimple.
-/

public section

namespace TauCeti

open Module Polynomial

universe u w

variable {k : Type u} {V : Type w} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

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

omit [FiniteDimensional k V] in
/-- An endomorphism `f` with `f ^ n = 1` for some `n` invertible in `k` is semisimple, because it
is annihilated by the squarefree polynomial `X ^ n - 1`. -/
theorem isSemisimple_of_pow_eq_one {f : End k V} {n : ℕ} (hn : (n : k) ≠ 0) (hf : f ^ n = 1) :
    f.IsSemisimple := by
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ n - 1) ?_ ?_
  · simpa using (Polynomial.separable_X_pow_sub_C (1 : k) hn one_ne_zero).squarefree
  · simp [hf]

end TauCeti
