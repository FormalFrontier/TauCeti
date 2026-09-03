/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.PowerBounded
public import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# A continuous archimedean valuation is bounded by one on the power-bounded elements

**Wedhorn Proposition 7.41.** If `v` is a continuous valuation whose value group is
archimedean, and some topologically nilpotent `b` has `v b ≠ 0`, then `v a ≤ 1` for every
power-bounded `a`.

The two hypotheses on `v` are what Wedhorn's `x ∈ Cont(A)ᵃ of height 1` supplies. The
archimedean condition is imposed on the **value group** `MonoidWithZeroHom.ValueGroup₀ v`, not on
the codomain, which is what Mathlib's `Valuation.nonempty_rankOne_iff_mulArchimedean` actually
yields from height one; a caller who happens to have an archimedean codomain gets the instance by
`MulArchimedean.comap embedding.toMonoidHom embedding_strictMono`. The archimedean step therefore
runs in `Γ_v` and transports back along the strictly monotone embedding. Analyticity gives the
topologically nilpotent `b` with `v b ≠ 0`, which is Wedhorn's Remark 7.40(1).

The argument is Wedhorn's. Suppose `1 < v a`. Archimedeanness gives `n` with
`(v b)⁻¹ ≤ v a ^ n`, hence `1 ≤ v (a ^ n * b)`. But `a ^ n` is power-bounded and `b` is
topologically nilpotent, so `a ^ n * b` is topologically nilpotent, and continuity forces
`v (a ^ n * b) < 1`. The two bounds are incompatible, so no such `a` exists.

## Main results

* `Valuation.IsContinuous.le_one_of_isPowerBounded`: Proposition 7.41. Stated in the
  `Valuation.IsContinuous` namespace so it is reachable by dot notation on the continuity
  hypothesis, alongside `Valuation.IsContinuous.lt_one_of_isTopologicallyNilpotent`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.41, whose proof
  this follows step by step, together with Remark 7.40(1) for the witness `b` and Proposition
  1.14 for height one implying archimedean.
-/

public section

namespace Valuation

open TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Wedhorn Proposition 7.41.** A continuous valuation whose value group is archimedean, and
which is nonzero on some topologically nilpotent element, is bounded by `1` on the power-bounded
elements.

The archimedean hypothesis is on the value group, which is what height one supplies; an
archimedean codomain gives it by `MulArchimedean.comap`.

The witness `b` is what analyticity supplies (Wedhorn Remark 7.40(1)), and it is not removable.
Give a *reduced* `A` the discrete topology: every element is then power-bounded, every valuation
is continuous (`Valuation.isContinuous_of_discreteTopology`), and a power of `x` vanishes only if
`x` does, so `0` is the sole topologically nilpotent element and no witness exists. Discrete `ℚ`
carrying a `p`-adic valuation is such an `A`, and there `1 < v p⁻¹` refutes the conclusion. -/
theorem IsContinuous.le_one_of_isPowerBounded {v : Valuation A Γ₀}
    [MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))] (hv : v.IsContinuous)
    {b : A} (hb : IsTopologicallyNilpotent b) (hb0 : v b ≠ 0) {a : A}
    (ha : IsPowerBounded a) : v a ≤ 1 := by
  by_contra! hgt
  -- archimedeanness of the value group `Γ_v`: some power of `v a` overtakes `(v b)⁻¹` there
  have hgt' : 1 < v.restrict a := by
    refine MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt.mp ?_
    simpa only [map_one, embedding_restrict] using hgt
  obtain ⟨n, hn'⟩ := MulArchimedean.arch (v.restrict b)⁻¹ hgt'
  -- transport the comparison back to `Γ₀` along the strictly monotone embedding
  have hn : (v b)⁻¹ ≤ v a ^ n := by
    simpa only [map_pow, map_inv₀, embedding_restrict] using
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.le_iff_le.mpr hn'
  -- so `a ^ n * b` has value at least `1`
  have hab : (1 : Γ₀) ≤ v (a ^ n * b) := by
    rw [map_mul, map_pow, ← inv_mul_cancel₀ hb0]
    exact mul_le_mul' hn le_rfl
  -- but it is topologically nilpotent, and a continuous valuation is `< 1` there
  exact absurd hab (not_le.mpr (hv.lt_one_of_isTopologicallyNilpotent
    ((ha.pow n).isTopologicallyNilpotent_mul hb)))

end Valuation
