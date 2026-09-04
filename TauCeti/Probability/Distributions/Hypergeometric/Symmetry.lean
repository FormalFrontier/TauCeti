/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic

/-!
# Symmetry of the hypergeometric distribution

The hypergeometric law is unchanged when the number of marked population elements and the sample
size are exchanged. Combinatorially, both descriptions count the size of the intersection of a
fixed `K`-element subset and a uniformly chosen `n`-element subset of an `N`-element population.

## Main result

* `TauCeti.Probability.hypergeometricMeasure_comm` — exchanging the marked count and sample size
  leaves the hypergeometric measure unchanged.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

/-- Exchanging the marked count and the sample size leaves the hypergeometric law unchanged. -/
theorem hypergeometricMeasure_comm (N K n : ℕ) :
    hypergeometricMeasure N K n = hypergeometricMeasure N n K := by
  by_cases hvalid : K ≤ N ∧ n ≤ N
  · obtain ⟨hK, hn⟩ := hvalid
    -- The valid laws are finite, so on the countable carrier it suffices to compare their real
    -- singleton masses. The explicit mass formulas isolate all totalized-subtraction cases.
    let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
    let _ := isProbabilityMeasure_hypergeometricMeasure hn hK
    refine Measure.ext_of_measureReal_singleton fun k ↦ ?_
    rw [hypergeometricMeasure_real_singleton hK hn,
      hypergeometricMeasure_real_singleton hn hK]
    by_cases hkK : k ≤ K <;> by_cases hkn : k ≤ n
    · simp only [ite_eq_left hkK, ite_eq_left hkn]
      by_cases hsupport : n - k ≤ N - K
      · have hsupport' : K - k ≤ N - n := by omega
        have hsubK : (N - k) - (K - k) = N - K := by omega
        have hsubn : (N - k) - (n - k) = N - n := by omega
        have hsubLeft : K - k + (n - k) - (K - k) = n - k := by omega
        have hsubRight : K - k + (n - k) - (n - k) = K - k := by omega
        have hmiddle :
            (N - k).choose (K - k) * (N - K).choose (n - k) =
              (N - k).choose (n - k) * (N - n).choose (K - k) := by
          -- After the `k` common elements are fixed, choose the marked-only and sampled-only
          -- elements in either order. Both sides are the same multinomial coefficient.
          calc
            _ = (N - k).choose (K - k) *
                ((N - k) - (K - k)).choose (K - k + (n - k) - (K - k)) := by
              rw [hsubK, hsubLeft]
            _ = (N - k).choose (K - k + (n - k)) *
                (K - k + (n - k)).choose (K - k) := by
              rw [Nat.choose_mul (n := N - k) (k := K - k + (n - k))
                (s := K - k) (by omega)]
            _ = (N - k).choose (K - k + (n - k)) *
                (K - k + (n - k)).choose (n - k) := by
              rw [Nat.choose_symm_add]
            _ = (N - k).choose (n - k) *
                ((N - k) - (n - k)).choose (K - k + (n - k) - (n - k)) := by
              rw [Nat.choose_mul (n := N - k) (k := K - k + (n - k))
                (s := n - k) (by omega)]
            _ = _ := by rw [hsubn, hsubRight]
        have hchooseK := Nat.choose_mul (n := N) (k := K) (s := k) hkK
        have hchoosen := Nat.choose_mul (n := N) (k := n) (s := k) hkn
        -- Cross-multiply the two mass formulas. The outer applications of `Nat.choose_mul`
        -- choose the common `k` elements first; `hmiddle` exchanges the remaining choices.
        have hcross :
            K.choose k * (N - K).choose (n - k) * N.choose K =
              n.choose k * (N - n).choose (K - k) * N.choose n := by
          calc
            _ = (N.choose K * K.choose k) * (N - K).choose (n - k) := by ring
            _ = (N.choose k * (N - k).choose (K - k)) *
                (N - K).choose (n - k) := by rw [hchooseK]
            _ = N.choose k * ((N - k).choose (K - k) *
                (N - K).choose (n - k)) := by ring
            _ = N.choose k * ((N - k).choose (n - k) *
                (N - n).choose (K - k)) := by rw [hmiddle]
            _ = (N.choose n * n.choose k) * (N - n).choose (K - k) := by
              rw [hchoosen]
              ring
            _ = _ := by ring
        rw [div_eq_div_iff]
        · exact_mod_cast hcross
        · exact_mod_cast Nat.choose_ne_zero hn
        · exact_mod_cast Nat.choose_ne_zero hK
      · have hsupport' : ¬ K - k ≤ N - n := by omega
        -- Failure of the remaining-support inequality is symmetric, so both masses vanish.
        rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hsupport),
          Nat.choose_eq_zero_of_lt (lt_of_not_ge hsupport')]
        simp
    · simp [hkK, hkn, Nat.choose_eq_zero_of_lt (lt_of_not_ge hkn)]
    · simp [hkK, hkn, Nat.choose_eq_zero_of_lt (lt_of_not_ge hkK)]
    · simp [hkK, hkn]
  · rw [hypergeometricMeasure_eq_zero_of_invalid hvalid,
      hypergeometricMeasure_eq_zero_of_invalid (by simpa [and_comm] using hvalid)]

end Probability

end TauCeti
