/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Limits of binomial coefficients along proportional sequences

For fixed `k`, the leading term of `a.choose k` is `a ^ k / k!`. This file records the
corresponding limit when `a` and the normalizing denominator vary together: if `a i / b i`
converges to `x` and `b i⁻¹` converges to zero, then

```text
  (a i).choose k / (b i) ^ k → x ^ k / k!.
```

The statement includes boundary limits such as `x = 0`; no divergence hypothesis on `a` is
needed. It is useful for finite-population limits, where one of a population and its complement
may stay bounded.

## Main result

* `TauCeti.tendsto_choose_div_pow_of_tendsto_div` — the normalized fixed-order binomial
  coefficient along an asymptotically proportional sequence.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

/-- A fixed-order binomial coefficient has its expected leading-term limit along any sequence
whose ratio to a common denominator converges.

The separate hypothesis that the inverse denominator tends to zero makes the statement applicable
to denominators other than the natural index. -/
theorem tendsto_choose_div_pow_of_tendsto_div {α : Type*} {l : Filter α} {a : α → ℕ}
    {b : α → ℝ} {x : ℝ}
    (hab : Tendsto (fun i ↦ (a i : ℝ) / b i) l (nhds x))
    (hb : Tendsto (fun i ↦ (b i)⁻¹) l (nhds 0)) (k : ℕ) :
    Tendsto (fun i ↦ ((a i).choose k : ℝ) / (b i) ^ k) l
      (nhds (x ^ k / (k.factorial : ℝ))) := by
  have hfactor (j : ℕ) :
      Tendsto (fun i ↦ (a i : ℝ) / b i - (j : ℝ) / b i) l (nhds x) := by
    have hj : Tendsto (fun i ↦ (j : ℝ) / b i) l (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul hb :
          Tendsto (fun i ↦ (j : ℝ) * (b i)⁻¹) l (nhds ((j : ℝ) * 0)))
    simpa only [sub_zero] using hab.sub hj
  have hprod :
      Tendsto (fun i ↦ ∏ j ∈ Finset.range k,
        ((a i : ℝ) / b i - (j : ℝ) / b i)) l (nhds (x ^ k)) := by
    simpa using tendsto_finsetProd (Finset.range k) fun j _ ↦ hfactor j
  refine Tendsto.congr' (Eventually.of_forall fun i ↦ ?_) (hprod.div_const (k.factorial : ℝ))
  symm
  dsimp only
  rw [Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range]
  simp_rw [← sub_div]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  ring

end TauCeti
