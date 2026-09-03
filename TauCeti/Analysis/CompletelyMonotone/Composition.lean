/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
public import TauCeti.Analysis.CompletelyMonotone.OpenClosure

/-!
# Composing completely monotone and Bernstein functions

This file proves the composition closure property called for by the `OneParameterSemigroups`
roadmap, Part B: if `g` is completely monotone and `f` is a Bernstein function, then `g ∘ f` is
again completely monotone. Two companions come out of the same argument: Bernstein functions are
closed under composition, and the prototype `t ↦ e^{-x f(t)}` is completely monotone for every
`x ≥ 0` and every Bernstein `f`.

## The induction

Writing `F = g ∘ f`, the chain and product rules give `F' = -\,[(-g') ∘ f] \cdot f'`, in which
both `-g'` and `f'` are completely monotone. Iterating this substitution never returns to a
composition alone, but always to a *product* of a composition with a completely monotone factor.
The workhorse `TauCeti.IsCompletelyMonotoneOnIoi.comp_isBernsteinFunction_mul` therefore carries
that product along: for completely monotone `g` and `h`, `t ↦ g (f t) · h t` is completely
monotone, that is,
`0 ≤ (-1)ⁿ dⁿ/dtⁿ [g(f t) · h t]` on `(0, ∞)`, proved by induction on `n` from the identity

`d/dt [g(f t) · h t] = -\,[(-g')(f t) · (f' t · h t)] - [g(f t) · (-h' t)]`,

whose two bracketed terms are again of the same shape, with `(-g', f' · h)` and `(g, -h')` in
place of `(g, h)`. Taking `h = 1` gives the composition theorem.

The argument runs on the *open* half-line, where a Bernstein function is smooth and where its
values are positive, so that the derivatives of `g` at `f t` are honest two-sided derivatives.
That positivity is not automatic — a Bernstein function may vanish — but the failure is total:
`TauCeti.IsBernsteinFunction.eq_zero_of_eq_zero` shows that a Bernstein function vanishing at one
positive point vanishes on all of `[0, ∞)`, because it is nonnegative, nondecreasing and concave.
In that degenerate case the composition is the constant `g 0`, and the theorems are immediate.

## Main declarations

* `TauCeti.IsBernsteinFunction.eq_zero_of_eq_zero`: a Bernstein function with a zero on `(0, ∞)`
  vanishes identically on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotoneOnIoi.comp_isBernsteinFunction_mul`: the product form
  `t ↦ g (f t) · h t` that the induction proves.
* `TauCeti.IsCompletelyMonotoneOnIoi.comp_isBernsteinFunction`: the open-half-line composition
  theorem, under the positivity hypothesis on the inner function.
* `TauCeti.IsContinuousCompletelyMonotoneOnIoi.comp_isBernsteinFunction`: **a completely monotone
  function composed with a Bernstein function is completely monotone** on the closed half-line.
* `TauCeti.IsBernsteinFunction.comp`: Bernstein functions are closed under composition.
* `TauCeti.IsBernsteinFunction.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul`: the prototype
  `t ↦ e^{-x f(t)}` is completely monotone.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Theorem 3.7 and Corollary 3.8.
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f g h : ℝ → ℝ}

/-! ### Bernstein functions with a zero -/

/-- A Bernstein function that vanishes at one positive point vanishes on the whole closed
half-line. Monotonicity pushes the value at the origin down to `0`, and concavity then traps the
graph between the chord through the two zeros and the horizontal axis. -/
theorem IsBernsteinFunction.eq_zero_of_eq_zero (hf : IsBernsteinFunction f) {t₀ : ℝ}
    (ht₀ : 0 < t₀) (h₀ : f t₀ = 0) {t : ℝ} (ht : 0 ≤ t) : f t = 0 := by
  have hzero : f 0 = 0 :=
    le_antisymm (h₀ ▸ hf.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 ht₀.le) ht₀.le)
      (hf.nonneg le_rfl)
  rcases le_or_gt t t₀ with hle | hlt
  · exact le_antisymm (h₀ ▸ hf.monotoneOn (mem_Ici.2 ht) (mem_Ici.2 ht₀.le) hle) (hf.nonneg ht)
  · have htpos : 0 < t := ht₀.trans hlt
    have hb : 0 < t₀ / t := div_pos ht₀ htpos
    have hb1 : t₀ / t < 1 := (div_lt_one htpos).2 hlt
    have hchord : (1 - t₀ / t) • (0 : ℝ) + (t₀ / t) • t = t₀ := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ htpos.ne']
    have hcc := hf.concaveOn.2 (mem_Ici.2 le_rfl) (mem_Ici.2 ht)
      (by linarith : (0 : ℝ) ≤ 1 - t₀ / t) hb.le (by ring)
    rw [hchord, hzero, h₀] at hcc
    simp only [smul_eq_mul, mul_zero, zero_add] at hcc
    nlinarith [hf.nonneg ht]

/-- A Bernstein function with no zero on the open half-line is positive there: this is the
dichotomy that lets the composition theorems split into a degenerate constant case and the main
case, where the inner function stays inside `(0, ∞)`. -/
theorem IsBernsteinFunction.pos_of_forall_ne_zero (hf : IsBernsteinFunction f)
    (hne : ¬∃ t₀ : ℝ, 0 < t₀ ∧ f t₀ = 0) {t : ℝ} (ht : 0 < t) : 0 < f t := by
  rcases (hf.nonneg ht.le).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ⟨t, ht, heq.symm⟩ hne

/-! ### The composition induction -/

/-- The induction behind the composition theorem: for a Bernstein function `f` that is positive
on `(0, ∞)` and completely monotone `g` and `h`, every alternating derivative of the product
`t ↦ g (f t) · h t` is nonnegative on `(0, ∞)`.

The functions `g` and `h` are quantified inside the statement because the induction step feeds
the hypothesis two *different* pairs; `IsCompletelyMonotoneOnIoi.comp_isBernsteinFunction_mul`
is the usable form. -/
private theorem neg_one_pow_mul_iteratedDeriv_comp_mul_nonneg (hf : IsBernsteinFunction f)
    (hpos : ∀ t : ℝ, 0 < t → 0 < f t) (n : ℕ) :
    ∀ g h : ℝ → ℝ, IsCompletelyMonotoneOnIoi g → IsCompletelyMonotoneOnIoi h →
      ∀ t : ℝ, 0 < t → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n (fun u => g (f u) * h u) t := by
  have hmaps : MapsTo f (Ioi 0) (Ioi 0) := fun u hu => mem_Ioi.2 (hpos u hu)
  -- Smoothness of the model product `t ↦ g (f t) · h t`, needed to split iterated derivatives.
  have hsmooth : ∀ g h : ℝ → ℝ, IsCompletelyMonotoneOnIoi g → IsCompletelyMonotoneOnIoi h →
      ContDiffOn ℝ ∞ (fun u => g (f u) * h u) (Ioi 0) := fun g h hg hh =>
    (hg.contDiffOn.comp hf.contDiffOn hmaps).mul hh.contDiffOn
  induction n with
  | zero =>
      intro g h hg hh t ht
      simpa [iteratedDeriv_zero] using mul_nonneg (hg.nonneg (hpos t ht)) (hh.nonneg ht)
  | succ n ih =>
      intro g h hg hh t ht
      -- The three completely monotone ingredients of the differentiated product.
      have hg₁ : IsCompletelyMonotoneOnIoi fun s => -deriv g s := hg.neg_deriv
      have hh₁ : IsCompletelyMonotoneOnIoi fun u => deriv f u * h u :=
        (hf.deriv_isCompletelyMonotoneOnIoi.mul hh).congr fun _ _ => rfl
      have hh₂ : IsCompletelyMonotoneOnIoi fun u => -deriv h u := hh.neg_deriv
      -- Differentiating once produces exactly the two pairs the induction hypothesis wants.
      have hderiv : ∀ u ∈ Ioi (0 : ℝ), deriv (fun v => g (f v) * h v) u =
          -(-deriv g (f u) * (deriv f u * h u) + g (f u) * -deriv h u) := by
        intro u hu
        have hdf : HasDerivAt f (deriv f u) u :=
          (hf.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds hu)).hasDerivAt
        have hdg : HasDerivAt g (deriv g (f u)) (f u) :=
          ((hg.contDiffOn.differentiableOn (by simp)).differentiableAt
            (isOpen_Ioi.mem_nhds (mem_Ioi.2 (hpos u hu)))).hasDerivAt
        have hdh : HasDerivAt h (deriv h u) u :=
          ((hh.contDiffOn.differentiableOn (by simp)).differentiableAt
            (isOpen_Ioi.mem_nhds hu)).hasDerivAt
        have hcomp : HasDerivAt (fun v => g (f v)) (deriv g (f u) * deriv f u) u :=
          HasDerivAt.comp u hdg hdf
        have hprod : HasDerivAt (fun v => g (f v) * h v)
            (deriv g (f u) * deriv f u * h u + g (f u) * deriv h u) u := hcomp.mul hdh
        rw [hprod.deriv]
        ring
      have hEq : deriv (fun v => g (f v) * h v) =ᶠ[𝓝 t]
          fun u => -(-deriv g (f u) * (deriv f u * h u) + g (f u) * -deriv h u) :=
        eventually_of_mem (isOpen_Ioi.mem_nhds ht) hderiv
      -- Both summands are smooth, so the `n`-th derivative of the sum splits.
      have hA : ContDiffAt ℝ (n : WithTop ℕ∞) (fun u => -deriv g (f u) * (deriv f u * h u)) t :=
        ((hsmooth _ _ hg₁ hh₁).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top)
      have hB : ContDiffAt ℝ (n : WithTop ℕ∞) (fun u => g (f u) * -deriv h u) t :=
        ((hsmooth _ _ hg hh₂).contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top)
      have hIHA : 0 ≤ (-1 : ℝ) ^ n *
          iteratedDeriv n (fun u => -deriv g (f u) * (deriv f u * h u)) t :=
        ih (fun s => -deriv g s) (fun u => deriv f u * h u) hg₁ hh₁ t ht
      have hIHB : 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n (fun u => g (f u) * -deriv h u) t :=
        ih g (fun u => -deriv h u) hg hh₂ t ht
      rw [iteratedDeriv_succ', hEq.iteratedDeriv_eq n, iteratedDeriv_fun_neg,
        iteratedDeriv_fun_add hA hB]
      have hsign : (-1 : ℝ) ^ (n + 1) *
            -(iteratedDeriv n (fun u => -deriv g (f u) * (deriv f u * h u)) t +
              iteratedDeriv n (fun u => g (f u) * -deriv h u) t) =
          (-1 : ℝ) ^ n * iteratedDeriv n (fun u => -deriv g (f u) * (deriv f u * h u)) t +
            (-1 : ℝ) ^ n * iteratedDeriv n (fun u => g (f u) * -deriv h u) t := by
        rw [pow_succ]
        ring
      rw [hsign]
      exact add_nonneg hIHA hIHB

/-! ### Composition theorems -/

/-- **The product form of the open-half-line composition theorem.** For completely monotone `g`
and `h` and a Bernstein function `f` that is positive on `(0, ∞)`, the product `t ↦ g (f t) · h t`
is completely monotone on `(0, ∞)`.

The extra factor `h` is what makes the induction close: differentiating once turns the pair
`(g, h)` into the two pairs `(-g', f' · h)` and `(g, -h')`, both again completely monotone. -/
theorem IsCompletelyMonotoneOnIoi.comp_isBernsteinFunction_mul (hg : IsCompletelyMonotoneOnIoi g)
    (hh : IsCompletelyMonotoneOnIoi h) (hf : IsBernsteinFunction f)
    (hpos : ∀ t : ℝ, 0 < t → 0 < f t) :
    IsCompletelyMonotoneOnIoi fun u => g (f u) * h u :=
  ⟨(hg.contDiffOn.comp hf.contDiffOn fun u hu => mem_Ioi.2 (hpos u hu)).mul hh.contDiffOn,
    fun n t ht => neg_one_pow_mul_iteratedDeriv_comp_mul_nonneg hf hpos n g h hg hh t ht⟩

/-- **Composition on the open half-line.** If `g` is completely monotone on `(0, ∞)` and `f` is a
Bernstein function that is positive on `(0, ∞)`, then `g ∘ f` is completely monotone on `(0, ∞)`.
The positivity hypothesis is what keeps `f t` inside the open half-line, where `g` is smooth; it
is removed in `TauCeti.IsContinuousCompletelyMonotoneOnIoi.comp_isBernsteinFunction`. -/
theorem IsCompletelyMonotoneOnIoi.comp_isBernsteinFunction (hg : IsCompletelyMonotoneOnIoi g)
    (hf : IsBernsteinFunction f) (hpos : ∀ t : ℝ, 0 < t → 0 < f t) :
    IsCompletelyMonotoneOnIoi (g ∘ f) := by
  have hone : IsCompletelyMonotoneOnIoi fun _ : ℝ => (1 : ℝ) :=
    (isCompletelyMonotone_const zero_le_one).isCompletelyMonotoneOnIoi
  refine (hg.comp_isBernsteinFunction_mul hone hf hpos).congr fun u _ => ?_
  simp [Function.comp_apply]

/-- **A completely monotone function composed with a Bernstein function is completely
monotone.** This is the closure property the `OneParameterSemigroups` roadmap asks for in Part B.

The conclusion is the closed-half-line predicate `IsContinuousCompletelyMonotoneOnIoi`, not the
stronger `IsCompletelyMonotone`: a Bernstein function such as `t ↦ √t` has no finite right
derivative at the origin, so the composition need not have one. -/
theorem IsContinuousCompletelyMonotoneOnIoi.comp_isBernsteinFunction
    (hg : IsContinuousCompletelyMonotoneOnIoi g)
    (hf : IsBernsteinFunction f) : IsContinuousCompletelyMonotoneOnIoi (g ∘ f) := by
  refine isContinuousCompletelyMonotoneOnIoi_iff.mpr
    ⟨hg.continuousOn.comp hf.continuousOn fun u hu => mem_Ici.2 (hf.nonneg hu), ?_⟩
  by_cases hvanish : ∃ t₀ : ℝ, 0 < t₀ ∧ f t₀ = 0
  · obtain ⟨t₀, ht₀, h₀⟩ := hvanish
    refine (isCompletelyMonotone_const (hg.nonneg le_rfl)).isCompletelyMonotoneOnIoi.congr ?_
    intro t ht
    simp [Function.comp_apply, hf.eq_zero_of_eq_zero ht₀ h₀ (le_of_lt ht)]
  · exact hg.isCompletelyMonotoneOnIoi.comp_isBernsteinFunction hf
      fun t ht => hf.pos_of_forall_ne_zero hvanish ht

/-- **Bernstein functions are closed under composition.** The derivative of `g ∘ f` is
`(g' ∘ f) · f'`, a product of the composition theorem's output with a completely monotone
factor. -/
theorem IsBernsteinFunction.comp (hg : IsBernsteinFunction g) (hf : IsBernsteinFunction f) :
    IsBernsteinFunction (g ∘ f) := by
  by_cases hvanish : ∃ t₀ : ℝ, 0 < t₀ ∧ f t₀ = 0
  · obtain ⟨t₀, ht₀, h₀⟩ := hvanish
    refine (isBernsteinFunction_const (hg.nonneg le_rfl)).congr fun t ht => ?_
    simp [Function.comp_apply, hf.eq_zero_of_eq_zero ht₀ h₀ (mem_Ici.1 ht)]
  · have hpos : ∀ t : ℝ, 0 < t → 0 < f t := fun t ht => hf.pos_of_forall_ne_zero hvanish ht
    have hmaps : MapsTo f (Ioi 0) (Ioi 0) := fun u hu => mem_Ioi.2 (hpos u hu)
    refine isBernsteinFunction_iff.mpr
      ⟨hg.continuousOn.comp hf.continuousOn fun u hu => mem_Ici.2 (hf.nonneg hu),
        hg.contDiffOn.comp hf.contDiffOn hmaps,
        fun t ht => hg.nonneg (hf.nonneg ht), ?_⟩
    have hcm : IsCompletelyMonotoneOnIoi fun u => deriv g (f u) * deriv f u :=
      hg.deriv_isCompletelyMonotoneOnIoi.comp_isBernsteinFunction_mul
        hf.deriv_isCompletelyMonotoneOnIoi hf hpos
    refine hcm.congr fun u hu => ?_
    have hdf : HasDerivAt f (deriv f u) u :=
      (hf.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds hu)).hasDerivAt
    have hdg : HasDerivAt g (deriv g (f u)) (f u) :=
      (hg.differentiableOn.differentiableAt
        (isOpen_Ioi.mem_nhds (mem_Ioi.2 (hpos u hu)))).hasDerivAt
    exact (HasDerivAt.comp u hdg hdf).deriv

/-- The prototype completely monotone functions attached to a Bernstein function: for `x ≥ 0`,
the composition `t ↦ e^{-x f(t)}` is completely monotone on the closed half-line. These are the
Laplace transforms of the one-parameter convolution semigroup subordinate to `f`. -/
theorem IsBernsteinFunction.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul
    (hf : IsBernsteinFunction f) {x : ℝ} (hx : 0 ≤ x) :
    IsContinuousCompletelyMonotoneOnIoi fun t => Real.exp (-x * f t) :=
  (IsContinuousCompletelyMonotoneOnIoi.of_isCompletelyMonotone
    (isCompletelyMonotone_exp_neg_mul hx)).comp_isBernsteinFunction hf

end TauCeti
