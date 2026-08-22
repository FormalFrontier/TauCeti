/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import TauCeti.Analysis.CompletelyMonotone.Closure
public import TauCeti.Analysis.CompletelyMonotone.Reparametrization

/-!
# Complete monotonicity in the finite-difference sense

`TauCeti.IsCompletelyMonotone` asks for a smooth function whose iterated *derivatives* alternate
in sign. There is a second, purely order-theoretic notion, which mentions no derivatives at all:
a function `f : ℝ → ℝ` is completely monotone in the **finite-difference** sense when every
iterated forward difference taken with an arbitrary list `[h₁, …, hₙ]` of nonnegative steps has
the sign `(-1)ⁿ`,
`0 ≤ (-1)ⁿ (Δ_{h₁} ⋯ Δ_{hₙ} f)(t)` for `t ≥ 0`,
where `Δ_h g = fun t => g (t + h) - g t` is Mathlib's `fwdDiff`. Low orders read as `f ≥ 0`,
`f` nonincreasing, `f` "convex along every pair of steps", and so on.

This file introduces the predicate `TauCeti.IsDifferenceCompletelyMonotone` and proves that on
smooth functions it is *exactly* complete monotonicity
(`TauCeti.isCompletelyMonotone_iff_isDifferenceCompletelyMonotone`). The two halves are genuinely
different in character:

* difference to derivative: fixing a list `l`, the sign hypothesis for `k :: l` says that the
  slope of `Δ_l f` over `[t, t + k]` has the sign `(-1)^(|l|+1)`; letting `k → 0⁺` turns that into
  the sign of `(Δ_l f)' = Δ_l f'`, so `-f'` again satisfies the hypothesis and an induction on the
  order finishes the argument;
* derivative to difference: if `f` is completely monotone and `a ≥ 0` then so is
  `t ↦ f t - f (t + a)`, because the `n`-th alternating derivative of `f` is itself completely
  monotone, hence nonincreasing (`TauCeti.IsCompletelyMonotone.sub_comp_add_const`). Iterating
  this over the list gives the sign of every mixed difference.

The finite-difference form is the hypothesis that arises in practice: the alternating differences
of a positive-definite function on the involutive semigroup `[0, ∞) × V` are positive definite,
so the mass of the associated spatial Bochner measure is a function of time all of whose mixed
differences alternate, with no smoothness available a priori. Combining the characterization here
with the mollification of
`TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Mollify` converts that hypothesis into the
input of the Hausdorff--Bernstein--Widder theorem.

## Main declarations

* `TauCeti.fwdDiffList`: the forward difference `Δ_{h₁} ⋯ Δ_{hₙ} f` along a list of steps.
* `TauCeti.fwdDiffList_congr`: on `[0, ∞)` a mixed difference with nonnegative steps only sees the
  values of the function there.
* `TauCeti.IsDifferenceCompletelyMonotone`: complete monotonicity in the finite-difference sense.
* `TauCeti.isDifferenceCompletelyMonotone_of_tendsto`: the predicate is closed under pointwise
  limits, unlike its derivative form.
* `TauCeti.IsDifferenceCompletelyMonotone.neg_derivWithin`: the negated derivative within the
  half-line of a differentiable finite-difference completely monotone function is again one.
* `TauCeti.IsDifferenceCompletelyMonotone.isCompletelyMonotone`: a `C^∞` function that is
  completely monotone in the finite-difference sense is completely monotone.
* `TauCeti.IsCompletelyMonotone.sub_comp_add_const`: if `f` is completely monotone and `0 ≤ a`
  then so is `t ↦ f t - f (t + a)`.
* `TauCeti.isCompletelyMonotone_iff_isDifferenceCompletelyMonotone`: the two notions agree on
  `C^∞` functions.

## References

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV.
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984).
-/

public section

open Set Filter
open scoped ContDiff Pointwise Topology

namespace TauCeti

variable {f g : ℝ → ℝ}

/-! ## Forward differences along a list of steps -/

/-- The iterated forward difference of `f` along a list of steps: `fwdDiffList [h₁, …, hₙ] f` is
`Δ_{h₁} (⋯ (Δ_{hₙ} f))`, built from Mathlib's `fwdDiff`. The order of the steps is irrelevant,
but keeping them in a list is what makes *mixed* step sizes available, which is strictly more
information than the iterates `(Δ_h)^[n]` of a single step. -/
@[expose] def fwdDiffList (l : List ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  l.foldr fwdDiff f

/-- The empty list of steps takes no difference at all. -/
@[simp]
theorem fwdDiffList_nil (f : ℝ → ℝ) : fwdDiffList [] f = f := rfl

/-- Consing a step applies one more forward difference on the outside. -/
@[simp]
theorem fwdDiffList_cons (h : ℝ) (l : List ℝ) (f : ℝ → ℝ) :
    fwdDiffList (h :: l) f = fwdDiff h (fwdDiffList l f) := rfl

/-- Concatenating step lists composes the corresponding difference operators. -/
theorem fwdDiffList_append (l l' : List ℝ) (f : ℝ → ℝ) :
    fwdDiffList (l ++ l') f = fwdDiffList l (fwdDiffList l' f) := by
  induction l with
  | nil => rfl
  | cons h l ih => rw [List.cons_append, fwdDiffList_cons, ih, fwdDiffList_cons]

/-- Permuting the step sizes does not change a mixed forward difference. -/
theorem fwdDiffList_eq_of_perm {l l' : List ℝ} (h : l.Perm l') (f : ℝ → ℝ) :
    fwdDiffList l f = fwdDiffList l' f := by
  let _ : LeftCommutative (fun h : ℝ => fun g : ℝ → ℝ => fwdDiff h g) :=
    ⟨fun a b g => by
      ext t
      simp only [fwdDiff]
      rw [show t + b + a = t + a + b by ring]
      ring⟩
  exact h.foldr_eq f

/-- Along a constant list the mixed difference is the iterated single-step difference. -/
theorem fwdDiffList_replicate (n : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    fwdDiffList (List.replicate n h) f = (fwdDiff h)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, fwdDiffList_cons, ih, Function.iterate_succ_apply']

/-- Mixed differences are additive-group homomorphisms: they commute with negation. -/
theorem fwdDiffList_neg (l : List ℝ) (f : ℝ → ℝ) :
    fwdDiffList l (fun t => -f t) = fun t => -fwdDiffList l f t := by
  induction l with
  | nil => rfl
  | cons h l ih =>
      ext t
      simp only [fwdDiffList_cons, ih, fwdDiff]
      ring

/-- Mixed differences commute with addition. -/
theorem fwdDiffList_add (l : List ℝ) (f g : ℝ → ℝ) :
    fwdDiffList l (fun t => f t + g t) = fun t => fwdDiffList l f t + fwdDiffList l g t := by
  induction l with
  | nil => rfl
  | cons h l ih =>
      ext t
      simp only [fwdDiffList_cons, ih, fwdDiff]
      ring

/-- Mixed differences commute with multiplication by a constant. -/
theorem fwdDiffList_const_mul (c : ℝ) (l : List ℝ) (f : ℝ → ℝ) :
    fwdDiffList l (fun t => c * f t) = fun t => c * fwdDiffList l f t := by
  induction l with
  | nil => rfl
  | cons h l ih =>
      ext t
      simp only [fwdDiffList_cons, ih, fwdDiff]
      ring

/-- Only the values of `f` on `[0, ∞)` matter for a mixed difference evaluated there, as long as
all the steps are nonnegative. -/
theorem fwdDiffList_congr {l : List ℝ} (hl : ∀ h ∈ l, 0 ≤ h) (hfg : ∀ u : ℝ, 0 ≤ u → g u = f u)
    {t : ℝ} (ht : 0 ≤ t) : fwdDiffList l g t = fwdDiffList l f t := by
  induction l generalizing t with
  | nil => exact hfg t ht
  | cons h l ih =>
      have hh : 0 ≤ h := hl h (by simp)
      have hrest : ∀ k ∈ l, 0 ≤ k := fun k hk => hl k (List.mem_cons_of_mem h hk)
      simp only [fwdDiffList_cons, fwdDiff]
      rw [ih hrest (by linarith : (0 : ℝ) ≤ t + h), ih hrest ht]

/-- A mixed difference of a continuous function is continuous. -/
theorem continuous_fwdDiffList (l : List ℝ) (hf : Continuous f) :
    Continuous (fwdDiffList l f) := by
  induction l with
  | nil => simpa using hf
  | cons h l ih => exact (ih.comp (continuous_id.add_const h)).sub ih

/-! ## The finite-difference predicate -/

/-- A function `f : ℝ → ℝ` is **completely monotone in the finite-difference sense** if every
mixed forward difference along a list of nonnegative steps has the alternating sign of its
length, at every point of `[0, ∞)`:
`0 ≤ (-1)ⁿ (Δ_{h₁} ⋯ Δ_{hₙ} f)(t)` for `h₁, …, hₙ ≥ 0` and `t ≥ 0`.

Unlike `TauCeti.IsCompletelyMonotone` this mentions no derivative, so it makes sense for an
arbitrary function; on `C^∞` functions the two agree
(`TauCeti.isCompletelyMonotone_iff_isDifferenceCompletelyMonotone`). Mixed steps, rather than the
iterates of a single step, are what makes the notion stable under differentiation. -/
@[expose] def IsDifferenceCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ∀ l : List ℝ, (∀ h ∈ l, 0 ≤ h) → ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ l.length * fwdDiffList l f t

/-- `IsDifferenceCompletelyMonotone f` unfolds to the alternating sign condition on every mixed
forward difference with nonnegative steps. -/
theorem isDifferenceCompletelyMonotone_iff {f : ℝ → ℝ} :
    IsDifferenceCompletelyMonotone f ↔
      ∀ l : List ℝ, (∀ h ∈ l, 0 ≤ h) → ∀ t : ℝ, 0 ≤ t →
        0 ≤ (-1) ^ l.length * fwdDiffList l f t :=
  Iff.rfl

namespace IsDifferenceCompletelyMonotone

/-- A function that is completely monotone in the finite-difference sense is nonnegative on
`[0, ∞)`: this is the hypothesis for the empty list of steps. -/
theorem nonneg (hf : IsDifferenceCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  simpa using hf [] (by simp) t ht

/-- A function that is completely monotone in the finite-difference sense is nonincreasing on
`[0, ∞)`: this is the hypothesis for a single step. -/
theorem apply_add_le (hf : IsDifferenceCompletelyMonotone f) {t h : ℝ} (ht : 0 ≤ t)
    (hh : 0 ≤ h) : f (t + h) ≤ f t := by
  have := hf [h] (by simpa using hh) t ht
  simp only [List.length_cons, List.length_nil, fwdDiffList_cons, fwdDiffList_nil, fwdDiff,
    zero_add, pow_one] at this
  linarith

/-- The predicate depends only on the values of the function on `[0, ∞)`. -/
theorem congr (hf : IsDifferenceCompletelyMonotone f) (hfg : ∀ t : ℝ, 0 ≤ t → g t = f t) :
    IsDifferenceCompletelyMonotone g := by
  intro l hl t ht
  rw [fwdDiffList_congr hl hfg ht]
  exact hf l hl t ht

/-- A function that is completely monotone in the finite-difference sense is nonincreasing on
`[0, ∞)`. -/
theorem antitoneOn (hf : IsDifferenceCompletelyMonotone f) : AntitoneOn f (Ici 0) := by
  intro a ha b _ hab
  simpa using hf.apply_add_le (mem_Ici.mp ha) (by linarith : (0 : ℝ) ≤ b - a)

/-- The finite-difference predicate is stable under taking one more difference: if `f` qualifies
and `0 ≤ h`, then so does `-Δ_h f`. -/
theorem neg_fwdDiff (hf : IsDifferenceCompletelyMonotone f) {h : ℝ} (hh : 0 ≤ h) :
    IsDifferenceCompletelyMonotone (fun t => -fwdDiff h f t) := by
  intro l hl t ht
  have hstep : ∀ k ∈ l ++ [h], 0 ≤ k := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hl k hk
    · simpa using (List.mem_singleton.mp hk) ▸ hh
  have hsign := hf (l ++ [h]) hstep t ht
  rw [fwdDiffList_append, List.length_append] at hsign
  have hneg : fwdDiffList l (fun t => -fwdDiff h f t) t = -fwdDiffList l (fwdDiff h f) t := by
    rw [fwdDiffList_neg]
  rw [hneg]
  simpa [pow_add, List.length_singleton] using hsign

end IsDifferenceCompletelyMonotone

/-- Mixed differences pass to a pointwise limit. -/
theorem tendsto_fwdDiffList {ι : Type*} {L : Filter ι} {F : ι → ℝ → ℝ} (l : List ℝ)
    (hF : ∀ u : ℝ, Tendsto (fun i => F i u) L (𝓝 (f u))) (t : ℝ) :
    Tendsto (fun i => fwdDiffList l (F i) t) L (𝓝 (fwdDiffList l f t)) := by
  induction l generalizing t with
  | nil => exact hF t
  | cons k l ih =>
      simp only [fwdDiffList_cons, fwdDiff]
      exact (ih (t + k)).sub (ih t)

/-- Complete monotonicity in the finite-difference sense is closed under pointwise limits. This
is a genuine advantage of the finite-difference formulation: the derivative form is not visibly
stable under pointwise convergence. -/
theorem isDifferenceCompletelyMonotone_of_tendsto {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} (hF : ∀ i, IsDifferenceCompletelyMonotone (F i))
    (hlim : ∀ u : ℝ, Tendsto (fun i => F i u) L (𝓝 (f u))) :
    IsDifferenceCompletelyMonotone f := fun l hl t ht =>
  ge_of_tendsto (tendsto_const_nhds.mul (tendsto_fwdDiffList l hlim t))
    (Eventually.of_forall fun i => hF i l hl t ht)

namespace IsDifferenceCompletelyMonotone

/-- Complete monotonicity in the finite-difference sense is closed under addition. -/
theorem add (hf : IsDifferenceCompletelyMonotone f) (hg : IsDifferenceCompletelyMonotone g) :
    IsDifferenceCompletelyMonotone (fun t => f t + g t) := by
  intro l hl t ht
  rw [fwdDiffList_add, mul_add]
  exact add_nonneg (hf l hl t ht) (hg l hl t ht)

/-- Complete monotonicity in the finite-difference sense is closed under multiplication by a
nonnegative constant. -/
theorem const_mul (hf : IsDifferenceCompletelyMonotone f) {c : ℝ} (hc : 0 ≤ c) :
    IsDifferenceCompletelyMonotone (fun t => c * f t) := by
  intro l hl t ht
  rw [fwdDiffList_const_mul, ← mul_assoc, mul_comm ((-1 : ℝ) ^ l.length) c, mul_assoc]
  exact mul_nonneg hc (hf l hl t ht)

end IsDifferenceCompletelyMonotone

/-! ## Differences commute with differentiation -/

/-- A mixed difference of a differentiable function is differentiable. -/
theorem differentiable_fwdDiffList (l : List ℝ) (hf : Differentiable ℝ f) :
    Differentiable ℝ (fwdDiffList l f) := by
  induction l with
  | nil => simpa using hf
  | cons h l ih =>
      intro t
      simp only [fwdDiffList_cons]
      exact ((ih (t + h)).comp t (by fun_prop)).sub (ih t)

/-- A mixed difference with nonnegative steps preserves differentiability on `[0, ∞)`. -/
private theorem differentiableOn_fwdDiffList (l : List ℝ) (hl : ∀ h ∈ l, 0 ≤ h)
    (hf : DifferentiableOn ℝ f (Ici 0)) : DifferentiableOn ℝ (fwdDiffList l f) (Ici 0) := by
  induction l with
  | nil => simpa using hf
  | cons h l ih =>
      have hh : 0 ≤ h := hl h (by simp)
      have hrest : ∀ k ∈ l, 0 ≤ k := fun k hk => hl k (List.mem_cons_of_mem h hk)
      intro t ht
      simp only [fwdDiffList_cons]
      have hshift : DifferentiableWithinAt ℝ (fun y => fwdDiffList l f (y + h)) (Ici 0) t := by
        have hcomp : DifferentiableWithinAt ℝ
            (fwdDiffList l f ∘ fun y : ℝ => y + h) (Ici 0) t :=
          DifferentiableWithinAt.comp (t := Ici 0) t
            ((ih hrest) (t + h) (mem_Ici.mpr (by linarith [mem_Ici.mp ht]))) (by fun_prop)
            (fun y hy => mem_Ici.mpr (by linarith [mem_Ici.mp hy]))
        simpa only [Function.comp_def] using hcomp
      exact hshift.sub ((ih hrest) t ht)

/-- Differentiating within `[0, ∞)` commutes with a mixed difference whose steps are
nonnegative. -/
private theorem derivWithin_fwdDiffList (l : List ℝ) (hl : ∀ h ∈ l, 0 ≤ h)
    (hf : DifferentiableOn ℝ f (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fwdDiffList l f) (Ici 0) t =
      fwdDiffList l (derivWithin f (Ici 0)) t := by
  induction l generalizing t with
  | nil => rfl
  | cons h l ih =>
      have hh : 0 ≤ h := hl h (by simp)
      have hrest : ∀ k ∈ l, 0 ≤ k := fun k hk => hl k (List.mem_cons_of_mem h hk)
      have hdiff := differentiableOn_fwdDiffList l hrest hf
      have hshift : DifferentiableWithinAt ℝ (fun y => fwdDiffList l f (y + h)) (Ici 0) t :=
        by
          have hcomp : DifferentiableWithinAt ℝ
              (fwdDiffList l f ∘ fun y : ℝ => y + h) (Ici 0) t :=
            DifferentiableWithinAt.comp (t := Ici 0) t
              (hdiff (t + h) (mem_Ici.mpr (by linarith))) (by fun_prop)
              (fun y hy => mem_Ici.mpr (by linarith [mem_Ici.mp hy]))
          simpa only [Function.comp_def] using hcomp
      rw [fwdDiffList_cons]
      change derivWithin (fun y => fwdDiffList l f (y + h) - fwdDiffList l f y) (Ici 0) t = _
      rw [derivWithin_fun_sub hshift (hdiff t (mem_Ici.mpr ht)), ih hrest ht,
        fwdDiffList_cons, fwdDiff]
      congr 1
      calc
        derivWithin (fun y => fwdDiffList l f (y + h)) (Ici 0) t =
            derivWithin (fwdDiffList l f) (Ici 0) (t + h) := by
          rw [derivWithin_comp_add_const]
          have hset : h +ᵥ Ici (0 : ℝ) = Ici h := by
            ext x
            simp only [Set.mem_vadd_set, mem_Ici, vadd_eq_add]
            exact ⟨by rintro ⟨y, hy, rfl⟩; linarith,
              fun hx => ⟨x - h, by linarith, by ring⟩⟩
          rw [hset]
          exact derivWithin_subset
            (by intro x hx; exact mem_Ici.mpr (le_trans hh (mem_Ici.mp hx)))
            ((uniqueDiffOn_Ici h) (t + h) (mem_Ici.mpr (by linarith)))
            (hdiff (t + h) (mem_Ici.mpr (by linarith)))
        _ = fwdDiffList l (derivWithin f (Ici 0)) (t + h) := ih hrest (by linarith)

/-- Forward differences commute with differentiation. -/
theorem deriv_fwdDiffList (l : List ℝ) (hf : Differentiable ℝ f) :
    deriv (fwdDiffList l f) = fwdDiffList l (deriv f) := by
  induction l with
  | nil => rfl
  | cons h l ih =>
      have hd : Differentiable ℝ (fwdDiffList l f) := differentiable_fwdDiffList l hf
      ext t
      have h₁ : HasDerivAt (fun y : ℝ => fwdDiffList l f (y + h))
          (deriv (fwdDiffList l f) (t + h)) t := by
        exact ((hd (t + h)).hasDerivAt).comp_add_const t h
      have h₂ : HasDerivAt (fwdDiffList (h :: l) f)
          (deriv (fwdDiffList l f) (t + h) - deriv (fwdDiffList l f) t) t :=
        h₁.sub (hd t).hasDerivAt
      have h₃ : fwdDiffList (h :: l) (deriv f) t
          = fwdDiffList l (deriv f) (t + h) - fwdDiffList l (deriv f) t := rfl
      rw [h₂.deriv, ih, h₃]

/-! ## From differences to derivatives -/

namespace IsDifferenceCompletelyMonotone

/-- Passing to the negated derivative within `[0, ∞)` preserves complete monotonicity in the
finite-difference sense. The sign of `(Δ_l f)'` is read off from the sign of the extra difference
`Δ_k (Δ_l f)` by letting the step `k` tend to `0` from the right. -/
theorem neg_derivWithin (hf : IsDifferenceCompletelyMonotone f)
    (hd : DifferentiableOn ℝ f (Ici 0)) :
    IsDifferenceCompletelyMonotone (fun t => -derivWithin f (Ici 0) t) := by
  intro l hl t ht
  set n := l.length with hn
  set u := fwdDiffList l f with hu
  have hud : DifferentiableOn ℝ u (Ici 0) := differentiableOn_fwdDiffList l hl hd
  -- The slope of `u` to the right of `t` has the sign `(-1)^(n+1)`.
  have hslope : ∀ y ∈ Ioi t, 0 ≤ (-1 : ℝ) ^ (n + 1) * slope u t y := by
    intro y hy
    have hy' : 0 < y - t := sub_pos.mpr (mem_Ioi.mp hy)
    have hstep : ∀ k ∈ (y - t) :: l, 0 ≤ k := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hy'.le
      · exact hl k hk
    have hsign := hf ((y - t) :: l) hstep t ht
    rw [fwdDiffList_cons, List.length_cons] at hsign
    simp only [fwdDiff, ← hu] at hsign
    rw [slope_def_field, div_eq_inv_mul, ← mul_assoc, mul_comm ((-1 : ℝ) ^ (n + 1)),
      mul_assoc]
    refine mul_nonneg (by positivity) ?_
    rw [add_comm t (y - t), sub_add_cancel] at hsign
    exact hsign
  -- Letting the step tend to `0` gives the sign of the derivative.
  have hlim : Tendsto (slope u t) (𝓝[>] t) (𝓝 (derivWithin u (Ici 0) t)) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp (hud t (mem_Ici.mpr ht)).hasDerivWithinAt).mono_left
      (nhdsWithin_mono t fun y hy =>
        ⟨mem_Ici.mpr (by linarith [mem_Ioi.mp hy]), ne_of_gt (mem_Ioi.mp hy)⟩)
  have hderiv : 0 ≤ (-1 : ℝ) ^ (n + 1) * derivWithin u (Ici 0) t := by
    refine ge_of_tendsto (tendsto_const_nhds.mul hlim) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy using hslope y hy
  have hrw : fwdDiffList l (fun t => -derivWithin f (Ici 0) t) t =
      -derivWithin u (Ici 0) t := by
    rw [fwdDiffList_neg]
    change -fwdDiffList l (derivWithin f (Ici 0)) t = -derivWithin u (Ici 0) t
    rw [← derivWithin_fwdDiffList l hl hd ht, hu]
  have hpow : (-1 : ℝ) ^ n * -derivWithin u (Ici 0) t =
      (-1 : ℝ) ^ (n + 1) * derivWithin u (Ici 0) t := by ring
  rw [hrw, hpow]
  exact hderiv

/-- A function that is `C^∞` on `[0, ∞)` and completely monotone in the finite-difference sense
has alternating iterated derivatives within that half-line. -/
theorem neg_one_pow_mul_iteratedDerivWithin_nonneg (hf : IsDifferenceCompletelyMonotone f)
    (hs : ContDiffOn ℝ ∞ f (Ici 0)) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t := by
  induction n generalizing f with
  | zero => simpa using hf.nonneg ht
  | succ n ih =>
      obtain ⟨hdiff, hderiv⟩ := contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ici 0) |>.mp hs
      have hnegs : ContDiffOn ℝ ∞ (fun t => -derivWithin f (Ici 0) t) (Ici 0) := hderiv.neg
      have := ih (hf.neg_derivWithin hdiff) hnegs
      rw [iteratedDerivWithin_fun_neg] at this
      rw [pow_succ, mul_comm ((-1 : ℝ) ^ n), mul_assoc, iteratedDerivWithin_succ']
      simpa using this

/-- **Finite differences detect complete monotonicity.** A `C^∞` function all of whose mixed
forward differences alternate in sign on `[0, ∞)` is completely monotone. -/
theorem isCompletelyMonotone (hf : IsDifferenceCompletelyMonotone f)
    (hs : ContDiffOn ℝ ∞ f (Ici 0)) : IsCompletelyMonotone f :=
  ⟨hs, fun n _t ht => hf.neg_one_pow_mul_iteratedDerivWithin_nonneg hs n ht⟩

end IsDifferenceCompletelyMonotone

/-! ## From derivatives to differences -/

namespace IsCompletelyMonotone

/-- A completely monotone function is completely monotone in the finite-difference sense. -/
theorem isDifferenceCompletelyMonotone (hf : IsCompletelyMonotone f) :
    IsDifferenceCompletelyMonotone f := by
  have key : ∀ l : List ℝ, (∀ h ∈ l, 0 ≤ h) → ∀ g : ℝ → ℝ, IsCompletelyMonotone g →
      IsCompletelyMonotone (fun t => (-1) ^ l.length * fwdDiffList l g t) := by
    intro l
    induction l with
    | nil => intro _ g hg; simpa using hg
    | cons h l ih =>
        intro hl g hg
        have hh : 0 ≤ h := hl h (by simp)
        have hrest : ∀ k ∈ l, 0 ≤ k := fun k hk => hl k (List.mem_cons_of_mem h hk)
        have hprev := ih hrest g hg
        have heq : (fun t => (-1 : ℝ) ^ (h :: l).length * fwdDiffList (h :: l) g t)
            = fun t => (-1 : ℝ) ^ l.length * fwdDiffList l g t
              - (-1 : ℝ) ^ l.length * fwdDiffList l g (t + h) := by
          ext t
          simp only [List.length_cons, fwdDiffList_cons, fwdDiff, pow_succ]
          ring
        rw [heq]
        exact hprev.sub_comp_add_const hh
  intro l hl t ht
  exact (key l hl f hf).nonneg ht

end IsCompletelyMonotone

/-- **The finite-difference characterization of complete monotonicity.** For a `C^∞` function,
alternating mixed forward differences on `[0, ∞)` are equivalent to alternating iterated
derivatives there. -/
theorem isCompletelyMonotone_iff_isDifferenceCompletelyMonotone
    (hs : ContDiffOn ℝ ∞ f (Ici 0)) :
    IsCompletelyMonotone f ↔ IsDifferenceCompletelyMonotone f :=
  ⟨IsCompletelyMonotone.isDifferenceCompletelyMonotone,
    fun hf => hf.isCompletelyMonotone hs⟩

end TauCeti
