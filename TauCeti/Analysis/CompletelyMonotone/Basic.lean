/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.AbsolutelyMonotone
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.MonotoneConvergence
public import TauCeti.Analysis.Calculus.IteratedDerivWithin

/-!
# Completely monotone functions

A function `f : ℝ → ℝ` is *completely monotone* if it is smooth on the closed half-line
`[0, ∞)` and its iterated derivatives there alternate in sign:
`(-1)ⁿ f⁽ⁿ⁾(t) ≥ 0` for every `n` and every `t ≥ 0`. Equivalently `f` is nonnegative,
nonincreasing, convex, and so on through every order. Bernstein's theorem identifies the
completely monotone functions on the *open* half-line `(0, ∞)` with the Laplace transforms of
positive measures on `[0, ∞)`. Demanding smoothness up to the boundary point `0`, as we do
here, is a genuine strengthening: it carves out the subclass whose representing measure has
every moment finite. (It thereby excludes some Laplace transforms of finite measures, such as
`t ↦ ∫₀^∞ e^{-x t} (1 + x)⁻² dx`, which is finite at `0` yet has `f'(0⁺) = -∞`.) The
prototypes `t ↦ e^{-x t}` (`x ≥ 0`) are the extreme rays out of which Bernstein's theorem
builds the general member.

The smoothness clause is essential and is not folded into the sign condition: an iterated
derivative defaults to a junk value where the function fails to be differentiable, so
without it a badly behaved `f` could satisfy `0 ≤ 0` vacuously. We phrase the sign condition
through `iteratedDerivWithin _ (Set.Ici 0)`, the derivative *within* the closed half-line,
which is the object that pairs cleanly with `ContDiffOn` (in particular at the boundary
point `0`); on the open half-line it agrees with the ordinary iterated derivative.

## Main declarations

* `TauCeti.IsCompletelyMonotone`: the predicate that `f` is smooth and sign-alternating on
  `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.congr`: complete monotonicity only depends on the values of the
  function on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.nonneg`, `TauCeti.IsCompletelyMonotone.derivWithin_nonpos`,
  `TauCeti.IsCompletelyMonotone.antitoneOn`: a completely monotone function is nonnegative
  and nonincreasing on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotoneOnIci.exists_nonneg_tendsto_atTop`,
  `TauCeti.IsCompletelyMonotoneOnIci.le_of_tendsto_atTop`: order-limit consequences of
  nonnegativity and monotonicity on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_iteratedDeriv_nonneg`: on the open half-line,
  the sign condition also holds for ordinary iterated derivatives.
* `TauCeti.IsCompletelyMonotone.add`, `TauCeti.IsCompletelyMonotone.sum`,
  `TauCeti.IsCompletelyMonotone.smul`: closure under addition, finite sums, and nonnegative
  scalar multiples.
* `TauCeti.IsCompletelyMonotoneOnIoi`: the open-half-line analogue, using ordinary iterated
  derivatives on `(0, ∞)`.
* `TauCeti.IsCompletelyMonotoneOnIci`: the closed-half-line predicate used by the
  finite-measure Hausdorff--Bernstein--Widder theorem: continuity on `[0, ∞)` plus complete
  monotonicity on `(0, ∞)`.
* `TauCeti.isCompletelyMonotone_const`: a nonnegative constant is completely monotone.
* `TauCeti.isCompletelyMonotone_exp_neg_mul`: the building block `t ↦ e^{-x t}` for `x ≥ 0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A function `f : ℝ → ℝ` is **completely monotone** if it is `C^∞` on the closed half-line
`[0, ∞)` and its iterated derivatives within `[0, ∞)` alternate in sign:
`0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. The smoothness clause prevents the sign
condition from being satisfied vacuously by a junk iterated derivative. -/
@[expose] def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ici 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t

/-- `IsCompletelyMonotone f` unfolds to its defining conjunction: `f` is `C^∞` on `[0, ∞)`
and its iterated derivatives within `[0, ∞)` alternate in sign. -/
lemma isCompletelyMonotone_iff {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔
      ContDiffOn ℝ ∞ f (Ici 0) ∧
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t :=
  Iff.rfl

/-- Completely monotone functions are exactly absolutely monotone functions after reflecting the
closed half-line through zero. -/
lemma isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔ AbsolutelyMonotoneOn (fun u => f (-u)) (Iic 0) := by
  rw [isCompletelyMonotone_iff,
    AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg (uniqueDiffOn_Iic 0)]
  constructor
  -- Reflect smoothness and the alternating-sign condition from `[0, ∞)` to `(-∞, 0]`.
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n u hu => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Ici 0) = Iic 0 := by
        ext x
        simp
      rw [← hpre]
      simpa [Function.comp_def] using
        hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)
    · rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) u]
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset]
      simpa [smul_eq_mul] using hsign n (-u) (neg_nonneg.mpr hu)
  -- Reflect the absolutely-monotone data back to the original closed half-line.
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n t ht => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Iic 0) = Ici 0 := by
        ext x
        simp
      rw [← hpre]
      simpa [Function.comp_def] using
        hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ)
    · have hsign' := hsign n (-t) (mem_Iic.mpr (neg_nonpos.mpr ht))
      rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) (-t)] at hsign'
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset] at hsign'
      simpa [smul_eq_mul] using hsign'

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- A completely monotone function is `C^∞` on `[0, ∞)`. -/
@[grind →]
lemma contDiffOn (hf : IsCompletelyMonotone f) : ContDiffOn ℝ ∞ f (Ici 0) := hf.1

/-- The sign-alternation property of the iterated derivatives of a completely monotone
function: `0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. -/
@[grind =>]
lemma neg_one_pow_mul_iteratedDerivWithin_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t := hf.2 n t ht

/-- On the open half-line, the completely monotone sign condition can be read using ordinary
iterated derivatives instead of derivatives within `[0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := by
  have hnhds : Ici (0 : ℝ) ∈ 𝓝 t :=
    mem_of_superset (isOpen_Ioi.mem_nhds ht) Ioi_subset_Ici_self
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
    (mem_Ici.mpr ht.le)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le

/-- A completely monotone function is nonnegative on `[0, ∞)`. -/
@[grind =>]
lemma nonneg (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  simpa [iteratedDerivWithin_zero] using hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 0 ht

/-- The derivative within `[0, ∞)` of a completely monotone function is nonpositive: it is
nonincreasing. -/
@[grind =>]
lemma derivWithin_nonpos (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin f (Ici 0) t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 1 ht
  rw [pow_one, iteratedDerivWithin_one] at h
  linarith

/-- Complete monotonicity is determined by the values of the function on `[0, ∞)`: if `g` agrees
with a completely monotone `f` throughout `[0, ∞)`, then `g` is completely monotone too. Both the
smoothness clause and the sign condition only see the function within `[0, ∞)`. -/
lemma congr (hf : IsCompletelyMonotone f) (h : Set.EqOn g f (Ici 0)) :
    IsCompletelyMonotone g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_congr h (mem_Ici.mpr ht)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht


end IsCompletelyMonotone

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- For a completely monotone `f`, the `k`-th iterated derivative within `[0, ∞)` is
differentiable at any `t > 0`, with derivative the `(k+1)`-th iterated derivative. -/
lemma hasDerivAt_iteratedDerivWithin_succ
    (hcm : IsCompletelyMonotone f) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDerivWithin k f (Ici 0))
      (iteratedDerivWithin (k + 1) f (Ici 0) t) t := by
  have horder : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  exact ContDiffOn.hasDerivAt_iteratedDerivWithin (k := k)
    (hcm.contDiffOn.of_le horder) (uniqueDiffOn_Ici 0) (Ici_mem_nhds ht)

/-- Completely monotone functions are closed under addition. -/
lemma add (hf : IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    IsCompletelyMonotone (f + g) := by
  rw [isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg]
  convert (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hf).add
    (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hg) using 1
  ext u
  simp [Pi.add_apply]

/-- Completely monotone functions are closed under multiplication by a nonnegative constant. -/
lemma smul (hf : IsCompletelyMonotone f) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (c • f) := by
  rw [isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg]
  convert (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hf).smul hc using 1
  ext u
  simp [Pi.smul_apply, smul_eq_mul]

end IsCompletelyMonotone

/-- A nonnegative constant function is completely monotone. -/
lemma isCompletelyMonotone_const {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (fun _ : ℝ => c) := by
  refine ⟨contDiffOn_const, fun n t _ => ?_⟩
  rcases n with _ | n
  · simpa [iteratedDerivWithin_const] using hc
  · simp [iteratedDerivWithin_const]

/-- Completely monotone functions are closed under finite sums. -/
theorem IsCompletelyMonotone.sum {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, IsCompletelyMonotone (f i)) :
    IsCompletelyMonotone (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using isCompletelyMonotone_const (c := 0) le_rfl
  | @insert i s hi ih =>
      have hsum := (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
      exact hsum.congr fun t _ => by
        simp [hi, Pi.add_apply]

/-- The prototype completely monotone function `t ↦ e^{-x t}` for `x ≥ 0`. Its `n`-th
derivative is `(-x)ⁿ e^{-x t}`, so `(-1)ⁿ` times it is `xⁿ e^{-x t} ≥ 0`. -/
lemma isCompletelyMonotone_exp_neg_mul {x : ℝ} (hx : 0 ≤ x) :
    IsCompletelyMonotone (fun t => Real.exp (-x * t)) := by
  have hcd : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-x * t)) := by fun_prop
  refine ⟨hcd.contDiffOn, fun n t ht => ?_⟩
  have hcat : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => Real.exp (-x * t)) t :=
    hcd.contDiffAt.of_le (by exact_mod_cast le_top)
  have hval : iteratedDerivWithin n (fun t : ℝ => Real.exp (-x * t)) (Ici 0) t
      = (-x) ^ n * Real.exp (-x * t) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcat (mem_Ici.mpr ht),
      iteratedDeriv_exp_const_mul]
  have hpow : (0 : ℝ) ≤ (-1) ^ n * (-x) ^ n := by
    rw [← mul_pow, neg_one_mul, neg_neg]
    exact pow_nonneg hx n
  rw [hval, ← mul_assoc]
  exact mul_nonneg hpow (Real.exp_nonneg _)

/-- Complete monotonicity on the open half-line `(0, ∞)`: the function is `C^∞` there and its
ordinary iterated derivatives alternate in sign. This is the version used for derivatives of
Bernstein functions, whose right derivatives need not be finite at `0`. -/
@[expose] def IsCompletelyMonotoneOnIoi (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1) ^ n * iteratedDeriv n f t

namespace IsCompletelyMonotoneOnIoi

variable {f g : ℝ → ℝ}

/-- A completely monotone function on `(0, ∞)` is smooth there. -/
@[grind →]
lemma contDiffOn (hf : IsCompletelyMonotoneOnIoi f) : ContDiffOn ℝ ∞ f (Ioi 0) := hf.1

/-- The sign-alternation property on `(0, ∞)`. -/
@[grind =>]
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotoneOnIoi f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := hf.2 n t ht

/-- A completely monotone function on `(0, ∞)` is nonnegative there. -/
@[grind =>]
lemma nonneg (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  simpa [iteratedDeriv_zero] using hf.neg_one_pow_mul_iteratedDeriv_nonneg 0 ht

/-- A function completely monotone on `(0, ∞)` that is continuous within `[0, ∞)` at the origin
is nonnegative on all of `[0, ∞)`: nonnegativity on `(0, ∞)` passes to the boundary point `0` in
the limit. -/
lemma nonneg_of_continuousWithinAt (hf : IsCompletelyMonotoneOnIoi f)
    (hcont : ContinuousWithinAt f (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases ht.lt_or_eq with h | h
  · exact hf.nonneg h
  · subst h
    have htends : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (nhds (f 0)) :=
      hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact ge_of_tendsto htends (eventually_mem_nhdsWithin.mono fun x hx => hf.nonneg hx)

/-- The derivative of a completely monotone function on `(0, ∞)` is nonpositive there. -/
@[grind =>]
lemma deriv_nonpos (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) :
    deriv f t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDeriv_nonneg 1 ht
  rw [pow_one, iteratedDeriv_one] at h
  linarith

/-- Complete monotonicity on `(0, ∞)` is preserved by pointwise equality there. -/
lemma congr (hf : IsCompletelyMonotoneOnIoi f) (h : Set.EqOn g f (Ioi 0)) :
    IsCompletelyMonotoneOnIoi g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [Filter.EventuallyEq.iteratedDeriv_eq n (h.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht))]
  exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht

/-- Complete monotonicity on `(0, ∞)` is closed under addition. -/
lemma add (hf : IsCompletelyMonotoneOnIoi f) (hg : IsCompletelyMonotoneOnIoi g) :
    IsCompletelyMonotoneOnIoi (f + g) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun n t ht => ?_⟩
  rw [iteratedDeriv_add
    ((hf.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))
    ((hg.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))]
  simpa [mul_add] using add_nonneg (hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht)
    (hg.neg_one_pow_mul_iteratedDeriv_nonneg n ht)

/-- Complete monotonicity on `(0, ∞)` is closed under multiplication by a nonnegative constant. -/
lemma smul (hf : IsCompletelyMonotoneOnIoi f) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotoneOnIoi (c • f) := by
  refine ⟨hf.contDiffOn.const_smul c, fun n t ht => ?_⟩
  rw [iteratedDeriv_const_smul_field]
  simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    mul_nonneg hc (hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht)

/-- The closed-half-line Tau Ceti predicate restricts to complete monotonicity on `(0, ∞)`. -/
lemma _root_.TauCeti.IsCompletelyMonotone.isCompletelyMonotoneOnIoi
    (hf : IsCompletelyMonotone f) : IsCompletelyMonotoneOnIoi f :=
  ⟨hf.contDiffOn.mono Ioi_subset_Ici_self,
    fun n _ ht => hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht⟩

/-- Positive right-translates of a function completely monotone on `(0, ∞)` satisfy the
strong closed-half-line predicate: the shift moves the boundary into the open half-line, where
all derivatives exist. Compare `IsCompletelyMonotone.comp_add_const`, which keeps the strong
predicate under nonnegative translates. -/
lemma isCompletelyMonotone_comp_add_const (hf : IsCompletelyMonotoneOnIoi f) {a : ℝ}
    (ha : 0 < a) :
    IsCompletelyMonotone (fun t : ℝ => f (t + a)) := by
  refine ⟨?_, fun n t ht => ?_⟩
  · have hmaps : MapsTo (fun t : ℝ => t + a) (Ici 0) (Ioi 0) := fun t ht =>
      mem_Ioi.mpr (by linarith [mem_Ici.mp ht])
    exact hf.contDiffOn.comp (by fun_prop) hmaps
  · have htpa : 0 < t + a := by linarith
    have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => f (t + a)) t := by
      have hc : ContDiffAt ℝ (n : WithTop ℕ∞) f (t + a) :=
        (hf.contDiffOn.contDiffAt
          (isOpen_Ioi.mem_nhds htpa)).of_le (by exact_mod_cast le_top)
      simpa [Function.comp_def] using hc.comp t
        (by fun_prop : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => t + a) t)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont (mem_Ici.mpr ht),
      iteratedDeriv_comp_add_const]
    exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n htpa

end IsCompletelyMonotoneOnIoi

/-! ## Closed-half-line complete monotonicity -/

/-- Roadmap-level complete monotonicity on the closed half-line.

This is the classical finite-measure hypothesis: the function is continuous on `[0, ∞)` and
completely monotone on the open half-line `(0, ∞)`. It is weaker at the endpoint than the existing
`IsCompletelyMonotone`, which requires all derivatives within `[0, ∞)` to exist at `0`. -/
def IsCompletelyMonotoneOnIci (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ici 0) ∧ IsCompletelyMonotoneOnIoi f

/-- `IsCompletelyMonotoneOnIci f` unfolds to continuity on `[0, ∞)` and complete monotonicity on
the open half-line. -/
lemma isCompletelyMonotoneOnIci_iff {f : ℝ → ℝ} :
    IsCompletelyMonotoneOnIci f ↔
      ContinuousOn f (Ici 0) ∧ IsCompletelyMonotoneOnIoi f :=
  Iff.rfl

namespace IsCompletelyMonotoneOnIci

variable {f g : ℝ → ℝ}

/-- A closed-half-line completely monotone function is continuous on `[0, ∞)`. -/
@[grind →]
lemma continuousOn (hf : IsCompletelyMonotoneOnIci f) : ContinuousOn f (Ici 0) := hf.1

/-- A closed-half-line completely monotone function is completely monotone on `(0, ∞)`. -/
@[grind =>]
lemma isCompletelyMonotoneOnIoi (hf : IsCompletelyMonotoneOnIci f) :
    IsCompletelyMonotoneOnIoi f := hf.2

/-- The existing strong Tau Ceti predicate implies the roadmap-level closed-half-line predicate. -/
lemma of_isCompletelyMonotone (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotoneOnIci f :=
  ⟨hf.contDiffOn.continuousOn, hf.isCompletelyMonotoneOnIoi⟩

/-- Closed-half-line complete monotonicity is closed under addition. -/
lemma add (hf : IsCompletelyMonotoneOnIci f) (hg : IsCompletelyMonotoneOnIci g) :
    IsCompletelyMonotoneOnIci (f + g) :=
  ⟨hf.continuousOn.add hg.continuousOn,
    hf.isCompletelyMonotoneOnIoi.add hg.isCompletelyMonotoneOnIoi⟩

/-- Closed-half-line complete monotonicity is closed under multiplication by a nonnegative
constant. -/
lemma smul (hf : IsCompletelyMonotoneOnIci f) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotoneOnIci (c • f) :=
  ⟨hf.continuousOn.const_smul c, hf.isCompletelyMonotoneOnIoi.smul hc⟩



/-- A closed-half-line completely monotone function is nonincreasing on `[0, ∞)`: the
derivative is nonpositive on the interior and continuity extends the monotonicity to the
endpoint. -/
lemma antitoneOn (hf : IsCompletelyMonotoneOnIci f) : AntitoneOn f (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hf.continuousOn
    (by
      simpa [interior_Ici] using
        hf.isCompletelyMonotoneOnIoi.contDiffOn.differentiableOn (by simp))
    fun x hx => ?_
  rw [interior_Ici] at hx
  exact hf.isCompletelyMonotoneOnIoi.deriv_nonpos hx

/-- A closed-half-line completely monotone function is nonnegative on `[0, ∞)`:
nonnegativity on the open half-line passes to `0` by continuity. -/
@[grind =>]
lemma nonneg (hf : IsCompletelyMonotoneOnIci f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t :=
  hf.isCompletelyMonotoneOnIoi.nonneg_of_continuousWithinAt
    (hf.continuousOn.continuousWithinAt (by simp)) ht

/-- A closed-half-line completely monotone function is nonnegative at `0`. -/
lemma nonneg_zero (hf : IsCompletelyMonotoneOnIci f) : 0 ≤ f 0 :=
  hf.nonneg le_rfl

/-- A closed-half-line completely monotone function lies below its value at `0` on `[0, ∞)`. -/
lemma le_apply_zero (hf : IsCompletelyMonotoneOnIci f) {t : ℝ} (ht : 0 ≤ t) : f t ≤ f 0 :=
  hf.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht


/-- Closed-half-line complete monotonicity is determined by values on `[0, ∞)`. -/
lemma congr (hf : IsCompletelyMonotoneOnIci f) (h : EqOn g f (Ici 0)) :
    IsCompletelyMonotoneOnIci g := by
  refine ⟨hf.continuousOn.congr fun x hx => h hx, ?_⟩
  exact hf.isCompletelyMonotoneOnIoi.congr fun x hx => h (Ioi_subset_Ici_self hx)

/-- Closed-half-line complete monotonicity is closed under finite sums. -/
protected lemma sum {ι : Type*} {s : Finset ι} {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, IsCompletelyMonotoneOnIci (F i)) :
    IsCompletelyMonotoneOnIci (fun t => ∑ i ∈ s, F i t) := by
  have h := Finset.sum_induction F IsCompletelyMonotoneOnIci
    (fun _ _ => IsCompletelyMonotoneOnIci.add)
    (of_isCompletelyMonotone (isCompletelyMonotone_const le_rfl)) hF
  have heq : (∑ i ∈ s, F i) = fun t => ∑ i ∈ s, F i t := funext fun t => Finset.sum_apply t s F
  rwa [heq] at h

end IsCompletelyMonotoneOnIci

/-- The `max`-truncation of a function antitone on a closed half-line is antitone everywhere:
the shared totalization step of the half-line limit lemmas below. -/
private lemma antitone_comp_max {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a)) :
    Antitone fun t : ℝ => f (max t a) := fun _ _ hab =>
  hf (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max_right a hab)

/-- A function antitone and bounded below on a closed half-line converges at infinity. -/
private lemma exists_tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    (hbdd : BddBelow (f '' Ici a)) :
    ∃ L, Tendsto f atTop (𝓝 L) := by
  set g := fun t : ℝ => f (max t a) with hg
  have hg_anti : Antitone g := antitone_comp_max hf
  have hg_bdd : BddBelow (Set.range g) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨b, by rintro y ⟨t, rfl⟩; exact hb ⟨max t a, mem_Ici.mpr (le_max_right _ _), rfl⟩⟩
  refine ⟨⨅ i, g i, ?_⟩
  exact (tendsto_atTop_ciInf hg_anti hg_bdd).congr'
    (eventually_atTop.mpr ⟨a, fun t ht => by simp [hg, max_eq_left ht]⟩)

/-- A function antitone on a closed half-line lies above its limit at infinity there. -/
private lemma le_of_tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    {L : ℝ} (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : a ≤ T) : L ≤ f T := by
  set g₀ := fun t : ℝ => f (max t a) with hg₀
  have hg_anti : Antitone g₀ := antitone_comp_max hf
  have := hg_anti.le_of_tendsto
    (hL.congr' (eventually_atTop.mpr ⟨a, fun t ht => by simp [hg₀, max_eq_left ht]⟩)) T
  simpa [hg₀, max_eq_left hT] using this

namespace IsCompletelyMonotoneOnIci

variable {f : ℝ → ℝ}

/-- A closed-half-line completely monotone function has a limit `L ≥ 0` at infinity: it is
antitone on `[0, ∞)` and bounded below by `0`. -/
lemma exists_nonneg_tendsto_atTop (hf : IsCompletelyMonotoneOnIci f) :
    ∃ L, Tendsto f atTop (𝓝 L) ∧ 0 ≤ L := by
  obtain ⟨L, hL⟩ := exists_tendsto_atTop_of_antitoneOn_Ici hf.antitoneOn
    ⟨0, by rintro y ⟨x, hx, rfl⟩; exact hf.nonneg hx⟩
  exact ⟨L, hL, ge_of_tendsto hL (eventually_atTop.mpr ⟨0, fun t ht => hf.nonneg ht⟩)⟩

/-- A closed-half-line completely monotone function lies above its limit at infinity on
`[0, ∞)`. -/
lemma le_of_tendsto_atTop (hcm : IsCompletelyMonotoneOnIci f) {L : ℝ}
    (hL : Tendsto f atTop (𝓝 L)) {T : ℝ} (hT : 0 ≤ T) : L ≤ f T :=
  le_of_tendsto_atTop_of_antitoneOn_Ici hcm.antitoneOn hL hT

end IsCompletelyMonotoneOnIci

namespace IsCompletelyMonotone

variable {f : ℝ → ℝ}

/-- A completely monotone function is nonincreasing on `[0, ∞)`: the strong predicate
implies the closed-half-line one, whose monotonicity applies. -/
lemma antitoneOn (hf : IsCompletelyMonotone f) : AntitoneOn f (Ici 0) :=
  (IsCompletelyMonotoneOnIci.of_isCompletelyMonotone hf).antitoneOn

end IsCompletelyMonotone

end TauCeti
