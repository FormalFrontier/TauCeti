/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# Bernstein functions

A *Bernstein function* is a nonnegative continuous function `f : ℝ → ℝ` on the closed half-line
`[0, ∞)`, smooth on the open half-line `(0, ∞)`, whose ordinary derivative is completely
monotone on `(0, ∞)`. Equivalently `f ≥ 0` and `f'` alternates in sign through every order:
`0 ≤ f'`, `0 ≥ f''`, `0 ≤ f'''`, and so on. These are exactly the functions `f` for which
`t ↦ e^{-s f(t)}` is completely monotone for every `s ≥ 0`; in probability they are the
Laplace exponents of subordinators, and the completely-monotone ↔ Bernstein correspondence
(a Bernstein function has completely monotone derivative, and a completely monotone function
composed with a Bernstein function stays completely monotone) is the backbone of the
Lévy–Khinchine theory.

The open-half-line smoothness clause is essential: an iterated derivative defaults to a junk
value where the function fails to be differentiable, so without smoothness on `(0, ∞)` a badly
behaved `f` could be declared "Bernstein" because its junk derivative `0` is (vacuously)
completely monotone. Continuity at the boundary is kept separate, so the definition includes
standard examples whose right derivative blows up at `0`.

A Bernstein function is nondecreasing (its derivative is nonnegative) and concave (its derivative
is nonincreasing) on `[0, ∞)`; both are recorded below. The class is closed under sums and
nonnegative scalar multiples, and the basic catalogue — constants, the identity, affine functions
`t ↦ c + d t` with `c, d ≥ 0`, and the prototype `t ↦ 1 - e^{-x t}` — is built from these.

## Main declarations

* `TauCeti.IsBernsteinFunction`: the predicate that `f` is continuous and nonnegative on
  `[0, ∞)`, smooth on `(0, ∞)`, and has completely monotone ordinary derivative on `(0, ∞)`.
* `TauCeti.IsBernsteinFunction.nonneg`, `TauCeti.IsBernsteinFunction.deriv_nonneg`,
  `TauCeti.IsBernsteinFunction.monotoneOn`, `TauCeti.IsBernsteinFunction.concaveOn`: a Bernstein
  function is nonnegative, has nonnegative derivative, is nondecreasing, and is concave on
  `[0, ∞)`.
* `TauCeti.IsBernsteinFunction.congr`: the property depends only on the values on `[0, ∞)`.
* `TauCeti.IsBernsteinFunction.add`, `TauCeti.IsBernsteinFunction.smul`,
  `TauCeti.IsBernsteinFunction.const_add`, `TauCeti.IsBernsteinFunction.sum`: closure under sums,
  nonnegative scalar multiples, adding a nonnegative constant, and finite sums.
* `TauCeti.isBernsteinFunction_const`, `TauCeti.isBernsteinFunction_id`,
  `TauCeti.isBernsteinFunction_affine`, `TauCeti.isBernsteinFunction_one_sub_exp_neg_mul`: the
  basic examples.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A function `f : ℝ → ℝ` is a **Bernstein function** if it is continuous and nonnegative on
`[0, ∞)`, `C^∞` on `(0, ∞)`, and its ordinary derivative is completely monotone on `(0, ∞)`.
The open-half-line derivative condition is the standard one and permits boundary singularities
such as the right derivative of `sqrt` at `0`. -/
def IsBernsteinFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ici 0) ∧ ContDiffOn ℝ ∞ f (Ioi 0) ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ f t) ∧ IsCompletelyMonotoneOnIoi (deriv f)

/-- A function is Bernstein exactly when it is continuous and nonnegative on `[0, ∞)`, smooth
on `(0, ∞)`, and has completely monotone derivative there. The body of `IsBernsteinFunction` is
not `@[expose]`d, so this is how downstream files build the predicate from its four clauses. -/
theorem isBernsteinFunction_iff {f : ℝ → ℝ} :
    IsBernsteinFunction f ↔
      ContinuousOn f (Ici 0) ∧ ContDiffOn ℝ ∞ f (Ioi 0) ∧
        (∀ t : ℝ, 0 ≤ t → 0 ≤ f t) ∧ IsCompletelyMonotoneOnIoi (deriv f) :=
  Iff.rfl

namespace IsBernsteinFunction

variable {f g : ℝ → ℝ}

/-- A Bernstein function is continuous on `[0, ∞)`. -/
lemma continuousOn (hf : IsBernsteinFunction f) : ContinuousOn f (Ici 0) := hf.1

/-- A Bernstein function is `C^∞` on `(0, ∞)`. -/
@[grind →]
lemma contDiffOn (hf : IsBernsteinFunction f) : ContDiffOn ℝ ∞ f (Ioi 0) := hf.2.1

/-- A Bernstein function is nonnegative on `[0, ∞)`. -/
@[grind =>]
lemma nonneg (hf : IsBernsteinFunction f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := hf.2.2.1 t ht

/-- The ordinary derivative of a Bernstein function is completely monotone on `(0, ∞)`. -/
@[grind =>]
lemma deriv_isCompletelyMonotoneOnIoi (hf : IsBernsteinFunction f) :
    IsCompletelyMonotoneOnIoi (deriv f) := hf.2.2.2

/-- A Bernstein function is differentiable on `(0, ∞)`. -/
lemma differentiableOn (hf : IsBernsteinFunction f) : DifferentiableOn ℝ f (Ioi 0) :=
  hf.contDiffOn.differentiableOn (by simp)

/-- The derivative of a Bernstein function is nonnegative on `(0, ∞)`: a Bernstein function is
nondecreasing. -/
@[grind =>]
lemma deriv_nonneg (hf : IsBernsteinFunction f) {t : ℝ} (ht : 0 < t) : 0 ≤ deriv f t :=
  hf.deriv_isCompletelyMonotoneOnIoi.nonneg ht

/-- A Bernstein function is nondecreasing on `[0, ∞)`. -/
lemma monotoneOn (hf : IsBernsteinFunction f) : MonotoneOn f (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuousOn
    (hf.differentiableOn.mono (by rw [interior_Ici])) fun x hx => ?_
  rw [interior_Ici] at hx
  exact hf.deriv_nonneg hx

/-- A Bernstein function is concave on `[0, ∞)`: its derivative is nonincreasing. -/
lemma concaveOn (hf : IsBernsteinFunction f) : ConcaveOn ℝ (Ici 0) f := by
  refine concaveOn_of_deriv2_nonpos (convex_Ici 0) hf.continuousOn
    (hf.differentiableOn.mono (by rw [interior_Ici]))
    ((hf.deriv_isCompletelyMonotoneOnIoi.contDiffOn.differentiableOn (by simp)).mono
      (by rw [interior_Ici]))
    fun x hx => ?_
  rw [interior_Ici] at hx
  simpa [Function.iterate_succ, Function.iterate_zero, Function.comp_def] using
    hf.deriv_isCompletelyMonotoneOnIoi.deriv_nonpos hx

/-- Being a Bernstein function depends only on the values on `[0, ∞)`. -/
theorem congr (hf : IsBernsteinFunction f) (h : Set.EqOn g f (Ici 0)) :
    IsBernsteinFunction g := by
  have hIoi : Set.EqOn g f (Ioi 0) := h.mono Ioi_subset_Ici_self
  have hderiv : Set.EqOn (deriv g) (deriv f) (Ioi 0) := fun x hx =>
    (hIoi.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx)).deriv_eq
  refine ⟨hf.continuousOn.congr h, hf.contDiffOn.congr fun x hx => hIoi hx, fun t ht => ?_, ?_⟩
  · rw [h ht]
    exact hf.nonneg ht
  · exact hf.deriv_isCompletelyMonotoneOnIoi.congr hderiv

/-- Bernstein functions are closed under addition. -/
theorem add (hf : IsBernsteinFunction f) (hg : IsBernsteinFunction g) :
    IsBernsteinFunction (f + g) := by
  refine ⟨hf.continuousOn.add hg.continuousOn, hf.contDiffOn.add hg.contDiffOn,
    fun t ht => add_nonneg (hf.nonneg ht) (hg.nonneg ht), ?_⟩
  have hd : Set.EqOn (deriv (f + g)) (deriv f + deriv g) (Ioi 0) := by
    intro x hx
    rw [Pi.add_apply,
      deriv_add (hf.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds hx))
        (hg.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds hx))]
  exact (hf.deriv_isCompletelyMonotoneOnIoi.add hg.deriv_isCompletelyMonotoneOnIoi).congr hd

/-- Bernstein functions are closed under multiplication by a nonnegative constant. -/
theorem smul (hf : IsBernsteinFunction f) {c : ℝ} (hc : 0 ≤ c) :
    IsBernsteinFunction (c • f) := by
  refine ⟨hf.continuousOn.const_smul c, hf.contDiffOn.const_smul c, fun t ht => ?_, ?_⟩
  · simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hc (hf.nonneg ht)
  have hd : Set.EqOn (deriv (c • f)) (c • deriv f) (Ioi 0) := by
    intro x hx
    rw [Pi.smul_apply,
      deriv_const_smul c (hf.differentiableOn.differentiableAt (isOpen_Ioi.mem_nhds hx))]
  exact (hf.deriv_isCompletelyMonotoneOnIoi.smul hc).congr hd

end IsBernsteinFunction

/-- A nonnegative constant function is a Bernstein function. -/
theorem isBernsteinFunction_const {c : ℝ} (hc : 0 ≤ c) :
    IsBernsteinFunction (fun _ : ℝ => c) := by
  refine ⟨continuousOn_const, contDiffOn_const, fun _ _ => hc, ?_⟩
  refine ⟨?_, fun n t _ => ?_⟩
  · simpa [deriv_const] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (0 : ℝ)) (Ioi 0))
  rcases n with _ | n
  · simp
  · simp

/-- The zero function is a Bernstein function. -/
theorem isBernsteinFunction_zero : IsBernsteinFunction (fun _ : ℝ => (0 : ℝ)) :=
  isBernsteinFunction_const le_rfl

namespace IsBernsteinFunction

/-- Adding a nonnegative constant to a Bernstein function again gives a Bernstein function. -/
theorem const_add {f : ℝ → ℝ} (hf : IsBernsteinFunction f) {c : ℝ} (hc : 0 ≤ c) :
    IsBernsteinFunction (fun t => c + f t) :=
  ((isBernsteinFunction_const hc).add hf).congr fun _ _ => by simp [Pi.add_apply]

/-- Bernstein functions are closed under finite sums. -/
theorem sum {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ} (hf : ∀ i ∈ s, IsBernsteinFunction (f i)) :
    IsBernsteinFunction (fun t => ∑ i ∈ s, f i t) := by
  have h := Finset.sum_induction f IsBernsteinFunction (fun _ _ => IsBernsteinFunction.add)
    isBernsteinFunction_zero hf
  have heq : (∑ i ∈ s, f i) = fun t => ∑ i ∈ s, f i t := funext fun t => Finset.sum_apply t s f
  rwa [heq] at h

end IsBernsteinFunction

/-- The identity function is a Bernstein function: it is nonnegative on `[0, ∞)` with constant
derivative `1`. -/
theorem isBernsteinFunction_id : IsBernsteinFunction (fun t : ℝ => t) := by
  refine ⟨continuousOn_id, contDiffOn_id, fun t ht => ht, ?_⟩
  have hd : Set.EqOn (deriv (fun t : ℝ => t)) (fun _ => (1 : ℝ)) (Ioi 0) := by
    intro x hx
    simp [deriv_id'']
  exact (isCompletelyMonotone_const zero_le_one).isCompletelyMonotoneOnIoi.congr hd

/-- An affine function `t ↦ c + d t` with nonnegative coefficients is a Bernstein function. -/
theorem isBernsteinFunction_affine {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsBernsteinFunction (fun t : ℝ => c + d * t) := by
  have h := (isBernsteinFunction_const hc).add (isBernsteinFunction_id.smul hd)
  have heq : ((fun _ : ℝ => c) + (d • fun t : ℝ => t)) = fun t : ℝ => c + d * t := by
    funext t; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rwa [heq] at h

/-- The prototype Bernstein function `t ↦ 1 - e^{-x t}` for `x ≥ 0`: it is nonnegative on
`[0, ∞)` and its derivative `t ↦ x e^{-x t}` is completely monotone. -/
theorem isBernsteinFunction_one_sub_exp_neg_mul {x : ℝ} (hx : 0 ≤ x) :
    IsBernsteinFunction (fun t : ℝ => 1 - Real.exp (-x * t)) := by
  -- The derivative is `t ↦ x e^{-x t}`, computed once and for all.
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 - Real.exp (-x * t))
      (x * Real.exp (-x * t)) t := by
    intro t
    have hb : HasDerivAt (fun t : ℝ => -x * t) (-x) t := by
      simpa using (hasDerivAt_id t).const_mul (-x)
    have he := (hb.exp).const_sub 1
    have key : x * Real.exp (-x * t) = -(Real.exp (-x * t) * -x) := by ring
    rw [key]; exact he
  refine ⟨?_, ?_, fun t ht => ?_, ?_⟩
  · fun_prop
  · fun_prop
  · -- `e^{-x t} ≤ 1` because `-x t ≤ 0`.
    have hle : Real.exp (-x * t) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  · have hcm : IsCompletelyMonotoneOnIoi (x • fun t : ℝ => Real.exp (-x * t)) :=
      ((isCompletelyMonotone_exp_neg_mul hx).smul hx).isCompletelyMonotoneOnIoi
    · have hd : Set.EqOn (deriv (fun t : ℝ => 1 - Real.exp (-x * t)))
          (x • fun t : ℝ => Real.exp (-x * t)) (Ioi 0) := by
        intro t ht
        rw [(hderiv t).deriv]
        simp [Pi.smul_apply, smul_eq_mul]
      exact hcm.congr hd

end TauCeti
