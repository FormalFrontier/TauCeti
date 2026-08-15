/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# The vanishing order of a modular form

`TauCeti.orderOfVanishingAt f z` is the order of vanishing of `f : ℍ → ℂ` at `z ∈ ℍ`, read
as the meromorphic order of `f ∘ ofComplex` at `z`. For a nonzero holomorphic function it
detects vanishing (`orderOfVanishingAt_eq_zero_iff`), and it transports along the slash
action of any positive-determinant matrix (`orderOfVanishingAt_slash`); for a
slash-invariant form it is therefore constant along the group action
(`orderOfVanishingAt_smul`, a corollary) — the interior half of the order dictionary
feeding the valence formula. The order at the cusps (`ℚ`-normalized at
irregular cusps in odd weight) belongs to the general-level layer and is not defined here.

## Main declarations

* `TauCeti.orderOfVanishingAt`.
* `TauCeti.orderOfVanishingAt_eq_zero_iff`: for a nonzero holomorphic function, the order
  at `z` vanishes exactly when the function does not vanish at `z`.
* `TauCeti.orderOfVanishingAt_mul`: orders add under multiplication, with the
  `Finset.prod` and power versions.
* `TauCeti.orderOfVanishingAt_pos_iff`: for a nonzero holomorphic function, positive
  order characterizes the zeros.
* `TauCeti.orderOfVanishingAt_slash`: the order of a slash translate at `z` is the order at
  `γ • z`, for any positive-determinant `γ`.
* `TauCeti.orderOfVanishingAt_smul`: invariance along the action of the group, a corollary
  of the slash statement.
* `TauCeti.orderOfVanishingAt_eq_of_coe_eq_add`: invariance under the period translation, for
  a periodic function.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex TauCeti.UpperHalfPlane

open scoped ModularForm MatrixGroups Manifold

namespace TauCeti

/-- The order of vanishing of `f : ℍ → ℂ` at `z ∈ ℍ`: the meromorphic order of
`f ∘ ofComplex` at `z`, with the conventions that a function vanishing in a neighborhood
of `z` (in particular the zero function) and a function not meromorphic at `z` both get
order `0`. -/
def orderOfVanishingAt (f : ℍ → ℂ) (z : ℍ) : ℤ :=
  (meromorphicOrderAt (f ∘ ofComplex) (z : ℂ)).untop₀

/-- The defining equality of `orderOfVanishingAt`: the definition is sealed by the module
system, so this restatement is the supported cross-module rewrite for it. -/
-- Not a `simp` lemma: unfolding the definition is not a normal form, and `simpNF` rejects
-- it against the dictionary lemmas below.
lemma orderOfVanishingAt_def (f : ℍ → ℂ) (z : ℍ) :
    orderOfVanishingAt f z = (meromorphicOrderAt (f ∘ ofComplex) (z : ℂ)).untop₀ := by
  unfold orderOfVanishingAt
  rfl

variable {f : ℍ → ℂ}

/-- At a point where a function in meromorphic normal form does not vanish, its order is
zero. -/
lemma orderOfVanishingAt_eq_zero_of_ne_zero {z : ℍ}
    (hf : MeromorphicNFAt (f ∘ ofComplex) (z : ℂ)) (hz : f z ≠ 0) :
    orderOfVanishingAt f z = 0 := by
  have : (f ∘ ofComplex) (z : ℂ) ≠ 0 := by
    simpa [Function.comp_apply, ofComplex_apply] using hz
  rw [orderOfVanishingAt, hf.meromorphicOrderAt_eq_zero_iff.mpr this]
  rfl

private lemma meromorphicOrderAt_comp_ofComplex_ne_top (hf : MDiff f) (hne : f ≠ 0)
    (z : ℍ) : meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) ≠ ⊤ := by
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hne
  refine MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (fun w hw ↦ (analyticAt_comp_ofComplex hf hw).meromorphicAt)
    (Convex.isPreconnected (convex_halfSpace_im_gt 0)) τ.im_pos z.im_pos ?_
  rw [((analyticAt_comp_ofComplex hf τ.im_pos).meromorphicNFAt).meromorphicOrderAt_eq_zero_iff.mpr
    (by simpa [Function.comp_apply, ofComplex_apply] using hτ)]
  exact WithTop.zero_ne_top

/-- A zero of a nonzero holomorphic function on `ℍ` has nonzero vanishing order. -/
lemma orderOfVanishingAt_ne_zero_of_eq_zero (hf : MDiff f) (hne : f ≠ 0) {z : ℍ}
    (hz : f z = 0) : orderOfVanishingAt f z ≠ 0 := by
  have h_nf : MeromorphicNFAt (f ∘ ofComplex) (z : ℂ) :=
    (analyticAt_comp_ofComplex hf z.im_pos).meromorphicNFAt
  have h_ne : meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) ≠ 0 := fun h0 ↦
    h_nf.meromorphicOrderAt_eq_zero_iff.mp h0 (by simp [ofComplex_apply, hz])
  rw [orderOfVanishingAt]
  exact fun h ↦ h_ne (((WithTop.untop₀_eq_zero).mp h).resolve_right
    (meromorphicOrderAt_comp_ofComplex_ne_top hf hne z))

/-- For a nonzero holomorphic function on `ℍ`, the vanishing order at `z` is zero exactly
when the function does not vanish at `z`. -/
@[simp]
lemma orderOfVanishingAt_eq_zero_iff (hf : MDiff f) (hne : f ≠ 0) {z : ℍ} :
    orderOfVanishingAt f z = 0 ↔ f z ≠ 0 :=
  ⟨fun h hz ↦ orderOfVanishingAt_ne_zero_of_eq_zero hf hne hz h,
    orderOfVanishingAt_eq_zero_of_ne_zero
      (analyticAt_comp_ofComplex hf z.im_pos).meromorphicNFAt⟩

/-- Vanishing orders add under multiplication of nonzero holomorphic functions. -/
lemma orderOfVanishingAt_mul {g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g)
    (hfne : f ≠ 0) (hgne : g ≠ 0) (z : ℍ) :
    orderOfVanishingAt (f * g) z = orderOfVanishingAt f z + orderOfVanishingAt g z := by
  have hmul : (f * g) ∘ ofComplex = (f ∘ ofComplex) * (g ∘ ofComplex) := rfl
  rw [orderOfVanishingAt_def, orderOfVanishingAt_def, orderOfVanishingAt_def, hmul,
    meromorphicOrderAt_mul (analyticAt_comp_ofComplex hf z.im_pos).meromorphicAt
      (analyticAt_comp_ofComplex hg z.im_pos).meromorphicAt]
  exact WithTop.untop₀_add (meromorphicOrderAt_comp_ofComplex_ne_top hf hfne z)
    (meromorphicOrderAt_comp_ofComplex_ne_top hg hgne z)

private lemma untop₀_sum {ι : Type*} {s : Finset ι} {g : ι → WithTop ℤ}
    (hg : ∀ i ∈ s, g i ≠ ⊤) :
    (∑ i ∈ s, g i).untop₀ = ∑ i ∈ s, (g i).untop₀ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s his ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      WithTop.untop₀_add (hg i (Finset.mem_cons_self i s))
        (WithTop.sum_ne_top.mpr fun j hj ↦ hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj ↦ hg j (Finset.mem_cons_of_mem hj)]

/-- Constant functions have vanishing order zero everywhere (including the zero function,
by the order-zero convention). -/
@[simp]
lemma orderOfVanishingAt_const (c : ℂ) (z : ℍ) :
    orderOfVanishingAt (fun _ ↦ c) z = 0 := by
  classical
  -- Composition with a constant is definitionally constant; the composition equality is by
  -- `rfl` since no `ofComplex` value is consumed.
  have hcomp : (fun _ : ℍ ↦ c) ∘ ofComplex = fun _ ↦ c := rfl
  rw [orderOfVanishingAt_def, hcomp, meromorphicOrderAt_const]
  split_ifs <;> rfl

/-- The zero function has vanishing order zero everywhere, by the order-zero convention.

This is what lets the finiteness and finite-support statements downstream drop their
nonvanishing hypotheses: the degenerate case is not excluded, it is trivially true. -/
@[simp]
lemma orderOfVanishingAt_zero (z : ℍ) : orderOfVanishingAt 0 z = 0 :=
  orderOfVanishingAt_const 0 z

/-- The vanishing order of a holomorphic function is nonnegative. -/
lemma orderOfVanishingAt_nonneg (hf : MDiff f) (z : ℍ) : 0 ≤ orderOfVanishingAt f z := by
  rw [orderOfVanishingAt_def]
  exact WithTop.untop₀_nonneg.mpr
    (analyticAt_comp_ofComplex hf z.im_pos).meromorphicOrderAt_nonneg

/-- For a nonzero holomorphic function, the vanishing order at `z` is positive exactly
when the function vanishes at `z`. -/
@[simp]
lemma orderOfVanishingAt_pos_iff (hf : MDiff f) (hne : f ≠ 0) {z : ℍ} :
    0 < orderOfVanishingAt f z ↔ f z = 0 := by
  constructor
  · intro h
    by_contra hz
    rw [orderOfVanishingAt_eq_zero_of_ne_zero
      (analyticAt_comp_ofComplex hf z.im_pos).meromorphicNFAt hz] at h
    exact lt_irrefl 0 h
  · exact fun hz ↦ lt_of_le_of_ne (orderOfVanishingAt_nonneg hf z)
      (Ne.symm (orderOfVanishingAt_ne_zero_of_eq_zero hf hne hz))

/-- Vanishing orders sum over finite products of nonzero holomorphic functions. -/
lemma orderOfVanishingAt_prod {ι : Type*} {s : Finset ι} {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, MDiff (F i)) (hFne : ∀ i ∈ s, F i ≠ 0) (z : ℍ) :
    orderOfVanishingAt (∏ i ∈ s, F i) z = ∑ i ∈ s, orderOfVanishingAt (F i) z := by
  have hcomp : (∏ i ∈ s, F i) ∘ ofComplex = fun w ↦ ∏ i ∈ s, (F i ∘ ofComplex) w :=
    funext fun w ↦ Finset.prod_apply ..
  simp only [orderOfVanishingAt_def]
  rw [hcomp, meromorphicOrderAt_fun_prod
    (fun i hi ↦ (analyticAt_comp_ofComplex (hF i hi) z.im_pos).meromorphicAt)]
  exact untop₀_sum fun i hi ↦
    meromorphicOrderAt_comp_ofComplex_ne_top (hF i hi) (hFne i hi) z

/-- Vanishing orders scale under powers of a holomorphic function. -/
lemma orderOfVanishingAt_pow (hf : MDiff f) (n : ℕ) (z : ℍ) :
    orderOfVanishingAt (f ^ n) z = n * orderOfVanishingAt f z := by
  have hcomp : (f ^ n) ∘ ofComplex = (f ∘ ofComplex) ^ n := rfl
  rw [orderOfVanishingAt_def, orderOfVanishingAt_def, hcomp,
    meromorphicOrderAt_pow (analyticAt_comp_ofComplex hf z.im_pos).meromorphicAt,
    WithTop.untop₀_mul]
  simp

variable {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]

/-- The vanishing order of a slash translate: the order of `g ∣[k] γ` at `z` is the order of
`g` at `γ • z`. Positive determinant makes the slash's `σ γ` twist trivial and keeps the
Möbius action on `ℍ`; no invariance of `g` under `γ` is assumed. -/
@[simp]
lemma orderOfVanishingAt_slash (g : ℍ → ℂ) {γ : GL (Fin 2) ℝ}
    (hdet : 0 < γ.val.det) (z : ℍ) :
    orderOfVanishingAt (g ∣[k] γ) z = orderOfVanishingAt g (γ • z) := by
  have hden_ne : denom γ (z : ℂ) ≠ 0 := denom_ne_zero γ z
  have hdet_ne : ((|(γ.det : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (γ.det : ℝˣ).ne_zero).ne'
  have hcongr : ((g ∣[k] γ) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w : ℂ ↦ ((|(γ.det : ℝ)| : ℝ) : ℂ) ^ (k - 1) * denom γ w ^ (-k)) *
        (fun w : ℂ ↦ g (γ • ofComplex w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    rw [Function.comp_apply, ModularForm.slash_apply_of_det_pos k hdet g (ofComplex w),
      Pi.mul_apply, ofComplex_apply_of_im_pos hw]
    ring
  -- `denom` is unfolded only here, where `fun_prop` needs to see the linear form in `w`.
  have h_an : AnalyticAt ℂ (fun w : ℂ ↦ ((|(γ.det : ℝ)| : ℝ) : ℂ) ^ (k - 1) *
      denom γ w ^ (-k)) (z : ℂ) :=
    AnalyticAt.mul analyticAt_const
      (AnalyticAt.zpow (by unfold denom; fun_prop) hden_ne)
  have h_ne : ((|(γ.det : ℝ)| : ℝ) : ℂ) ^ (k - 1) * denom γ (z : ℂ) ^ (-k) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hdet_ne) (zpow_ne_zero _ hden_ne)
  unfold orderOfVanishingAt
  rw [meromorphicOrderAt_congr (hcongr.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_mul_of_ne_zero h_an h_ne, meromorphicOrderAt_comp_smul hdet,
    Function.comp_def]

/-- The vanishing order of a slash-invariant form is constant along the action of any
positive-determinant element of the group. -/
-- Not a `simp` lemma: the subgroup `Γ` occurs only in the hypotheses, so `simpNF` rejects
-- the annotation (`simp` could never instantiate it from the left-hand side).
lemma orderOfVanishingAt_smul [SlashInvariantFormClass F Γ k] (f : F) {γ}
    (hγ : γ ∈ Γ) (hdet : 0 < γ.val.det) (z : ℍ) :
    orderOfVanishingAt f (γ • z) = orderOfVanishingAt f z := by
  rw [← orderOfVanishingAt_slash (k := k) (⇑f) hdet z,
    SlashInvariantFormClass.slash_action_eq f γ hγ]

/-- The meromorphic order of a `c`-periodic function agrees at `z + c` and at `z`. Only a proof
helper for `orderOfVanishingAt_eq_of_coe_eq_add`: it is a fact about periodic functions on `ℂ`,
with no modular-forms content, so it is not exported from this module. -/
private theorem meromorphicOrderAt_add_of_periodic {g : ℂ → ℂ} {c : ℂ}
    (hper : Function.Periodic g c) (z : ℂ) :
    meromorphicOrderAt g (z + c) = meromorphicOrderAt g z := by
  rw [← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := g) (c := c) (x := z)]
  exact congrArg (fun h => meromorphicOrderAt h z) (funext fun x => hper x)

/-- The vanishing order of a `c`-periodic function on `ℍ` agrees at `z` and at `z + c`. For a
level-one form and `c = 1` this is what makes the two `ρ`-corners of the fundamental domain
contribute equally to the valence formula. -/
theorem orderOfVanishingAt_eq_of_coe_eq_add {c : ℂ} (hper : Function.Periodic (f ∘ ofComplex) c)
    {z w : ℍ} (hzw : (w : ℂ) = (z : ℂ) + c) :
    orderOfVanishingAt f w = orderOfVanishingAt f z := by
  rw [orderOfVanishingAt_def, orderOfVanishingAt_def, hzw,
    meromorphicOrderAt_add_of_periodic hper]


end TauCeti

end
