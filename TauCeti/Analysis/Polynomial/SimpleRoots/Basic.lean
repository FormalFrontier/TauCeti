/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Polynomial.SymmetricPower
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.FieldTheory.Separable

/-!
# Simple roots depend analytically on the coefficients

`TauCeti.Sym.coeffEquiv` presents the `n`-th symmetric power of an algebraically closed field as
the affine space `Fin n → K` of coefficient tuples, and
`TauCeti/Analysis/Polynomial/SymmetricPower.lean` proves that presentation a *homeomorphism*: the
roots of a monic polynomial depend continuously on its coefficients. This file upgrades continuity
to **analyticity** wherever the roots are simple, which is the analytic input that the elementary
symmetric charts of `Sym^g(Σ)` need in order to be holomorphic.

## The argument

The roots are not a polynomial function of the coefficients, so nothing here is formal. The whole
file rests on one application of the implicit function theorem to the *free monic polynomial*

`f (c, z) = z ^ n + ∑ i, c i * z ^ i`,

that is, to `TauCeti.Polynomial.monicOfCoeff`, the specialization of Mathlib's
`Polynomial.freeMonic` at a concrete coefficient tuple. It is a polynomial in the coefficient tuple
`c` and the argument `z` jointly, hence analytic. Its partial derivative in `z` at a point
`(c₀, z₀)` is the scalar `P'(z₀)`, where `P` is the monic polynomial with lower coefficients `c₀`;
multiplication by that scalar is an invertible operator exactly when `z₀` is a **simple** root of
`P`. The implicit function theorem then produces a function `ψ` of the coefficients, analytic at
`c₀`, with `ψ c₀ = z₀`, whose value stays a root of the nearby polynomials:
`TauCeti.Polynomial.exists_analyticAt_isRoot_monicOfCoeff`.

Applying this at each of the `n` roots of a polynomial whose roots are pairwise distinct, and
noting that pairwise distinctness persists in a neighbourhood, gives an analytic *ordered*
parametrization `Ψ` of the whole unordered root tuple:
`TauCeti.Polynomial.exists_analyticAt_monicOfCoeff_eq_prod_X_sub_C`. That is the multiplicity-free
half of the statement "the inverse elementary symmetric chart is holomorphic"; the diagonal, where
roots collide, is genuinely harder and is not treated here.

Note that no ordering of the roots is canonical: the conclusion is the existence of an analytic
ordered lift of the (unordered) inverse chart, not analyticity of a preferred root function.

## Main declarations

* `TauCeti.Polynomial.analyticAt_eval_monicOfCoeff`: the free monic polynomial is analytic in its
  coefficients and its argument jointly.
* `TauCeti.Polynomial.exists_analyticAt_isRoot_monicOfCoeff`: **a simple root moves analytically**
  with the coefficients.
* `TauCeti.Polynomial.exists_analyticAt_monicOfCoeff_eq_prod_X_sub_C`: a monic polynomial with `n`
  distinct roots has an analytic ordered parametrization of its roots on a neighbourhood of its
  coefficient tuple.
* `TauCeti.Sym.exists_analyticAt_coeffEquiv_symm_eq_ofFn`: the same statement read through the
  elementary symmetric chart, as an analytic ordered lift of the inverse chart.
* `TauCeti.Sym.exists_analyticAt_coeffEquiv_ofFn_localInverse`: **the coefficient map of an
  ordered tuple is a local analytic isomorphism** at every tuple of pairwise distinct points, the
  ordered lift being a two-sided local inverse there.
* `TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm`: **a coordinate change acts analytically
  on the elementary symmetric coordinates at multiplicity-free points**. A map `φ` of the
  underlying field induces a map of coefficient tuples, sending the coefficients of a polynomial to
  those of the polynomial whose roots are the `φ`-images of its roots; it is analytic at every
  coefficient tuple whose roots are distinct and at which `φ` is analytic.

Lane F4.1 of the analytic Heegaard Floer roadmap opens with "`Sym^g(Σ)` geometry: smooth complex
structure (elementary symmetric functions)", after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1). A holomorphic coordinate on the
surface identifies a neighbourhood in `Sym^g(Σ)` with an open subset of `Sym^g(ℂ)`
(`TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`), and
`TauCeti.Sym.analyticAt_coeffEquiv_map_coeffEquiv_symm` says that changing that coordinate acts
analytically on the elementary symmetric coordinates of one such patch, at multiplicity-free
tuples. That is the analytic ingredient for the transition maps of the atlas of
`TauCeti/Geometry/Manifold/SymmetricPower.lean`. A chart there splits a tuple into the factors
lying in `k` disjoint patches, of degrees `m 1, …, m k`, and regroups the resulting blocks of
coefficients along a bijection `(Σ i, Fin (m i)) ≃ Fin n`; that assembly is carried out in
`TauCeti/Analysis/Polynomial/SimpleRoots/Family.lean`. The diagonal, where the points of a tuple
collide, is not treated here.

Everything is stated over an `RCLike` field, so it covers the real as well as the complex case,
except for the elementary polynomial calculus, which needs only a nontrivially normed field; only
the statements that mention the chart itself need the field algebraically closed.
-/

public section

open Filter Polynomial Topology
open scoped ContDiff

namespace TauCeti

namespace Polynomial

/-! ### The free monic polynomial -/

section Elementary

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The free monic polynomial of degree `n`, evaluated at a coefficient tuple and an argument, is
analytic in the two jointly: it is `z ^ n + ∑ i, c i * z ^ i`. -/
theorem analyticAt_eval_monicOfCoeff (q : (Fin n → 𝕜) × 𝕜) :
    AnalyticAt 𝕜 (fun p : (Fin n → 𝕜) × 𝕜 => (monicOfCoeff p.1).eval p.2) q := by
  have hsnd : AnalyticAt 𝕜 (fun p : (Fin n → 𝕜) × 𝕜 => p.2) q := analyticAt_snd
  have hfst : ∀ i : Fin n, AnalyticAt 𝕜 (fun p : (Fin n → 𝕜) × 𝕜 => p.1 i) q := fun i =>
    ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).analyticAt _).comp
      analyticAt_fst
  simp only [eval_monicOfCoeff]
  exact (hsnd.pow n).add (Finset.univ.analyticAt_fun_sum fun i _ => (hfst i).mul (hsnd.pow _))

end Elementary

/-! ### A simple root moves analytically -/

section SimpleRoot

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- **A simple root moves analytically.** If `z₀` is a root of the monic polynomial with lower
coefficients `c₀` at which the derivative does not vanish, then there is a function `ψ` of the
coefficients, analytic at `c₀`, with `ψ c₀ = z₀`, whose value at every nearby coefficient tuple is
a root of the corresponding monic polynomial.

This is the implicit function theorem applied to the free monic polynomial: its partial derivative
in the argument is multiplication by `P'(z₀)`, which is invertible exactly under the simplicity
hypothesis. -/
theorem exists_analyticAt_isRoot_monicOfCoeff {c₀ : Fin n → 𝕜} {z₀ : 𝕜}
    (hroot : (monicOfCoeff c₀).IsRoot z₀)
    (hsimple : (derivative (monicOfCoeff c₀)).eval z₀ ≠ 0) :
    ∃ ψ : (Fin n → 𝕜) → 𝕜, ψ c₀ = z₀ ∧ AnalyticAt 𝕜 ψ c₀ ∧
      ∀ᶠ c in 𝓝 c₀, (monicOfCoeff c).IsRoot (ψ c) := by
  set f : (Fin n → 𝕜) × 𝕜 → 𝕜 := fun p => (monicOfCoeff p.1).eval p.2
  have cdf : ContDiffAt 𝕜 ω f (c₀, z₀) := (analyticAt_eval_monicOfCoeff _).contDiffAt
  set e : 𝕜 ≃L[𝕜] 𝕜 := ContinuousLinearEquiv.unitsEquivAut 𝕜 (Units.mk0 _ hsimple)
  have hpartial : HasFDerivAt (fun z : 𝕜 => f (c₀, z)) (e : 𝕜 →L[𝕜] 𝕜) z₀ :=
    ((monicOfCoeff c₀).hasDerivAt z₀).hasFDerivAt_equiv hsimple
  have hdiff : HasFDerivAt f (fderiv 𝕜 f (c₀, z₀)) (c₀, z₀) :=
    (cdf.differentiableAt (by simp)).hasFDerivAt
  have hinr : HasFDerivAt (fun z : 𝕜 => ((c₀ : Fin n → 𝕜), z))
      (ContinuousLinearMap.inr 𝕜 (Fin n → 𝕜) 𝕜) z₀ :=
    (hasFDerivAt_const c₀ z₀).prodMk (hasFDerivAt_id z₀)
  have hcomp : fderiv 𝕜 f (c₀, z₀) ∘L ContinuousLinearMap.inr 𝕜 (Fin n → 𝕜) 𝕜
      = (e : 𝕜 →L[𝕜] 𝕜) := (hdiff.comp z₀ hinr).unique hpartial
  have if₂ : (fderiv 𝕜 f (c₀, z₀) ∘L ContinuousLinearMap.inr 𝕜 (Fin n → 𝕜) 𝕜).IsInvertible := by
    rw [hcomp]
    exact ⟨e, rfl⟩
  refine ⟨cdf.implicitFunction (by simp) if₂, cdf.implicitFunction_apply_self _ if₂,
    (cdf.contDiffAt_implicitFunction _ if₂).analyticAt, ?_⟩
  filter_upwards [cdf.eventually_apply_implicitFunction (by simp) if₂] with c hc
  have h₀ : f (c₀, z₀) = 0 := hroot
  exact hc.trans h₀

/-! ### An analytic ordered parametrization of a multiplicity-free root tuple -/

/-- **The roots of a monic polynomial with distinct roots move analytically.** If the monic
polynomial with lower coefficients `c₀` is `∏ i, (X - z i)` for a tuple `z` of pairwise distinct
points, then there is a tuple-valued function `Ψ`, analytic at `c₀`, with `Ψ c₀ = z`, which orders
the roots of every nearby monic polynomial.

No ordering of the roots is canonical, so the ordered lift `Ψ` is not unique; what is asserted is
that some analytic ordering exists near `c₀`. -/
theorem exists_analyticAt_monicOfCoeff_eq_prod_X_sub_C {c₀ z : Fin n → 𝕜}
    (hz : Function.Injective z) (hc₀ : monicOfCoeff c₀ = ∏ i, (X - C (z i))) :
    ∃ Ψ : (Fin n → 𝕜) → (Fin n → 𝕜), Ψ c₀ = z ∧ AnalyticAt 𝕜 Ψ c₀ ∧
      ∀ᶠ c in 𝓝 c₀, monicOfCoeff c = ∏ i, (X - C (Ψ c i)) := by
  have hroot : ∀ i, (monicOfCoeff c₀).eval (z i) = 0 := by
    intro i
    rw [hc₀, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hsep : (monicOfCoeff c₀).Separable := hc₀ ▸ separable_prod_X_sub_C_iff.2 hz
  have hsimple : ∀ i, (derivative (monicOfCoeff c₀)).eval (z i) ≠ 0 := fun i =>
    hsep.eval₂_derivative_ne_zero (RingHom.id 𝕜) (hroot i)
  choose ψ hψ₀ hψa hψr using fun i => exists_analyticAt_isRoot_monicOfCoeff (hroot i) (hsimple i)
  refine ⟨fun c i => ψ i c, funext hψ₀, AnalyticAt.pi hψa, ?_⟩
  have hne : ∀ i j : Fin n, ∀ᶠ c in 𝓝 c₀, i ≠ j → ψ i c ≠ ψ j c := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · exact .of_forall fun _ h => absurd rfl h
    · filter_upwards [((hψa i).continuousAt.ne_iff_eventually_ne (hψa j).continuousAt).1
        (by rw [hψ₀ i, hψ₀ j]; exact fun h => hij (hz h))] with c hc _ using hc
  filter_upwards [eventually_all.2 hψr,
    eventually_all.2 fun i => eventually_all.2 fun j => hne i j] with c hcr hcne
  have hcinj : Function.Injective fun i => ψ i c := fun i j hij => by
    by_contra h
    exact hcne i j h hij
  exact (Sym.toMonic_ofFn_eq_of_forall_isRoot (monic_monicOfCoeff c) (natDegree_monicOfCoeff c)
    hcinj hcr).symm.trans (Sym.toMonic_ofFn _)

end SimpleRoot

end Polynomial

namespace Sym

section AlgClosed

variable {𝕜 : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] {n : ℕ}

/-- The inverse elementary symmetric chart admits an analytic ordered lift at every
multiplicity-free coefficient tuple: near such a tuple the unordered root tuple is `ofFn` of an
analytic ordered tuple. -/
theorem exists_analyticAt_coeffEquiv_symm_eq_ofFn {c₀ z : Fin n → 𝕜} (hz : Function.Injective z)
    (hc₀ : (coeffEquiv 𝕜 n).symm c₀ = ofFn z) :
    ∃ Ψ : (Fin n → 𝕜) → (Fin n → 𝕜), Ψ c₀ = z ∧ AnalyticAt 𝕜 Ψ c₀ ∧
      ∀ᶠ c in 𝓝 c₀, (coeffEquiv 𝕜 n).symm c = ofFn (Ψ c) := by
  obtain ⟨Ψ, hΨ₀, hΨa, hΨ⟩ :=
    Polynomial.exists_analyticAt_monicOfCoeff_eq_prod_X_sub_C hz
      (((toMonic_coeffEquiv_symm c₀).symm.trans (by rw [hc₀])).trans (toMonic_ofFn z))
  refine ⟨Ψ, hΨ₀, hΨa, ?_⟩
  filter_upwards [hΨ] with c hc
  exact toMonic_injective
    (Subtype.ext (((toMonic_coeffEquiv_symm c).trans hc).trans (toMonic_ofFn _).symm))

/-- **The coefficient map is a local analytic isomorphism away from the diagonal.** At an ordered
tuple `z` of pairwise distinct points there is an analytic `Ψ` inverting, on both sides and near
`z`, the map that reads off the elementary symmetric coordinates of an ordered tuple.

The left inverse property is what pins the *ordering* down: a nearby polynomial has the same roots
as its ordered lift up to a permutation, and the permutation is forced to be the identity because
each `Ψ i` stays near `z i` while the `z i` are distinct. -/
theorem exists_analyticAt_coeffEquiv_ofFn_localInverse {z : Fin n → 𝕜}
    (hz : Function.Injective z) :
    ∃ Ψ : (Fin n → 𝕜) → (Fin n → 𝕜), Ψ (coeffEquiv 𝕜 n (ofFn z)) = z ∧
      AnalyticAt 𝕜 Ψ (coeffEquiv 𝕜 n (ofFn z)) ∧
      (∀ᶠ w in 𝓝 z, Ψ (coeffEquiv 𝕜 n (ofFn w)) = w) ∧
      (∀ᶠ c in 𝓝 (coeffEquiv 𝕜 n (ofFn z)), coeffEquiv 𝕜 n (ofFn (Ψ c)) = c) := by
  obtain ⟨Ψ, hΨ₀, hΨa, hΨ⟩ :=
    exists_analyticAt_coeffEquiv_symm_eq_ofFn hz (Equiv.symm_apply_apply (coeffEquiv 𝕜 n) (ofFn z))
  have hσ : ContinuousAt (fun w : Fin n → 𝕜 => coeffEquiv 𝕜 n (ofFn w)) z :=
    (analyticAt_coeffEquiv_ofFn z).continuousAt
  refine ⟨Ψ, hΨ₀, hΨa, ?_, ?_⟩
  · -- Each `Ψ i` of a nearby coefficient tuple is one of the nearby roots, and proximity to the
    -- distinct `z i` forces it to be the `i`-th one.
    have hmem : ∀ᶠ w in 𝓝 z, ∀ i, ∃ j, w j = Ψ (coeffEquiv 𝕜 n (ofFn w)) i := by
      filter_upwards [hσ.eventually hΨ] with w hw i
      rw [Equiv.symm_apply_apply] at hw
      have hmem : Ψ (coeffEquiv 𝕜 n (ofFn w)) i ∈ ofFn (Ψ (coeffEquiv 𝕜 n (ofFn w))) :=
        mem_ofFn.2 ⟨i, rfl⟩
      rw [← hw] at hmem
      exact mem_ofFn.1 hmem
    have hne : ∀ i j : Fin n,
        ∀ᶠ w in 𝓝 z, i ≠ j → Ψ (coeffEquiv 𝕜 n (ofFn w)) i ≠ w j := by
      intro i j
      rcases eq_or_ne i j with rfl | hij
      · exact .of_forall fun _ h => absurd rfl h
      · have hΨi : ContinuousAt (fun w : Fin n → 𝕜 => Ψ (coeffEquiv 𝕜 n (ofFn w)) i) z :=
          ContinuousAt.comp' (f := fun w : Fin n → 𝕜 => coeffEquiv 𝕜 n (ofFn w))
            (analyticAt_pi_iff.1 hΨa i).continuousAt hσ
        filter_upwards [(hΨi.ne_iff_eventually_ne (continuousAt_apply j z)).1
          (by rw [hΨ₀]; exact fun h => hij (hz h))] with w hw _ using hw
    filter_upwards [hmem, eventually_all.2 fun i => eventually_all.2 fun j => hne i j] with
      w hw hwne
    refine funext fun i => ?_
    obtain ⟨j, hj⟩ := hw i
    rcases eq_or_ne i j with rfl | hij
    · exact hj.symm
    · exact absurd hj.symm (hwne i j hij)
  · filter_upwards [hΨ] with c hc
    rw [← hc, Equiv.apply_symm_apply]

/-- **A coordinate change acts analytically on the elementary symmetric coordinates away from the
diagonal.** A map `φ` of the field induces a map of coefficient tuples, taking the coefficients of
a monic polynomial to those of the monic polynomial whose roots are the `φ`-images of its roots.
That induced map is analytic at every coefficient tuple whose roots are pairwise distinct and at
each of which `φ` is analytic.

Read on `Sym^g(Σ)`, `φ` is a change of holomorphic coordinate on the surface, so this is the
analytic ingredient, at multiplicity-free tuples, for the holomorphy of the transition maps of the
elementary symmetric atlas of `TauCeti/Geometry/Manifold/SymmetricPower.lean`: it treats one
coordinate patch (`TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`), and assembling the patches a
chart there decomposes a tuple into is not done. -/
theorem analyticAt_coeffEquiv_map_coeffEquiv_symm {φ : 𝕜 → 𝕜} {c₀ z : Fin n → 𝕜}
    (hz : Function.Injective z) (hc₀ : (coeffEquiv 𝕜 n).symm c₀ = ofFn z)
    (hφ : ∀ i, AnalyticAt 𝕜 φ (z i)) :
    AnalyticAt 𝕜 (fun c => coeffEquiv 𝕜 n (_root_.Sym.map φ ((coeffEquiv 𝕜 n).symm c))) c₀ := by
  obtain ⟨Ψ, hΨ₀, hΨa, hΨ⟩ := exists_analyticAt_coeffEquiv_symm_eq_ofFn hz hc₀
  have hcomp : AnalyticAt 𝕜 (fun c => fun i => φ (Ψ c i)) c₀ := by
    refine AnalyticAt.pi fun i => ?_
    have hi : AnalyticAt 𝕜 (fun c => Ψ c i) c₀ := analyticAt_pi_iff.1 hΨa i
    have hφ' : AnalyticAt 𝕜 φ (Ψ c₀ i) := by
      rw [hΨ₀]
      exact hφ i
    exact AnalyticAt.comp (f := fun c => Ψ c i) hφ' hi
  refine AnalyticAt.congr ((analyticAt_coeffEquiv_ofFn _).comp hcomp) ?_
  filter_upwards [hΨ] with c hc
  rw [hc, map_ofFn]
  rfl

end AlgClosed

end Sym

end TauCeti
