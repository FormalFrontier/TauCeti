/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W2p

/-!
# Third-order weak Sobolev spaces

This file constructs the real-valued Sobolev space `W^{3,p}(Ω)` on an open subset of a
finite-dimensional real inner product space. It builds directly on `TauCeti.W2p`: an element
records a second-order Sobolev function together with an `Lᵖ` field of continuous linear maps,
and the latter is required to be the weak Fréchet derivative of the weak Hessian.

The admissibility condition is imposed as the common kernel of continuous Hölder pairings.
Hence `TauCeti.W3p` is a closed subspace of the product of `W^{2,p}(Ω)` and the `Lᵖ` third
derivative field, and is complete. Its graph norm is

`(∥u∥_{W²ᵖ}² + ∥D³u∥_p²)¹⁄²`.

The value and weak gradient are read off as `TauCeti.W1p.value` and `TauCeti.W1p.gradient` of
`TauCeti.W2p.firstOrder` of `TauCeti.W3p.secondOrder`; the weak Hessian is
`TauCeti.W2p.hessian` of `TauCeti.W3p.secondOrder`.

No boundedness or boundary regularity of `Ω` is used. The third derivative is represented
basis-free as an element of `E →L[ℝ] (E →L[ℝ] E)`: a derivative direction, followed by the
two directions already represented by the Hessian and the Riesz pairing. Permutation symmetry is
not imposed in the definition and is not yet formalized here.

## Main declarations

* `TauCeti.w3pSubmodule`: the closed subspace of second-order jets and weak third derivatives.
* `TauCeti.W3p`: the complete third-order weak Sobolev space.
* `TauCeti.W3p.hasWeakFDerivOn_hessian`: the recorded third derivative is the weak derivative
  of the recorded weak Hessian.

## References

This is the third-order case of Lane A.1, target 1, in `TauCetiRoadmap/PDE/README.md`. The
iterated weak-derivative definition and closed-graph completeness argument follow L. C. Evans,
*Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

/-- The ambient graph space for a third-order Sobolev function: a second-order Sobolev function
and an `Lᵖ` candidate third derivative, with their Euclidean product norm. -/
abbrev Sobolev3JetLp (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] :=
  WeakDerivStepJetLp mu Omega p (W2p mu Omega p) (E →L[ℝ] E)

/-- The third-order weak Sobolev subspace. Its last component is required to be the weak
Fréchet derivative of the weak Hessian in its second-order component. -/
def w3pSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] : ClosedSubmodule ℝ (Sobolev3JetLp mu Omega p) :=
  weakDerivStepSubmodule (X := W2p mu Omega p) mu Omega p
    (W2p.hessianL (mu := mu) (Omega := Omega) (p := p))

/-- Membership in `w3pSubmodule` is the family of third-derivative integration-by-parts
identities. -/
theorem mem_w3pSubmodule_iff (J : Sobolev3JetLp mu Omega p) :
    J ∈ w3pSubmodule mu Omega p ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • W2p.hessian (WithLp.fst J) x ∂mu) +
          ∫ x, phi x • WithLp.snd J x v ∂mu = 0 := by
  simp only [w3pSubmodule, mem_weakDerivStepSubmodule_iff, W2p.hessianL_apply]

/-- A jet belongs to `w3pSubmodule` exactly when its third derivative is the weak Fréchet
derivative of its weak Hessian. -/
theorem mem_w3pSubmodule_iff_hasWeakFDerivOn (J : Sobolev3JetLp mu Omega p) :
    J ∈ w3pSubmodule mu Omega p ↔
      HasWeakFDerivOn mu Omega (W2p.hessian (WithLp.fst J))
        (WithLp.snd J : Lp (E →L[ℝ] (E →L[ℝ] E)) p (mu.restrict Omega)) := by
  simp only [w3pSubmodule, mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn, W2p.hessianL_apply]

/-- The third-order, real-valued weak Sobolev space `W^{3,p}(Ω)`, represented by its second-order
Sobolev jet and weak third derivative. -/
abbrev W3p (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] := (w3pSubmodule mu Omega p).toSubmodule

/-- The continuous projection from `W3p` to its second-order Sobolev component. -/
def W3p.secondOrderL : W3p mu Omega p →L[ℝ] W2p mu Omega p :=
  (WithLp.fstL 2 ℝ _ _).comp (w3pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The second-order Sobolev component of a third-order Sobolev function. -/
def W3p.secondOrder (u : W3p mu Omega p) : W2p mu Omega p :=
  W3p.secondOrderL (mu := mu) (Omega := Omega) (p := p) u

@[simp]
theorem W3p.secondOrderL_apply (u : W3p mu Omega p) :
    W3p.secondOrderL (mu := mu) (Omega := Omega) (p := p) u =
      W3p.secondOrder u := (rfl)

theorem W3p.secondOrder_coe (u : W3p mu Omega p) :
    W3p.secondOrder u = WithLp.fst (u : Sobolev3JetLp mu Omega p) := (rfl)

/-- The continuous projection from `W3p` to its weak third derivative. -/
def W3p.thirdDerivativeL : W3p mu Omega p →L[ℝ]
    Lp (E →L[ℝ] (E →L[ℝ] E)) p (mu.restrict Omega) :=
  (WithLp.sndL 2 ℝ _ _).comp (w3pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The `Lᵖ` weak third derivative of a third-order Sobolev function. -/
def W3p.thirdDerivative (u : W3p mu Omega p) :
    Lp (E →L[ℝ] (E →L[ℝ] E)) p (mu.restrict Omega) :=
  W3p.thirdDerivativeL (mu := mu) (Omega := Omega) (p := p) u

@[simp]
theorem W3p.thirdDerivativeL_apply (u : W3p mu Omega p) :
    W3p.thirdDerivativeL (mu := mu) (Omega := Omega) (p := p) u =
      W3p.thirdDerivative u := (rfl)

theorem W3p.thirdDerivative_coe (u : W3p mu Omega p) :
    W3p.thirdDerivative u = WithLp.snd (u : Sobolev3JetLp mu Omega p) := (rfl)

/-- Construct a third-order Sobolev function from a second-order Sobolev function and a weak
third derivative. -/
def W3p.mk (u : W2p mu Omega p)
    (T : Lp (E →L[ℝ] (E →L[ℝ] E)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W2p.hessian u) T) : W3p mu Omega p :=
  ⟨WithLp.toLp 2 (u, T), (mem_w3pSubmodule_iff_hasWeakFDerivOn _).mpr (by simpa)⟩

@[simp]
theorem W3p.secondOrder_mk (u : W2p mu Omega p)
    (T : Lp (E →L[ℝ] (E →L[ℝ] E)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W2p.hessian u) T) :
    W3p.secondOrder (W3p.mk u T h) = u := by
  rw [W3p.secondOrder_coe]
  simp [W3p.mk]

@[simp]
theorem W3p.thirdDerivative_mk (u : W2p mu Omega p)
    (T : Lp (E →L[ℝ] (E →L[ℝ] E)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (W2p.hessian u) T) :
    W3p.thirdDerivative (W3p.mk u T h) = T := by
  rw [W3p.thirdDerivative_coe]
  simp [W3p.mk]

/-- Two third-order Sobolev functions are equal when their second-order components and weak
third derivatives are equal. -/
theorem W3p.ext_secondOrder {u v : W3p mu Omega p}
    (hsecondOrder : W3p.secondOrder u = W3p.secondOrder v)
    (hthird : W3p.thirdDerivative u = W3p.thirdDerivative v) : u = v := by
  refine Subtype.ext ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective ?_)
  apply Prod.ext
  · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_fst,
      W3p.secondOrder_coe] using hsecondOrder
  · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_snd,
      W3p.thirdDerivative_coe] using hthird

/-- The third derivative of a third-order Sobolev function is the weak Fréchet derivative of its
weak Hessian. -/
theorem W3p.hasWeakFDerivOn_hessian (u : W3p mu Omega p) :
    HasWeakFDerivOn mu Omega (W2p.hessian (W3p.secondOrder u)) (W3p.thirdDerivative u) := by
  rw [W3p.secondOrder_coe, W3p.thirdDerivative_coe]
  exact (mem_w3pSubmodule_iff_hasWeakFDerivOn u.1).mp u.2

/-- Two third-order Sobolev functions are equal when their `Lᵖ` value components are equal.
Successive uniqueness of weak derivatives determines every higher component. -/
@[ext]
theorem W3p.ext {u v : W3p mu Omega p}
    (hvalue : W1p.value (W2p.firstOrder (W3p.secondOrder u)) =
      W1p.value (W2p.firstOrder (W3p.secondOrder v))) : u = v := by
  have hsecondOrder : W3p.secondOrder u = W3p.secondOrder v := W2p.ext hvalue
  have hv : HasWeakFDerivOn mu Omega (W2p.hessian (W3p.secondOrder u))
      (W3p.thirdDerivative v) := by
    rw [hsecondOrder]
    exact W3p.hasWeakFDerivOn_hessian v
  have hthird : W3p.thirdDerivative u = W3p.thirdDerivative v :=
    Lp.ext ((W3p.hasWeakFDerivOn_hessian u).ae_eq hv)
  exact W3p.ext_secondOrder hsecondOrder hthird

/-- The norm of a third-order Sobolev function controls its second-order component. -/
theorem W3p.norm_secondOrder_le (u : W3p mu Omega p) : ‖W3p.secondOrder u‖ ≤ ‖u‖ := by
  rw [W3p.secondOrder_coe]
  exact WithLp.norm_fst_le (W2p mu Omega p) u.1

/-- The norm of a third-order Sobolev function controls its value component. -/
theorem W3p.norm_value_le (u : W3p mu Omega p) :
    ‖W1p.value (W2p.firstOrder (W3p.secondOrder u))‖ ≤ ‖u‖ :=
  (W2p.norm_value_le (W3p.secondOrder u)).trans (W3p.norm_secondOrder_le u)

/-- The norm of a third-order Sobolev function controls its weak gradient. -/
theorem W3p.norm_gradient_le (u : W3p mu Omega p) :
    ‖W1p.gradient (W2p.firstOrder (W3p.secondOrder u))‖ ≤ ‖u‖ :=
  (W2p.norm_gradient_le (W3p.secondOrder u)).trans (W3p.norm_secondOrder_le u)

/-- The norm of a third-order Sobolev function controls its weak Hessian. -/
theorem W3p.norm_hessian_le (u : W3p mu Omega p) :
    ‖W2p.hessian (W3p.secondOrder u)‖ ≤ ‖u‖ :=
  (W2p.norm_hessian_le (W3p.secondOrder u)).trans (W3p.norm_secondOrder_le u)

/-- The norm of a third-order Sobolev function controls its weak third derivative. -/
theorem W3p.norm_thirdDerivative_le (u : W3p mu Omega p) :
    ‖W3p.thirdDerivative u‖ ≤ ‖u‖ := by
  rw [W3p.thirdDerivative_coe]
  exact WithLp.norm_snd_le (W2p mu Omega p) u.1

/-- The norm on `W3p` is the Euclidean graph norm of the second-order Sobolev component and the
weak third derivative. -/
theorem W3p.norm_sq_eq_norm_secondOrder_sq_add_norm_thirdDerivative_sq (u : W3p mu Omega p) :
    ‖u‖ ^ 2 = ‖W3p.secondOrder u‖ ^ 2 + ‖W3p.thirdDerivative u‖ ^ 2 := by
  rw [Submodule.coe_norm, W3p.secondOrder_coe, W3p.thirdDerivative_coe]
  exact WithLp.prod_norm_sq_eq_of_L2 u.1

namespace W3p

/-- At exponent two, the norm on `W3p` is the sum-of-squares graph norm of the value and its
first three weak derivatives. -/
lemma norm_sq_eq_norm_value_sq_add_norm_gradient_sq_add_norm_hessian_sq_add_norm_thirdDerivative_sq
    (u : W3p mu Omega 2) :
    ‖u‖ ^ 2 = ‖W1p.value (W2p.firstOrder (W3p.secondOrder u))‖ ^ 2 +
      ‖W1p.gradient (W2p.firstOrder (W3p.secondOrder u))‖ ^ 2 +
      ‖W2p.hessian (W3p.secondOrder u)‖ ^ 2 + ‖W3p.thirdDerivative u‖ ^ 2 := by
  rw [W3p.norm_sq_eq_norm_secondOrder_sq_add_norm_thirdDerivative_sq,
    W2p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq_add_norm_hessian_sq]

end W3p

/-- `W^{3,p}(Ω)` is complete in its iterated weak-derivative graph norm. -/
instance : CompleteSpace (W3p mu Omega p) :=
  (w3pSubmodule mu Omega p).isClosed.completeSpace_coe

end TauCeti
