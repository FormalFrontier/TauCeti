/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# The metric of a compatible pair

A symplectic form `ω` compatible with an almost complex structure `J` determines a Riemannian
metric `g(v, w) = ω(v, J w)`. This file records the standard compatible-triple identities tying
`ω`, `J`, and `g` together, and packages the metric of a compatible pair as a genuine inner
product through Mathlib's `InnerProductSpace.Core`.

The metric is `TauCeti.SymplecticForm.associatedBilinForm`, already defined in
`AlmostComplex.lean`. Compatibility makes it symmetric and positive definite (recorded there);
here we add the relations that turn `(ω, J, g)` into a compatible triple: `J` is a `g`-isometry,
`J` is `g`-skew-adjoint, and `ω` is recovered from `g` and `J`. The capstone
`TauCeti.SymplecticForm.Compatible.innerProductCore` exhibits `g` as an inner product, the
witness that the pointwise compatibility definition is non-vacuous and behaves as a metric
should; the energy of a `J`-holomorphic curve in the analytic Heegaard Floer roadmap is measured
against exactly this metric.

## Main declarations

* `TauCeti.SymplecticForm.associatedBilinForm_apply_right_apply`: `g(v, J w) = -ω(v, w)`, holding
  for any `J` from the identity `J² = -1` alone.
* `TauCeti.SymplecticForm.Invariant.associatedBilinForm_apply_left_apply`: `g(J v, w) = ω(v, w)`,
  recovering `ω` from the metric.
* `TauCeti.SymplecticForm.Invariant.associatedBilinForm_invariant`: `J` is a `g`-isometry,
  `g(J v, J w) = g(v, w)`.
* `TauCeti.SymplecticForm.Invariant.associatedBilinForm_skewAdjoint`: `J` is `g`-skew-adjoint,
  `g(J v, w) = -g(v, J w)`.
* `TauCeti.SymplecticForm.Invariant.associatedBilinForm_add_apply_self`: the symmetric
  polarization identity for `g(a + J b, a + J b)`.
* `TauCeti.SymplecticForm.Compatible.associatedBilinForm_nondegenerate`: the metric is
  nondegenerate.
* `TauCeti.SymplecticForm.Compatible.innerProductCore`: the metric of a compatible pair as an
  `InnerProductSpace.Core ℝ V`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: a compatible pair `(ω, J)` determines a metric `g(v, w) = ω(v, J w)`.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- Applying `J` to the right argument of the metric `g(v, w) = ω(v, J w)` negates the symplectic
form: `g(v, J w) = -ω(v, w)`. This uses only `J² = -1`, not compatibility. -/
lemma associatedBilinForm_apply_right_apply (v w : V) :
    ω.associatedBilinForm J v (J w) = -ω v w := by
  rw [associatedBilinForm_apply, AlmostComplexStructure.apply_apply]
  exact map_neg (ω.toBilinForm v) w

namespace Invariant

/-- Pointwise form of invariance under applying `J` to both arguments. -/
@[simp]
lemma apply (hinv : ω.Invariant J) (v w : V) : ω (J v) (J w) = ω v w :=
  (ω.invariant_iff J).mp hinv v w

/-- The metric recovers the symplectic form: `g(J v, w) = ω(v, w)`. -/
lemma associatedBilinForm_apply_left_apply (hinv : ω.Invariant J) (v w : V) :
    ω.associatedBilinForm J (J v) w = ω v w := by
  rw [associatedBilinForm_apply, hinv.apply]

/-- Pointwise recovery of the symplectic form from the metric and `J`: `ω(v, w) = g(J v, w)`. -/
lemma symplecticForm_apply_eq_associatedBilinForm_apply_left_apply
    (hinv : ω.Invariant J) (v w : V) :
    ω v w = ω.associatedBilinForm J (J v) w :=
  (hinv.associatedBilinForm_apply_left_apply v w).symm

/-- `J` is an isometry of the metric `g`: `g(J v, J w) = g(v, w)`. -/
lemma associatedBilinForm_invariant (hinv : ω.Invariant J) (v w : V) :
    ω.associatedBilinForm J (J v) (J w) = ω.associatedBilinForm J v w := by
  rw [hinv.associatedBilinForm_apply_left_apply v (J w), associatedBilinForm_apply]

/-- `J` is skew-adjoint for the metric `g`: `g(J v, w) = -g(v, J w)`. -/
lemma associatedBilinForm_skewAdjoint (hinv : ω.Invariant J) (v w : V) :
    ω.associatedBilinForm J (J v) w = -ω.associatedBilinForm J v (J w) := by
  rw [hinv.associatedBilinForm_apply_left_apply, associatedBilinForm_apply_right_apply, neg_neg]

/-- The polarization identity for the associated metric of a `J`-invariant form:
`g(a + J b, a + J b) = g(a, a) + g(b, b) - 2 ω(a, b)`, where
`g = ω.associatedBilinForm J`. -/
lemma associatedBilinForm_add_apply_self (hinv : ω.Invariant J) (a b : V) :
    ω.associatedBilinForm J (a + J b) (a + J b) =
      ω.associatedBilinForm J a a + ω.associatedBilinForm J b b - 2 * ω a b := by
  have hpol := hinv.associatedBilinForm_isSymm.polarization a (J b)
  have hcross : ω.associatedBilinForm J a (J b) = -ω a b :=
    associatedBilinForm_apply_right_apply a b
  have hself : ω.associatedBilinForm J (J b) (J b) = ω.associatedBilinForm J b b :=
    ω.associatedBilinForm_apply_apply_self_eq J b
  linarith

end Invariant

/-- The metric `g(v, v) = ω(v, J v)` is nonnegative under positive-definiteness. -/
lemma associatedBilinForm_self_nonneg
    (hpositive : (ω.associatedBilinForm J).toQuadraticMap.PosDef) (v : V) :
    0 ≤ ω.associatedBilinForm J v v := by
  simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hpositive.nonneg v

/-- The diagonal `ω(v, J v)` is nonnegative under positive-definiteness of the associated metric. -/
lemma symplecticForm_apply_apply_self_nonneg
    (hpositive : (ω.associatedBilinForm J).toQuadraticMap.PosDef) (v : V) : 0 ≤ ω v (J v) :=
  associatedBilinForm_self_nonneg hpositive v

/-- Positive-definiteness of the associated metric detects zero vectors on the diagonal. -/
lemma associatedBilinForm_self_eq_zero
    (hpositive : (ω.associatedBilinForm J).toQuadraticMap.PosDef) {v : V} :
    ω.associatedBilinForm J v v = 0 ↔ v = 0 := by
  refine ⟨fun hv => hpositive.anisotropic v ?_, ?_⟩
  · simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hv
  · rintro rfl
    simp

namespace Compatible

/-- The metric recovers the symplectic form: `g(J v, w) = ω(v, w)`. -/
lemma associatedBilinForm_apply_left_apply (h : ω.Compatible J) (v w : V) :
    ω.associatedBilinForm J (J v) w = ω v w :=
  h.invariant.associatedBilinForm_apply_left_apply v w

/-- Pointwise recovery of the symplectic form from the metric and `J`: `ω(v, w) = g(J v, w)`. -/
lemma symplecticForm_apply_eq_associatedBilinForm_apply_left_apply
    (h : ω.Compatible J) (v w : V) :
    ω v w = ω.associatedBilinForm J (J v) w :=
  h.invariant.symplecticForm_apply_eq_associatedBilinForm_apply_left_apply v w

/-- `J` is an isometry of the metric `g`: `g(J v, J w) = g(v, w)`. -/
lemma associatedBilinForm_invariant (h : ω.Compatible J) (v w : V) :
    ω.associatedBilinForm J (J v) (J w) = ω.associatedBilinForm J v w :=
  h.invariant.associatedBilinForm_invariant v w

/-- `J` is skew-adjoint for the metric `g`: `g(J v, w) = -g(v, J w)`. -/
lemma associatedBilinForm_skewAdjoint (h : ω.Compatible J) (v w : V) :
    ω.associatedBilinForm J (J v) w = -ω.associatedBilinForm J v (J w) :=
  h.invariant.associatedBilinForm_skewAdjoint v w

/-- The metric `g(v, v) = ω(v, J v)` is nonnegative. -/
lemma associatedBilinForm_self_nonneg (h : ω.Compatible J) (v : V) :
    0 ≤ ω.associatedBilinForm J v v :=
  SymplecticForm.associatedBilinForm_self_nonneg h.positive v

/-- The diagonal `ω(v, J v)` of the associated metric is nonnegative. -/
lemma symplecticForm_apply_apply_self_nonneg (h : ω.Compatible J) (v : V) : 0 ≤ ω v (J v) :=
  SymplecticForm.symplecticForm_apply_apply_self_nonneg h.positive v

/-- The metric is positive definite in the sense that `g(v, v) = 0` exactly when `v = 0`. -/
lemma associatedBilinForm_self_eq_zero (h : ω.Compatible J) {v : V} :
    ω.associatedBilinForm J v v = 0 ↔ v = 0 :=
  SymplecticForm.associatedBilinForm_self_eq_zero h.positive

/-- The metric of a compatible pair is nondegenerate. -/
lemma associatedBilinForm_nondegenerate (h : ω.Compatible J) :
    (ω.associatedBilinForm J).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    h.associatedBilinForm_isSymm.isRefl).mpr ?_
  rw [LinearMap.separatingLeft_iff_linear_nontrivial]
  intro v hv
  refine h.associatedBilinForm_self_eq_zero.mp ?_
  simpa using LinearMap.congr_fun hv v

/-- The metric of a compatible pair, packaged as an `InnerProductSpace.Core ℝ V`.

The inner product is the associated metric `⟪v, w⟫ = ω(v, J w)`. -/
@[expose, implicit_reducible]
noncomputable def innerProductCore (h : ω.Compatible J) : InnerProductSpace.Core ℝ V where
  inner v w := ω v (J w)
  conj_inner_symm v w := by
    simpa [associatedBilinForm_apply, RCLike.conj_to_real]
      using h.associatedBilinForm_apply_swap w v
  re_inner_nonneg v := by
    simpa using h.symplecticForm_apply_apply_self_nonneg v
  add_left v w x := by
    simp
  smul_left v w r := by
    simp [smul_eq_mul]
  definite v hv := h.associatedBilinForm_self_eq_zero.mp hv

/-- The inner product from `innerProductCore` is the associated metric `ω(v, J w)`. -/
@[simp]
lemma innerProductCore_inner (h : ω.Compatible J) (v w : V) :
    @inner ℝ V h.innerProductCore.toInner v w = ω v (J w) :=
  rfl

end Compatible

end SymplecticForm

end TauCeti
