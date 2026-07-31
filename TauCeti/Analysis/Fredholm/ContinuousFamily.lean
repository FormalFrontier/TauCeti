/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.Fredholm.SmallPerturbation

/-!
# Continuous families of Fredholm operators

The Fredholm index is locally constant in a continuous family of Fredholm operators. Consequently,
it is constant when the parameter space is preconnected, and in particular at the endpoints of a
path of Fredholm operators.

This is the continuous-family form of stability under small perturbations. It is a basic input to
the spectral-flow and Riemann--Roch-with-boundary developments in Lanes F0 and F1.3 of the analytic
Heegaard Floer roadmap: a family can change index only by leaving the Fredholm locus.

The proofs use the operator-norm neighborhood on which
`ContinuousLinearMap.IsFredholm.eventually_isFredholm_and_index_eq` makes the index constant,
together with Mathlib's general API for locally constant functions on preconnected spaces.

## Main declarations

* `Continuous.isLocallyConstant_fredholmIndex`: the index of a continuous Fredholm family is
  locally constant.
* `ContinuousOn.fredholmIndex_eq_of_isPreconnected`: two parameters in the same preconnected set
  give operators of equal index.
* `Continuous.fredholmIndex_eq_of_preconnectedSpace`: a continuous Fredholm family over a
  preconnected space has constant index.
* `Path.fredholmIndex_eq`: the endpoints of a continuous Fredholm path have equal index.
* `fredholmIndex_eq_of_segment`: two operators joined by a Fredholm affine segment have equal
  index.

The index convention and its perturbation stability follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

variable {K E F X : Type*}
variable [NontriviallyNormedField K] [CompleteSpace K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace K F]
variable [TopologicalSpace X]

/-- The Fredholm index of a continuous family of Fredholm operators is locally constant on the
parameter space. -/
theorem Continuous.isLocallyConstant_fredholmIndex {A : X → E →L[K] F}
    (hA : Continuous A) (hFredholm : ∀ x, ContinuousLinearMap.IsFredholm (A x)) :
    IsLocallyConstant fun x ↦ ContinuousLinearMap.index (A x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [hA.continuousAt (hFredholm x).eventually_isFredholm_and_index_eq] with y hy
  exact hy.2

/-- Along a continuous family of Fredholm operators, parameters in the same preconnected set give
operators with equal index. -/
theorem ContinuousOn.fredholmIndex_eq_of_isPreconnected {A : X → E →L[K] F} {s : Set X}
    (hA : ContinuousOn A s)
    (hFredholm : ∀ x ∈ s, ContinuousLinearMap.IsFredholm (A x))
    (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ContinuousLinearMap.index (A x) = ContinuousLinearMap.index (A y) := by
  letI := Subtype.preconnectedSpace hs
  exact (Continuous.isLocallyConstant_fredholmIndex hA.domRestrict
    (fun x ↦ hFredholm x x.2)).apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

/-- A continuous family of Fredholm operators over a preconnected parameter space has constant
index. -/
theorem Continuous.fredholmIndex_eq_of_preconnectedSpace [PreconnectedSpace X]
    {A : X → E →L[K] F} (hA : Continuous A)
    (hFredholm : ∀ x, ContinuousLinearMap.IsFredholm (A x)) (x y : X) :
    ContinuousLinearMap.index (A x) = ContinuousLinearMap.index (A y) :=
  (Continuous.isLocallyConstant_fredholmIndex hA hFredholm).apply_eq_of_preconnectedSpace x y

/-- The endpoints of a continuous path of Fredholm operators have the same index. -/
theorem Path.fredholmIndex_eq {T S : E →L[K] F} (A : Path T S)
    (hFredholm : ∀ t, ContinuousLinearMap.IsFredholm (A t)) :
    ContinuousLinearMap.index T = ContinuousLinearMap.index S := by
  simpa only [A.source, A.target] using
    Continuous.fredholmIndex_eq_of_preconnectedSpace A.continuous hFredholm 0 1

section Real

variable {E' F' : Type*}
variable [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
variable [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- Two real operators have equal index if every operator on the affine segment between them is
Fredholm. -/
theorem fredholmIndex_eq_of_segment (T S : E' →L[ℝ] F')
    (hFredholm : ∀ t : unitInterval,
      ContinuousLinearMap.IsFredholm ((1 - (t : ℝ)) • T + (t : ℝ) • S)) :
    ContinuousLinearMap.index T = ContinuousLinearMap.index S := by
  apply Path.fredholmIndex_eq (Path.segment T S)
  simpa only [Path.segment_apply, AffineMap.lineMap_apply_module] using hFredholm

end Real

end TauCeti

end
