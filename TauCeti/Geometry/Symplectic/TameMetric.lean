/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# The metric of a tame pair

A symplectic form `ω` taming an almost complex structure `J` need not be `J`-invariant, so the
bilinear form `ω(v, J w)` from `AlmostComplex.lean` is in general not symmetric. Its symmetric
part, however, always is a metric: `gₛ(v, w) = ω(v, J w) + ω(w, J v)` is symmetric, automatically
`J`-invariant, and -- under taming alone -- positive definite. This is the standard "every tame
`J` carries a `J`-invariant metric" construction (McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, Section 2.5), the first step of the proof that the space of tame almost
complex structures is contractible, recorded here at the pointwise linear-algebra level.

The roadmap keeps tame and compatible as separate named hypotheses, so this file builds the
metric from the strictly weaker `SymplecticForm.Tames` predicate, paralleling the compatible
construction `SymplecticForm.Compatible.innerProductCore` rather than reusing it. When `ω` is
in fact compatible, the symmetric part is just twice the asymmetric metric `ω(·, J ·)`, which is
recorded as the bridge `SymplecticForm.Compatible.symmetrizedBilinForm_apply`.

## Main declarations

* `TauCeti.SymplecticForm.symmetrizedBilinForm`: the symmetric part `gₛ(v, w) = ω(v, J w) +
  ω(w, J v)` of the metric of `(ω, J)`.
* `TauCeti.SymplecticForm.symmetrizedBilinForm_isSymm`: `gₛ` is symmetric, for any `J`.
* `TauCeti.SymplecticForm.symmetrizedBilinForm_invariant`: `gₛ(J v, J w) = gₛ(v, w)`, for any
  taming-or-not `ω`; the symmetric part is always `J`-invariant.
* `TauCeti.SymplecticForm.Tames.symmetrizedBilinForm_posDef`: under taming, `gₛ` is positive
  definite.
* `TauCeti.SymplecticForm.Tames.innerProductCore`: the symmetric part of the metric of a tame
  pair as an `InnerProductSpace.Core ℝ V`.
* `TauCeti.SymplecticForm.Tames.innerProductCore_inner_invariant`: the packaged inner product is
  `J`-invariant, `⟪J v, J w⟫ = ⟪v, w⟫`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Sections 2.1 and 2.5.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (ω : SymplecticForm V) (J : AlmostComplexStructure V)

/-- The symmetric part of the metric of `(ω, J)`: `gₛ(v, w) = ω(v, J w) + ω(w, J v)`.

Unlike `SymplecticForm.associatedBilinForm`, this is symmetric for every `J`, and `J`-invariant;
taming makes it positive definite, hence an inner product. -/
def symmetrizedBilinForm : LinearMap.BilinForm ℝ V :=
  ω.associatedBilinForm J + (ω.associatedBilinForm J).flip

@[simp]
lemma symmetrizedBilinForm_apply (v w : V) :
    ω.symmetrizedBilinForm J v w = ω v (J w) + ω w (J v) := by
  simp [symmetrizedBilinForm]

variable {ω J}

/-- The symmetric part of the metric is symmetric, for any almost complex structure. -/
lemma symmetrizedBilinForm_isSymm : (ω.symmetrizedBilinForm J).IsSymm :=
  ⟨fun v w => by simp only [symmetrizedBilinForm_apply]; ring⟩

/-- The symmetric part of the metric is `J`-invariant, for any symplectic form: `gₛ(J v, J w) =
gₛ(v, w)`. This uses only `J² = -1` and skew-symmetry of `ω`, not taming. -/
lemma symmetrizedBilinForm_invariant (v w : V) :
    ω.symmetrizedBilinForm J (J v) (J w) = ω.symmetrizedBilinForm J v w := by
  have e₁ : ω (J v) (-w) = ω w (J v) :=
    (map_neg (ω.toBilinForm (J v)) w).trans (ω.neg_eq (J v) w)
  have e₂ : ω (J w) (-v) = ω v (J w) :=
    (map_neg (ω.toBilinForm (J w)) v).trans (ω.neg_eq (J w) v)
  rw [symmetrizedBilinForm_apply, symmetrizedBilinForm_apply,
    AlmostComplexStructure.apply_apply, AlmostComplexStructure.apply_apply, e₁, e₂, add_comm]

/-- The diagonal of the symmetric part is twice the symplectic diagonal: `gₛ(v, v) = 2 ω(v, Jv)`. -/
lemma symmetrizedBilinForm_apply_self (v : V) :
    ω.symmetrizedBilinForm J v v = 2 * ω v (J v) := by
  rw [symmetrizedBilinForm_apply, two_mul]

namespace Tames

/-- The symplectic diagonal `ω(v, J v)` is nonnegative under taming. -/
lemma symplecticForm_apply_apply_self_nonneg (h : ω.Tames J) (v : V) : 0 ≤ ω v (J v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (h v hv).le

/-- The diagonal of the symmetric part is positive on nonzero vectors. -/
lemma symmetrizedBilinForm_self_pos (h : ω.Tames J) {v : V} (hv : v ≠ 0) :
    0 < ω.symmetrizedBilinForm J v v := by
  rw [symmetrizedBilinForm_apply_self]
  have := h v hv
  linarith

/-- The diagonal of the symmetric part is nonnegative. -/
lemma symmetrizedBilinForm_self_nonneg (h : ω.Tames J) (v : V) :
    0 ≤ ω.symmetrizedBilinForm J v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (h.symmetrizedBilinForm_self_pos hv).le

/-- Under taming, the symmetric part of the metric is positive definite. -/
lemma symmetrizedBilinForm_posDef (h : ω.Tames J) :
    (ω.symmetrizedBilinForm J).toQuadraticMap.PosDef := fun v hv => by
  simpa [LinearMap.BilinMap.toQuadraticMap_apply] using h.symmetrizedBilinForm_self_pos hv

/-- The diagonal of the symmetric part detects zero vectors. -/
lemma symmetrizedBilinForm_self_eq_zero (h : ω.Tames J) {v : V} :
    ω.symmetrizedBilinForm J v v = 0 ↔ v = 0 := by
  refine ⟨fun hv => ?_, ?_⟩
  · by_contra hne
    exact (h.symmetrizedBilinForm_self_pos hne).ne' hv
  · rintro rfl
    simp

/-- The symmetric part of the metric of a tame pair is nondegenerate. -/
lemma symmetrizedBilinForm_nondegenerate (h : ω.Tames J) :
    (ω.symmetrizedBilinForm J).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    symmetrizedBilinForm_isSymm.isRefl).mpr ?_
  rw [LinearMap.separatingLeft_iff_linear_nontrivial]
  intro v hv
  refine h.symmetrizedBilinForm_self_eq_zero.mp ?_
  simpa using LinearMap.congr_fun hv v

/-- The symmetric part of the metric of a tame pair, packaged as an `InnerProductSpace.Core ℝ V`.

The inner product is `⟪v, w⟫ = ω(v, J w) + ω(w, J v)`, the symmetric part of `ω(·, J ·)`. -/
@[expose, implicit_reducible]
noncomputable def innerProductCore (h : ω.Tames J) : InnerProductSpace.Core ℝ V where
  inner v w := ω.symmetrizedBilinForm J v w
  conj_inner_symm v w := by
    simpa only [RCLike.conj_to_real] using symmetrizedBilinForm_isSymm.eq w v
  re_inner_nonneg v := by
    simpa using h.symmetrizedBilinForm_self_nonneg v
  add_left v w x := by
    simp only [map_add, LinearMap.add_apply]
  smul_left v w r := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]
  definite v hv := h.symmetrizedBilinForm_self_eq_zero.mp hv

/-- The inner product from `innerProductCore` is the symmetric part `ω(v, J w) + ω(w, J v)`. -/
@[simp]
lemma innerProductCore_inner (h : ω.Tames J) (v w : V) :
    @inner ℝ V h.innerProductCore.toInner v w = ω v (J w) + ω w (J v) :=
  -- `inner` for `innerProductCore` is the field `ω.symmetrizedBilinForm J v w` by construction.
  symmetrizedBilinForm_apply ω J v w

/-- The inner product from `innerProductCore` is `J`-invariant: `⟪J v, J w⟫ = ⟪v, w⟫`. -/
lemma innerProductCore_inner_invariant (h : ω.Tames J) (v w : V) :
    @inner ℝ V h.innerProductCore.toInner (J v) (J w)
      = @inner ℝ V h.innerProductCore.toInner v w :=
  -- `inner` for `innerProductCore` is the field `ω.symmetrizedBilinForm J · ·` by construction.
  symmetrizedBilinForm_invariant v w

end Tames

namespace Compatible

/-- When `ω` is compatible with `J`, its asymmetric metric `ω(·, J ·)` is already symmetric, so
the symmetric part is just twice it: `gₛ(v, w) = 2 ω(v, J w)`. -/
lemma symmetrizedBilinForm_apply (h : ω.Compatible J) (v w : V) :
    ω.symmetrizedBilinForm J v w = 2 * ω v (J w) := by
  rw [SymplecticForm.symmetrizedBilinForm_apply, ← h.associatedBilinForm_apply_swap v w, two_mul]

end Compatible

end SymplecticForm

end TauCeti
