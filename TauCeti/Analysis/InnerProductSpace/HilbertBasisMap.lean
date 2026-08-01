/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Transporting Hilbert bases by linear isometric equivalences

This file adds the Hilbert-basis analogue of `Basis.map`: a Hilbert basis of a Hilbert space
can be transported across a linear isometric equivalence. It also follows Mathlib's
`OrthonormalBasis.map` API for transporting orthonormal bases. The construction is the Part 0
`HilbertBasis.mapₗᵢ` primitive from the `OrthogonalL2Bases` roadmap, used later to move weighted
orthogonal-polynomial bases across the weight-change isometry.

The API is intentionally small: the representation equality and pointwise simp lemmas expose the
transport, while Mathlib's existing Hilbert-basis coordinate and Parseval lemmas supply the derived
coordinate identities after rewriting through the inverse isometry.
-/

public section

namespace TauCeti

variable {ι : Type*} {𝕜 : Type*} {E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Transport a Hilbert basis along a linear isometric equivalence. -/
protected noncomputable def _root_.HilbertBasis.mapₗᵢ
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    _root_.HilbertBasis ι 𝕜 F :=
  _root_.HilbertBasis.ofRepr (e.symm.trans b.repr)

/-- The coordinate representation of `b.mapₗᵢ e` is `b.repr` after applying `e.symm`. -/
@[simp]
theorem _root_.HilbertBasis.repr_mapₗᵢ (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e).repr = e.symm.trans b.repr :=
  congrArg _root_.HilbertBasis.repr (_root_.HilbertBasis.mapₗᵢ.eq_1 b e)

/-- The `i`th vector of the transported basis is the image of the `i`th vector. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_apply (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (i : ι) :
    b.mapₗᵢ e i = e (b i) :=
  by
    classical
    rw [← _root_.HilbertBasis.repr_symm_single, _root_.HilbertBasis.repr_mapₗᵢ,
      LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
      _root_.HilbertBasis.repr_symm_single]
    simp

/-- Function-level form of `HilbertBasis.mapₗᵢ_apply`. -/
@[simp]
theorem _root_.HilbertBasis.coe_mapₗᵢ (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    ⇑(b.mapₗᵢ e) = e ∘ b :=
  funext (b.mapₗᵢ_apply e)

/-- Transport along the identity isometry leaves a Hilbert basis unchanged. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_refl (b : _root_.HilbertBasis ι 𝕜 E) :
    b.mapₗᵢ (LinearIsometryEquiv.refl 𝕜 E) = b := by
  cases b
  rfl

/-- Transporting along two linear isometric equivalences is the same as transporting along their
composition. -/
@[simp]
theorem _root_.HilbertBasis.mapₗᵢ_trans {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) (f : F ≃ₗᵢ[𝕜] G) :
    (b.mapₗᵢ e).mapₗᵢ f = b.mapₗᵢ (e.trans f) := by
  cases b
  rfl

/-- Transporting a Hilbert basis across an isometry and then back across the inverse isometry
recovers the original basis. -/
theorem _root_.HilbertBasis.mapₗᵢ_symm (b : _root_.HilbertBasis ι 𝕜 E) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e).mapₗᵢ e.symm = b := by
  rw [_root_.HilbertBasis.mapₗᵢ_trans]
  simp

/-- Transporting a Hilbert basis back across an inverse isometry and then forward again recovers
the original basis. -/
theorem _root_.HilbertBasis.mapₗᵢ_symm_self (b : _root_.HilbertBasis ι 𝕜 F) (e : E ≃ₗᵢ[𝕜] F) :
    (b.mapₗᵢ e.symm).mapₗᵢ e = b := by
  rw [_root_.HilbertBasis.mapₗᵢ_trans]
  simp

end TauCeti
