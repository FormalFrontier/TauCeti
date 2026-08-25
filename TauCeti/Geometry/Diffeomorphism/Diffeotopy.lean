/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Smooth ambient isotopies

A `Diffeotopy J n M` is a `C^n` motion of a real manifold `M` through
self-diffeomorphisms, starting at the identity.  It is bundled by its level-preserving total
diffeomorphism of `I × M`: this makes invertibility in the time and space variables part of the
data and ensures that no unrelated choices of inverse maps are carried by the structure.

The time interval is Mathlib's `unitInterval`, with its manifold-with-boundary structure modelled
on `𝓡∂ 1`.  The total diffeomorphism is required to preserve the time coordinate.  Its slice at
each `t : I` is therefore a self-diffeomorphism of `M`; `Diffeotopy.timeSlice` packages that fact.
Diffeotopies compose and invert, and forgetting smoothness gives the existing
`TauCeti.AmbientIsotopy`.

This supplies the smooth ambient-isotopy half of the geometric-topology roadmap's requirement
that isotopy notions be defined generally before they are specialized to knots.  The non-ambient
smooth isotopy of arbitrary maps is separate and is not defined here.  The specialization to
bundled smooth embeddings, used for geometric knot presentations, is in
`TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic`.

## Main definitions

* `TauCeti.Diffeotopy`: a level-preserving diffeomorphism of `I × M` starting at the identity.
* `TauCeti.Diffeotopy.timeSlice`: the self-diffeomorphism of `M` at a fixed time.
* `TauCeti.Diffeotopy.refl`, `trans`, and `symm`: the constant, composite, and inverse
  diffeotopies.
* `TauCeti.Diffeotopy.toAmbientIsotopy`: forget smoothness to obtain a continuous ambient
  isotopy.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for ambient
  isotopy of knots.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 2, for smooth isotopies
  and diffeotopies.
-/

public section

noncomputable section

namespace TauCeti

open unitInterval
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A `C^n` **diffeotopy** of a real manifold `M`: a level-preserving diffeomorphism of
`I × M` which is the identity at time zero.

Bundling the level-preserving total map as a `Diffeomorph` makes every time slice invertible and
makes its inverse canonical. -/
structure Diffeotopy (J : ModelWithCorners ℝ E H) (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  /-- The level-preserving total diffeomorphism of `I × M`. -/
  toDiffeomorph :
    (I × M) ≃ₘ^n⟮(𝓡∂ 1).prod J, (𝓡∂ 1).prod J⟯ I × M
  /-- The total diffeomorphism preserves the time coordinate. -/
  fst_apply (p : I × M) : (toDiffeomorph p).1 = p.1
  /-- The motion starts at the identity. -/
  snd_apply_zero (x : M) : (toDiffeomorph (0, x)).2 = x

namespace Diffeotopy

instance instCoeFun : CoeFun (Diffeotopy J n M) fun _ => I × M → M where
  coe Φ p := (Φ.toDiffeomorph p).2

variable (Φ : Diffeotopy J n M)

/-- The total diffeomorphism of a diffeotopy sends `(t, x)` to `(t, Φ (t, x))`. -/
theorem toDiffeomorph_apply (p : I × M) : Φ.toDiffeomorph p = (p.1, Φ p) := by
  exact Prod.ext (Φ.fst_apply p) rfl

/-- A diffeotopy starts at the identity. -/
@[simp]
theorem apply_zero (x : M) : Φ (0, x) = x :=
  Φ.snd_apply_zero x

/-- A diffeotopy is a `C^n` map of time and space into the ambient manifold. -/
theorem contMDiff : ContMDiff ((𝓡∂ 1).prod J) J n Φ :=
  contMDiff_snd.comp Φ.toDiffeomorph.contMDiff

/-- The inverse total diffeomorphism also preserves the time coordinate. -/
@[simp]
theorem fst_symm_apply (p : I × M) : (Φ.toDiffeomorph.symm p).1 = p.1 := by
  have h := Φ.fst_apply (Φ.toDiffeomorph.symm p)
  rw [Φ.toDiffeomorph.apply_symm_apply] at h
  exact h.symm

/-- The time-`t` slice of a diffeotopy, bundled as a self-diffeomorphism of `M`. -/
def timeSlice (t : I) : M ≃ₘ^n⟮J, J⟯ M where
  toEquiv :=
    { toFun := fun x ↦ Φ (t, x)
      invFun := fun y ↦ (Φ.toDiffeomorph.symm (t, y)).2
      left_inv := fun x ↦ by
        change (Φ.toDiffeomorph.symm (t, (Φ.toDiffeomorph (t, x)).2)).2 = x
        have hp : (t, (Φ.toDiffeomorph (t, x)).2) = Φ.toDiffeomorph (t, x) := by
          exact Prod.ext (Φ.fst_apply (t, x)).symm rfl
        rw [hp, Φ.toDiffeomorph.symm_apply_apply]
      right_inv := fun y ↦ by
        change (Φ.toDiffeomorph (t, (Φ.toDiffeomorph.symm (t, y)).2)).2 = y
        have hp : (t, (Φ.toDiffeomorph.symm (t, y)).2) =
            Φ.toDiffeomorph.symm (t, y) := by
          exact Prod.ext (Φ.fst_symm_apply (t, y)).symm rfl
        rw [hp, Φ.toDiffeomorph.apply_symm_apply] }
  contMDiff_toFun :=
    Φ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun :=
    contMDiff_snd.comp
      (Φ.toDiffeomorph.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))

/-- Evaluating the time-`t` diffeomorphism is evaluating the diffeotopy at `(t, x)`. -/
@[simp]
theorem timeSlice_apply (t : I) (x : M) : Φ.timeSlice t x = Φ (t, x) :=
  (rfl)

/-- The inverse of the time-`t` diffeomorphism is the spatial component of the inverse total
diffeomorphism at time `t`. -/
@[simp]
theorem timeSlice_symm_apply (t : I) (x : M) :
    (Φ.timeSlice t).symm x = (Φ.toDiffeomorph.symm (t, x)).2 :=
  (rfl)

/-- The time-zero slice of a diffeotopy is the identity diffeomorphism. -/
@[simp]
theorem timeSlice_zero : Φ.timeSlice 0 = _root_.Diffeomorph.refl J M n := by
  apply _root_.Diffeomorph.ext
  exact Φ.apply_zero

/-- The final self-diffeomorphism of a diffeotopy. -/
def final : M ≃ₘ^n⟮J, J⟯ M :=
  Φ.timeSlice 1

/-- The final diffeomorphism acts by the time-one slice. -/
@[simp]
theorem final_apply (x : M) : Φ.final x = Φ (1, x) :=
  (rfl)

/-- The constant diffeotopy at the identity. -/
def refl (J : ModelWithCorners ℝ E H) (n : ℕ∞ω) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Diffeotopy J n M where
  toDiffeomorph := _root_.Diffeomorph.refl ((𝓡∂ 1).prod J) (I × M) n
  fst_apply _ := rfl
  snd_apply_zero _ := rfl

/-- The constant diffeotopy fixes every point at every time. -/
@[simp]
theorem refl_apply (p : I × M) : refl J n M p = p.2 :=
  (rfl)

/-- The time slice of the constant diffeotopy is the identity. -/
@[simp]
theorem timeSlice_refl (t : I) : (refl J n M).timeSlice t =
    _root_.Diffeomorph.refl J M n := by
  apply _root_.Diffeomorph.ext
  intro x
  rfl

/-- Compose two diffeotopies pointwise, first `Φ` and then `Ψ`. -/
def trans (Φ Ψ : Diffeotopy J n M) : Diffeotopy J n M where
  toDiffeomorph := Φ.toDiffeomorph.trans Ψ.toDiffeomorph
  fst_apply p := by
    rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) p,
      Function.comp_apply, Ψ.fst_apply, Φ.fst_apply]
  snd_apply_zero x := by
    rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) (0, x),
      Function.comp_apply, Φ.toDiffeomorph_apply, Φ.apply_zero]
    exact Ψ.snd_apply_zero x

/-- Composition of diffeotopies is pointwise composition of their time slices. -/
@[simp]
theorem trans_apply (Ψ : Diffeotopy J n M) (p : I × M) :
    Φ.trans Ψ p = Ψ (p.1, Φ p) := by
  rw [trans.eq_def]
  change (Ψ.toDiffeomorph (Φ.toDiffeomorph p)).2 = _
  rw [Φ.toDiffeomorph_apply]

/-- The time slice of a composite diffeotopy is the composite of its time slices. -/
@[simp]
theorem timeSlice_trans (Ψ : Diffeotopy J n M) (t : I) :
    (Φ.trans Ψ).timeSlice t = (Φ.timeSlice t).trans (Ψ.timeSlice t) := by
  apply _root_.Diffeomorph.ext
  intro x
  change Φ.trans Ψ (t, x) = Ψ (t, Φ (t, x))
  exact Φ.trans_apply Ψ (t, x)

/-- The final diffeomorphism of a composite diffeotopy is the composite of the final
diffeomorphisms. -/
@[simp 1100]
theorem final_trans (Ψ : Diffeotopy J n M) (x : M) :
    (Φ.trans Ψ).final x = Ψ.final (Φ.final x) := by
  rw [final_apply, trans_apply, ← final_apply, ← final_apply]

/-- Reverse a diffeotopy by taking the inverse of its level-preserving total diffeomorphism. -/
def symm (Φ : Diffeotopy J n M) : Diffeotopy J n M where
  toDiffeomorph := Φ.toDiffeomorph.symm
  fst_apply := Φ.fst_symm_apply
  snd_apply_zero x := by
    have hp : (0, x) = Φ.toDiffeomorph (0, x) := by
      exact Prod.ext (Φ.fst_apply (0, x)).symm (Φ.apply_zero x).symm
    rw [hp, Φ.toDiffeomorph.symm_apply_apply]

/-- A diffeotopy followed by its inverse fixes every point. -/
@[simp]
theorem symm_apply_apply (p : I × M) : Φ.symm (p.1, Φ p) = p.2 := by
  change (Φ.toDiffeomorph.symm (p.1, (Φ.toDiffeomorph p).2)).2 = p.2
  have hp : (p.1, (Φ.toDiffeomorph p).2) = Φ.toDiffeomorph p := by
    exact Prod.ext (Φ.fst_apply p).symm rfl
  rw [hp, Φ.toDiffeomorph.symm_apply_apply]

/-- The inverse diffeotopy followed by the original fixes every point. -/
@[simp]
theorem apply_symm_apply (p : I × M) : Φ (p.1, Φ.symm p) = p.2 := by
  change (Φ.toDiffeomorph (p.1, (Φ.toDiffeomorph.symm p).2)).2 = p.2
  have hp : (p.1, (Φ.toDiffeomorph.symm p).2) = Φ.toDiffeomorph.symm p := by
    exact Prod.ext (Φ.fst_symm_apply p).symm rfl
  rw [hp, Φ.toDiffeomorph.apply_symm_apply]

/-- The time slice of the inverse diffeotopy is the inverse time slice. -/
@[simp]
theorem timeSlice_symm (t : I) :
    Φ.symm.timeSlice t = (Φ.timeSlice t).symm := by
  apply _root_.Diffeomorph.ext
  intro x
  rw [timeSlice_apply, timeSlice_symm_apply]
  rfl

/-- The final diffeomorphism of the inverse diffeotopy undoes the original final
diffeomorphism. -/
@[simp↓ 1100]
theorem symm_final_final (x : M) :
    Φ.symm.final (Φ.final x) = x := by
  rw [final_apply, final_apply]
  exact Φ.symm_apply_apply (1, x)

/-- The final diffeomorphism undoes the final diffeomorphism of the inverse diffeotopy. -/
@[simp↓ 1100]
theorem final_symm_final (x : M) :
    Φ.final (Φ.symm.final x) = x := by
  rw [final_apply, final_apply]
  exact Φ.apply_symm_apply (1, x)

/-- Forgetting smoothness turns a diffeotopy into a continuous ambient isotopy. -/
def toAmbientIsotopy : AmbientIsotopy M where
  toContinuousMap := ⟨Φ, Φ.contMDiff.continuous⟩
  isHomeomorph_total' := by
    have hfun : (fun p : I × M ↦ (p.1, Φ p)) = Φ.toDiffeomorph := by
      funext p
      exact (Φ.toDiffeomorph_apply p).symm
    rw [hfun]
    exact Φ.toDiffeomorph.toHomeomorph.isHomeomorph
  map_zero_left' := Φ.apply_zero

/-- Forgetting smoothness does not change the ambient motion. -/
@[simp]
theorem toAmbientIsotopy_apply (p : I × M) : Φ.toAmbientIsotopy.toContinuousMap p = Φ p :=
  (rfl)

/-- Forgetting smoothness commutes with taking the final map. -/
@[simp 1100]
theorem toAmbientIsotopy_final_apply (x : M) :
    Φ.toAmbientIsotopy.final x = Φ.final x := by
  rw [AmbientIsotopy.final_apply, toAmbientIsotopy_apply, final_apply]

/-- Two diffeotopies are equal when their ambient motions agree pointwise. -/
@[ext]
theorem ext {Φ Ψ : Diffeotopy J n M} (h : ∀ p, Φ p = Ψ p) : Φ = Ψ := by
  cases Φ with
  | mk φ hφ hφ0 =>
    cases Ψ with
    | mk ψ hψ hψ0 =>
      congr 1
      apply _root_.Diffeomorph.ext
      intro p
      exact Prod.ext ((hφ p).trans (hψ p).symm) (h p)

end Diffeotopy

end TauCeti
