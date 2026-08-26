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
Diffeotopies coerce to their spatial component, so `Φ (t, x)` is the point of `M` reached from
`x` at time `t`.
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
* `TauCeti.Diffeotopy.final`: the self-diffeomorphism at time one.
* `TauCeti.Diffeotopy.refl`, `trans`, and `symm`: the constant, composite, and inverse
  diffeotopies.
* `TauCeti.Diffeotopy.toAmbientIsotopy`: forget smoothness to obtain a continuous ambient
  isotopy.

## Main results

* `TauCeti.Diffeotopy.timeSlice_trans` and `timeSlice_symm`: time slices commute with composition
  and inversion.
* `TauCeti.Diffeotopy.final_trans` and `final_symm`: the corresponding calculus for final
  diffeomorphisms.
* `TauCeti.Diffeotopy.toAmbientIsotopy_final_apply`: forgetting smoothness preserves the final
  action.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for ambient
  isotopy of knots.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for smooth
  isotopies and diffeotopies.
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
  snd_apply_zero' (x : M) : (toDiffeomorph (0, x)).2 = x

namespace Diffeotopy

/-- Apply a diffeotopy as `Φ (t, x)`: the spatial component of the total diffeomorphism. -/
instance instCoeFun : CoeFun (Diffeotopy J n M) fun _ => I × M → M where
  coe Φ p := (Φ.toDiffeomorph p).2

attribute [simp] Diffeotopy.fst_apply

variable (Φ : Diffeotopy J n M)

/-- Applying a diffeotopy returns the spatial component of its total diffeomorphism. -/
@[simp]
theorem coe_apply (p : I × M) : Φ p = (Φ.toDiffeomorph p).2 :=
  (rfl)

/-- The total diffeomorphism of a diffeotopy sends `(t, x)` to `(t, Φ (t, x))`. -/
theorem toDiffeomorph_apply (p : I × M) : Φ.toDiffeomorph p = (p.1, Φ p) := by
  exact Prod.ext (Φ.fst_apply p) rfl

/-- A diffeotopy starts at the identity. -/
@[simp]
theorem apply_zero (x : M) : Φ (0, x) = x :=
  Φ.snd_apply_zero' x

/-- A diffeotopy is a `C^n` map of time and space into the ambient manifold. -/
theorem contMDiff : ContMDiff ((𝓡∂ 1).prod J) J n Φ :=
  contMDiff_snd.comp Φ.toDiffeomorph.contMDiff

/-- The inverse total diffeomorphism also preserves the time coordinate. -/
@[simp]
theorem fst_symm_apply (p : I × M) : (Φ.toDiffeomorph.symm p).1 = p.1 := by
  have h := Φ.fst_apply (Φ.toDiffeomorph.symm p)
  rw [Φ.toDiffeomorph.apply_symm_apply] at h
  exact h.symm

/-- The inverse total diffeomorphism sends `p` to its time coordinate paired with its spatial
component. -/
theorem toDiffeomorph_symm_apply (p : I × M) :
    Φ.toDiffeomorph.symm p = (p.1, (Φ.toDiffeomorph.symm p).2) := by
  exact Prod.ext (Φ.fst_symm_apply p) rfl

/-- The time-`t` slice of a diffeotopy, bundled as a self-diffeomorphism of `M`. -/
def timeSlice (t : I) : M ≃ₘ^n⟮J, J⟯ M where
  toEquiv :=
    { toFun := fun x ↦ Φ (t, x)
      invFun := fun y ↦ (Φ.toDiffeomorph.symm (t, y)).2
      left_inv := fun x ↦ by
        simp only [coe_apply]
        have hp : (t, (Φ.toDiffeomorph (t, x)).2) = Φ.toDiffeomorph (t, x) :=
          (Φ.toDiffeomorph_apply (t, x)).symm
        rw [hp, Φ.toDiffeomorph.symm_apply_apply]
      right_inv := fun y ↦ by
        simp only [coe_apply]
        have hp : (t, (Φ.toDiffeomorph.symm (t, y)).2) =
            Φ.toDiffeomorph.symm (t, y) := (Φ.toDiffeomorph_symm_apply (t, y)).symm
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

/-- The time-zero slice of a diffeotopy is the identity diffeomorphism. -/
@[simp]
theorem timeSlice_zero : Φ.timeSlice 0 = _root_.Diffeomorph.refl J M n := by
  apply _root_.Diffeomorph.ext
  exact Φ.apply_zero

/-- The time-`1` self-diffeomorphism of a diffeotopy. -/
def final : M ≃ₘ^n⟮J, J⟯ M :=
  Φ.timeSlice 1

/-- The final diffeomorphism is the time-one slice. -/
theorem final_def : Φ.final = Φ.timeSlice 1 :=
  (rfl)

/-- The final diffeomorphism acts by the time-one slice. -/
@[simp]
theorem final_apply (x : M) : Φ.final x = Φ (1, x) :=
  (rfl)

/-- The constant diffeotopy at the identity. -/
def refl (J : ModelWithCorners ℝ E H) (n : ℕ∞ω) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Diffeotopy J n M where
  toDiffeomorph := _root_.Diffeomorph.refl ((𝓡∂ 1).prod J) (I × M) n
  fst_apply _ := rfl
  snd_apply_zero' _ := rfl

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

/-- The final diffeomorphism of the constant diffeotopy is the identity. -/
@[simp]
theorem final_refl : (refl J n M).final = _root_.Diffeomorph.refl J M n := by
  rw [final_def, timeSlice_refl]

/-- Compose two diffeotopies pointwise, first `Φ` and then `Ψ`. -/
def trans (Φ Ψ : Diffeotopy J n M) : Diffeotopy J n M where
  toDiffeomorph := Φ.toDiffeomorph.trans Ψ.toDiffeomorph
  fst_apply p := by
    rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) p,
      Function.comp_apply, Ψ.fst_apply, Φ.fst_apply]
  snd_apply_zero' x := by
    rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) (0, x),
      Function.comp_apply, Φ.toDiffeomorph_apply, Φ.apply_zero]
    exact Ψ.apply_zero x

/-- Evaluating a composite diffeotopy applies `Φ` and then `Ψ` at the same time. -/
@[simp]
theorem trans_apply (Ψ : Diffeotopy J n M) (p : I × M) :
    Φ.trans Ψ p = Ψ (p.1, Φ p) := by
  simp only [coe_apply]
  unfold trans
  rw [congr_fun (_root_.Diffeomorph.coe_trans Φ.toDiffeomorph Ψ.toDiffeomorph) p,
    Function.comp_apply, Φ.toDiffeomorph_apply]

/-- The time slice of a composite diffeotopy is the composite of its time slices. -/
@[simp]
theorem timeSlice_trans (Ψ : Diffeotopy J n M) (t : I) :
    (Φ.trans Ψ).timeSlice t = (Φ.timeSlice t).trans (Ψ.timeSlice t) := by
  apply _root_.Diffeomorph.ext
  intro x
  simpa only [timeSlice_apply, _root_.Diffeomorph.coe_trans, Function.comp_apply] using
    Φ.trans_apply Ψ (t, x)

/-- The final diffeomorphism of a composite diffeotopy is the composite of the final
diffeomorphisms. -/
@[simp]
theorem final_trans (Ψ : Diffeotopy J n M) :
    (Φ.trans Ψ).final = Φ.final.trans Ψ.final := by
  simpa only [final_def] using Φ.timeSlice_trans Ψ 1

/-- Reverse a diffeotopy by taking the inverse of its level-preserving total diffeomorphism. -/
def symm (Φ : Diffeotopy J n M) : Diffeotopy J n M where
  toDiffeomorph := Φ.toDiffeomorph.symm
  fst_apply := Φ.fst_symm_apply
  snd_apply_zero' x := by
    have hp : Φ.toDiffeomorph (0, x) = (0, x) := by
      rw [Φ.toDiffeomorph_apply, Φ.apply_zero]
    rw [← hp, Φ.toDiffeomorph.symm_apply_apply]

/-- Evaluating the inverse diffeotopy uses the spatial component of the inverse total
diffeomorphism. -/
@[simp]
theorem symm_apply (p : I × M) : Φ.symm p = (Φ.toDiffeomorph.symm p).2 :=
  (rfl)

/-- The inverse of the time-`t` slice acts by the inverse diffeotopy at time `t`. -/
@[simp]
theorem symm_timeSlice_apply (t : I) (x : M) :
    (Φ.timeSlice t).symm x = Φ.symm (t, x) :=
  (rfl)

/-- The time slice of the inverse diffeotopy is the inverse time slice. -/
@[simp]
theorem timeSlice_symm (t : I) :
    Φ.symm.timeSlice t = (Φ.timeSlice t).symm := by
  apply _root_.Diffeomorph.ext
  intro x
  rw [timeSlice_apply, symm_timeSlice_apply]

/-- A diffeotopy followed by its inverse fixes every point. -/
@[simp]
theorem symm_apply_apply (p : I × M) :
    (Φ.toDiffeomorph.symm (p.1, (Φ.toDiffeomorph p).2)).2 = p.2 := by
  have hp : (p.1, (Φ.toDiffeomorph p).2) = Φ.toDiffeomorph p :=
    Prod.ext (Φ.fst_apply p).symm rfl
  rw [hp, Φ.toDiffeomorph.symm_apply_apply]

/-- The inverse diffeotopy followed by the original fixes every point. -/
@[simp]
theorem apply_symm_apply (p : I × M) :
    (Φ.toDiffeomorph (p.1, (Φ.toDiffeomorph.symm p).2)).2 = p.2 := by
  have hp : (p.1, (Φ.toDiffeomorph.symm p).2) = Φ.toDiffeomorph.symm p :=
    Prod.ext (Φ.fst_symm_apply p).symm rfl
  rw [hp, Φ.toDiffeomorph.apply_symm_apply]

/-- The final diffeomorphism of the inverse diffeotopy is the inverse final diffeomorphism. -/
@[simp]
theorem final_symm : Φ.symm.final = Φ.final.symm := by
  simpa only [final_def] using Φ.timeSlice_symm 1

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

/-- Forgetting smoothness commutes with composition of diffeotopies. -/
@[simp]
theorem toAmbientIsotopy_trans (Ψ : Diffeotopy J n M) :
    (Φ.trans Ψ).toAmbientIsotopy = Φ.toAmbientIsotopy.trans Ψ.toAmbientIsotopy := by
  apply AmbientIsotopy.ext
  intro p
  rw [toAmbientIsotopy_apply, AmbientIsotopy.trans_apply, toAmbientIsotopy_apply,
    toAmbientIsotopy_apply, trans_apply]

/-- Forgetting smoothness commutes with inversion of diffeotopies. -/
@[simp]
theorem toAmbientIsotopy_symm :
    Φ.symm.toAmbientIsotopy = Φ.toAmbientIsotopy.symm := by
  have htotal : Φ.toAmbientIsotopy.totalHomeomorph = Φ.toDiffeomorph.toHomeomorph := by
    apply Homeomorph.ext
    intro p
    rw [AmbientIsotopy.totalHomeomorph_apply]
    simpa only [toAmbientIsotopy_apply, _root_.Diffeomorph.coe_toHomeomorph] using
      (Φ.toDiffeomorph_apply p).symm
  apply AmbientIsotopy.ext
  intro p
  rw [toAmbientIsotopy_apply, AmbientIsotopy.symm_apply, htotal, symm_apply]
  simp only [_root_.Diffeomorph.coe_toHomeomorph_symm]

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

/-- The constant diffeotopy is a left identity for composition. -/
@[simp]
theorem refl_trans : (refl J n M).trans Φ = Φ := by
  apply ext
  intro p
  simp

/-- The constant diffeotopy is a right identity for composition. -/
@[simp]
theorem trans_refl : Φ.trans (refl J n M) = Φ := by
  apply ext
  intro p
  simp

/-- Composition of diffeotopies is associative. -/
theorem trans_assoc (Ψ Θ : Diffeotopy J n M) :
    (Φ.trans Ψ).trans Θ = Φ.trans (Ψ.trans Θ) := by
  apply ext
  intro p
  simp

/-- Inverting a diffeotopy twice recovers the original diffeotopy. -/
@[simp]
theorem symm_symm : Φ.symm.symm = Φ := by
  have htotal : Φ.symm.toDiffeomorph.symm = Φ.toDiffeomorph := by
    apply _root_.Diffeomorph.ext
    intro p
    rfl
  apply ext
  intro p
  rw [symm_apply, htotal, coe_apply]

/-- A diffeotopy followed by its inverse is the constant diffeotopy. -/
@[simp]
theorem self_trans_symm : Φ.trans Φ.symm = refl J n M := by
  apply ext
  intro p
  simp

/-- A diffeotopy inverse followed by the original is the constant diffeotopy. -/
@[simp]
theorem symm_trans_self : Φ.symm.trans Φ = refl J n M := by
  apply ext
  intro p
  simp

end Diffeotopy

end TauCeti
