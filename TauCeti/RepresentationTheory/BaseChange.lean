/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Base change of representations

This file extends a representation's scalars by base-changing each linear endomorphism. It also
records the descent step needed for fixed vectors: a nonzero common fixed vector after a field
extension yields a nonzero common fixed vector over the base field.

## Main declarations

* `Representation.baseChange`: scalar extension of a representation.
* `Representation.exists_common_fixed_vector_of_baseChange`: descent of a nonzero common
  fixed vector.
-/

public section

namespace TauCeti.Representation

open TensorProduct

universe u v w x

noncomputable section

variable {G : Type w} {V : Type x} [Monoid G]

section BaseChange

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid V] [Module R V]

/-- Extend the scalars of a representation by base-changing each linear endomorphism. -/
def _root_.Representation.baseChange (A : Type v) [CommSemiring A] [Algebra R A]
    (ρ : _root_.Representation R G V) : _root_.Representation A G (A ⊗[R] V) :=
  ((Module.End.baseChangeHom R A V :
      Module.End R V →ₐ[R] Module.End A (A ⊗[R] V)) :
    Module.End R V →* Module.End A (A ⊗[R] V)).comp ρ

/-- The action of a base-changed representation is the base change of the original action. -/
@[simp]
theorem _root_.Representation.baseChange_apply (ρ : _root_.Representation R G V) (g : G) :
    _root_.Representation.baseChange A ρ g = (ρ g).baseChange A :=
  by
    rw [_root_.Representation.baseChange, MonoidHom.comp_apply]
    rfl

end BaseChange

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [AddCommGroup V] [Module K V]

/-- A nonzero common fixed vector after a field extension descends to a nonzero common fixed
vector over the base field. -/
theorem _root_.Representation.exists_common_fixed_vector_of_baseChange
    (ρ : _root_.Representation K G V) {w : L ⊗[K] V} (hw : w ≠ 0)
    (hfixed : ∀ g, _root_.Representation.baseChange L ρ g w = w) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  let b := Module.Free.chooseBasis K V
  have hwrepr : (b.baseChange L).repr w ≠ 0 := fun h ↦
    hw ((b.baseChange L).repr.map_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hwrepr
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_ne_zero K hi
  let descend : L ⊗[K] V →ₗ[K] V :=
    (TensorProduct.lid K V).toLinearMap.comp (phi.rTensor V)
  have hbmap : (b.baseChange K).map (TensorProduct.lid K V) = b := by
    ext j
    simp
  have hbmap_repr (y : K ⊗[K] V) (j) :
      b.repr (TensorProduct.lid K V y) j = (b.baseChange K).repr y j := by
    have h := congrArg (fun c : Module.Basis _ K V ↦
      c.repr (TensorProduct.lid K V y) j) hbmap
    rw [Module.Basis.map_repr] at h
    simpa using h.symm
  have descend_repr (x : L ⊗[K] V) (j) :
      b.repr (descend x) j = phi ((b.baseChange L).repr x j) := by
    have descend_apply :
        descend x = TensorProduct.lid K V ((phi.rTensor V) x) := rfl
    calc
      b.repr (descend x) j =
          (b.baseChange K).repr ((phi.rTensor V) x) j := by
        rw [descend_apply]
        exact hbmap_repr ((phi.rTensor V) x) j
      _ = phi ((b.baseChange L).repr x j) := by
        rw [LinearMap.rTensor_def]
        exact (Module.Basis.map_baseChange_repr b phi x j).symm
  have descend_baseChange (f : Module.End K V) (x : L ⊗[K] V) :
      descend (f.baseChange L x) = f (descend x) := by
    have hcomm :
        (phi.rTensor V).comp (f.lTensor L) = (f.lTensor K).comp (phi.rTensor V) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    have hlid :
        (TensorProduct.lid K V).toLinearMap.comp (f.lTensor K) =
          f.comp (TensorProduct.lid K V).toLinearMap := by
      ext a
      simp
    calc
      descend (f.baseChange L x) =
          TensorProduct.lid K V ((phi.rTensor V) ((f.lTensor L) x)) := by
        rw [LinearMap.baseChange_eq_ltensor]
        rfl
      _ = TensorProduct.lid K V ((f.lTensor K) ((phi.rTensor V) x)) := by
        apply congrArg (TensorProduct.lid K V)
        simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hcomm x
      _ = f (TensorProduct.lid K V ((phi.rTensor V) x)) :=
        LinearMap.congr_fun hlid ((phi.rTensor V) x)
      _ = f (descend x) := rfl
  refine ⟨descend w, ?_, fun g ↦ ?_⟩
  · intro hzero
    apply hphi
    rw [← descend_repr w i, hzero]
    simp
  · rw [← descend_baseChange]
    exact congrArg descend (hfixed g)

end

end TauCeti.Representation
