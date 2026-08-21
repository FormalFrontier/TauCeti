/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Analytic.IsolatedZeros

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology

/-!
# The open box around the truncated fundamental domain

The open coordinate box `(-1, 1) ×ℂ (1/2, M)`: it is open, it lies inside the upper
half-plane, and it contains the standard fundamental domain truncated at any height below `M`.
A function analytic on the upper half-plane and nonzero somewhere has finitely many zeros in
the box, because the box is squeezed between compacts of the half-plane.

The box is the ambient open set of the valence formula's residue side: its openness and the
finiteness of the zero set inside it are what let the boundary contour integral of a
logarithmic derivative be traded for a finite winding-weighted sum over the zeros.

## Main declarations

* `TauCeti.ModularForm.fdBox`: the open box.
* `TauCeti.ModularForm.coe_truncatedFundamentalDomain_subset_fdBox`: the truncated fundamental
  domain lies in the box.
* `TauCeti.ModularForm.finite_setOf_mem_fdBox_and_eq_zero`: an analytic function on the upper
  half-plane that is nonzero somewhere has finitely many zeros in the box.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/ResidueSideInfra.lean`) this file ports onto
  the current Mathlib pin.
-/

public section

open Complex Set UpperHalfPlane

namespace TauCeti

namespace ModularForm

/-- The open coordinate box `(-1, 1) ×ℂ (1/2, M)` around the truncated fundamental domain. Its
floor `1/2` sits strictly below the fundamental domain's lowest point `√3/2` while keeping the
closed box inside the upper half-plane. -/
def fdBox (M : ℝ) : Set ℂ := Ioo (-1) 1 ×ℂ Ioo (1 / 2) M

/-- Membership in the box, unfolded to the coordinate bounds. -/
@[simp]
theorem mem_fdBox {M : ℝ} {z : ℂ} :
    z ∈ fdBox M ↔ (-1 < z.re ∧ z.re < 1) ∧ 1 / 2 < z.im ∧ z.im < M := by
  simp [fdBox, mem_reProdIm]

/-- The box is open. -/
theorem isOpen_fdBox (M : ℝ) : IsOpen (fdBox M) := isOpen_Ioo.reProdIm isOpen_Ioo

/-- The box lies inside the open upper half-plane: its floor is positive. -/
theorem fdBox_subset_upperHalfPlaneSet {M : ℝ} : fdBox M ⊆ upperHalfPlaneSet := fun z hz =>
  lt_trans (by norm_num) (mem_fdBox.mp hz).2.1

/-- The standard fundamental domain truncated at height `H` lies inside the open box of any
height `M > H`. -/
theorem coe_truncatedFundamentalDomain_subset_fdBox {H M : ℝ} (hHM : H < M) :
    UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ fdBox M := by
  rw [ModularGroup.coe_truncatedFundamentalDomain]
  rintro z ⟨him0, himH, hre, hnorm⟩
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.one_le_sqrt] at hnorm
  rw [abs_le] at hre
  refine mem_fdBox.mpr ⟨⟨by linarith, by linarith⟩, by nlinarith, by linarith⟩

/-- **Finiteness of the zeros in the box.** A function analytic on the upper half-plane and
nonzero at some point of it has finitely many zeros in `fdBox M`. -/
theorem finite_setOf_mem_fdBox_and_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℂ → E} {x : ℂ} (M : ℝ)
    (hg : AnalyticOnNhd ℂ g upperHalfPlaneSet) (hx : 0 < x.im) (hgx : g x ≠ 0) :
    {z ∈ fdBox M | g z = 0}.Finite := by
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ℂ Icc (1 / 2) M) := isCompact_Icc.reProdIm isCompact_Icc
  have hKU : Icc (-1 : ℝ) 1 ×ℂ Icc (1 / 2) M ⊆ upperHalfPlaneSet := fun z hz =>
    lt_of_lt_of_le (by norm_num) (mem_reProdIm.mp hz).2.1
  have hconn : IsPreconnected upperHalfPlaneSet := (convex_halfSpace_im_gt 0).isPreconnected
  refine (finite_setOf_mem_and_eq_zero_of_isCompact hg hconn hx hgx hK hKU).subset
    fun z hz => ?_
  obtain ⟨hbox, hgz⟩ := hz
  obtain ⟨hre, him⟩ := mem_reProdIm.mp hbox
  exact ⟨mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hre, Ioo_subset_Icc_self him⟩, hgz⟩

end ModularForm

end TauCeti

end
