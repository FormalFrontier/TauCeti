/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Ring

/-!
# Euler and Tits forms of a finite quiver

The Euler form records the oriented incidence data of a finite quiver. Its diagonal,
the Tits form, is the numerical form used by reflection functors and Gabriel's theorem.

The last section evaluates both forms on the simple dimension vectors `αᵢ = Pi.single i 1`;
in particular `TauCeti.titsPolarForm_single_single` computes the Gram matrix of the polarized
Tits form as `2·I - (A + Aᵀ)`, for `A` the matrix of arrow counts.

The definitions follow the Layer 4 signatures in
`TauCetiRoadmap/TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/Suggested.lean`.
See Derksen--Weyman, *An Introduction to Quiver Representations*.
-/

namespace TauCeti

open scoped BigOperators

universe u v

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- The Euler (or Ringel) form of a finite quiver. Arrows are counted with multiplicity. -/
public def eulerForm : LinearMap.BilinForm ℤ (Q → ℤ) :=
  LinearMap.mk₂ ℤ
    (fun d e =>
      (∑ v : Q, d v * e v) - ∑ a : Q, ∑ b : Q, ∑ _ : a ⟶ b, d a * e b)
    (by
      intro d₁ d₂ e
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      ring)
    (by
      intro c d e
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum, ← mul_assoc])
    (by
      intro d e₁ e₂
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring)
    (by
      intro c d e
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [← mul_assoc, mul_comm (d _) c]
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum, ← mul_assoc])

/-- The defining sum for the Euler form. -/
@[simp]
public theorem eulerForm_def (d e : Q → ℤ) :
    eulerForm Q d e =
      (∑ v : Q, d v * e v) - ∑ a : Q, ∑ b : Q, ∑ _ : a ⟶ b, d a * e b :=
  by apply LinearMap.mk₂_apply

/-- The Euler form with the arrows between each pair of vertices counted by cardinality. -/
public theorem eulerForm_eq_sum_card (d e : Q → ℤ) :
    eulerForm Q d e =
      (∑ v : Q, d v * e v)
        - ∑ a : Q, ∑ b : Q, (Fintype.card (a ⟶ b) : ℤ) * (d a * e b) := by
  rw [eulerForm_def]
  congr 1
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The Tits form of a finite quiver, the diagonal of its Euler form. -/
public def titsForm : QuadraticMap ℤ (Q → ℤ) ℤ :=
  (eulerForm Q).toQuadraticMap

/-- The defining equation for the Tits form. -/
@[simp]
public theorem titsForm_def (d : Q → ℤ) : titsForm Q d = eulerForm Q d d :=
  LinearMap.BilinMap.toQuadraticMap_apply _ _

/-- The symmetric bilinear form obtained by polarizing the Tits form. -/
public def titsPolarForm : LinearMap.BilinForm ℤ (Q → ℤ) :=
  (titsForm Q).polarBilin

/-- The defining equation for the polarized Tits form. -/
@[simp]
public theorem titsPolarForm_def (d e : Q → ℤ) :
    titsPolarForm Q d e = eulerForm Q d e + eulerForm Q e d := by
  simp only [titsPolarForm, QuadraticMap.polarBilin_apply_apply, titsForm,
    LinearMap.BilinMap.polar_toQuadraticMap]

/-- The Tits form evaluated at a sum. -/
public theorem titsForm_add (d e : Q → ℤ) :
    titsForm Q (d + e) = titsForm Q d + titsForm Q e + titsPolarForm Q d e := by
  simpa only [titsPolarForm, QuadraticMap.polarBilin_apply_apply] using
    QuadraticMap.map_add (titsForm Q) d e

/-- The Tits form evaluated at a difference. -/
public theorem titsForm_sub (d e : Q → ℤ) :
    titsForm Q (d - e) = titsForm Q d + titsForm Q e - titsPolarForm Q d e := by
  rw [sub_eq_add_neg, QuadraticMap.map_add (titsForm Q) d (-e), QuadraticMap.map_neg]
  simp only [titsPolarForm, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_neg_right,
    sub_eq_add_neg]

/-- The polarized Tits form is symmetric. -/
public theorem titsPolarForm_comm (d e : Q → ℤ) :
    titsPolarForm Q d e = titsPolarForm Q e d := by
  simpa only [titsPolarForm, QuadraticMap.polarBilin_apply_apply] using
    QuadraticMap.polar_comm (titsForm Q) d e

/-! ### The Euler and Tits forms in the simple dimension vectors -/

variable [DecidableEq Q]

/-- The Euler form with a simple dimension vector on the left counts the arrows out of `i`. -/
public theorem eulerForm_single_left (i : Q) (e : Q → ℤ) :
    eulerForm Q (Pi.single i 1) e = e i - ∑ b : Q, (Fintype.card (i ⟶ b) : ℤ) * e b := by
  have h₁ : ∑ v : Q, (Pi.single i 1 : Q → ℤ) v * e v = e i := by
    simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq']
  have h₂ : ∀ a : Q, (∑ b : Q, ∑ _f : a ⟶ b, (Pi.single i 1 : Q → ℤ) a * e b)
      = (Pi.single i 1 : Q → ℤ) a * ∑ b : Q, (Fintype.card (a ⟶ b) : ℤ) * e b := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [eulerForm_def, h₁, Finset.sum_congr rfl fun a _ ↦ h₂ a]
  simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq']

/-- The Euler form with a simple dimension vector on the right counts the arrows into `j`. -/
public theorem eulerForm_single_right (d : Q → ℤ) (j : Q) :
    eulerForm Q d (Pi.single j 1) = d j - ∑ a : Q, (Fintype.card (a ⟶ j) : ℤ) * d a := by
  have h₁ : ∑ v : Q, d v * (Pi.single j 1 : Q → ℤ) v = d j := by
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  have h₂ : ∀ a : Q, (∑ b : Q, ∑ _f : a ⟶ b, d a * (Pi.single j 1 : Q → ℤ) b)
      = (Fintype.card (a ⟶ j) : ℤ) * d a := by
    intro a
    have h₃ : ∀ b : Q, (∑ _f : a ⟶ b, d a * (Pi.single j 1 : Q → ℤ) b)
        = if b = j then (Fintype.card (a ⟶ b) : ℤ) * d a else 0 := by
      intro b
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Pi.single_apply]
      split <;> simp
    rw [Finset.sum_congr rfl fun b _ ↦ h₃ b, Finset.sum_ite_eq' Finset.univ j]
    simp
  rw [eulerForm_def, h₁, Finset.sum_congr rfl fun a _ ↦ h₂ a]

/-- The Euler form in the simple dimension vectors: `⟨αᵢ, αⱼ⟩ = δᵢⱼ - #(i ⟶ j)`. -/
public theorem eulerForm_single_single (i j : Q) :
    eulerForm Q (Pi.single i 1) (Pi.single j 1)
      = (if i = j then 1 else 0) - (Fintype.card (i ⟶ j) : ℤ) := by
  rw [eulerForm_single_left]
  simp [Pi.single_apply, mul_ite, eq_comm]

/-- The Tits form of a simple dimension vector is one minus the number of loops at that vertex. -/
public theorem titsForm_single (i : Q) :
    titsForm Q (Pi.single i 1) = 1 - (Fintype.card (i ⟶ i) : ℤ) := by
  rw [titsForm_def, eulerForm_single_single]
  simp

/-- A loopless vertex has a simple dimension vector of Tits norm one, that is, `αᵢ` is a root. -/
public theorem titsForm_single_of_isEmpty {i : Q} (h : IsEmpty (i ⟶ i)) :
    titsForm Q (Pi.single i 1) = 1 := by
  rw [titsForm_single, Fintype.card_eq_zero_iff.mpr h]
  simp

/-- The polarized Tits form against a simple dimension vector, in coordinates. -/
public theorem titsPolarForm_single_left (i : Q) (d : Q → ℤ) :
    titsPolarForm Q (Pi.single i 1) d
      = 2 * d i - ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [titsPolarForm_def, eulerForm_single_left, eulerForm_single_right]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- The polarized Tits form against a simple dimension vector on the right, in coordinates. -/
public theorem titsPolarForm_single_right (d : Q → ℤ) (i : Q) :
    titsPolarForm Q d (Pi.single i 1)
      = 2 * d i - ∑ v : Q, ((Fintype.card (i ⟶ v) : ℤ) + (Fintype.card (v ⟶ i) : ℤ)) * d v := by
  rw [titsPolarForm_comm, titsPolarForm_single_left]

/-- The Gram matrix of the polarized Tits form in the simple dimension vectors is
`2·I - (A + Aᵀ)`, for `A` the matrix of arrow counts: the symmetrized Cartan matrix of `Q`. -/
public theorem titsPolarForm_single_single (i j : Q) :
    titsPolarForm Q (Pi.single i 1) (Pi.single j 1)
      = 2 * (if i = j then 1 else 0)
        - ((Fintype.card (i ⟶ j) : ℤ) + (Fintype.card (j ⟶ i) : ℤ)) := by
  rw [titsPolarForm_def, eulerForm_single_single, eulerForm_single_single]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos (rfl : i = i)]
    ring
  · rw [if_neg hij, if_neg hij.symm]
    ring

/-- A loopless vertex has `⟨αᵢ, αᵢ⟩ = 2` for the polarized Tits form: the normalization that
makes the simple reflection at `i` an involution. -/
public theorem titsPolarForm_single_self_of_isEmpty {i : Q} (h : IsEmpty (i ⟶ i)) :
    titsPolarForm Q (Pi.single i 1) (Pi.single i 1) = 2 := by
  rw [titsPolarForm_single_single, Fintype.card_eq_zero_iff.mpr h]
  simp

end TauCeti
