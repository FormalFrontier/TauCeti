module

public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Ring

/-!
# Euler and Tits forms of a finite quiver

The Euler form records the oriented incidence data of a finite quiver. Its diagonal,
the Tits form, is the numerical form used by reflection functors and Gabriel's theorem.

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

end TauCeti
