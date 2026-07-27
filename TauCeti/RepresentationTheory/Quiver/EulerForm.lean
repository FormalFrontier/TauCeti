import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Euler and Tits forms of a finite quiver

The Euler form records the oriented incidence data of a finite quiver.  Its diagonal,
the Tits form, is the numerical form used by reflection functors and Gabriel's theorem.
-/

namespace TauCeti

open scoped BigOperators

universe u v

variable (Q : Type u) [Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- The Euler (or Ringel) form of a finite quiver.  Arrows are counted with multiplicity. -/
def eulerForm (d e : Q → ℤ) : ℤ :=
  (∑ v : Q, d v * e v) - ∑ a : Q, ∑ b : Q, ∑ _ : a ⟶ b, d a * e b

/-- The Tits form of a finite quiver, the diagonal of its Euler form. -/
def titsForm (d : Q → ℤ) : ℤ :=
  eulerForm Q d d

/-- The symmetric bilinear form obtained by polarizing the Tits form. -/
def titsPolarForm (d e : Q → ℤ) : ℤ :=
  eulerForm Q d e + eulerForm Q e d

@[simp]
theorem eulerForm_zero_left (e : Q → ℤ) : eulerForm Q 0 e = 0 := by
  simp [eulerForm]

@[simp]
theorem eulerForm_zero_right (d : Q → ℤ) : eulerForm Q d 0 = 0 := by
  simp [eulerForm]

@[simp]
theorem eulerForm_neg_left (d e : Q → ℤ) : eulerForm Q (-d) e = -eulerForm Q d e := by
  simp only [eulerForm, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

@[simp]
theorem eulerForm_neg_right (d e : Q → ℤ) : eulerForm Q d (-e) = -eulerForm Q d e := by
  simp only [eulerForm, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The Euler form is additive in its first argument. -/
theorem eulerForm_add_left (d₁ d₂ e : Q → ℤ) :
    eulerForm Q (d₁ + d₂) e = eulerForm Q d₁ e + eulerForm Q d₂ e := by
  simp only [eulerForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- The Euler form is additive in its second argument. -/
theorem eulerForm_add_right (d e₁ e₂ : Q → ℤ) :
    eulerForm Q d (e₁ + e₂) = eulerForm Q d e₁ + eulerForm Q d e₂ := by
  simp only [eulerForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- The Euler form respects subtraction in its first argument. -/
theorem eulerForm_sub_left (d₁ d₂ e : Q → ℤ) :
    eulerForm Q (d₁ - d₂) e = eulerForm Q d₁ e - eulerForm Q d₂ e := by
  rw [sub_eq_add_neg, eulerForm_add_left, eulerForm_neg_left]
  rfl

/-- The Euler form respects subtraction in its second argument. -/
theorem eulerForm_sub_right (d e₁ e₂ : Q → ℤ) :
    eulerForm Q d (e₁ - e₂) = eulerForm Q d e₁ - eulerForm Q d e₂ := by
  rw [sub_eq_add_neg, eulerForm_add_right, eulerForm_neg_right]
  rfl

@[simp]
theorem titsPolarForm_zero_left (e : Q → ℤ) : titsPolarForm Q 0 e = 0 := by
  simp [titsPolarForm]

@[simp]
theorem titsPolarForm_zero_right (d : Q → ℤ) : titsPolarForm Q d 0 = 0 := by
  simp [titsPolarForm]

/-- The polarized Tits form is symmetric. -/
theorem titsPolarForm_comm (d e : Q → ℤ) : titsPolarForm Q d e = titsPolarForm Q e d := by
  simp only [titsPolarForm]
  ring

@[simp]
theorem titsPolarForm_neg_left (d e : Q → ℤ) :
    titsPolarForm Q (-d) e = -titsPolarForm Q d e := by
  rw [titsPolarForm, eulerForm_neg_left, eulerForm_neg_right]
  rw [titsPolarForm]
  ring

@[simp]
theorem titsPolarForm_neg_right (d e : Q → ℤ) :
    titsPolarForm Q d (-e) = -titsPolarForm Q d e := by
  rw [titsPolarForm, eulerForm_neg_right, eulerForm_neg_left]
  rw [titsPolarForm]
  ring

/-- The polarized Tits form is additive in its first argument. -/
theorem titsPolarForm_add_left (d₁ d₂ e : Q → ℤ) :
    titsPolarForm Q (d₁ + d₂) e = titsPolarForm Q d₁ e + titsPolarForm Q d₂ e := by
  rw [titsPolarForm, eulerForm_add_left, eulerForm_add_right]
  rw [titsPolarForm, titsPolarForm]
  ring

/-- The polarized Tits form is additive in its second argument. -/
theorem titsPolarForm_add_right (d e₁ e₂ : Q → ℤ) :
    titsPolarForm Q d (e₁ + e₂) = titsPolarForm Q d e₁ + titsPolarForm Q d e₂ := by
  rw [titsPolarForm, eulerForm_add_right, eulerForm_add_left]
  rw [titsPolarForm, titsPolarForm]
  ring

/-- The polarized Tits form respects subtraction in its first argument. -/
theorem titsPolarForm_sub_left (d₁ d₂ e : Q → ℤ) :
    titsPolarForm Q (d₁ - d₂) e = titsPolarForm Q d₁ e - titsPolarForm Q d₂ e := by
  rw [sub_eq_add_neg, titsPolarForm_add_left, titsPolarForm_neg_left]
  rfl

/-- The polarized Tits form respects subtraction in its second argument. -/
theorem titsPolarForm_sub_right (d e₁ e₂ : Q → ℤ) :
    titsPolarForm Q d (e₁ - e₂) = titsPolarForm Q d e₁ - titsPolarForm Q d e₂ := by
  rw [sub_eq_add_neg, titsPolarForm_add_right, titsPolarForm_neg_right]
  rfl

/-- The Tits form is the diagonal evaluation of the Euler form. -/
theorem titsForm_eq_eulerForm (d : Q → ℤ) : titsForm Q d = eulerForm Q d d := rfl

@[simp]
theorem titsForm_zero : titsForm Q 0 = 0 :=
  eulerForm_zero_left Q 0

@[simp]
theorem titsForm_neg (d : Q → ℤ) : titsForm Q (-d) = titsForm Q d := by
  change eulerForm Q (-d) (-d) = eulerForm Q d d
  rw [eulerForm_neg_left, eulerForm_neg_right]
  simp

/-- Polarizing the Tits form recovers the symmetric form associated to the Euler form. -/
theorem titsForm_add (d e : Q → ℤ) :
    titsForm Q (d + e) = titsForm Q d + titsForm Q e + titsPolarForm Q d e := by
  rw [titsPolarForm]
  simp only [titsForm, eulerForm, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- The polarization identity for the Tits form. -/
theorem titsForm_sub (d e : Q → ℤ) :
    titsForm Q (d - e) = titsForm Q d + titsForm Q e - titsPolarForm Q d e := by
  rw [sub_eq_add_neg, titsForm_add, titsForm_neg, titsPolarForm_neg_right]
  rfl

end TauCeti
