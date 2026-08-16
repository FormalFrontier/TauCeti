/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
public import Mathlib.LinearAlgebra.Basis.Submodule
public import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# Bases of divided powers

In an associative rational algebra, the divided powers of an element differ from its ordinary
powers by the nonzero scalars `1 / n!`. Consequently the two families span the same rational
submodule and one is linearly independent exactly when the other is. When they are independent,
the divided powers also give a canonical integral basis of their `ℤ`-span.

This isolates the root-vector factor in the integral PBW argument for the Kostant form. For a
Chevalley root vector, rational PBW supplies independence of the ordinary powers; the results here
then turn its divided powers into the integral basis used in the Chevalley--Demazure construction
of Layer 9 of the ReductiveGroups roadmap. The Cartan factor is instead built from the binomial
polynomials `(X choose n)`.

## Main declarations

* `TauCeti.Associative.dividedPowerSpan`: the rational submodule spanned by divided powers.
* `TauCeti.Associative.dividedPowerSpan_eq_span_pow`: divided and ordinary powers have the same
  rational span.
* `TauCeti.Associative.linearIndependent_dividedPower_iff`: divided powers are rationally
  independent exactly when ordinary powers are.
* `TauCeti.Associative.dividedPowerSpanBasis`: the resulting basis of the rational span.
* `TauCeti.Associative.dividedPowerLattice`: the integral span of the divided powers.
* `TauCeti.Associative.dividedPowerLatticeBasis`: its canonical `ℤ`-basis.
* `TauCeti.Associative.mem_dividedPowerLattice_iff`: membership as a finite integral linear
  combination.
* `TauCeti.Associative.mem_dividedPowerLattice_iff_existsUnique_sum_dividedPower_eq`: unique finite
  expansion in divided powers for elements of the integral lattice.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 26.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., II.1.
-/

public section

namespace TauCeti.Associative

open Set Submodule

universe u

section Semiring

variable {A : Type u} [Semiring A] [Algebra ℚ A]

/-- The rational submodule spanned by the divided powers of `x`. -/
noncomputable def dividedPowerSpan (x : A) : Submodule ℚ A :=
  span ℚ (range fun n : ℕ => dividedPower n x)

/-- The defining equation of `dividedPowerSpan`. -/
theorem dividedPowerSpan_def (x : A) :
    dividedPowerSpan x = span ℚ (range fun n : ℕ => dividedPower n x) := by
  unfold dividedPowerSpan
  rfl

/-- Every divided power of `x` belongs to `dividedPowerSpan x`. -/
@[simp]
theorem dividedPower_mem_dividedPowerSpan (x : A) (n : ℕ) :
    dividedPower n x ∈ dividedPowerSpan x :=
  subset_span (mem_range_self n)

/-- Containment characterization for `dividedPowerSpan x`. -/
@[simp]
theorem dividedPowerSpan_le_iff {x : A} {p : Submodule ℚ A} :
    dividedPowerSpan x ≤ p ↔ ∀ n : ℕ, dividedPower n x ∈ p := by
  rw [dividedPowerSpan_def, span_le, Set.range_subset_iff]
  rfl

/-- The divided powers of an element and its ordinary powers span the same rational submodule. -/
theorem dividedPowerSpan_eq_span_pow (x : A) :
    dividedPowerSpan x = span ℚ (range fun n : ℕ => x ^ n) := by
  apply le_antisymm
  · rw [dividedPowerSpan_le_iff]
    intro n
    rw [dividedPower_def]
    exact smul_mem _ _ (subset_span (mem_range_self n))
  · rw [span_le, range_subset_iff]
    intro n
    rw [← factorial_smul_dividedPower_eq_pow]
    exact smul_mem _ _ (dividedPower_mem_dividedPowerSpan x n)

private noncomputable def invFactorialUnit (n : ℕ) : ℚˣ :=
  Units.mk0 (n.factorial : ℚ)⁻¹ <| inv_ne_zero <| by exact_mod_cast n.factorial_ne_zero

private theorem invFactorialUnit_smul_pow (x : A) (n : ℕ) :
    invFactorialUnit n • x ^ n = dividedPower n x := by
  rw [Units.smul_def, invFactorialUnit, Units.val_mk0, dividedPower_def]

/-- Divided powers are linearly independent over `ℚ` exactly when the ordinary powers are. -/
theorem linearIndependent_dividedPower_iff (x : A) :
    LinearIndependent ℚ (fun n : ℕ => dividedPower n x) ↔
      LinearIndependent ℚ (fun n : ℕ => x ^ n) := by
  rw [← LinearIndependent.units_smul_iff (fun n : ℕ => x ^ n) invFactorialUnit]
  convert Iff.rfl using 2
  exact funext (invFactorialUnit_smul_pow x)

/-- Divided powers are linearly independent whenever the ordinary powers are. -/
theorem linearIndependent_dividedPower {x : A}
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) :
    LinearIndependent ℚ (fun n : ℕ => dividedPower n x) :=
  (linearIndependent_dividedPower_iff x).2 h

/-- When the powers of `x` are linearly independent, the divided powers form a basis of their
rational span. -/
noncomputable def dividedPowerSpanBasis (x : A)
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) :
    Module.Basis ℕ ℚ (dividedPowerSpan x) :=
  Module.Basis.span (linearIndependent_dividedPower h)

/-- The rational-span basis evaluates to the corresponding divided power in the ambient algebra. -/
@[simp]
theorem coe_dividedPowerSpanBasis_apply (x : A)
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) (n : ℕ) :
    (dividedPowerSpanBasis x h n : A) = dividedPower n x := by
  exact Module.Basis.coe_span_apply (linearIndependent_dividedPower h) n

end Semiring

section Ring

variable {A : Type u} [Ring A] [Algebra ℚ A]

/-- The integral lattice spanned by the divided powers of `x`. -/
noncomputable def dividedPowerLattice (x : A) : Submodule ℤ A :=
  span ℤ (range fun n : ℕ => dividedPower n x)

/-- The defining equation of `dividedPowerLattice`. -/
theorem dividedPowerLattice_def (x : A) :
    dividedPowerLattice x = span ℤ (range fun n : ℕ => dividedPower n x) := by
  unfold dividedPowerLattice
  rfl

/-- Every divided power of `x` belongs to `dividedPowerLattice x`. -/
@[simp]
theorem dividedPower_mem_dividedPowerLattice (x : A) (n : ℕ) :
    dividedPower n x ∈ dividedPowerLattice x :=
  subset_span (mem_range_self n)

/-- Containment characterization for `dividedPowerLattice x`. -/
@[simp]
theorem dividedPowerLattice_le_iff {x : A} {p : Submodule ℤ A} :
    dividedPowerLattice x ≤ p ↔ ∀ n : ℕ, dividedPower n x ∈ p := by
  rw [dividedPowerLattice_def, span_le, Set.range_subset_iff]
  rfl

/-- Membership in the divided-power lattice means being a finite integral linear combination of
divided powers. -/
theorem mem_dividedPowerLattice_iff {x y : A} :
    y ∈ dividedPowerLattice x ↔
      ∃ c : ℕ →₀ ℤ, c.sum (fun n a => a • dividedPower n x) = y := by
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- Rational independence of the ordinary powers makes the divided powers integrally independent. -/
theorem linearIndependent_dividedPower_int {x : A}
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) :
    LinearIndependent ℤ (fun n : ℕ => dividedPower n x) :=
  (linearIndependent_dividedPower h).restrict_scalars (smul_left_injective ℤ one_ne_zero)

/-- When the divided powers of `x` are integrally independent, they form a `ℤ`-basis of their
integral lattice. -/
noncomputable def dividedPowerLatticeBasis (x : A)
    (h : LinearIndependent ℤ (fun n : ℕ => dividedPower n x)) :
    Module.Basis ℕ ℤ (dividedPowerLattice x) :=
  Module.Basis.span h

/-- The integral-lattice basis evaluates to the corresponding divided power in the ambient
algebra. -/
@[simp]
theorem coe_dividedPowerLatticeBasis_apply (x : A)
    (h : LinearIndependent ℤ (fun n : ℕ => dividedPower n x)) (n : ℕ) :
    (dividedPowerLatticeBasis x h n : A) = dividedPower n x := by
  exact Module.Basis.coe_span_apply h n

/-- Under integral independence of the divided powers, every element of the divided-power lattice
has a unique finite expansion in divided powers. -/
theorem mem_dividedPowerLattice_iff_existsUnique_sum_dividedPower_eq {x y : A}
    (h : LinearIndependent ℤ (fun n : ℕ => dividedPower n x)) :
    y ∈ dividedPowerLattice x ↔
      ∃! c : ℕ →₀ ℤ, c.sum (fun n a => a • dividedPower n x) = y := by
  rw [dividedPowerLattice_def]
  exact TauCeti.LinearIndependent.mem_span_range_iff_existsUnique h y

/-- Rational independence of the powers gives the canonical `ℤ`-basis of the integral
divided-power lattice. -/
noncomputable def dividedPowerLatticeBasisOfPow (x : A)
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) :
    Module.Basis ℕ ℤ (dividedPowerLattice x) :=
  dividedPowerLatticeBasis x (linearIndependent_dividedPower_int h)

/-- Under rational independence of the powers, every element of the divided-power lattice has a
unique finite expansion in divided powers. -/
theorem mem_dividedPowerLattice_iff_existsUnique_sum_dividedPower_eq_of_pow {x y : A}
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) :
    y ∈ dividedPowerLattice x ↔
      ∃! c : ℕ →₀ ℤ, c.sum (fun n a => a • dividedPower n x) = y :=
  mem_dividedPowerLattice_iff_existsUnique_sum_dividedPower_eq
    (linearIndependent_dividedPower_int h)

end Ring

end TauCeti.Associative
