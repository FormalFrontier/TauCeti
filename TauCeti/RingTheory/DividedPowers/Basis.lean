/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
public import Mathlib.LinearAlgebra.Basis.Submodule

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

* `TauCeti.Associative.span_dividedPower_eq_span_pow`: divided and ordinary powers have the same
  rational span.
* `TauCeti.Associative.linearIndependent_dividedPower_iff`: divided powers are rationally
  independent exactly when ordinary powers are.
* `TauCeti.Associative.dividedPowerSpanBasis`: the resulting basis of the rational span.
* `TauCeti.Associative.dividedPowerLattice`: the integral span of the divided powers.
* `TauCeti.Associative.dividedPowerLatticeBasis`: its canonical `ℤ`-basis.
* `TauCeti.Associative.mem_dividedPowerLattice_iff`: membership as a finite integral linear
  combination.

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

/-- The divided powers of an element and its ordinary powers span the same rational submodule. -/
theorem span_dividedPower_eq_span_pow (x : A) :
    span ℚ (range fun n : ℕ => dividedPower n x) = span ℚ (range fun n : ℕ => x ^ n) := by
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨n, rfl⟩
    change dividedPower n x ∈ span ℚ (range fun n : ℕ => x ^ n)
    rw [dividedPower_def]
    exact smul_mem _ _ (subset_span (mem_range_self n))
  · rw [span_le]
    rintro _ ⟨n, rfl⟩
    change x ^ n ∈ span ℚ (range fun n : ℕ => dividedPower n x)
    rw [← factorial_smul_dividedPower_eq_pow]
    exact smul_mem _ _ (subset_span (mem_range_self n))

private noncomputable def invFactorialUnit (n : ℕ) : ℚˣ :=
  Units.mk0 (n.factorial : ℚ)⁻¹ <| inv_ne_zero <| by exact_mod_cast n.factorial_ne_zero

private theorem invFactorialUnit_smul_pow (x : A) (n : ℕ) :
    invFactorialUnit n • x ^ n = dividedPower n x := by
  change (n.factorial : ℚ)⁻¹ • x ^ n = dividedPower n x
  exact (dividedPower_def n x).symm

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

/-- The rational submodule spanned by the divided powers of `x`. -/
noncomputable def dividedPowerSpan (x : A) : Submodule ℚ A :=
  span ℚ (range fun n : ℕ => dividedPower n x)

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

/-- When the powers of `x` are rationally independent, the divided powers form a `ℤ`-basis of
their integral lattice. -/
noncomputable def dividedPowerLatticeBasis (x : A)
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) :
    Module.Basis ℕ ℤ (dividedPowerLattice x) :=
  Module.Basis.span (linearIndependent_dividedPower_int h)

/-- The integral-lattice basis evaluates to the corresponding divided power in the ambient
algebra. -/
@[simp]
theorem coe_dividedPowerLatticeBasis_apply (x : A)
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) (n : ℕ) :
    (dividedPowerLatticeBasis x h n : A) = dividedPower n x := by
  exact Module.Basis.coe_span_apply (linearIndependent_dividedPower_int h) n

/-- Under rational independence of the powers, every element of the divided-power lattice has a
unique finite expansion in divided powers. -/
theorem existsUnique_sum_dividedPower_eq {x y : A}
    (h : LinearIndependent ℚ (fun n : ℕ => x ^ n)) :
    y ∈ dividedPowerLattice x ↔
      ∃! c : ℕ →₀ ℤ, c.sum (fun n a => a • dividedPower n x) = y := by
  rw [mem_dividedPowerLattice_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, hc, fun d hd => ?_⟩
    apply linearIndependent_dividedPower_int h
    simpa only [Finsupp.linearCombination_apply] using hd.trans hc.symm
  · exact ExistsUnique.exists

end Ring

end TauCeti.Associative
