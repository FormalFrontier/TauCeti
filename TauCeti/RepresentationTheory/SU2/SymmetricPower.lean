/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.SU2.Basic
import TauCeti.Algebra.GroupWithZero.Units.Basic
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete

/-!
# The symmetric powers of the standard representation of `SU(2)`

The candidate irreducible representations of `SU(2)` are the symmetric powers `Symᵈ(ℂ²)` of the
standard representation, of dimension `d + 1`.  This file builds them, as the restriction of the
symmetric powers of the standard representation of `GL₂(ℂ)` along the inclusion of `SU(2)`, and
computes their characters on the maximal torus.

The character computation is the **weight string**: on `diag(z, z⁻¹)` the character of `Symᵈ` is

`z^d + z^{d-2} + ⋯ + z^{-d}`,

each of the `d + 1` weights `d, d-2, …, -d` occurring exactly once.  This is what the
highest-weight classification of the irreducible representations of `SU(2)` runs on, and the
value at the identity is the dimension `d + 1`, the number of those weights.

The route is Layer 1's `TauCeti.char_symPowerRep_diagonal`, which gives the character at a
diagonal matrix as the complete homogeneous symmetric polynomial `h_d` in the diagonal entries,
together with its rank-two evaluation `TauCeti.eval_hsymm_fin_two`: the geometric-looking sum
`∑ᵢ x^i y^{d-i}`.

## Main definitions

* `TauCeti.SU2.toGL`: `SU(2)` as a subgroup of `GL₂(ℂ)`.
* `TauCeti.SU2.symPower`: the `d`-th symmetric power of the standard representation of `SU(2)`.

## Main results

* `TauCeti.SU2.character_symPower_torusHom` and
  `TauCeti.SU2.character_symPower_torusHom_zpow`: the character of `Symᵈ` on the maximal torus is
  the weight string `∑_{i ≤ d} z^{2i - d}`.
* `TauCeti.SU2.character_symPower_torusExp`: the same in exponential coordinates,
  `∑_{i ≤ d} e^{i(2i - d)θ}`.
* `TauCeti.SU2.finrank_symPower` and `TauCeti.SU2.character_symPower_one`: the dimension, and so
  the character at the identity, is `d + 1`.

## References

* [Compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  Layer 6, the `SU(2)` engine: the irreducibles `Symⁿ(ℂ²)` and the weight/string decomposition of
  their characters on the maximal torus.
* Daniel Bump, *Lie Groups*, second edition, Chapter 3.
-/

public section

open Finset Matrix
open scoped TensorProduct

namespace TauCeti

/-! ### The symmetric powers of the standard representation -/

namespace SU2

/-- `SU(2)` as a subgroup of `GL₂(ℂ)`: an element of the group `SU(2)` is a unit there, and a unit
of a submonoid of the matrices is a unit of the matrices. -/
def toGL : SU2 →* GL (Fin 2) ℂ :=
  (Units.map (Submonoid.subtype _)).comp toUnits.toMonoidHom

@[simp]
theorem coe_toGL (g : SU2) :
    (toGL g : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) := (rfl)

/-- The inclusion of `SU(2)` into `GL₂(ℂ)` is injective: it does not move the underlying matrix. -/
theorem toGL_injective : Function.Injective (toGL : SU2 → GL (Fin 2) ℂ) := fun g h hgh =>
  Subtype.ext (by rw [← coe_toGL, ← coe_toGL, hgh])

/-- **The maximal torus of `SU(2)` inside the diagonal torus of `GL₂(ℂ)`**: `torusHom z` is the
diagonal matrix `diag(z, z⁻¹)`. -/
theorem toGL_torusHom (z : Circle) :
    toGL (torusHom z) = diagGL ![Circle.toUnits z, (Circle.toUnits z)⁻¹] := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_toGL, coe_torusHom, diagGL_coe]
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix_apply_zero_zero, torusMatrix_apply_zero_one, torusMatrix_apply_one_zero,
      torusMatrix_apply_one_one, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne,
      Units.val_inv_eq_inv_val]

variable (d : ℕ)

/-- **The `d`-th symmetric power of the standard representation of `SU(2)`**, the candidate
irreducible of dimension `d + 1`: the restriction along `TauCeti.SU2.toGL` of the symmetric power
of the standard representation of `GL₂(ℂ)`. -/
noncomputable def symPower : Representation ℂ SU2 (Sym[ℂ]^d (Fin 2 → ℂ)) :=
  (symPowerRep ℂ 2 d).comp toGL

@[simp]
theorem symPower_apply (g : SU2) : symPower d g = symPowerRep ℂ 2 d (toGL g) := (rfl)

/-- **The space `Symᵈ(ℂ²)` carrying `TauCeti.SU2.symPower d` has dimension `d + 1`**: a symmetric
power of a free module is free on the unordered tuples of basis indices, of which there are
`Nat.multichoose 2 d = d + 1` in two variables. -/
@[simp]
theorem finrank_symPower : Module.finrank ℂ (Sym[ℂ]^d (Fin 2 → ℂ)) = d + 1 := by
  rw [SymmetricPower.finrank_eq, Module.finrank_fin_fun, Nat.multichoose_two]

/-- **The weight string.**  On the maximal torus the character of `Symᵈ(ℂ²)` is
`z^{-d} + z^{2-d} + ⋯ + z^d`: the `d + 1` weights `-d, 2-d, …, d` each occur once. -/
theorem character_symPower_torusHom (z : Circle) :
    (symPower d).character (torusHom z)
      = ∑ i ∈ range (d + 1), (z : ℂ) ^ i * ((z : ℂ)⁻¹) ^ (d - i) := by
  rw [Representation.character, symPower_apply, toGL_torusHom, ← Representation.character,
    char_symPowerRep_diagonal, eval_hsymm_fin_two]
  refine sum_congr rfl fun i _ => ?_
  simp

/-- The weight string with the weights displayed as integer exponents `2i - d`. -/
theorem character_symPower_torusHom_zpow (z : Circle) :
    (symPower d).character (torusHom z)
      = ∑ i ∈ range (d + 1), (z : ℂ) ^ (2 * (i : ℤ) - d) := by
  rw [character_symPower_torusHom]
  -- the diagonal entries `z` and `z⁻¹` contribute `i` and `d - i` factors to the `i`-th monomial
  exact sum_congr rfl fun i hi =>
    pow_mul_inv_pow_eq_zpow₀ (Circle.coe_ne_zero z) (Nat.lt_succ_iff.mp (mem_range.mp hi))

/-- **The weight string in exponential coordinates.**  Writing the torus element as
`diag(e^{iθ}, e^{-iθ})`, the character of `Symᵈ(ℂ²)` is `∑ᵢ e^{i(2i-d)θ}`: the classical
`e^{idθ} + e^{i(d-2)θ} + ⋯ + e^{-idθ}`. -/
theorem character_symPower_torusExp (θ : ℝ) :
    (symPower d).character (torusExp θ)
      = ∑ i ∈ range (d + 1), Complex.exp ((2 * (i : ℂ) - d) * (θ * Complex.I)) := by
  rw [torusExp_def, character_symPower_torusHom_zpow]
  refine sum_congr rfl fun i _ => ?_
  rw [Circle.coe_exp, ← Complex.exp_int_mul]
  push_cast
  ring_nf

/-- **The dimension is `d + 1`**: the character at the identity is the rank of the underlying
space, which is the number `d + 1` of weights of the string above, each of multiplicity one. -/
theorem character_symPower_one : (symPower d).character 1 = (d : ℂ) + 1 := by
  rw [Representation.char_one, finrank_symPower]
  push_cast
  ring

end SU2

end TauCeti
