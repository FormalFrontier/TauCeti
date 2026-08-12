/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.SU2.Basic

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
value `d + 1` at the identity is read off it at `z = 1`.

The route is Layer 1's `TauCeti.char_symPowerRep_diagonal`, which gives the character at a
diagonal matrix as the complete homogeneous symmetric polynomial `h_d` in the diagonal entries.
The rank-two case of that polynomial is the geometric-looking sum `∑ᵢ x^i y^{d-i}`, proved here
from the bijection `TauCeti.symFinTwoEquiv` between the `d`-element multisets over a two-element
type and `Fin (d + 1)`, which records how many of the entries are `0`.

## Main definitions

* `TauCeti.symFinTwoEquiv`: multisets of size `d` over `Fin 2` are counted by `Fin (d + 1)`.
* `TauCeti.SU2.toGL`: `SU(2)` as a subgroup of `GL₂(ℂ)`.
* `TauCeti.SU2.symPower`: the `d`-th symmetric power of the standard representation of `SU(2)`.

## Main results

* `TauCeti.eval_hsymm_fin_two`: `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`.
* `TauCeti.SU2.character_symPower_torusHom` and
  `TauCeti.SU2.character_symPower_torusHom_zpow`: the character of `Symᵈ` on the maximal torus is
  the weight string `∑_{i ≤ d} z^{2i - d}`.
* `TauCeti.SU2.character_symPower_torusExp`: the same in exponential coordinates,
  `∑_{i ≤ d} e^{i(2i - d)θ}`.
* `TauCeti.SU2.character_symPower_one`: the dimension is `d + 1`.

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

/-! ### Multisets over a two-element type -/

/-- **A multiset of size `d` over `Fin 2` is determined by how many of its entries are `0`**, and
that count can be anything from `0` to `d`.  This is the rank-two instance of the count
`#(Sym α d) = (#α + d - 1).choose d`, in the form the symmetric-polynomial computation below
consumes. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) where
  toFun s := ⟨Multiset.count 0 s.1, by
    have h := Multiset.count_le_card (0 : Fin 2) s.1
    rw [s.2] at h
    omega⟩
  invFun i := ⟨Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1, by
    have hi : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.2
    simp only [Multiset.card_add, Multiset.card_replicate]
    omega⟩
  left_inv s := by
    obtain ⟨m, hm⟩ := s
    have hcount : Multiset.count (0 : Fin 2) m + Multiset.count (1 : Fin 2) m = d := by
      have := Multiset.sum_count_eq_card (s := (univ : Finset (Fin 2))) (m := m)
        (fun a _ => mem_univ a)
      rw [Fin.sum_univ_two, hm] at this
      exact this
    refine Subtype.ext (Multiset.ext.mpr fun a => ?_)
    have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases ha with rfl | rfl
    · simp [Multiset.count_add, Multiset.count_replicate]
    · simp only [Multiset.count_add, Multiset.count_replicate]
      norm_num
      omega
  right_inv i := by
    have hi : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.2
    refine Fin.ext ?_
    simp [Multiset.count_replicate]

/-- The inverse of `TauCeti.symFinTwoEquiv` spelled out: `i` many `0`s and `d - i` many `1`s. -/
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := (rfl)

/-- **The complete homogeneous symmetric polynomial in two variables**: `h_d(x, y)` is the sum of
all `d + 1` monomials `xⁱ y^{d-i}` of degree `d`. -/
theorem eval_hsymm_fin_two {R : Type*} [CommSemiring R] (f : Fin 2 → R) (d : ℕ) :
    MvPolynomial.eval f (MvPolynomial.hsymm (Fin 2) R d)
      = ∑ i ∈ range (d + 1), f 0 ^ i * f 1 ^ (d - i) := by
  rw [eval_hsymm, ← Fin.sum_univ_eq_sum_range _ (d + 1),
    ← Equiv.sum_comp (symFinTwoEquiv d).symm]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [coe_symFinTwoEquiv_symm_apply]
  simp

/-! ### The symmetric powers of the standard representation -/

namespace SU2

/-- `SU(2)` as a subgroup of `GL₂(ℂ)`: an element of the group `SU(2)` is a unit there, and a unit
of a submonoid of the matrices is a unit of the matrices. -/
def toGL : SU2 →* GL (Fin 2) ℂ :=
  (Units.map (Submonoid.subtype _)).comp toUnits.toMonoidHom

@[simp]
theorem coe_toGL (g : SU2) :
    (toGL g : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) := (rfl)

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
  refine sum_congr rfl fun i hi => ?_
  have hi' : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show (2 * (i : ℤ) - d) = (i : ℤ) - ((d - i : ℕ) : ℤ) by omega,
    zpow_sub₀ (Circle.coe_ne_zero z), zpow_natCast, zpow_natCast, inv_pow,
    div_eq_mul_inv]

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

/-- **The dimension is `d + 1`**, read off the weight string at `z = 1`: there are `d + 1`
weights, each of multiplicity one. -/
theorem character_symPower_one : (symPower d).character 1 = (d : ℂ) + 1 := by
  have h := character_symPower_torusHom d 1
  rw [show torusHom (1 : Circle) = 1 from map_one _] at h
  rw [h]
  simp

end SU2

end TauCeti
