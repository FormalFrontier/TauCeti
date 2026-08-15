/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.SU2.SymmetricPower
import Mathlib.Analysis.Real.Pi.Irrational
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# The weight decomposition of `Symᵈ(ℂ²)` under the maximal torus of `SU(2)`

`TauCeti/RepresentationTheory/SU2/SymmetricPower.lean` computes the *character* of the symmetric
power `Symᵈ(ℂ²)` of the standard representation of `SU(2)` on the maximal torus as the weight
string `z^{-d} + z^{2-d} + ⋯ + z^d`.  A character is a trace, so it records the weights only with
multiplicity; this file builds the decomposition behind it.

The monomial basis of `Symᵈ(ℂ²)`, reindexed by `Fin (d + 1)` through
`TauCeti.symFinTwoEquiv`, is a basis of **weight vectors**: `diag(z, z⁻¹)` acts on the `i`-th one
by the scalar `z^{2i - d}`.  The `d + 1` weights `2i - d` are pairwise distinct, so each weight
occurs with multiplicity exactly one, and the character above,
`TauCeti.SU2.character_symPower_torusHom_zpow`, is their sum.

Two consequences make this the form the highest-weight classification uses.

* **A torus-stable subspace is spanned by weight vectors.**  Nothing forces this for a single
  operator with repeated eigenvalues; here the eigenvalues are distinct, which is exactly the
  hypothesis of the general coordinate argument
  `TauCeti/LinearAlgebra/Eigenspace/DiagonalBasis.lean`.  Feeding it a torus element whose
  integer powers are pairwise distinct — `exp(i)`, by the irrationality of `π` — separates the
  `d + 1` weights at once.  That element is a device of the proof and stays private to this file.
* **The weight spaces are lines.**  A nonzero vector on which the whole torus acts through a
  single character `z ↦ z^m` is a multiple of one basis vector, and `m` is one of the `d + 1`
  weights.

## Main definitions

* `TauCeti.SU2.weightBasis`: the weight basis of `Symᵈ(ℂ²)`, indexed by `Fin (d + 1)`.
* `TauCeti.SU2.weight`: the weight `2i - d` of the `i`-th weight vector.

## Main results

* `TauCeti.SU2.symPower_torusHom_weightBasis`: `diag(z, z⁻¹)` acts on the `i`-th weight vector by
  `z^{2i - d}`, and `TauCeti.SU2.weight_injective`: the weights are pairwise distinct.
* `TauCeti.SU2.weightBasis_mem_of_repr_ne_zero` and `TauCeti.SU2.eq_span_weightBasis_mem`: a
  torus-stable subspace contains every weight vector occurring in one of its elements, and is
  spanned by the weight vectors it contains.
* `TauCeti.SU2.exists_weight_eq_of_forall_torusHom_smul`: a nonzero vector on which the torus acts
  through a single character `z ↦ z^m` is a multiple of a single weight vector, and `m` is that
  vector's weight.

## References

This is the "weight/string decomposition" milestone of the `SU(2)` engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`, which asks for the weights
`{d, d-2, …, -d}` of `Symᵈ(ℂ²)` "each with multiplicity one, computed from the diagonal action",
as the input to the highest-weight argument.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 3.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §5.
-/

public section

open Finset Matrix
open scoped TensorProduct

namespace TauCeti

namespace SU2

variable (d : ℕ)

/-! ### The weight basis and the weights -/

/-- **The weight basis of `Symᵈ(ℂ²)`**: the monomial basis of the symmetric power, whose index
`i : Fin (d + 1)` counts the factors equal to the first standard basis vector of `ℂ²`.  Its
elements are eigenvectors of the maximal torus, by
`TauCeti.SU2.symPower_torusHom_weightBasis`. -/
noncomputable def weightBasis : Module.Basis (Fin (d + 1)) ℂ (Sym[ℂ]^d(Fin 2 → ℂ)) :=
  ((Pi.basisFun ℂ (Fin 2)).symmetricPower d).reindex (symFinTwoEquiv d)

/-- The `i`-th weight vector is the monomial basis vector of `Symᵈ(ℂ²)` with `i` factors equal to
the first standard basis vector of `ℂ²` and `d - i` equal to the second. -/
theorem weightBasis_apply (i : Fin (d + 1)) :
    weightBasis d i =
      (Pi.basisFun ℂ (Fin 2)).symmetricPower d ((symFinTwoEquiv d).symm i) :=
  Module.Basis.reindex_apply _ _ _

/-- **The weight** of the `i`-th weight vector: the torus element `diag(z, z⁻¹)` acts on it by
`z^{2i - d}`.  As `i` runs over `Fin (d + 1)` these are the `d + 1` integers
`-d, 2 - d, …, d - 2, d`. -/
def weight (i : Fin (d + 1)) : ℤ := 2 * (i : ℕ) - (d : ℤ)

/-- The weight of the `i`-th weight vector, unfolded. -/
theorem weight_def (i : Fin (d + 1)) : weight d i = 2 * (i : ℕ) - (d : ℤ) := (rfl)

/-- The lowest weight of `Symᵈ(ℂ²)` is `-d`, on the monomial with no factor of the first basis
vector. -/
@[simp]
theorem weight_zero : weight d 0 = -(d : ℤ) := by simp [weight_def]

/-- The highest weight of `Symᵈ(ℂ²)` is `d`, on the `d`-th power of the first basis vector. -/
@[simp]
theorem weight_last : weight d (Fin.last d) = (d : ℤ) := by
  rw [weight_def, Fin.val_last]
  ring

/-- **The `d + 1` weights `2i - d` are pairwise distinct.**  Together with
`TauCeti.SU2.symPower_torusHom_weightBasis` this is what makes each weight of `Symᵈ(ℂ²)` occur
with multiplicity one, in the form `TauCeti.SU2.exists_weight_eq_of_forall_torusHom_smul`. -/
theorem weight_injective : Function.Injective (weight d) := by
  intro i j hij
  rw [weight_def, weight_def] at hij
  exact Fin.ext (by omega)

/-! ### The torus acts diagonally in the weight basis -/

/-- **The maximal torus is diagonal in the weight basis**: `diag(z, z⁻¹)` multiplies the `i`-th
weight vector by `z^{2i - d}`.  This is the weight decomposition of `Symᵈ(ℂ²)`, of which the
character `TauCeti.SU2.character_symPower_torusHom` is the trace. -/
theorem symPower_torusHom_weightBasis (z : Circle) (i : Fin (d + 1)) :
    symPower d (torusHom z) (weightBasis d i) = (z : ℂ) ^ weight d i • weightBasis d i := by
  have hi : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
  rw [weightBasis_apply, symPower_apply, toGL_torusHom,
    Representation.symmetricPower_apply,
    SymmetricPower.map_basis_symmetricPower_of_apply_basis (Pi.basisFun ℂ (Fin 2)) _
      (fun j => ((![Circle.toUnits z, (Circle.toUnits z)⁻¹] j : ℂˣ) : ℂ))
      (stdRep_diagGL_apply_basisFun _)]
  congr 1
  -- the eigenvalue is `z` on the `i` factors of index `0` and `z⁻¹` on the `d - i` of index `1`
  rw [weight_def, ← coe_pow_mul_coe_inv_pow z hi]
  simp [coe_symFinTwoEquiv_symm_apply]

/-- The coordinates of a vector in the weight basis are scaled by the weights: the torus is
diagonal, so it multiplies the `i`-th coordinate by `z^{2i - d}`. -/
theorem weightBasis_repr_symPower_torusHom (z : Circle) (w : Sym[ℂ]^d(Fin 2 → ℂ))
    (i : Fin (d + 1)) :
    (weightBasis d).repr (symPower d (torusHom z) w) i
      = (z : ℂ) ^ weight d i * (weightBasis d).repr w i :=
  (weightBasis d).repr_apply_of_apply_basis (symPower_torusHom_weightBasis d z) w i

/-! ### A torus element with pairwise distinct powers -/

/-- **A generic element of the maximal torus**: `exp(i)`, an element of infinite order.  Its
integer powers are pairwise distinct (`coe_genericTorus_zpow_injective`) because `π` is
irrational, so it already separates the `d + 1` weights of `Symᵈ(ℂ²)` for every `d` at once.

This is the separating element the proofs below run on, not part of the interface: the results
they prove are stated for the whole torus. -/
private noncomputable def genericTorus : Circle := Circle.exp 1

/-- **The powers of `genericTorus` are pairwise distinct.**  An equality
`exp(i)^m = exp(i)^n` says `m - n` is an integer multiple of `2π`, which forces `m = n` since `π`
is irrational. -/
private theorem coe_genericTorus_zpow_injective :
    Function.Injective fun m : ℤ => (genericTorus : ℂ) ^ m := by
  intro m n hmn
  have h : (genericTorus ^ m : Circle) = genericTorus ^ n :=
    Subtype.ext (by simpa only [Circle.coe_zpow] using hmn)
  rw [genericTorus, ← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, mul_one, mul_one] at h
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 h
  rcases eq_or_ne k 0 with rfl | hk0
  · have hmn' : (m : ℝ) = (n : ℝ) := by simpa using hk
    exact_mod_cast hmn'
  · refine absurd ?_ ((irrational_pi.intCast_mul (m := 2 * k) (by omega)).ne_int (m - n))
    push_cast
    linear_combination -hk

/-- The generic torus element separates the weights of `Symᵈ(ℂ²)`: it acts on the `d + 1` weight
vectors by `d + 1` pairwise distinct scalars. -/
private theorem coe_genericTorus_zpow_weight_injective :
    Function.Injective fun i : Fin (d + 1) => (genericTorus : ℂ) ^ weight d i :=
  fun _ _ h => weight_injective d (coe_genericTorus_zpow_injective h)

/-! ### Torus-stable subspaces are spanned by weight vectors -/

variable {d}

/-- **A torus-stable subspace contains every weight vector that occurs in one of its elements.**
The torus is diagonal in the weight basis and the weights `weight d i` are pairwise distinct, so
a single torus element already separates the coordinates of a vector. -/
theorem weightBasis_mem_of_repr_ne_zero {W : Submodule ℂ (Sym[ℂ]^d(Fin 2 → ℂ))}
    (hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ W → symPower d (torusHom z) v ∈ W)
    {w : Sym[ℂ]^d(Fin 2 → ℂ)} (hw : w ∈ W) {i : Fin (d + 1)}
    (hi : (weightBasis d).repr w i ≠ 0) : weightBasis d i ∈ W :=
  (weightBasis d).self_mem_of_repr_ne_zero (symPower_torusHom_weightBasis d genericTorus)
    (coe_genericTorus_zpow_weight_injective d) (hW genericTorus) hw hi

/-- **A torus-stable subspace of `Symᵈ(ℂ²)` is spanned by the weight vectors it contains.** -/
theorem eq_span_weightBasis_mem {W : Submodule ℂ (Sym[ℂ]^d(Fin 2 → ℂ))}
    (hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ W → symPower d (torusHom z) v ∈ W) :
    W = Submodule.span ℂ {v | ∃ i : Fin (d + 1), weightBasis d i = v ∧ v ∈ W} :=
  (weightBasis d).eq_span_self_mem (symPower_torusHom_weightBasis d genericTorus)
    (coe_genericTorus_zpow_weight_injective d) (hW genericTorus)

/-! ### The weight spaces are lines -/

/-- **A vector transforming under a single character of the torus is a weight vector.**  A nonzero
`w` on which the whole maximal torus acts through `z ↦ z^m` is a multiple of a single weight
vector, and `m` is that vector's weight, one of the `d + 1` integers `2i - d`. -/
theorem exists_weight_eq_of_forall_torusHom_smul {w : Sym[ℂ]^d(Fin 2 → ℂ)} (hw : w ≠ 0) {m : ℤ}
    (hsmul : ∀ z : Circle, symPower d (torusHom z) w = ((z : ℂ) ^ m) • w) :
    ∃ i : Fin (d + 1), weight d i = m ∧ w ∈ Submodule.span ℂ {weightBasis d i} := by
  obtain ⟨i, hi, hspan⟩ := (weightBasis d).exists_eq_and_mem_span_singleton
    (symPower_torusHom_weightBasis d genericTorus) (coe_genericTorus_zpow_weight_injective d) hw
    (hsmul genericTorus)
  exact ⟨i, coe_genericTorus_zpow_injective hi, hspan⟩

end SU2

end TauCeti
