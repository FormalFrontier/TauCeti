/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.SU2.SymmetricPower
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# The weight decomposition of `Symᵈ(ℂ²)` under the maximal torus of `SU(2)`

`TauCeti/RepresentationTheory/SU2/SymmetricPower.lean` computes the *character* of the symmetric
power `Symᵈ(ℂ²)` of the standard representation of `SU(2)` on the maximal torus as the weight
string `z^{-d} + z^{2-d} + ⋯ + z^d`.  A character is a trace, so it records the weights only with
multiplicity; this file builds the decomposition behind it.

The monomial basis of `Symᵈ(ℂ²)`, reindexed by `Fin (d + 1)` through
`TauCeti.symFinTwoEquiv`, is a basis of **weight vectors**: `diag(z, z⁻¹)` acts on the `i`-th one
by the scalar `z^{2i - d}`.  The `d + 1` weights `2i - d` are pairwise distinct, so each weight
occurs with multiplicity exactly one, and the character above is their sum.

Two consequences make this the form the highest-weight classification uses.

* **A torus-stable subspace is spanned by weight vectors.**  Nothing forces this for a single
  operator with repeated eigenvalues; here the eigenvalues are distinct, and the proof is the
  usual one: subtracting an eigenvalue multiple of a vector from its image under a fixed
  generic torus element kills one coordinate and keeps the others, so an induction on the number
  of nonzero coordinates strips a vector down to a single weight vector.  The generic element is
  `TauCeti.SU2.genericTorus = exp(i)`, whose powers are pairwise distinct because `π` is
  irrational.
* **The weight spaces are lines.**  A nonzero vector on which the whole torus acts through a
  single character `z ↦ z^m` is a multiple of one basis vector, and `m` is one of the `d + 1`
  weights.

## Main definitions

* `TauCeti.SU2.weightBasis`: the weight basis of `Symᵈ(ℂ²)`, indexed by `Fin (d + 1)`.
* `TauCeti.SU2.weight`: the weight `2i - d` of the `i`-th weight vector.
* `TauCeti.SU2.genericTorus`: a torus element whose integer powers are pairwise distinct.

## Main results

* `TauCeti.SU2.symPower_torusHom_weightBasis`: `diag(z, z⁻¹)` acts on the `i`-th weight vector by
  `z^{2i - d}`, and `TauCeti.SU2.weight_injective`: the weights are pairwise distinct.
* `TauCeti.SU2.character_symPower_torusHom_eq_sum_weight`: the character on the torus is the sum
  of the weights, which is the weight string of
  `TauCeti.SU2.character_symPower_torusHom_zpow` reindexed.
* `TauCeti.SU2.weightBasis_mem_of_repr_ne_zero` and `TauCeti.SU2.eq_span_weightBasis`: a
  torus-stable subspace contains every weight vector occurring in one of its elements, and is
  spanned by the weight vectors it contains.
* `TauCeti.SU2.exists_weight_eq_of_forall_torusHom_smul`: a nonzero vector on which the torus acts
  through a single character `z ↦ z^m` spans a weight line, and `m` is one of the weights.

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

/-- **The weights are pairwise distinct**: every weight of `Symᵈ(ℂ²)` occurs with multiplicity
one. -/
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
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  have hi : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
  rw [weightBasis_apply, symPower_apply, toGL_torusHom,
    Representation.symmetricPower_apply,
    SymmetricPower.map_symmetricPower_of_apply_basis (Pi.basisFun ℂ (Fin 2)) _
      (fun j => ((![Circle.toUnits z, (Circle.toUnits z)⁻¹] j : ℂˣ) : ℂ))
      (stdRep_diagGL_apply_basisFun _)]
  congr 1
  rw [coe_symFinTwoEquiv_symm_apply, Multiset.map_add, Multiset.map_replicate,
    Multiset.map_replicate, Multiset.prod_add, Multiset.prod_replicate, Multiset.prod_replicate]
  -- the eigenvalue is `z` on the `i` factors of index `0` and `z⁻¹` on the `d - i` of index `1`
  have h0 : ((![Circle.toUnits z, (Circle.toUnits z)⁻¹] 0 : ℂˣ) : ℂ) = (z : ℂ) := by simp
  have h1 : ((![Circle.toUnits z, (Circle.toUnits z)⁻¹] 1 : ℂˣ) : ℂ) = (z : ℂ)⁻¹ := by simp
  have hexp : weight d i = (i : ℕ) - ((d - (i : ℕ) : ℕ) : ℤ) := by
    rw [weight_def]
    omega
  rw [h0, h1, hexp, zpow_sub₀ hz, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]

/-- **The character is the sum of the weights.**  This is the weight string
`TauCeti.SU2.character_symPower_torusHom_zpow` written over the index set of the weight basis. -/
theorem character_symPower_torusHom_eq_sum_weight (z : Circle) :
    (symPower d).character (torusHom z) = ∑ i : Fin (d + 1), (z : ℂ) ^ weight d i := by
  rw [character_symPower_torusHom_zpow]
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (z : ℂ) ^ (2 * (j : ℤ) - (d : ℤ))) (d + 1)).symm

/-- The coordinates of a vector in the weight basis are scaled by the weights: the torus is
diagonal, so it multiplies the `i`-th coordinate by `z^{2i - d}`. -/
theorem repr_symPower_torusHom (z : Circle) (w : Sym[ℂ]^d(Fin 2 → ℂ)) (i : Fin (d + 1)) :
    (weightBasis d).repr (symPower d (torusHom z) w) i
      = (z : ℂ) ^ weight d i * (weightBasis d).repr w i := by
  have key : symPower d (torusHom z) w
      = ∑ k, ((z : ℂ) ^ weight d k * (weightBasis d).repr w k) • weightBasis d k := by
    conv_lhs => rw [← (weightBasis d).sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, symPower_torusHom_weightBasis, smul_smul, mul_comm]
  rw [key]
  exact congrFun ((weightBasis d).repr_sum_self _) i

/-! ### A torus element with pairwise distinct powers -/

/-- **A generic element of the maximal torus**: `exp(i)`, an element of infinite order.  Its
integer powers are pairwise distinct (`TauCeti.SU2.coe_genericTorus_zpow_injective`) because `π`
is irrational, so it already separates the `d + 1` weights of `Symᵈ(ℂ²)` for every `d` at once. -/
noncomputable def genericTorus : Circle := Circle.exp 1

/-- **The powers of `TauCeti.SU2.genericTorus` are pairwise distinct.**  An equality
`exp(i)^m = exp(i)^n` says `m - n` is an integer multiple of `2π`, which forces `m = n` since `π`
is irrational. -/
theorem coe_genericTorus_zpow_injective :
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
theorem coe_genericTorus_zpow_weight_injective :
    Function.Injective fun i : Fin (d + 1) => (genericTorus : ℂ) ^ weight d i :=
  fun _ _ h => weight_injective d (coe_genericTorus_zpow_injective h)

/-! ### Torus-stable subspaces are spanned by weight vectors -/

variable {d}

private theorem weightBasis_mem_aux {W : Submodule ℂ (Sym[ℂ]^d(Fin 2 → ℂ))}
    (hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ W → symPower d (torusHom z) v ∈ W) :
    ∀ (n : ℕ) (w : Sym[ℂ]^d(Fin 2 → ℂ)), w ∈ W →
      ((weightBasis d).repr w).support.card ≤ n →
        ∀ i : Fin (d + 1), (weightBasis d).repr w i ≠ 0 → weightBasis d i ∈ W := by
  classical
  intro n
  induction n with
  | zero =>
    intro w _ hcard i hi
    have hsupp : ((weightBasis d).repr w).support = ∅ :=
      Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    exact absurd (Finsupp.notMem_support_iff.1 (by rw [hsupp]; exact Finset.notMem_empty i)) hi
  | succ n ih =>
    intro w hw hcard i hi
    by_cases hsub : ((weightBasis d).repr w).support ⊆ {i}
    · -- the only nonzero coordinate is the `i`-th, so `w` is already a multiple of `b i`
      have hsum : ∑ k, (weightBasis d).repr w k • weightBasis d k
          = (weightBasis d).repr w i • weightBasis d i := by
        refine Finset.sum_eq_single i (fun k _ hk => ?_) fun h => absurd (Finset.mem_univ i) h
        rw [Finsupp.notMem_support_iff.1 fun hks => hk (Finset.mem_singleton.1 (hsub hks)),
          zero_smul]
      obtain ⟨c, hc0, hcw⟩ : ∃ c : ℂ, c ≠ 0 ∧ w = c • weightBasis d i :=
        ⟨(weightBasis d).repr w i, hi, by rw [← hsum, (weightBasis d).sum_repr]⟩
      have hbi : weightBasis d i = c⁻¹ • w := by
        rw [hcw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hbi]
      exact W.smul_mem _ hw
    · -- otherwise some other coordinate `j` is nonzero, and can be cleared
      obtain ⟨j, hjs, hji⟩ := Finset.not_subset.1 hsub
      have hjne : j ≠ i := fun h => hji (Finset.mem_singleton.2 h)
      set w' := symPower d (torusHom genericTorus) w
        - ((genericTorus : ℂ) ^ weight d j) • w with hw'def
      have hw'W : w' ∈ W := W.sub_mem (hW _ _ hw) (W.smul_mem _ hw)
      have hrepr : ∀ k : Fin (d + 1), (weightBasis d).repr w' k
          = ((genericTorus : ℂ) ^ weight d k - (genericTorus : ℂ) ^ weight d j)
              * (weightBasis d).repr w k := by
        intro k
        rw [hw'def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
          repr_symPower_torusHom, smul_eq_mul, sub_mul]
      have hsupp' : ((weightBasis d).repr w').support ⊆
          ((weightBasis d).repr w).support.erase j := by
        intro k hk
        have hk0 : (weightBasis d).repr w' k ≠ 0 := Finsupp.mem_support_iff.1 hk
        rw [hrepr k] at hk0
        refine Finset.mem_erase.2 ⟨?_, Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hk0)⟩
        rintro rfl
        exact hk0 (by rw [sub_self, zero_mul])
      have hcard' : ((weightBasis d).repr w').support.card ≤ n := by
        have hle := Finset.card_le_card hsupp'
        rw [Finset.card_erase_of_mem hjs] at hle
        have hpos : 0 < ((weightBasis d).repr w).support.card := Finset.card_pos.2 ⟨j, hjs⟩
        omega
      refine ih w' hw'W hcard' i ?_
      rw [hrepr i]
      refine mul_ne_zero (sub_ne_zero.2 fun h => ?_) hi
      exact hjne (coe_genericTorus_zpow_weight_injective d h).symm

/-- **A torus-stable subspace contains every weight vector that occurs in one of its elements.**
The weights of `Symᵈ(ℂ²)` are pairwise distinct, so the coordinates of a vector in the weight
basis can be separated by repeatedly clearing one of them with the generic torus element. -/
theorem weightBasis_mem_of_repr_ne_zero {W : Submodule ℂ (Sym[ℂ]^d(Fin 2 → ℂ))}
    (hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ W → symPower d (torusHom z) v ∈ W)
    {w : Sym[ℂ]^d(Fin 2 → ℂ)} (hw : w ∈ W) {i : Fin (d + 1)}
    (hi : (weightBasis d).repr w i ≠ 0) : weightBasis d i ∈ W :=
  weightBasis_mem_aux hW _ w hw le_rfl i hi

/-- **A torus-stable subspace of `Symᵈ(ℂ²)` is spanned by the weight vectors it contains.** -/
theorem eq_span_weightBasis {W : Submodule ℂ (Sym[ℂ]^d(Fin 2 → ℂ))}
    (hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ W → symPower d (torusHom z) v ∈ W) :
    W = Submodule.span ℂ {v | ∃ i : Fin (d + 1), weightBasis d i = v ∧ v ∈ W} := by
  classical
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 ?_)
  · rw [← (weightBasis d).sum_repr w]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (weightBasis d).repr w k = 0
    · rw [hk, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨k, rfl, weightBasis_mem_of_repr_ne_zero hW hw hk⟩)
  · rintro v ⟨-, -, hv⟩
    exact hv

/-! ### The weight spaces are lines -/

/-- **The weight spaces of `Symᵈ(ℂ²)` are one-dimensional, and the weights are the `2i - d`.**  A
nonzero vector on which the whole maximal torus acts through the single character `z ↦ z^m` is a
multiple of a single weight vector, whose weight is `m`. -/
theorem exists_weight_eq_of_forall_torusHom_smul {w : Sym[ℂ]^d(Fin 2 → ℂ)} (hw : w ≠ 0) {m : ℤ}
    (hsmul : ∀ z : Circle, symPower d (torusHom z) w = ((z : ℂ) ^ m) • w) :
    ∃ i : Fin (d + 1), weight d i = m ∧ w ∈ Submodule.span ℂ {weightBasis d i} := by
  classical
  have hcoord : ∀ k : Fin (d + 1),
      (genericTorus : ℂ) ^ weight d k * (weightBasis d).repr w k
        = (genericTorus : ℂ) ^ m * (weightBasis d).repr w k := by
    intro k
    rw [← repr_symPower_torusHom d genericTorus w k, hsmul genericTorus, map_smul,
      Finsupp.smul_apply, smul_eq_mul]
  have hrne : (weightBasis d).repr w ≠ 0 := fun h =>
    hw ((weightBasis d).repr.map_eq_zero_iff.1 h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hrne
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi
  have hwi : weight d i = m := coe_genericTorus_zpow_injective (mul_right_cancel₀ hi (hcoord i))
  refine ⟨i, hwi, ?_⟩
  have hzero : ∀ k : Fin (d + 1), k ≠ i → (weightBasis d).repr w k = 0 := by
    intro k hk
    by_contra hk0
    refine hk (coe_genericTorus_zpow_weight_injective d ?_)
    change (genericTorus : ℂ) ^ weight d k = (genericTorus : ℂ) ^ weight d i
    rw [hwi]
    exact mul_right_cancel₀ hk0 (hcoord k)
  have hsum : ∑ k, (weightBasis d).repr w k • weightBasis d k
      = (weightBasis d).repr w i • weightBasis d i := by
    refine Finset.sum_eq_single i (fun k _ hk => ?_) fun h => absurd (Finset.mem_univ i) h
    rw [hzero k hk, zero_smul]
  have hwe : w = (weightBasis d).repr w i • weightBasis d i := by
    rw [← hsum, (weightBasis d).sum_repr]
  rw [hwe]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end SU2

end TauCeti
