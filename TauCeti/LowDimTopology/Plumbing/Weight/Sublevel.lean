/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import TauCeti.LowDimTopology.Plumbing.NegativeDefinite
public import TauCeti.LowDimTopology.Plumbing.Weight.Basic

/-!
# Sublevel sets of the plumbing-lattice weight function

Némethi builds lattice homology out of the sublevel sets `S_c = {x | χ_k(x) ≤ c}` of the
characteristic weight function of a **negative-definite** plumbing: the lattice complex is
filtered by them, and the invariants read off from that filtration — including the `d`-invariant
analogues — only make sense because each `S_c` is a *finite* set of lattice points and because
`χ_k` attains a minimum. This file proves both facts.

The mechanism is completing the square. Write `A` for the intersection matrix, `d = det A`, and
`u = adjugate A *ᵥ k`, so that `A *ᵥ u = d • k` and hence `A(x, u) = d ⟪k, x⟫`. Expanding the
self-pairing of `2d • x + u` therefore gives

`A(2d • x + u, 2d • x + u) = 4 d² (⟪k, x⟫ + A(x, x)) + A(u, u)`,

whose middle factor is exactly the weight numerator `2 χ_k(x) = -(⟪k, x⟫ + A(x, x))`. So a
sublevel set of `χ_k` is carried, by the injective affine map `x ↦ 2d • x + u`, into a superlevel
set of the intersection-form self-pairing, and those are finite on a negative-definite plumbing by
`IsNegativeDefinite.finite_setOf_le_intersectionForm_self`. Negative-definiteness enters twice: it
makes `d ≠ 0`, so the affine map is injective, and it makes the target set finite.

Finiteness immediately yields a minimizer: the lattice points with `χ_k(x) ≤ χ_k(0)` form a finite
nonempty set, and a minimum over it is a global minimum. That minimum is the numerical input to the
`d`-invariant of the plumbed three-manifold in the spin^c structure recorded by `k`.

## Main results

* `TauCeti.PlumbingGraph.intersectionForm_adjugate_mulVec`: pairing against `adjugate A *ᵥ k`
  computes `det A` times the linear form `⟪k, -⟫`.
* `TauCeti.PlumbingGraph.intersectionForm_self_smul_add_adjugate_mulVec`: the completed square
  relating the self-pairing of `2d • x + u` to the weight numerator.
* `TauCeti.PlumbingGraph.finite_setOf_le_characteristicWeightNumerator`: superlevel sets of the
  weight numerator are finite.
* `TauCeti.PlumbingGraph.finite_setOf_characteristicWeight_le`: sublevel sets of the
  characteristic weight are finite.
* `TauCeti.PlumbingGraph.exists_forall_characteristicWeight_le`: the characteristic weight attains
  a global minimum, and `TauCeti.PlumbingGraph.bddBelow_range_characteristicWeight`: its range is
  bounded below.
* `TauCeti.PlumbingGraph.minCharacteristicWeight`: that minimum as an integer, with
  `TauCeti.PlumbingGraph.minCharacteristicWeight_le` and
  `TauCeti.PlumbingGraph.exists_characteristicWeight_eq_minCharacteristicWeight` saying it is a
  lower bound and that it is attained.
* `TauCeti.PlumbingGraph.two_mul_characteristicWeight_smul_single`: the weight along a single basis
  sphere, as an explicit quadratic.
* `TauCeti.PlumbingGraph.not_bddAbove_range_characteristicWeight`: on a nonempty vertex set the
  weight is unbounded above, so the sublevel sets are proper.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
whose target is "Némethi's lattice (co)homology `ℍ⁻`/`ℍ⁰` as a `ℤ[U]`-module from lattice points
and weight functions … and `d`-invariant analogues": the sublevel sets treated here are the ones
that filtration is taken over. See Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

open scoped Matrix

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- Pairing a lattice point against the covector `adjugate A *ᵥ k` computes `det A` times the
linear form `⟪k, -⟫`.

This is the integral substitute for "`k` is `A` applied to a rational vector": multiplying by the
adjugate clears the denominators, at the cost of the factor `det A`. -/
theorem intersectionForm_adjugate_mulVec (k x : V → ℤ) :
    P.intersectionForm x (P.intersectionMatrix.adjugate *ᵥ k) =
      P.intersectionMatrix.det * ∑ v, k v * x v := by
  rw [← P.sum_intersectionMatrix_mulVec_mul (P.intersectionMatrix.adjugate *ᵥ k) x]
  have hmul : P.intersectionMatrix *ᵥ (P.intersectionMatrix.adjugate *ᵥ k) =
      P.intersectionMatrix.det • k := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hmul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The completed square for the characteristic-weight numerator: with `d = det A` and
`u = adjugate A *ᵥ k`, the self-pairing of `2d • x + u` is `4 d²` times the weight numerator at
`x`, up to the constant `A(u, u)`.

Every dependence on `x` is now inside a single self-pairing, which is what turns a level set of the
weight into a level set of the intersection form. -/
theorem intersectionForm_self_smul_add_adjugate_mulVec (k x : V → ℤ) :
    P.intersectionForm
        ((2 * P.intersectionMatrix.det) • x + P.intersectionMatrix.adjugate *ᵥ k)
        ((2 * P.intersectionMatrix.det) • x + P.intersectionMatrix.adjugate *ᵥ k) =
      4 * P.intersectionMatrix.det ^ 2 * P.characteristicWeightNumerator k x +
        P.intersectionForm (P.intersectionMatrix.adjugate *ᵥ k)
          (P.intersectionMatrix.adjugate *ᵥ k) := by
  rw [P.intersectionForm_self_add]
  have hleft : P.intersectionForm ((2 * P.intersectionMatrix.det) • x)
      ((2 * P.intersectionMatrix.det) • x) =
      (2 * P.intersectionMatrix.det) ^ 2 * P.intersectionForm x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hcross : P.intersectionForm ((2 * P.intersectionMatrix.det) • x)
      (P.intersectionMatrix.adjugate *ᵥ k) =
      2 * P.intersectionMatrix.det *
        P.intersectionForm x (P.intersectionMatrix.adjugate *ᵥ k) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hleft, hcross, P.intersectionForm_adjugate_mulVec k x, P.characteristicWeightNumerator_def]
  ring

/-- On a negative-definite plumbing only finitely many lattice points have characteristic-weight
numerator above a fixed bound.

The affine map `x ↦ 2 (det A) • x + adjugate A *ᵥ k` is injective because negative-definiteness
forces `det A ≠ 0`, and by the completed square it carries the superlevel set into a superlevel
set of the intersection-form self-pairing, which is finite. -/
theorem finite_setOf_le_characteristicWeightNumerator (h : P.IsNegativeDefinite) (k : V → ℤ)
    (c : ℤ) : {x : V → ℤ | c ≤ P.characteristicWeightNumerator k x}.Finite := by
  have hd : P.intersectionMatrix.det ≠ 0 := h.det_intersectionMatrix_ne_zero
  have hd2 : (2 : ℤ) * P.intersectionMatrix.det ≠ 0 := mul_ne_zero two_ne_zero hd
  have hinj : Function.Injective
      fun x : V → ℤ => (2 * P.intersectionMatrix.det) • x + P.intersectionMatrix.adjugate *ᵥ k := by
    intro a b hab
    exact smul_right_injective (V → ℤ) hd2 (add_left_injective _ hab)
  have hfin := h.finite_setOf_le_intersectionForm_self
    (4 * P.intersectionMatrix.det ^ 2 * c +
      P.intersectionForm (P.intersectionMatrix.adjugate *ᵥ k)
        (P.intersectionMatrix.adjugate *ᵥ k))
  refine (Set.Finite.preimage hinj.injOn hfin).subset fun x hx => ?_
  have hxc : c ≤ P.characteristicWeightNumerator k x := hx
  have hsq : (0 : ℤ) ≤ 4 * P.intersectionMatrix.det ^ 2 := by positivity
  have hgoal : 4 * P.intersectionMatrix.det ^ 2 * c +
      P.intersectionForm (P.intersectionMatrix.adjugate *ᵥ k)
        (P.intersectionMatrix.adjugate *ᵥ k) ≤
      P.intersectionForm
        ((2 * P.intersectionMatrix.det) • x + P.intersectionMatrix.adjugate *ᵥ k)
        ((2 * P.intersectionMatrix.det) • x + P.intersectionMatrix.adjugate *ᵥ k) := by
    rw [P.intersectionForm_self_smul_add_adjugate_mulVec k x]
    linarith [mul_le_mul_of_nonneg_left hxc hsq]
  exact hgoal

/-- On a negative-definite plumbing every sublevel set of the characteristic weight function is
finite: only finitely many lattice points satisfy `χ_k(x) ≤ N`.

This is the finiteness that makes Némethi's filtration of the lattice complex by weight sublevel
sets a filtration by *finitely generated* pieces. -/
theorem finite_setOf_characteristicWeight_le (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) (N : ℤ) :
    {x : V → ℤ | P.characteristicWeight k x ≤ N}.Finite := by
  refine (P.finite_setOf_le_characteristicWeightNumerator h k.val (-(2 * N))).subset fun x hx => ?_
  have hxN : P.characteristicWeight k x ≤ N := hx
  have hnum := P.two_mul_characteristicWeight k x
  have hgoal : -(2 * N) ≤ P.characteristicWeightNumerator k.val x := by linarith
  exact hgoal

/-- On a negative-definite plumbing the characteristic weight function attains a global minimum.

The lattice points with `χ_k(x) ≤ χ_k(0)` form a finite nonempty set, and a point minimizing `χ_k`
over it minimizes `χ_k` everywhere. The value at such a point is the numerical input to the
`d`-invariant of the plumbed three-manifold in the spin^c structure recorded by `k`. -/
theorem exists_forall_characteristicWeight_le (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) :
    ∃ x₀ : V → ℤ, ∀ x : V → ℤ, P.characteristicWeight k x₀ ≤ P.characteristicWeight k x := by
  have hfin := P.finite_setOf_characteristicWeight_le h k (P.characteristicWeight k 0)
  have hmem : (0 : V → ℤ) ∈ {x : V → ℤ | P.characteristicWeight k x ≤
      P.characteristicWeight k 0} :=
    le_refl (P.characteristicWeight k 0)
  obtain ⟨x₀, _, hx₀⟩ :=
    Set.exists_min_image _ (P.characteristicWeight k) hfin ⟨0, hmem⟩
  refine ⟨x₀, fun x => ?_⟩
  by_cases hx : P.characteristicWeight k x ≤ P.characteristicWeight k 0
  · exact hx₀ x hx
  · exact (hx₀ 0 hmem).trans (le_of_not_ge hx)

/-- On a negative-definite plumbing the characteristic weight function is bounded below. -/
theorem bddBelow_range_characteristicWeight (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) : BddBelow (Set.range (P.characteristicWeight k)) := by
  obtain ⟨x₀, hx₀⟩ := P.exists_forall_characteristicWeight_le h k
  exact ⟨P.characteristicWeight k x₀, by rintro _ ⟨x, rfl⟩; exact hx₀ x⟩

/-- The minimum value of the characteristic weight function, as an integer: the infimum of its
range.

On a negative-definite plumbing this is a genuine minimum — `minCharacteristicWeight_le` bounds
the weight below by it and `exists_characteristicWeight_eq_minCharacteristicWeight` attains it —
and it is the numerical input to the `d`-invariant of the plumbed three-manifold in the spin^c
structure recorded by `k`. Without negative-definiteness the range need not be bounded below and
the value is the junk value `0` of `Int.csInf_of_not_bddBelow`. -/
noncomputable def minCharacteristicWeight (k : P.characteristicVectors) : ℤ :=
  sInf (Set.range (P.characteristicWeight k))

/-- On a negative-definite plumbing the minimum characteristic weight is a lower bound for the
characteristic weight. -/
theorem minCharacteristicWeight_le (h : P.IsNegativeDefinite) (k : P.characteristicVectors)
    (x : V → ℤ) : P.minCharacteristicWeight k ≤ P.characteristicWeight k x :=
  csInf_le (P.bddBelow_range_characteristicWeight h k) ⟨x, rfl⟩

/-- On a negative-definite plumbing the minimum characteristic weight is attained: some lattice
point has that exact weight. -/
theorem exists_characteristicWeight_eq_minCharacteristicWeight (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) :
    ∃ x : V → ℤ, P.characteristicWeight k x = P.minCharacteristicWeight k :=
  Int.csInf_mem (Set.range_nonempty _) (P.bddBelow_range_characteristicWeight h k)

/-- The characteristic weight along a single basis sphere, as an explicit quadratic in the
multiplier: `2 χ_k(m • e_v) = -(m ⟪k, e_v⟫ + m² (e_v · e_v))`. -/
theorem two_mul_characteristicWeight_smul_single (k : P.characteristicVectors) (v : V) (m : ℤ) :
    2 * P.characteristicWeight k (m • Pi.single v 1) =
      -(m * k.val v + m ^ 2 * P.weight v) := by
  rw [P.two_mul_characteristicWeight k (m • Pi.single v 1), P.characteristicWeightNumerator_def]
  have hlin : ∑ u, k.val u * (m • (Pi.single v 1 : V → ℤ)) u = m * k.val v := by
    rw [Finset.sum_eq_single v (fun u _ hu => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne hu, smul_zero, mul_zero])
      (fun hv => absurd (Finset.mem_univ v) hv)]
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    ring
  have hquad : P.intersectionForm (m • Pi.single v 1) (m • Pi.single v 1) =
      m ^ 2 * P.weight v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [P.intersectionForm_single v v, P.intersectionMatrix_diag]
    ring
  rw [hlin, hquad]

/-- On a negative-definite plumbing with at least one vertex the characteristic weight function is
unbounded above: pushing a lattice point far along a single basis sphere sends `χ_k` to `+∞`,
because that sphere's framing is negative.

Together with `finite_setOf_characteristicWeight_le` this says that the weight sublevel sets form a
genuine exhaustion of the lattice by finite subsets each of which is *proper*: no single sublevel
set is the whole lattice. -/
theorem not_bddAbove_range_characteristicWeight (h : P.IsNegativeDefinite) [Nonempty V]
    (k : P.characteristicVectors) : ¬ BddAbove (Set.range (P.characteristicWeight k)) := by
  rintro ⟨N, hN⟩
  obtain ⟨v⟩ := ‹Nonempty V›
  set m : ℤ := |k.val v| + |2 * N| + 1 with hm
  have hm1 : 1 ≤ m := by
    have := abs_nonneg (k.val v)
    have := abs_nonneg (2 * N)
    omega
  have hgap : |2 * N| + 1 ≤ m - k.val v := by
    have := le_abs_self (k.val v)
    omega
  have hweight : 1 ≤ -P.weight v := by
    have := IsNegativeDefinite.weight_neg P h v
    omega
  have hval : 2 * P.characteristicWeight k (m • Pi.single v 1) =
      m * (m * -P.weight v - k.val v) := by
    rw [P.two_mul_characteristicWeight_smul_single k v m]
    ring
  have hbig : 2 * N < 2 * P.characteristicWeight k (m • Pi.single v 1) := by
    rw [hval]
    -- the linear factor already exceeds `2 N`, and the multiplier `m` is at least one
    have hstep : |2 * N| + 1 ≤ m * -P.weight v - k.val v := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ m) (by linarith : (0 : ℤ) ≤ -P.weight v - 1)]
    have hstep0 : (0 : ℤ) ≤ m * -P.weight v - k.val v := by
      have := abs_nonneg (2 * N)
      linarith
    have hgrow : m * -P.weight v - k.val v ≤ m * (m * -P.weight v - k.val v) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ m - 1) hstep0]
    linarith [le_abs_self (2 * N)]
  exact absurd (hN ⟨m • Pi.single v 1, rfl⟩) (by omega)

end PlumbingGraph

end TauCeti
