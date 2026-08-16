/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import Mathlib.GroupTheory.Torsion

/-!
# Primary components of finite bilinear and quadratic modules

The primary components of a finite abelian group are already defined by Mathlib as
`AddCommGroup.primaryComponent`. This file proves the form-theoretic fact needed to decompose
finite bilinear and quadratic modules: components belonging to distinct primes are orthogonal.

For a bilinear module, orthogonality follows because the value of the pairing on a `p`-primary and
a `q`-primary element is annihilated by powers of both `p` and `q`.  Those powers are coprime when
the primes are distinct.  The quadratic statements then follow from the polar identity.  Finite-sum
versions record that both raw forms split as sums of their restrictions whenever the summands lie
in pairwise distinct primary components.

## Main results

* `TauCeti.FiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent`: distinct primary
  components are orthogonal elementwise.
* `TauCeti.FiniteBilinearModule.primaryComponent_le_orthogonalComplement_primaryComponent`: the
  corresponding inclusion of additive subgroups.
* `TauCeti.FiniteBilinearModule.pairing_sum_eq_sum_pairing_of_mem_primaryComponent`: a bilinear
  pairing of primary decompositions is the sum of the component pairings.
* `TauCeti.FiniteQuadraticModule.quadratic_sum_of_mem_primaryComponent`: a quadratic value on a
  sum of primary components is the sum of the component values.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This is the primary-decomposition part of Layer 3 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

universe u

private theorem eq_zero_of_coprime_nsmul_eq_zero {M : Type*} [AddMonoid M] {m n : ℕ} {x : M}
    (hmn : m.Coprime n) (hm : m • x = 0) (hn : n • x = 0) : x = 0 := by
  have horder_m : addOrderOf x ∣ m := by
    rwa [addOrderOf_dvd_iff_nsmul_eq_zero]
  have horder_n : addOrderOf x ∣ n := by
    rwa [addOrderOf_dvd_iff_nsmul_eq_zero]
  rw [← AddMonoid.addOrderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes hmn horder_m horder_n

namespace FiniteBilinearModule

variable (A : FiniteBilinearModule)

/-! ## Orthogonality -/

/-- Elements in the primary components for two distinct primes pair to zero. -/
theorem pairing_eq_zero_of_mem_primaryComponent {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {x y : A} (hx : x ∈ AddCommGroup.primaryComponent A p)
    (hy : y ∈ AddCommGroup.primaryComponent A q) : A.pairing x y = 0 := by
  rw [AddCommGroup.mem_primaryComponent] at hx hy
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  apply eq_zero_of_coprime_nsmul_eq_zero (Nat.coprime_pow_primes m n hp hq hpq)
  · rw [A.pairing_comm x y, ← map_nsmul (A.pairing y) (p ^ m) x, hm, map_zero]
  · rw [← map_nsmul (A.pairing x) (q ^ n) y, hn, map_zero]

/-- The `p`-primary component is contained in the orthogonal complement of the `q`-primary
component when `p` and `q` are distinct primes. -/
theorem primaryComponent_le_orthogonalComplement_primaryComponent {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    AddCommGroup.primaryComponent A p ≤
      A.orthogonalComplement (AddCommGroup.primaryComponent A q) := by
  intro x hx
  rw [A.mem_orthogonalComplement_iff]
  intro y hy
  exact A.pairing_eq_zero_of_mem_primaryComponent hp hq hpq hx hy

/-! ## Finite sums -/

/-- Pairing sums of elements from pairwise distinct primary components keeps only the diagonal
component pairings.  This is the raw bilinear identity used by the canonical primary-decomposition
isometry. -/
theorem pairing_sum_eq_sum_pairing_of_mem_primaryComponent {ι : Type*}
    (s : Finset ι) (p : ι → ℕ) (x y : ι → A)
    (hprime : ∀ i ∈ s, (p i).Prime)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i ≠ p j)
    (hx : ∀ i ∈ s, x i ∈ AddCommGroup.primaryComponent A (p i))
    (hy : ∀ i ∈ s, y i ∈ AddCommGroup.primaryComponent A (p i)) :
    A.pairing (∑ i ∈ s, x i) (∑ i ∈ s, y i) =
      ∑ i ∈ s, A.pairing (x i) (y i) := by
  classical
  rw [← A.toBilin_apply, A.toBilin.map_sum₂ s x]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum (A.toBilin (x i)) y s]
  have hoff : ∀ j ∈ s, j ≠ i → A.toBilin (x i) (y j) = 0 := by
    intro j hj hji
    rw [A.toBilin_apply]
    exact A.pairing_eq_zero_of_mem_primaryComponent (hprime i hi) (hprime j hj)
      (hdistinct i hi j hj hji.symm) (hx i hi) (hy j hj)
  rw [Finset.sum_eq_single i hoff (fun hnot ↦ (hnot hi).elim), A.toBilin_apply]

end FiniteBilinearModule

namespace FiniteQuadraticModule

variable (A : FiniteQuadraticModule)

/-- A quadratic map is additive on elements belonging to primary components for distinct primes. -/
theorem quadratic_add_of_mem_primaryComponent {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {x y : A}
    (hx : x ∈ AddCommGroup.primaryComponent A p)
    (hy : y ∈ AddCommGroup.primaryComponent A q) :
    A.quadratic (x + y) = A.quadratic x + A.quadratic y := by
  rw [QuadraticMap.map_add A.quadratic, A.polar_eq_pairing,
    A.toFiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent hp hq hpq hx hy, add_zero]

/-- The quadratic value of a sum of elements from pairwise distinct primary components is the sum
of their quadratic values.  This is the raw quadratic identity used by the canonical
primary-decomposition isometry. -/
theorem quadratic_sum_of_mem_primaryComponent {ι : Type*}
    (s : Finset ι) (p : ι → ℕ) (x : ι → A)
    (hprime : ∀ i ∈ s, (p i).Prime)
    (hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i ≠ p j)
    (hx : ∀ i ∈ s, x i ∈ AddCommGroup.primaryComponent A (p i)) :
    A.quadratic (∑ i ∈ s, x i) = ∑ i ∈ s, A.quadratic (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hiprime : (p i).Prime := hprime i (Finset.mem_insert_self i s)
      have hisum :
          A.toFiniteBilinearModule.pairing (x i) (∑ j ∈ s, x j) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        exact A.toFiniteBilinearModule.pairing_eq_zero_of_mem_primaryComponent hiprime
          (hprime j (Finset.mem_insert_of_mem hj))
          (hdistinct i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
            (Ne.symm (ne_of_mem_of_not_mem hj hi)))
          (hx i (Finset.mem_insert_self i s)) (hx j (Finset.mem_insert_of_mem hj))
      rw [Finset.sum_insert hi, QuadraticMap.map_add A.quadratic, A.polar_eq_pairing, hisum,
        add_zero, Finset.sum_insert hi]
      exact congrArg (A.quadratic (x i) + ·) <| ih
        (fun j hj ↦ hprime j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hjk ↦ hdistinct j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk)
        (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))

end FiniteQuadraticModule

end TauCeti
