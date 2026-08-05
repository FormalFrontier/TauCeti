/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# Algebra homomorphisms out of a finite product of copies of a field

The algebra `ι → k` of functions on a finite type `ι` with values in a field `k` has exactly `|ι|`
homomorphisms of `k`-algebras to `k`, namely the evaluations. This file proves that, in the form
`TauCeti.exists_eq_evalAlgHom`.

The proof is the usual idempotent argument. The indicator functions `Pi.single i 1` are a complete
family of orthogonal idempotents, so their images under a homomorphism `φ` are orthogonal
idempotents of `k` summing to `1`. A field has no idempotents besides `0` and `1`, and orthogonality
leaves at most one of them equal to `1`, so exactly one does; `φ` is evaluation at that index.

Nothing weaker than a field will do for the base: over `k = k₁ × k₂` the homomorphism
`(f₀, f₁) ↦ ((f₀).1, (f₁).2)` out of `Fin 2 → k` is not an evaluation. What the argument really
uses is that `k` has no idempotents other than `0` and `1`.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} [Field k] {ι : Type v} [Finite ι]

/-- **Every `k`-algebra homomorphism from `ι → k` to `k` is an evaluation**, for `ι` finite and `k`
a field. -/
theorem exists_eq_evalAlgHom (φ : (ι → k) →ₐ[k] k) :
    ∃ i, φ = Pi.evalAlgHom k (fun _ => k) i := by
  classical
  cases nonempty_fintype ι
  set a : ι → k := fun i => φ (Pi.single i 1) with ha
  have hsingle : ∀ (j : ι) (c : k), (Pi.single j c : ι → k) = c • Pi.single j 1 := by
    intro j c
    funext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [Pi.single_eq_of_ne hx]
  -- the indicator functions are a complete family of orthogonal idempotents
  have hortho : ∀ i j, i ≠ j → (Pi.single i 1 : ι → k) * Pi.single j 1 = 0 := by
    intro i j hij
    funext x
    by_cases hx : x = i
    · subst hx; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne hx]
  have hsum : ∑ i, a i = 1 := by
    rw [ha, ← map_sum]
    simpa using congrArg φ (Finset.univ_sum_single (1 : ι → k))
  have hidem : ∀ i, IsIdempotentElem (a i) := by
    intro i
    rw [IsIdempotentElem, ha, ← map_mul]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx; simp
    · simp [Pi.single_eq_of_ne hx]
  -- so each value of `φ` on an indicator is `0` or `1`, and exactly one of them is `1`
  obtain ⟨i, hi⟩ : ∃ i, a i = 1 := by
    by_contra hcon
    simp only [not_exists] at hcon
    have : ∑ i, a i = 0 := Finset.sum_eq_zero fun i _ =>
      (IsIdempotentElem.iff_eq_zero_or_one.mp (hidem i)).resolve_right (hcon i)
    exact one_ne_zero (hsum.symm.trans this)
  have hne : ∀ j, j ≠ i → a j = 0 := by
    intro j hj
    have : a i * a j = 0 := by rw [ha, ← map_mul, hortho i j (Ne.symm hj), map_zero]
    simpa [hi] using this
  -- and then `φ` reads off the value at that index
  refine ⟨i, AlgHom.ext fun f => ?_⟩
  have hval : φ f = ∑ j, f j * a j := by
    conv_lhs => rw [← Finset.univ_sum_single f]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hsingle j (f j), map_smul, smul_eq_mul]
  rw [hval, Finset.sum_eq_single i (fun j _ hj => by rw [hne j hj, mul_zero]) (by simp), hi,
    mul_one]
  rfl

end TauCeti
