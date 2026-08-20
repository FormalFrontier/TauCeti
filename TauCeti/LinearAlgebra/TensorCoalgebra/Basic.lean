/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Tensor words and deconcatenation

For an `R`-module `M`, reduced tensor words are the direct sum of its positive tensor powers.  This
file constructs that module and its reduced deconcatenation map, which cuts a positive word at
every nontrivial position.

The construction uses Mathlib's `TensorPower` and direct-sum/tensor-product equivalences.  It is
the coalgebra-side input for the suspended bar construction in the `DGAInfinity` roadmap.

## Main definitions

* `TauCeti.ReducedTensorWords`: the direct sum of positive tensor powers.
* `TensorPower.splitAt`: split a tensor power at a specified position.
* `TauCeti.ReducedTensorWords.deconcatenation`: sum over every nontrivial cut of a tensor word.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN uP

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorPower

/-- Split a tensor power after its first `k` factors. -/
noncomputable def splitAt (n k : ℕ) (hk : k ≤ n) :
    TensorPower R n M →ₗ[R] TensorPower R k M ⊗[R] TensorPower R (n - k) M :=
  (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap ∘ₗ
    (TensorPower.cast R M (Nat.add_sub_of_le hk).symm).toLinearMap

@[simp]
theorem mulEquiv_splitAt (n k : ℕ) (hk : k ≤ n) (x : TensorPower R n M) :
    TensorPower.mulEquiv (splitAt R M n k hk x) =
      TensorPower.cast R M (Nat.add_sub_of_le hk).symm x := by
  simp [splitAt]

/-- Splitting a pure tensor separates its first `k` entries from the remaining entries. -/
@[simp]
theorem splitAt_tprod (n k : ℕ) (hk : k ≤ n) (x : Fin n → M) :
    splitAt R M n k hk (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i : Fin k ↦ x (Fin.castLE hk i)) ⊗ₜ[R]
        PiTensorProduct.tprod R (fun j : Fin (n - k) ↦ x ⟨k + j.1, by omega⟩) := by
  apply TensorPower.mulEquiv.injective
  rw [mulEquiv_splitAt, TensorPower.cast_tprod, ← TensorPower.gMul_def,
    TensorPower.tprod_mul_tprod]
  congr 1
  funext i
  simp only [Function.comp_apply]
  by_cases hi : i.1 < k
  · let j : Fin k := ⟨i.1, hi⟩
    have hij : Fin.castAdd (n - k) j = i := by ext; rfl
    rw [← hij, Fin.append_left]
    congr 1
  · let j : Fin (n - k) := ⟨i.1 - k, by omega⟩
    have hij : Fin.natAdd k j = i := by ext; simp [j]; omega
    rw [← hij, Fin.append_right]
    congr 1

end TensorPower

namespace TauCeti

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The module of nonempty tensor words. -/
abbrev ReducedTensorWords : Type _ := ⨁ n : {n : ℕ // 0 < n}, TensorPower R n.1 M

namespace ReducedTensorWords

/-- Include a positive tensor power into reduced tensor words. -/
noncomputable def of (n : {n : ℕ // 0 < n}) :
    TensorPower R n.1 M →ₗ[R] ReducedTensorWords R M :=
  DirectSum.lof R {n : ℕ // 0 < n} (fun n ↦ TensorPower R n.1 M) n

/-- Project reduced tensor words to a fixed positive tensor length. -/
noncomputable def component (n : {n : ℕ // 0 < n}) :
    ReducedTensorWords R M →ₗ[R] TensorPower R n.1 M :=
  DirectSum.component R {n : ℕ // 0 < n} (fun n ↦ TensorPower R n.1 M) n

@[simp]
theorem component_of (n : {n : ℕ // 0 < n}) (x : TensorPower R n.1 M) :
    component R M n (of R M n x) = x := by
  simp [component, of]

/-- Projecting an included tensor power vanishes when the two lengths differ. -/
@[simp]
theorem component_of_of_ne {m n : {n : ℕ // 0 < n}} (h : m ≠ n) (x : TensorPower R m.1 M) :
    component R M n (of R M m x) = 0 := by
  simp [component, of, DirectSum.component.of, h]

/-- Projecting an included tensor power returns the tensor power itself at the matching length
and zero at every other length. -/
theorem component_of' (m n : {n : ℕ // 0 < n}) (x : TensorPower R m.1 M) :
    component R M n (of R M m x) = if h : m = n then h ▸ x else 0 := by
  simp [component, of, DirectSum.component.of]

/-- Deconcatenation on words of one fixed length, summed over all nontrivial cuts. -/
noncomputable def deconcatenationComponent (n : {n : ℕ // 0 < n}) :
    TensorPower R n.1 M →ₗ[R] ReducedTensorWords R M ⊗[R] ReducedTensorWords R M :=
  ∑ i : Fin (n.1 - 1),
    TensorProduct.map
        (of R M ⟨i.1 + 1, by omega⟩)
        (of R M ⟨n.1 - (i.1 + 1), by omega⟩) ∘ₗ
      TensorPower.splitAt R M n.1 (i.1 + 1) (by omega)

/-- Reduced deconcatenation cuts a nonempty tensor word at every nontrivial position.

Words of lengths zero and one have no nontrivial cuts; only positive lengths occur in the source,
so length one is sent to zero. -/
noncomputable def deconcatenation :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M ⊗[R] ReducedTensorWords R M :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ (deconcatenationComponent R M)

@[simp]
theorem deconcatenation_of (n : {n : ℕ // 0 < n}) (x : TensorPower R n.1 M) :
    deconcatenation R M (of R M n x) = deconcatenationComponent R M n x := by
  simp [deconcatenation, of]

/-- On a pure tensor, reduced deconcatenation is the sum of its prefix--suffix cuts. -/
theorem deconcatenation_of_tprod (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M) :
    deconcatenation R M (of R M n (PiTensorProduct.tprod R x)) =
      ∑ i : Fin (n.1 - 1),
        of R M ⟨i.1 + 1, by omega⟩
            (PiTensorProduct.tprod R
              (fun j : Fin (i.1 + 1) ↦ x (Fin.castLE (by omega) j))) ⊗ₜ[R]
          of R M ⟨n.1 - (i.1 + 1), by omega⟩
            (PiTensorProduct.tprod R
              (fun j : Fin (n.1 - (i.1 + 1)) ↦ x ⟨i.1 + 1 + j.1, by omega⟩)) := by
  rw [deconcatenation_of]
  simp only [deconcatenationComponent, LinearMap.sum_apply, LinearMap.comp_apply,
    TensorPower.splitAt_tprod, TensorProduct.map_tmul]

/-- On tensor words of length one, reduced deconcatenation is zero. -/
theorem deconcatenation_of_length_one (x : TensorPower R 1 M) :
    deconcatenation R M (of R M ⟨1, by omega⟩ x) = 0 := by
  rw [deconcatenation_of]
  unfold deconcatenationComponent
  have hempty : (Finset.univ : Finset (Fin (1 - 1))) = ∅ := by
    ext i
    exact Fin.elim0 i
  rw [hempty, Finset.sum_empty, LinearMap.zero_apply]

section Map

variable {M : Type uM} {N : Type uN} {P : Type uP} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Apply a linear map to every letter of a reduced tensor word. -/
noncomputable def map (f : M →ₗ[R] N) : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    of R N n ∘ₗ PiTensorProduct.map fun _ ↦ f

/-- Mapping a homogeneous tensor word applies the tensor power of the map in the same length. -/
@[simp]
theorem map_of (f : M →ₗ[R] N) (n : {n : ℕ // 0 < n}) (x : TensorPower R n.1 M) :
    ReducedTensorWords.map (R := R) f (of R M n x) =
      of R N n (PiTensorProduct.map (fun _ ↦ f) x) := by
  simp [map, of]

/-- Mapping a pure tensor applies the map to each of its letters. -/
theorem map_of_tprod (f : M →ₗ[R] N) (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M) :
    ReducedTensorWords.map (R := R) f (of R M n (PiTensorProduct.tprod R x)) =
      of R N n (PiTensorProduct.tprod R fun i ↦ f (x i)) := by
  simp

/-- Mapping the identity map over the letters is the identity. -/
@[simp]
theorem map_id : ReducedTensorWords.map (R := R) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro n
  apply LinearMap.ext
  intro x
  simp [map, of]

/-- Mapping a composite over the letters composes the two letterwise maps. -/
theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    ReducedTensorWords.map (R := R) (g ∘ₗ f) =
      ReducedTensorWords.map (R := R) g ∘ₗ ReducedTensorWords.map (R := R) f := by
  apply DirectSum.linearMap_ext R
  intro n
  apply LinearMap.ext
  intro x
  simp [map, of, PiTensorProduct.map_comp]

/-- Reduced deconcatenation is natural with respect to linear maps of the letters. -/
theorem deconcatenation_natural (f : M →ₗ[R] N) :
    deconcatenation R N ∘ₗ ReducedTensorWords.map (R := R) f =
      TensorProduct.map (ReducedTensorWords.map (R := R) f)
          (ReducedTensorWords.map (R := R) f) ∘ₗ deconcatenation R M := by
  apply DirectSum.linearMap_ext R
  intro n
  apply LinearMap.ext
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      simp only [LinearMap.comp_apply, map_smul]
      congr 1
      -- Refold the direct-sum inclusions: their positive-length proof terms otherwise prevent the
      -- pure-tensor rewrite lemmas from matching this elaborated goal.
      change deconcatenation R N
          (ReducedTensorWords.map (R := R) f
            (of R M n (PiTensorProduct.tprod R x))) =
        TensorProduct.map (ReducedTensorWords.map (R := R) f)
            (ReducedTensorWords.map (R := R) f)
          (deconcatenation R M (of R M n (PiTensorProduct.tprod R x)))
      rw [map_of_tprod]
      rw [deconcatenation_of_tprod, deconcatenation_of_tprod]
      simp only [map_sum, TensorProduct.map_tmul, map, of, DirectSum.toModule_lof,
        LinearMap.comp_apply, PiTensorProduct.map_tprod]
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply, hx, hy]

end Map

end ReducedTensorWords

end TauCeti
