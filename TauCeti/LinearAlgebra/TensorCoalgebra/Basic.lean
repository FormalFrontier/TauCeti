/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.LinearAlgebra.TensorPower.Basic

/-!
# Tensor words and deconcatenation

For an `R`-module `M`, reduced tensor words are the direct sum of its positive tensor powers.  This
file constructs that module and its reduced deconcatenation map, which cuts a positive word at
every nontrivial position.  It also defines blocks of consecutive letters in a tensor word, used
to express iterated cuts.

The construction uses Mathlib's `TensorPower` and direct-sum/tensor-product equivalences, together
with `TensorPower.splitAt`.  It is the coalgebra-side input for the suspended bar construction in
the `DGAInfinity` roadmap.

## Main definitions

* `TauCeti.ReducedTensorWords`: the direct sum of positive tensor powers.
* `TauCeti.ReducedTensorWords.deconcatenation`: sum over every nontrivial cut of a tensor word.
* `TauCeti.ReducedTensorWords.subword`: a block of consecutive letters in a tensor word.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN uP

namespace TauCeti

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The module of nonempty tensor words. -/
abbrev ReducedTensorWords : Type _ := ⨁ n : {n : ℕ // 0 < n}, TensorPower R n.1 M

namespace ReducedTensorWords

/-- Include a positive tensor power into reduced tensor words. -/
noncomputable def of (n : {n : ℕ // 0 < n}) :
    TensorPower R n.1 M →ₗ[R] ReducedTensorWords R M :=
  DirectSum.lof R {n : ℕ // 0 < n} (fun n ↦ TensorPower R n.1 M) n

/-- The positive tensor-power inclusions generate all reduced tensor words. -/
theorem iSup_range_of : ⨆ n : {n : ℕ // 0 < n}, LinearMap.range (of R M n) = ⊤ := by
  simpa only [of, DirectSum.lof] using
    (DFinsupp.iSup_range_lsingle (R := R)
      (M := fun n : {n : ℕ // 0 < n} ↦ TensorPower R n.1 M))

/-- Two linear maps out of reduced tensor words agree if they agree on pure tensor words. -/
theorem linearMap_ext {N : Type uN} [AddCommMonoid N] [Module R N]
    {f g : ReducedTensorWords R M →ₗ[R] N}
    (h : ∀ n (x : Fin n.1 → M),
      f (of R M n (PiTensorProduct.tprod R x)) =
        g (of R M n (PiTensorProduct.tprod R x))) : f = g := by
  apply DirectSum.linearMap_ext R
  intro n
  apply PiTensorProduct.ext
  ext x
  exact h n x

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

/-- Deconcatenation on words of one fixed length, summed over all nontrivial cuts. -/
noncomputable def deconcatenationComponent (n : {n : ℕ // 0 < n}) :
    TensorPower R n.1 M →ₗ[R] ReducedTensorWords R M ⊗[R] ReducedTensorWords R M :=
  ∑ i : Fin (n.1 - 1),
    TensorProduct.map
        (of R M ⟨i.1 + 1, by omega⟩)
        (of R M ⟨n.1 - (i.1 + 1), by omega⟩) ∘ₗ
      TensorPower.splitAt R M n.1 (i.1 + 1) (by omega)

/-- On a pure tensor, deconcatenation is the sum of its prefix--suffix cuts. -/
@[simp]
theorem deconcatenationComponent_tprod (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M) :
    deconcatenationComponent R M n (PiTensorProduct.tprod R x) =
      ∑ i : Fin (n.1 - 1),
        of R M ⟨i.1 + 1, by omega⟩
            (PiTensorProduct.tprod R
              (fun j : Fin (i.1 + 1) ↦ x (Fin.castLE (by omega) j))) ⊗ₜ[R]
          of R M ⟨n.1 - (i.1 + 1), by omega⟩
            (PiTensorProduct.tprod R
              (fun j : Fin (n.1 - (i.1 + 1)) ↦ x ⟨i.1 + 1 + j.1, by omega⟩)) := by
  simp only [deconcatenationComponent, LinearMap.sum_apply, LinearMap.comp_apply,
    TensorPower.splitAt_tprod, TensorProduct.map_tmul]

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

/-- On tensor words of length one, reduced deconcatenation is zero. -/
theorem deconcatenation_of_length_one (x : TensorPower R 1 M) :
    deconcatenation R M (of R M ⟨1, by omega⟩ x) = 0 := by
  rw [deconcatenation_of]
  unfold deconcatenationComponent
  have hempty : (Finset.univ : Finset (Fin (1 - 1))) = ∅ := by
    ext i
    exact Fin.elim0 i
  rw [hempty, Finset.sum_empty, LinearMap.zero_apply]

section Subword

variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- The tensor word `x a ⊗ ⋯ ⊗ x (a + b - 1)`, of length `b` and starting at position `a`.

It is zero when the requested block is empty or runs past the end of `x`; the intended range of
the definition is `0 < b` and `a + b ≤ n`. -/
noncomputable def subword {n : ℕ} (x : Fin n → M) (a b : ℕ) : ReducedTensorWords R M :=
  if h : 0 < b ∧ a + b ≤ n then
    of R M ⟨b, h.1⟩ (PiTensorProduct.tprod R fun j : Fin b ↦ x ⟨a + j.1, by have := j.isLt; omega⟩)
  else 0

/-- On its intended range, a subword is the pure tensor of the selected block of letters. -/
theorem subword_eq_of_tprod {n : ℕ} (x : Fin n → M) {a b : ℕ} (hb : 0 < b) (hab : a + b ≤ n) :
    subword R x a b =
      of R M ⟨b, hb⟩
        (PiTensorProduct.tprod R fun j : Fin b ↦ x ⟨a + j.1, by have := j.isLt; omega⟩) := by
  rw [subword, dite_eq_left ⟨hb, hab⟩]

@[simp]
theorem subword_length_zero {n : ℕ} (x : Fin n → M) (a : ℕ) : subword R x a 0 = 0 := by
  simp [subword]

/-- A block running past the end of the tuple is zero. -/
@[simp]
theorem subword_eq_zero_of_lt_add {n : ℕ} (x : Fin n → M) {a b : ℕ} (hab : n < a + b) :
    subword R x a b = 0 := by
  rw [subword, dite_eq_right (by omega)]

/-- A whole tuple is the subword of full length starting at its beginning. -/
theorem of_tprod_eq_subword {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x) = subword R x 0 n := by
  rw [subword_eq_of_tprod R x hn (by omega)]
  congr 1
  exact congrArg _ (funext fun j ↦ (congrArg x (Fin.ext (Nat.zero_add j.1))).symm)

/-- Deconcatenating a block cuts it at each of its nontrivial internal positions. -/
theorem deconcatenation_subword {n : ℕ} (x : Fin n → M) {a b : ℕ} :
    deconcatenation R M (subword R x a b) =
      ∑ c ∈ Finset.Ioo 0 b, subword R x a c ⊗ₜ[R] subword R x (a + c) (b - c) := by
  by_cases hab : a + b ≤ n
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      simp
    rw [subword_eq_of_tprod R x hb hab, deconcatenation_of, deconcatenationComponent_tprod]
    dsimp only [Subtype.val]
    let g := fun c ↦ subword R x a c ⊗ₜ[R] subword R x (a + c) (b - c)
    calc
      _ = ∑ i : Fin (b - 1), g (i.1 + 1) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hi := i.isLt
        dsimp only [g]
        rw [subword_eq_of_tprod R x (a := a) (b := i.1 + 1) (by omega) (by omega),
          subword_eq_of_tprod R x (a := a + (i.1 + 1)) (b := b - (i.1 + 1))
            (by omega) (by omega)]
        congr 1
        refine congrArg _ (congrArg _ (funext fun j ↦ congrArg x (Fin.ext ?_)))
        dsimp only [Subtype.val]
        omega
      _ = ∑ i ∈ Finset.range (b - 1), g (i + 1) :=
        Fin.sum_univ_eq_sum_range (fun i ↦ g (i + 1)) (b - 1)
      _ = ∑ i ∈ Finset.Ico 0 (b - 1), g (1 + i) := by
        rw [Nat.Ico_zero_eq_range]
        simp only [Nat.add_comm]
      _ = ∑ c ∈ Finset.Ico (0 + 1) (b - 1 + 1), g c :=
        Finset.sum_Ico_add g 0 (b - 1) 1
      _ = ∑ c ∈ Finset.Ioo 0 b, g c := by
        rw [Nat.sub_add_cancel (by omega), ← Order.succ_eq_add_one (0 : ℕ),
          Finset.Ico_succ_left_eq_Ioo]
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
    symm
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    simp only [Finset.mem_Ioo] at hc
    by_cases hac : a + c ≤ n
    · rw [subword_eq_zero_of_lt_add R x (a := a + c) (b := b - c) (by omega),
        TensorProduct.tmul_zero]
    · rw [subword_eq_zero_of_lt_add R x (a := a) (b := c) (by omega),
        TensorProduct.zero_tmul]

end Subword

section Map

variable {M : Type uM} {N : Type uN} {P : Type uP} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- Apply a linear map to every letter of a reduced tensor word. -/
noncomputable def map (f : M →ₗ[R] N) : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  DirectSum.lmap fun _ ↦ PiTensorProduct.map fun _ ↦ f

/-- Mapping a homogeneous tensor word applies the tensor power of the map in the same length. -/
@[simp]
theorem map_of (f : M →ₗ[R] N) (n : {n : ℕ // 0 < n}) (x : TensorPower R n.1 M) :
    ReducedTensorWords.map (R := R) f (of R M n x) =
      of R N n (PiTensorProduct.map (fun _ ↦ f) x) := by
  simp [map, of]

/-- Each length component of a mapped tensor word is the tensor power of the map applied to that
component. -/
@[simp]
theorem component_map (f : M →ₗ[R] N) (n : {n : ℕ // 0 < n}) (x : ReducedTensorWords R M) :
    component R N n (ReducedTensorWords.map (R := R) f x) =
      PiTensorProduct.map (fun _ ↦ f) (component R M n x) := by
  simp only [component, map, ← DirectSum.apply_eq_component, DirectSum.lmap_apply]

/-- Mapping a pure tensor applies the map to each of its letters. -/
theorem map_of_tprod (f : M →ₗ[R] N) (n : {n : ℕ // 0 < n}) (x : Fin n.1 → M) :
    ReducedTensorWords.map (R := R) f (of R M n (PiTensorProduct.tprod R x)) =
      of R N n (PiTensorProduct.tprod R fun i ↦ f (x i)) := by
  simp

/-- Mapping the identity map over the letters is the identity. -/
@[simp]
theorem map_id : ReducedTensorWords.map (R := R) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  simp only [map, PiTensorProduct.map_id, DirectSum.lmap_id]

/-- Mapping a composite over the letters composes the two letterwise maps. -/
@[simp]
theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    ReducedTensorWords.map (R := R) (g ∘ₗ f) =
      ReducedTensorWords.map (R := R) g ∘ₗ ReducedTensorWords.map (R := R) f := by
  simp only [map, PiTensorProduct.map_comp, DirectSum.lmap_comp]

/-- Reduced deconcatenation is natural with respect to linear maps of the letters. -/
theorem deconcatenation_natural (f : M →ₗ[R] N) :
    deconcatenation R N ∘ₗ ReducedTensorWords.map (R := R) f =
      TensorProduct.map (ReducedTensorWords.map (R := R) f)
          (ReducedTensorWords.map (R := R) f) ∘ₗ deconcatenation R M := by
  apply linearMap_ext R M
  intro n x
  simp only [LinearMap.comp_apply]
  rw [map_of_tprod]
  simp only [deconcatenation_of, deconcatenationComponent_tprod]
  simp only [map_sum, TensorProduct.map_tmul, map, of, DirectSum.lmap_lof,
    PiTensorProduct.map_tprod]

end Map

end ReducedTensorWords

end TauCeti
