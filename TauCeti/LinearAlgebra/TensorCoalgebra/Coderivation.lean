/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Basic

/-!
# Coderivations of the reduced tensor coalgebra

For an `R`-module `M`, the reduced tensor words `⨁_{n ≥ 1} M^{⊗n}` carry the reduced
deconcatenation coproduct `Δ` built in `TauCeti.ReducedTensorWords.deconcatenation`.  A
*coderivation* is an endomorphism `D` of that module obeying the co-Leibniz rule
`Δ ∘ D = (D ⊗ 1 + 1 ⊗ D) ∘ Δ`.  Its *Taylor components* are the maps `M^{⊗n} ⟶ M` obtained by
restricting `D` to the words of length `n` and reading off the length-one part of the result.

This file defines coderivations and Taylor components, and proves that a coderivation of the
reduced tensor coalgebra is determined by its Taylor components.

The proof rests on a computation of the primitive elements: a tensor word killed by
deconcatenation is a single letter.  Indeed the `(1, n - 1)` bidegree part of `Δ` on a word of
length `n` is the cut after its first letter, and cutting is injective, so no component of
length at least two can survive.  The uniqueness statement then follows by induction on the
length of a word.  On words of length `n` the right-hand side of the co-Leibniz rule only sees the
coderivation on strictly shorter words, so two coderivations with the same Taylor components send
a word of length `n` to two tensor words with the same deconcatenation; their letters agree
because they are the `n`-th Taylor components, and a tensor word is determined by that pair.

An `A∞` structure on `A` is stored, in the suspended convention of the `DGAInfinity` roadmap, as
a square-zero degree-one coderivation `b` of the tensor coalgebra of `sA`, and the operations
`m_n` are the Taylor components of `b`.  Uniqueness is what makes the passage from `b` to the
family `(m_n)` lossless.  The converse construction, extending a prescribed family of Taylor
components to a coderivation, is not proved here.

## Main definitions

* `TauCeti.ReducedTensorWords.letter`, `TauCeti.ReducedTensorWords.ofLetter`: the length-one
  component of a tensor word, and a single letter viewed as a tensor word.
* `TauCeti.ReducedTensorWords.IsCoderivation`: the co-Leibniz rule for deconcatenation.
* `TauCeti.ReducedTensorWords.coderivations`: coderivations as a submodule of the endomorphisms.
* `TauCeti.ReducedTensorWords.taylor`: the Taylor components of an endomorphism.

## Main results

* `TauCeti.ReducedTensorWords.deconcatenation_eq_zero_iff`: the primitives of the reduced tensor
  coalgebra are exactly the single letters.
* `TauCeti.ReducedTensorWords.IsCoderivation.eq_of_taylor_eq` and
  `TauCeti.ReducedTensorWords.taylor_injOn`: a coderivation is determined by its Taylor
  components.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

section Semiring

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The tensor length of a single letter. -/
abbrev lengthOne : {n : ℕ // 0 < n} := ⟨1, Nat.one_pos⟩

/-- A tensor word of length one is a single letter. -/
noncomputable def tensorPowerOne : TensorPower R 1 M ≃ₗ[R] M :=
  PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0

/-- The letter of a reduced tensor word: its length-one component, read as an element of `M`. -/
noncomputable def letter : ReducedTensorWords R M →ₗ[R] M :=
  (tensorPowerOne R M).toLinearMap ∘ₗ component R M lengthOne

/-- A single letter, viewed as a reduced tensor word of length one. -/
noncomputable def ofLetter : M →ₗ[R] ReducedTensorWords R M :=
  of R M lengthOne ∘ₗ (tensorPowerOne R M).symm.toLinearMap

/-- A linear map out of reduced tensor words is determined by its restrictions to the tensor
words of each fixed length. -/
theorem linearMap_ext {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : ReducedTensorWords R M →ₗ[R] N}
    (h : ∀ n x, f (of R M n x) = g (of R M n x)) : f = g :=
  DirectSum.linearMap_ext R fun n ↦ LinearMap.ext fun x ↦ h n x

/-- Two reduced tensor words agreeing in every length are equal. -/
theorem ext_component {x y : ReducedTensorWords R M}
    (h : ∀ n, component R M n x = component R M n y) : x = y :=
  DirectSum.ext_component R h

/-- The letter of a tensor word is its length-one component, read through the length-one
identification. -/
theorem letter_apply (x : ReducedTensorWords R M) :
    letter R M x = tensorPowerOne R M (component R M lengthOne x) :=
  (rfl)

/-- Reading off the letter of a single letter returns it. -/
@[simp]
theorem letter_ofLetter (a : M) : letter R M (ofLetter R M a) = a := by
  rw [letter_apply, ofLetter, LinearMap.comp_apply, component_of, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- A single letter has no nontrivial cut. -/
@[simp]
theorem deconcatenation_ofLetter (a : M) : deconcatenation R M (ofLetter R M a) = 0 := by
  rw [ofLetter, LinearMap.comp_apply]
  exact deconcatenation_of_length_one R M _

/-- The `(1, n - 1)` bidegree part of reduced deconcatenation, evaluated on a pure tensor word of
length `m`: only the cut after the first letter can contribute, and it does so exactly when
`m = n`. -/
theorem map_component_deconcatenation_tprod (n m : {n : ℕ // 0 < n}) (hn : 2 ≤ n.1)
    (x : Fin m.1 → M) :
    TensorProduct.map (component R M lengthOne) (component R M ⟨n.1 - 1, by omega⟩)
        (deconcatenation R M (of R M m (PiTensorProduct.tprod R x))) =
      TensorPower.splitAt R M n.1 1 (by omega)
        (component R M n (of R M m (PiTensorProduct.tprod R x))) := by
  rw [deconcatenation_of, deconcatenationComponent_tprod]
  simp only [map_sum, TensorProduct.map_tmul]
  rcases eq_or_ne m n with rfl | hmn
  · rw [component_of, TensorPower.splitAt_tprod,
      Finset.sum_eq_single (⟨0, by omega⟩ : Fin (m.1 - 1))]
    · simp only [Fin.val_mk, Nat.zero_add]
      rw [component_of, component_of]
    · intro i _ hi
      have hi0 : i.1 ≠ 0 := fun h ↦ hi (Fin.ext h)
      rw [component_of_of_ne R M (by simp only [ne_eq, Subtype.mk.injEq]; omega),
        TensorProduct.zero_tmul]
    · intro hi
      exact absurd (Finset.mem_univ _) hi
  · rw [component_of_of_ne R M hmn, map_zero]
    have hm : 0 < (m : ℕ) := m.2
    have hmn' : (m : ℕ) ≠ (n : ℕ) := fun h ↦ hmn (Subtype.ext h)
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hi1 : i.1 + 1 < (m : ℕ) := by have := i.isLt; omega
    rcases eq_or_ne i.1 0 with hi | hi
    · have h2 := component_of_of_ne R M
        (m := (⟨(m : ℕ) - (i.1 + 1), by omega⟩ : {n : ℕ // 0 < n}))
        (n := (⟨(n : ℕ) - 1, by omega⟩ : {n : ℕ // 0 < n}))
        (by simp only [ne_eq, Subtype.mk.injEq]; omega)
      rw [h2, TensorProduct.tmul_zero]
    · have h1 := component_of_of_ne R M
        (m := (⟨i.1 + 1, by omega⟩ : {n : ℕ // 0 < n})) (n := lengthOne)
        (by simp only [ne_eq, Subtype.mk.injEq]; omega)
      rw [h1, TensorProduct.zero_tmul]

/-- Reading off the `(1, n - 1)` bidegree part of reduced deconcatenation recovers the cut of a
word of length `n` after its first letter. -/
theorem map_component_deconcatenation (n : {n : ℕ // 0 < n}) (hn : 2 ≤ n.1) :
    TensorProduct.map (component R M lengthOne) (component R M ⟨n.1 - 1, by omega⟩) ∘ₗ
        deconcatenation R M =
      TensorPower.splitAt R M n.1 1 (by omega) ∘ₗ component R M n := by
  refine linearMap_ext R M fun m x ↦ ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r y =>
      simp only [LinearMap.comp_apply, map_smul]
      exact congrArg (r • ·) (map_component_deconcatenation_tprod R M n m hn y)
  | add a b ha hb =>
      simp only [LinearMap.comp_apply, map_add] at ha hb ⊢
      rw [ha, hb]

/-- A reduced tensor word is determined by its deconcatenation together with its letter: the
components of length at least two are read off from the cut after the first letter, and the
length-one component is the letter. -/
theorem eq_of_deconcatenation_eq_of_letter_eq {x y : ReducedTensorWords R M}
    (hd : deconcatenation R M x = deconcatenation R M y) (hl : letter R M x = letter R M y) :
    x = y := by
  refine ext_component R M fun n ↦ ?_
  rcases eq_or_ne n lengthOne with rfl | hn
  · have h := congrArg (tensorPowerOne R M).symm hl
    rwa [letter_apply, letter_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply] at h
  · have h2 : 2 ≤ n.1 := by
      have h1 := n.2
      rcases Nat.lt_or_ge n.1 2 with h | h
      · exact absurd (Subtype.ext (by omega : n.1 = 1)) hn
      · exact h
    refine TensorPower.splitAt_injective R M n.1 1 (by omega) ?_
    have hx := congrArg (fun f ↦ f x) (map_component_deconcatenation R M n h2)
    have hy := congrArg (fun f ↦ f y) (map_component_deconcatenation R M n h2)
    simp only [LinearMap.comp_apply] at hx hy
    rw [← hx, ← hy, hd]

/-- The primitive elements of the reduced tensor coalgebra are exactly the single letters. -/
theorem deconcatenation_eq_zero_iff {x : ReducedTensorWords R M} :
    deconcatenation R M x = 0 ↔ x ∈ LinearMap.range (ofLetter R M) := by
  refine ⟨fun hx ↦ ⟨letter R M x, ?_⟩, ?_⟩
  · refine (eq_of_deconcatenation_eq_of_letter_eq R M ?_ ?_).symm
    · rw [deconcatenation_ofLetter, hx]
    · rw [letter_ofLetter]
  · rintro ⟨a, rfl⟩
    exact deconcatenation_ofLetter R M a

section Congr

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- Two maps agreeing on every tensor word shorter than `m` agree on the left half of every cut
of a tensor word of length `m`. -/
theorem rTensor_comp_deconcatenation_comp_of_congr (f g : ReducedTensorWords R M →ₗ[R] N)
    (m : {n : ℕ // 0 < n})
    (hfg : ∀ a : {n : ℕ // 0 < n}, a.1 < m.1 → f ∘ₗ of R M a = g ∘ₗ of R M a) :
    LinearMap.rTensor (ReducedTensorWords R M) f ∘ₗ deconcatenation R M ∘ₗ of R M m =
      LinearMap.rTensor (ReducedTensorWords R M) g ∘ₗ deconcatenation R M ∘ₗ of R M m := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun y ↦ ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    deconcatenation_of, deconcatenationComponent_tprod, map_sum, LinearMap.rTensor_tmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : i.1 + 1 < m.1 := by have := i.isLt; omega
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hfg ⟨i.1 + 1, by omega⟩ hi]

/-- Two maps agreeing on every tensor word shorter than `m` agree on the right half of every cut
of a tensor word of length `m`. -/
theorem lTensor_comp_deconcatenation_comp_of_congr (f g : ReducedTensorWords R M →ₗ[R] N)
    (m : {n : ℕ // 0 < n})
    (hfg : ∀ a : {n : ℕ // 0 < n}, a.1 < m.1 → f ∘ₗ of R M a = g ∘ₗ of R M a) :
    LinearMap.lTensor (ReducedTensorWords R M) f ∘ₗ deconcatenation R M ∘ₗ of R M m =
      LinearMap.lTensor (ReducedTensorWords R M) g ∘ₗ deconcatenation R M ∘ₗ of R M m := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun y ↦ ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    deconcatenation_of, deconcatenationComponent_tprod, map_sum, LinearMap.lTensor_tmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : m.1 - (i.1 + 1) < m.1 := by have := i.isLt; omega
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    hfg ⟨m.1 - (i.1 + 1), by have := i.isLt; omega⟩ hi]

end Congr

/-- A coderivation of the reduced tensor coalgebra: an endomorphism obeying the co-Leibniz rule
`Δ ∘ D = (D ⊗ 1 + 1 ⊗ D) ∘ Δ` for reduced deconcatenation. -/
def IsCoderivation (D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) : Prop :=
  deconcatenation R M ∘ₗ D =
    (LinearMap.rTensor (ReducedTensorWords R M) D +
      LinearMap.lTensor (ReducedTensorWords R M) D) ∘ₗ deconcatenation R M

/-- The defining equation of a coderivation, restated for use outside this file. -/
theorem isCoderivation_iff {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    IsCoderivation R M D ↔ deconcatenation R M ∘ₗ D =
      (LinearMap.rTensor (ReducedTensorWords R M) D +
        LinearMap.lTensor (ReducedTensorWords R M) D) ∘ₗ deconcatenation R M :=
  Iff.rfl

/-- The co-Leibniz rule of a coderivation, evaluated at a tensor word. -/
theorem IsCoderivation.apply {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hD : IsCoderivation R M D) (x : ReducedTensorWords R M) :
    deconcatenation R M (D x) =
      LinearMap.rTensor (ReducedTensorWords R M) D (deconcatenation R M x) +
        LinearMap.lTensor (ReducedTensorWords R M) D (deconcatenation R M x) := by
  have h := congrArg (fun g ↦ g x) ((isCoderivation_iff R M).1 hD)
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using h

/-- The coderivations of the reduced tensor coalgebra, as a submodule of its endomorphisms. -/
def coderivations : Submodule R (Module.End R (ReducedTensorWords R M)) where
  carrier := {D | IsCoderivation R M D}
  add_mem' {D E} hD hE := by
    simp only [Set.mem_ofPred_eq, isCoderivation_iff] at hD hE ⊢
    rw [LinearMap.comp_add, hD, hE, LinearMap.rTensor_add, LinearMap.lTensor_add,
      ← LinearMap.add_comp]
    abel_nf
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, isCoderivation_iff, LinearMap.comp_zero,
      LinearMap.rTensor_zero, LinearMap.lTensor_zero, add_zero, LinearMap.zero_comp]
  smul_mem' r D hD := by
    simp only [Set.mem_ofPred_eq, isCoderivation_iff] at hD ⊢
    rw [LinearMap.comp_smul, hD, LinearMap.rTensor_smul, LinearMap.lTensor_smul, ← smul_add,
      LinearMap.smul_comp]

/-- Membership in the submodule of coderivations is the co-Leibniz rule. -/
@[simp]
theorem mem_coderivations_iff {D : Module.End R (ReducedTensorWords R M)} :
    D ∈ coderivations R M ↔ IsCoderivation R M D :=
  Iff.rfl

/-- The `n`-th Taylor component of an endomorphism of reduced tensor words: its effect on words
of length `n`, read off in length one. -/
noncomputable def taylor (D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (n : {n : ℕ // 0 < n}) : TensorPower R n.1 M →ₗ[R] M :=
  letter R M ∘ₗ D ∘ₗ of R M n

/-- The value of a Taylor component on a tensor word. -/
@[simp]
theorem taylor_apply (D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (n : {n : ℕ // 0 < n}) (x : TensorPower R n.1 M) :
    taylor R M D n x = letter R M (D (of R M n x)) :=
  (rfl)

/-- A coderivation of the reduced tensor coalgebra is determined by its Taylor components. -/
theorem IsCoderivation.eq_of_taylor_eq
    {D E : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hD : IsCoderivation R M D)
    (hE : IsCoderivation R M E) (h : ∀ n, taylor R M D n = taylor R M E n) : D = E := by
  have key : ∀ k : ℕ, ∀ n : {n : ℕ // 0 < n}, n.1 ≤ k → D ∘ₗ of R M n = E ∘ₗ of R M n := by
    intro k
    induction k with
    | zero => exact fun n hn ↦ absurd hn (by have := n.2; omega)
    | succ k ih =>
        intro n hn
        have hshort : ∀ a : {n : ℕ // 0 < n}, a.1 < n.1 → D ∘ₗ of R M a = E ∘ₗ of R M a :=
          fun a ha ↦ ih a (by omega)
        refine LinearMap.ext fun x ↦ ?_
        simp only [LinearMap.comp_apply]
        refine eq_of_deconcatenation_eq_of_letter_eq R M ?_ ?_
        · rw [hD.apply, hE.apply]
          have h1 := congrArg (fun g ↦ g x)
            (rTensor_comp_deconcatenation_comp_of_congr R M D E n hshort)
          have h2 := congrArg (fun g ↦ g x)
            (lTensor_comp_deconcatenation_comp_of_congr R M D E n hshort)
          simp only [LinearMap.comp_apply] at h1 h2
          rw [h1, h2]
        · have hx := congrArg (fun g ↦ g x) (h n)
          simpa only [taylor_apply] using hx
  refine linearMap_ext R M fun n x ↦ ?_
  have hx := congrArg (fun g ↦ g x) (key n.1 n le_rfl)
  simpa only [LinearMap.comp_apply] using hx

/-- A coderivation of the reduced tensor coalgebra whose Taylor components all vanish is zero. -/
theorem IsCoderivation.eq_zero_of_taylor_eq_zero
    {D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hD : IsCoderivation R M D)
    (h : ∀ n, taylor R M D n = 0) : D = 0 :=
  hD.eq_of_taylor_eq R M ((coderivations R M).zero_mem) fun n ↦ by
    rw [h n]
    exact (LinearMap.ext fun x ↦ by rw [taylor_apply, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply]).symm

/-- Taking Taylor components is injective on coderivations of the reduced tensor coalgebra. -/
theorem taylor_injOn : Set.InjOn (taylor R M) (coderivations R M) :=
  fun _ hD _ hE h ↦ IsCoderivation.eq_of_taylor_eq R M hD hE (congrFun h)

end Semiring

end ReducedTensorWords

end TauCeti
