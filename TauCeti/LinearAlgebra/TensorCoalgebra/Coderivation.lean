/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Range
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives
public import TauCeti.LinearAlgebra.TensorCoalgebra.Splice

/-!
# Coderivations of the reduced tensor coalgebra

For an `R`-module `M`, the reduced tensor words `⨁_{n ≥ 1} M^{⊗n}` carry the reduced
deconcatenation coproduct `Δ` built in `TauCeti.ReducedTensorWords.deconcatenation`.  A
*coderivation* is a linear endomorphism `b` satisfying the co-Leibniz rule
`Δ ∘ b = (b ⊗ 1 + 1 ⊗ b) ∘ Δ`.  This file proves that coderivations are exactly their Taylor
components: composing with the projection `letter` onto single letters is a linear isomorphism
from the coderivations onto the linear maps `⨁_{n ≥ 1} M^{⊗n} ⟶ M`.

That coderivations are *determined* by their Taylor components is an induction along the
conilpotence filtration: a word of length at most `n + 1` is cut into two words of length at most
`n`, so the right-hand side of the co-Leibniz rule is already known by induction, and a tensor word
is determined by its cut together with its letter.  That *every* family of components occurs is the
explicit Taylor expansion `coderiv`, which collapses each nonempty block of letters of a word to the
single letter the components produce from that block.  Verifying its co-Leibniz rule is a
reindexing: on both sides the summands are indexed by a cut position together with a collapsed
block, and a cut never splits a block nor the letter that replaced one.

This is the encoding in which an `A∞` algebra is a square-zero coderivation of the bar coalgebra of
a suspended graded module, and its Taylor components are the operations `m_n`; that use is
downstream, in the `DGAInfinity` roadmap.

## Main definitions

* `TauCeti.ReducedTensorWords.IsCoderivation`: the co-Leibniz rule.
* `TauCeti.ReducedTensorWords.coderiv`: the coderivation with prescribed Taylor components.
* `TauCeti.ReducedTensorWords.coderivations`: the submodule of coderivations.

## Main results

* `TauCeti.ReducedTensorWords.IsCoderivation.eq_of_letter_comp_eq`: a coderivation is determined by
  its Taylor components.
* `TauCeti.ReducedTensorWords.isCoderivation_coderiv` and
  `TauCeti.ReducedTensorWords.letter_comp_coderiv`: `coderiv F` is a coderivation with Taylor
  components `F`.
* `TauCeti.ReducedTensorWords.coderivEquivTaylor`: coderivations are linearly isomorphic to their
  Taylor components.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/
public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

variable (R : Type uR) {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Evaluation of a concatenated tuple at an index that is not presented as an index of one of
the two factors. -/
private theorem append_eq_dite {α : Type*} {k l : ℕ} (u : Fin k → α) (v : Fin l → α)
    (i : Fin (k + l)) :
    Fin.append u v i = if hi : i.1 < k then u ⟨i.1, hi⟩ else v ⟨i.1 - k, by omega⟩ := by
  induction i using Fin.addCases with
  | left j =>
      have hj : (Fin.castAdd l j).1 < k := j.isLt
      rw [Fin.append_left, dite_eq_left hj]
      rfl
  | right j =>
      have hj : ¬(Fin.natAdd k j).1 < k := by
        simp only [Fin.val_natAdd]
        omega
      have hj_sub : (j : ℕ) = k + (j : ℕ) - k := by omega
      rw [Fin.append_right, dite_eq_right hj]
      exact congrArg v (Fin.ext hj_sub)

/-- The `(p, d)` summand of the Taylor expansion of a coderivation with components `F`, on tensor
words of length `n`: collapse the `d` letters at position `p` to the single letter that `F`
produces from them.

It is zero unless the collapsed block is nonempty and fits, that is unless `0 < d` and
`p + d ≤ n`.

This is an implementation device for the coderivation/Taylor correspondence, kept public because
the graded, signed correspondence in
`TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation` precomposes it with a twist of the
letters preceding the collapsed block. -/
noncomputable def coderivSummand (F : ReducedTensorWords R M →ₗ[R] M) (n p d : ℕ) :
    TensorPower R n M →ₗ[R] ReducedTensorWords R M :=
  if h : 0 < d ∧ p + d ≤ n then
    let hlength : p + (1 + (n - p - d)) = n + 1 - d := by omega
    of R M ⟨n + 1 - d, by omega⟩ ∘ₗ
      (TensorPower.cast R M hlength).toLinearMap ∘ₗ
      (TensorPower.mulEquiv (R := R) (M := M)).toLinearMap ∘ₗ
      LinearMap.lTensor (TensorPower R p M)
        ((TensorPower.mulEquiv (R := R) (M := M)).toLinearMap ∘ₗ
          LinearMap.rTensor (TensorPower R (n - p - d) M)
            ((TauCeti.TensorPower.oneEquiv R M).symm.toLinearMap ∘ₗ F ∘ₗ of R M ⟨d, h.1⟩)) ∘ₗ
      LinearMap.lTensor (TensorPower R p M) (TensorPower.splitAt R M (n - p) d (by omega)) ∘ₗ
      TensorPower.splitAt R M n p (by omega)
  else 0

/-- Outside its range a Taylor summand vanishes. -/
theorem coderivSummand_eq_zero (F : ReducedTensorWords R M →ₗ[R] M) {n p d : ℕ}
    (h : ¬(0 < d ∧ p + d ≤ n)) : coderivSummand R F n p d = 0 := by
  rw [coderivSummand, dite_eq_right h]

/-- On a pure tensor word, a Taylor summand is the splice of the value of `F` on the collapsed
block. -/
theorem coderivSummand_tprod (F : ReducedTensorWords R M →ₗ[R] M) {n p d : ℕ} (hd : 0 < d)
    (hpd : p + d ≤ n) (x : Fin n → M) :
    coderivSummand R F n p d (PiTensorProduct.tprod R x) =
      splice R x 0 n p d (F (subword R x p d)) := by
  rw [coderivSummand, dite_eq_left ⟨hd, hpd⟩]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    TensorPower.splitAt_tprod, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
    TauCeti.TensorPower.oneEquiv_symm_apply, ← TensorPower.gMul_def,
    TensorPower.tprod_mul_tprod, TensorPower.cast_tprod, Fin.val_castLE]
  rw [← subword_eq_of_tprod R x (a := p) (b := d) hd (by omega),
    splice_eq_of_tprod R x _ hd (by omega) (by omega)]
  refine of_tprod_congr R M _ rfl fun i ↦ ?_
  have hi := i.isLt
  rw [Function.comp_apply, append_eq_dite]
  simp only [Fin.val_cast]
  by_cases h₁ : i.1 < p
  · rw [dite_eq_left h₁, dite_eq_left h₁]
    exact congrArg x (Fin.ext (by simp only [Fin.val_castLE]; omega))
  · rw [dite_eq_right h₁, dite_eq_right h₁, append_eq_dite]
    by_cases h₂ : i.1 = p
    · have hi_sub : i.1 - p < 1 := by omega
      rw [dite_eq_left hi_sub, dite_eq_left h₂]
    · have hi_sub : ¬i.1 - p < 1 := by omega
      rw [dite_eq_right hi_sub, dite_eq_right h₂]
      exact congrArg x (by simp only [Fin.mk.injEq]; omega)


/-- The linear endomorphism of the reduced tensor coalgebra whose Taylor components are `F`: on a
tensor word it collapses each nonempty block of letters to the single letter that `F` produces
from that block, and sums over all blocks. -/
noncomputable def coderiv (F : ReducedTensorWords R M →ₗ[R] M) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦
    ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), coderivSummand R F n.1 p d

/-- Evaluation of `coderiv F` on a homogeneous tensor word `of R M n z`: the sum, over a position
`p` and a block length `d`, of the Taylor summands collapsing the `d` letters at position `p`.

The public form of this evaluation rule is `TauCeti.ReducedTensorWords.coderiv_subword`, which
states the same sum in terms of `TauCeti.ReducedTensorWords.splice`. -/
private theorem coderiv_of (F : ReducedTensorWords R M →ₗ[R] M) (n : {n : ℕ // 0 < n})
    (z : TensorPower R n.1 M) :
    coderiv R F (of R M n z) =
      ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), coderivSummand R F n.1 p d z := by
  rw [coderiv, toModule_of]
  simp only [LinearMap.sum_apply]

/-- A Taylor summand on a tensor word that is a block of a longer tuple, read back in that
tuple. -/
theorem coderivSummand_tprod_of_eq (F : ReducedTensorWords R M →ₗ[R] M) {n b : ℕ}
    (x : Fin n → M) (y : Fin b → M) {a : ℕ} (hab : a + b ≤ n)
    (hy : ∀ (j : ℕ) (hj : j < b), y ⟨j, hj⟩ = x ⟨a + j, by omega⟩) (p d : ℕ) :
    coderivSummand R F b p d (PiTensorProduct.tprod R y) =
      splice R x a b p d (F (subword R x (a + p) d)) := by
  by_cases h : 0 < d ∧ p + d ≤ b
  · rw [coderivSummand_tprod R F h.1 h.2,
      subword_congr R y x (a := p) (a' := a + p) (by omega) (by omega) fun j hj ↦ by
        rw [hy (p + j) (by omega)]
        exact congrArg x (by simp only [Fin.mk.injEq]; omega)]
    exact splice_congr R y x _ (by omega) (by omega) fun j hj ↦ by
      rw [hy (0 + j) (by omega)]
      exact congrArg x (by simp only [Fin.mk.injEq]; omega)
  · rw [coderivSummand_eq_zero R F h, LinearMap.zero_apply, splice_eq_zero_of_not_fits R x _ h]

/-- The Taylor expansion of `coderiv F` on a block of a tensor word.  The two ranges may be taken
as large as convenient, since a summand whose collapsed block does not fit inside the block
vanishes; that is what lets the expansions of a word and of its two halves be summed over one
common range. -/
theorem coderiv_subword (F : ReducedTensorWords R M →ₗ[R] M) {n : ℕ} (x : Fin n → M) {a b K : ℕ}
    (hK : b ≤ K) :
    coderiv R F (subword R x a b) =
      ∑ p ∈ Finset.range K, ∑ d ∈ Finset.range (K + 1),
        splice R x a b p d (F (subword R x (a + p) d)) := by
  by_cases hab : a + b ≤ n
  · have hvanish : ∀ p d : ℕ, b ≤ p ∨ b < d →
        splice R x a b p d (F (subword R x (a + p) d)) = 0 := fun p d h ↦
      splice_eq_zero_of_not_fits R x _ (by omega)
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [subword_length_zero, map_zero]
      exact (Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
        hvanish p d (Or.inl (Nat.zero_le p))).symm
    rw [subword_eq_of_tprod R x hb hab, coderiv_of,
      ← sum_sum_range_eq_of_eq_zero_right hK _ hvanish]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun d _ ↦
      coderivSummand_tprod_of_eq R F x _ hab (fun j hj ↦ rfl) p d
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
    symm
    exact Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
      splice_eq_zero_of_length_lt_add R x _ (by omega)


/-- A linear endomorphism of the reduced tensor coalgebra is a *coderivation* when it satisfies
the co-Leibniz rule: cutting its value is the same as cutting first and applying it to one of the
two halves. -/
def IsCoderivation (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) : Prop :=
  deconcatenation R M ∘ₗ b =
    (LinearMap.rTensor (ReducedTensorWords R M) b +
        LinearMap.lTensor (ReducedTensorWords R M) b) ∘ₗ deconcatenation R M

variable {R}

/-- The co-Leibniz rule of a coderivation, applied to an element. -/
theorem IsCoderivation.deconcatenation_apply
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hb : IsCoderivation R b)
    (z : ReducedTensorWords R M) :
    deconcatenation R M (b z) =
      LinearMap.rTensor (ReducedTensorWords R M) b (deconcatenation R M z) +
        LinearMap.lTensor (ReducedTensorWords R M) b (deconcatenation R M z) := by
  have h := congrArg (fun f ↦ f z) hb
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] using h

/-- The co-Leibniz identity of a coderivation, as a reusable `Iff`: this exposes the body of
`IsCoderivation` to consumers in other modules, for which the definition's body is not exposed. -/
theorem isCoderivation_iff {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    IsCoderivation R b ↔
      (deconcatenation R M ∘ₗ b =
        (LinearMap.rTensor (ReducedTensorWords R M) b +
            LinearMap.lTensor (ReducedTensorWords R M) b) ∘ₗ deconcatenation R M) :=
  Iff.rfl

/-- Two endomorphisms agreeing on a submodule have the same twisted co-Leibniz term on tensors
of two elements of that submodule, where an auxiliary twist `τ` acts on the left half of every
cut before `b` is applied to the right half. -/
theorem rTensor_add_lTensor_rTensor_congr
    {b₁ b₂ τ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (P : Submodule R (ReducedTensorWords R M)) (h : ∀ z ∈ P, b₁ z = b₂ z) (w : P ⊗[R] P) :
    LinearMap.rTensor (ReducedTensorWords R M) b₁ (TensorProduct.mapIncl P P w) +
        LinearMap.lTensor (ReducedTensorWords R M) b₁
          (LinearMap.rTensor (ReducedTensorWords R M) τ (TensorProduct.mapIncl P P w)) =
      LinearMap.rTensor (ReducedTensorWords R M) b₂ (TensorProduct.mapIncl P P w) +
        LinearMap.lTensor (ReducedTensorWords R M) b₂
          (LinearMap.rTensor (ReducedTensorWords R M) τ (TensorProduct.mapIncl P P w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      rw [h _ u.2, h _ v.2]
  | add u v hu hv =>
      simp only [map_add]
      rw [add_add_add_comm, hu, hv, ← add_add_add_comm]

/-- Two endomorphisms satisfying the same twisted co-Leibniz identity
`Δ ∘ b = (b ⊗ 1) ∘ Δ + (1 ⊗ b) ∘ (τ ⊗ 1) ∘ Δ` and agreeing after projection onto letters are
equal, by induction along the conilpotence filtration.  This is the determinedness argument
shared by `IsCoderivation.eq_of_letter_comp_eq` (with `τ = LinearMap.id`) and
`IsGradedCoderivation.eq_of_letter_comp_eq`. -/
theorem eq_of_letter_comp_eq_of_twist
    {b₁ b₂ τ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (h₁ : deconcatenation R M ∘ₗ b₁ =
      LinearMap.rTensor (ReducedTensorWords R M) b₁ ∘ₗ deconcatenation R M +
        (LinearMap.lTensor (ReducedTensorWords R M) b₁ ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R M) τ) ∘ₗ deconcatenation R M)
    (h₂ : deconcatenation R M ∘ₗ b₂ =
      LinearMap.rTensor (ReducedTensorWords R M) b₂ ∘ₗ deconcatenation R M +
        (LinearMap.lTensor (ReducedTensorWords R M) b₂ ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R M) τ) ∘ₗ deconcatenation R M)
    (hl : letter R M ∘ₗ b₁ = letter R M ∘ₗ b₂) : b₁ = b₂ := by
  have hletter : ∀ z, letter R M (b₁ z) = letter R M (b₂ z) := fun z ↦ by
    have h := congrArg (fun f ↦ f z) hl
    simpa only [LinearMap.coe_comp, Function.comp_apply] using h
  have happly₁ : ∀ z, deconcatenation R M (b₁ z) =
      LinearMap.rTensor (ReducedTensorWords R M) b₁ (deconcatenation R M z) +
        LinearMap.lTensor (ReducedTensorWords R M) b₁
          (LinearMap.rTensor (ReducedTensorWords R M) τ (deconcatenation R M z)) := fun z ↦ by
    have h := congrArg (fun f ↦ f z) h₁
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] using h
  have happly₂ : ∀ z, deconcatenation R M (b₂ z) =
      LinearMap.rTensor (ReducedTensorWords R M) b₂ (deconcatenation R M z) +
        LinearMap.lTensor (ReducedTensorWords R M) b₂
          (LinearMap.rTensor (ReducedTensorWords R M) τ (deconcatenation R M z)) := fun z ↦ by
    have h := congrArg (fun f ↦ f z) h₂
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] using h
  have key : ∀ n : ℕ, ∀ z ∈ filtration R M n, b₁ z = b₂ z := by
    intro n
    induction n with
    | zero =>
        intro z hz
        rw [filtration_zero] at hz
        rw [(Submodule.mem_bot R).1 hz, map_zero, map_zero]
    | succ n ih =>
        intro z hz
        refine eq_of_deconcatenation_eq_of_letter_eq R M ?_ (hletter z)
        obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
        rw [happly₁, happly₂, ← hw]
        exact rTensor_add_lTensor_rTensor_congr _ ih w
  refine LinearMap.ext fun z ↦ ?_
  have hz : z ∈ ⨆ n : ℕ, filtration R M n := by rw [iSup_filtration_eq_top]; trivial
  obtain ⟨n, hn⟩ :=
    (Submodule.mem_iSup_of_directed _ (filtration_monotone R M).directed_le).1 hz
  exact key n z hn

/-- A coderivation of the reduced tensor coalgebra is determined by its Taylor components, that is
by its composite with the projection onto single letters.  Two coderivations agreeing there agree
on every tensor word, by induction along the conilpotence filtration. -/
theorem IsCoderivation.eq_of_letter_comp_eq
    {b₁ b₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (h₁ : IsCoderivation R b₁)
    (h₂ : IsCoderivation R b₂) (hl : letter R M ∘ₗ b₁ = letter R M ∘ₗ b₂) : b₁ = b₂ := by
  refine eq_of_letter_comp_eq_of_twist (τ := LinearMap.id) ?_ ?_ hl
  · rw [isCoderivation_iff] at h₁
    rwa [LinearMap.rTensor_id, LinearMap.comp_id, ← LinearMap.add_comp]
  · rw [isCoderivation_iff] at h₂
    rwa [LinearMap.rTensor_id, LinearMap.comp_id, ← LinearMap.add_comp]

variable (R)

/-- Off the triangle `c + p < n`, every right-half term of the co-Leibniz rule vanishes: an empty
collapse is zero outright, and an overrunning collapse vanishes because the cut half is shorter
than the end of the collapsed block. -/
theorem sum_tmul_splice_eq_zero {n : ℕ} (x : Fin n → M) {c p : ℕ}
    (u : ReducedTensorWords R M) (e : ℕ → M) (hp : n ≤ c + p) :
    ∑ d ∈ Finset.range (n + 1), u ⊗ₜ[R] splice R x c (n - c) p d (e d) = 0 := by
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  rw [splice_eq_zero_of_not_fits R x _ (by omega), TensorProduct.tmul_zero]

/-- `coderiv F` is a coderivation.  Both sides of the co-Leibniz rule are the sum, over a cut
position and a collapsed block, of the tensor of the two halves with the block collapsed in
whichever half contains it; a block is never split by a cut, and a cut never splits the new
letter. -/
@[simp]
theorem isCoderivation_coderiv (F : ReducedTensorWords R M →ₗ[R] M) :
    IsCoderivation R (coderiv R F) := by
  refine linearMap_ext R M fun n x ↦ ?_
  have hn : 0 < n.1 := n.2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
  rw [of_tprod_eq_subword R hn x]
  have hLHS : deconcatenation R M (coderiv R F (subword R x 0 n.1)) =
      (∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range (p + 1),
          subword R x 0 c ⊗ₜ[R]
            splice R x c (n.1 - c) (p - c) d (F (subword R x p d))) +
        ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range n.1,
          splice R x 0 c p d (F (subword R x p d)) ⊗ₜ[R] subword R x c (n.1 - c) := by
    rw [coderiv_subword R F x (a := 0) (b := n.1) (K := n.1) (le_refl n.1), map_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [deconcatenation_splice R x _]
    simp only [Nat.zero_add]
  have hdelta : deconcatenation R M (subword R x 0 n.1) =
      ∑ c ∈ Finset.range n.1, subword R x 0 c ⊗ₜ[R] subword R x c (n.1 - c) := by
    rw [deconcatenation_subword R x (a := 0) (b := n.1)]
    simp only [Nat.zero_add]
    exact sum_Ioo_eq_sum_range n.1 _ (by rw [subword_length_zero, TensorProduct.zero_tmul])
  have hRHS : LinearMap.rTensor (ReducedTensorWords R M) (coderiv R F)
        (deconcatenation R M (subword R x 0 n.1)) +
      LinearMap.lTensor (ReducedTensorWords R M) (coderiv R F)
        (deconcatenation R M (subword R x 0 n.1)) =
      (∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          splice R x 0 c p d (F (subword R x p d)) ⊗ₜ[R] subword R x c (n.1 - c)) +
        ∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          subword R x 0 c ⊗ₜ[R]
            splice R x c (n.1 - c) p d (F (subword R x (c + p) d)) := by
    rw [hdelta, map_sum, map_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun c hc ↦ ?_ <;>
      simp only [Finset.mem_range] at hc
    · rw [LinearMap.rTensor_tmul,
        coderiv_subword R F x (a := 0) (b := c) (K := n.1) (by omega),
        TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun p _ ↦ by
        rw [TensorProduct.sum_tmul]
        simp only [Nat.zero_add]
    · rw [LinearMap.lTensor_tmul,
        coderiv_subword R F x (a := c) (b := n.1 - c) (K := n.1) (by omega),
        TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun p _ ↦ by rw [TensorProduct.tmul_sum]
  rw [hLHS, hRHS, add_comm]
  congr 1
  · exact Eq.trans (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm) Finset.sum_comm
  · have hg : ∀ c q : ℕ, n.1 ≤ c + q →
        (∑ d ∈ Finset.range (n.1 + 1), subword R x 0 c ⊗ₜ[R]
          splice R x c (n.1 - c) q d (F (subword R x (c + q) d))) = 0 :=
      fun c q h ↦ sum_tmul_splice_eq_zero R x (subword R x 0 c) _ h
    refine Eq.trans ?_ (sum_range_triangle n.1 _ hg)
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc ↦ Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [Finset.mem_range] at hc
    have hcp : c + (p - c) = p := by omega
    rw [hcp]


/-- The letter of a spliced word vanishes unless the whole block was collapsed, since otherwise
the word has length at least two. -/
theorem letter_splice_eq_zero {n : ℕ} (x : Fin n → M) {a b p d : ℕ} (e : M) (hdb : d ≠ b) :
    letter R M (splice R x a b p d e) = 0 := by
  by_cases h : 0 < d ∧ p + d ≤ b ∧ a + b ≤ n
  · rw [letter_apply, splice_eq_of_tprod R x e h.1 h.2.1 h.2.2,
      component_of_of_ne R M
        (by simp only [ne_eq, Subtype.ext_iff, Positive.val_one]; omega), map_zero]
  · rw [splice_eq_zero R x e h, map_zero]

/-- The letter of a spliced word vanishes unless the collapse replaces the entire word. -/
theorem letter_splice_eq_zero_of_not_whole {n : ℕ} (x : Fin n → M) {p d : ℕ} (e : M)
    (h : ¬(p = 0 ∧ d = n)) : letter R M (splice R x 0 n p d e) = 0 := by
  rcases eq_or_ne d n with rfl | hne
  · have hp : p ≠ 0 := fun hp => h ⟨hp, rfl⟩
    rw [splice_eq_zero_of_block_lt_add R x e (by omega), map_zero]
  · exact letter_splice_eq_zero R x e hne

/-- Collapsing a whole block leaves the single new letter. -/
theorem letter_splice_self {n : ℕ} (x : Fin n → M) {a b : ℕ} (e : M) (hb : 0 < b)
    (hab : a + b ≤ n) : letter R M (splice R x a b 0 b e) = e := by
  rw [letter_apply, splice_eq_of_tprod R x e hb (by omega) hab,
    component_of_eq R M (m := ⟨b + 1 - b, by omega⟩) (n := 1)
      (Subtype.ext (by simp only [Positive.val_one]; omega)),
    TensorPower.cast_tprod, TauCeti.TensorPower.oneEquiv_tprod]
  simp only [Function.comp_apply]
  rw [dite_eq_right (by simp), dite_eq_left (by simp)]

/-- The Taylor components of `coderiv F` are `F`: the only summand of the expansion that leaves a
single letter is the one collapsing the whole word. -/
@[simp]
theorem letter_comp_coderiv (F : ReducedTensorWords R M →ₗ[R] M) :
    letter R M ∘ₗ coderiv R F = F := by
  refine linearMap_ext R M fun n x ↦ ?_
  have hn : 0 < n.1 := n.2
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [of_tprod_eq_subword R hn x,
    coderiv_subword R F x (a := 0) (b := n.1) (K := n.1) (le_refl n.1), map_sum]
  refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
  · intro p _ hp
    rw [map_sum]
    refine Finset.sum_eq_zero fun d _ ↦ letter_splice_eq_zero_of_not_whole R x _ (by omega)
  · intro hp
    exact absurd (Finset.mem_range.2 hn) hp
  · rw [map_sum]
    refine (Finset.sum_eq_single n.1
      (fun d _ hd ↦ letter_splice_eq_zero_of_not_whole R x _ (by omega)) ?_).trans ?_
    · intro hd
      exact absurd (Finset.mem_range.2 (by omega)) hd
    · rw [letter_splice_self R x _ hn (by omega), Nat.zero_add]

variable (M)

/-- The submodule of coderivations of the reduced tensor coalgebra.  Membership in it is
`TauCeti.ReducedTensorWords.mem_coderivations`. -/
def coderivations : Submodule R (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) where
  carrier := {b | IsCoderivation R b}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, IsCoderivation, LinearMap.comp_zero, LinearMap.rTensor_zero,
      LinearMap.lTensor_zero, add_zero, LinearMap.zero_comp]
  add_mem' := by
    intro b₁ b₂ h₁ h₂
    simp only [Set.mem_ofPred_eq, IsCoderivation, LinearMap.comp_add, LinearMap.rTensor_add,
      LinearMap.lTensor_add] at h₁ h₂ ⊢
    rw [h₁, h₂, ← LinearMap.add_comp]
    exact congrArg (· ∘ₗ deconcatenation R M) (add_add_add_comm _ _ _ _)
  smul_mem' := by
    intro r b hb
    simp only [Set.mem_ofPred_eq, IsCoderivation, LinearMap.comp_smul, LinearMap.rTensor_smul,
      LinearMap.lTensor_smul] at hb ⊢
    rw [hb, ← smul_add, LinearMap.smul_comp]

@[simp]
theorem mem_coderivations {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    b ∈ coderivations R M ↔ IsCoderivation R b := Iff.rfl

/-- Coderivations of the reduced tensor coalgebra are exactly their Taylor components: taking the
letter of the value is a linear isomorphism onto the maps to single letters, with inverse the
Taylor expansion `coderiv`.

Its body is sealed; reason about it through
`TauCeti.ReducedTensorWords.coderivEquivTaylor_apply` and
`TauCeti.ReducedTensorWords.coderivEquivTaylor_symm_apply`. -/
noncomputable def coderivEquivTaylor :
    coderivations R M ≃ₗ[R] (ReducedTensorWords R M →ₗ[R] M) where
  toFun b := letter R M ∘ₗ b.1
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := LinearMap.comp_smul _ _ _
  invFun F := ⟨coderiv R F, (mem_coderivations R M).2 (isCoderivation_coderiv R F)⟩
  left_inv b := Subtype.ext <| (isCoderivation_coderiv R _).eq_of_letter_comp_eq
    ((mem_coderivations R M).1 b.2) (letter_comp_coderiv R _)
  right_inv F := letter_comp_coderiv R F

@[simp]
theorem coderivEquivTaylor_apply (b : coderivations R M) :
    coderivEquivTaylor R M b = letter R M ∘ₗ b.1 := (rfl)

@[simp]
theorem coderivEquivTaylor_symm_apply (F : ReducedTensorWords R M →ₗ[R] M) :
    (coderivEquivTaylor R M).symm F =
      ⟨coderiv R F, (mem_coderivations R M).2 (isCoderivation_coderiv R F)⟩ := (rfl)

end ReducedTensorWords

end TauCeti
