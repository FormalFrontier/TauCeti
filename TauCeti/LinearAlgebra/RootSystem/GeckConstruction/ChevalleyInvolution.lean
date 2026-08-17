/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic

/-!
# The Chevalley involution of Geck's Lie algebra

Geck's construction realizes a reduced crystallographic root system as an explicit matrix Lie
algebra. Mathlib supplies an involutive conjugation exchanging its simple raising and lowering
generators, but that conjugation has the unsigned formulas `eᵢ ↦ fᵢ` and `fᵢ ↦ eᵢ`.

This file constructs the signed Chevalley involution. First conjugate by the diagonal matrix which
acts on the coordinate indexed by a root `α` through `(-1) ^ height(α)`. Since every simple root
has height one, this grading involution fixes `hᵢ` and negates both `eᵢ` and `fᵢ`. Composing it with
Mathlib's opposition involution gives

```text
hᵢ ↦ -hᵢ,    eᵢ ↦ -fᵢ,    fᵢ ↦ -eᵢ.
```

The resulting automorphism is characterized by these equations and is its own inverse. This is
the Chevalley involution on the concrete split semisimple Lie algebra produced from a root datum,
the Lie-algebra input to the Chevalley--Demazure construction in Layer 9 of the ReductiveGroups
roadmap and hence to milestone L0 of the CFSGStatement roadmap.

## Main definitions and results

* `TauCeti.geckChevalleyInvolution`: the signed involution of Geck's constructed Lie algebra.
* `TauCeti.geckChevalleyInvolution_h`, `TauCeti.geckChevalleyInvolution_e`, and
  `TauCeti.geckChevalleyInvolution_f`: its values on the Chevalley generators.
* `TauCeti.eq_geckChevalleyInvolution`: uniqueness from those generator values.
* `TauCeti.geckChevalleyInvolution_symm`: the involution is its own inverse.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
-/

public section

namespace TauCeti

open Matrix Set
open _root_.RootPairing.GeckConstruction

noncomputable section

universe u v w

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type*}
  [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] (b : P.Base)

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The height-parity involution -/

/-- The height-parity sign on the natural basis of Geck's defining representation. The auxiliary
summand indexed by the simple roots has sign `1`; a root coordinate has sign
`(-1) ^ height(α)`. -/
private def geckHeightSign : b.support ⊕ ι → R
  | .inl _ => 1
  | .inr i => (b.height i).negOnePow

/-- The diagonal height-parity matrix in Geck's defining representation. -/
private def geckHeightMatrix : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  diagonal (geckHeightSign b)

omit [Fintype ι] [DecidableEq ι] [IsDomain R] [P.IsCrystallographic] in
private theorem geckHeightSign_mul_self (i : b.support ⊕ ι) :
    geckHeightSign b i * geckHeightSign b i = 1 := by
  cases i with
  | inl i => simp [geckHeightSign]
  | inr i =>
      change ((b.height i).negOnePow : R) * (b.height i).negOnePow = 1
      obtain hi | hi := Int.even_or_odd (b.height i)
      · rw [Int.negOnePow_even _ hi]
        simp
      · rw [Int.negOnePow_odd _ hi]
        simp

omit [Fintype ι] [DecidableEq ι] [IsDomain R] [P.IsCrystallographic] in
private theorem geckHeightSign_simple (i : b.support) :
    geckHeightSign b (.inr i) = -1 := by
  simp [geckHeightSign, b.height_one_of_mem_support i.property]

omit [Fintype ι] [DecidableEq ι] [IsDomain R] [P.IsCrystallographic] in
private theorem geckHeightSign_neg_simple (i : b.support) :
    let _ := P.indexNeg
    geckHeightSign b (.inr (-i : ι)) = -1 := by
  let _ := P.indexNeg
  change ((b.height (-i : ι)).negOnePow : R) = -1
  rw [b.height_reflectionPerm_self, b.height_one_of_mem_support i.property]
  norm_num

omit [Fintype ι] [DecidableEq ι] [IsDomain R] [P.IsCrystallographic] in
private theorem geckHeightSign_mul_eq_neg_one_of_add {i : b.support} {j k : ι}
    (hjk : P.root j = P.root i + P.root k) :
    geckHeightSign b (.inr j) * geckHeightSign b (.inr k) = -1 := by
  simp only [geckHeightSign]
  rw [b.height_add hjk, b.height_one_of_mem_support i.property, Int.negOnePow_add]
  norm_num [Int.coe_negOnePow]
  simpa [geckHeightSign] using geckHeightSign_mul_self b (.inr k)

omit [Fintype ι] [DecidableEq ι] [IsDomain R] [P.IsCrystallographic] in
private theorem geckHeightSign_mul_eq_neg_one_of_sub {i : b.support} {j k : ι}
    (hjk : P.root j = P.root k - P.root i) :
    geckHeightSign b (.inr j) * geckHeightSign b (.inr k) = -1 := by
  simp only [geckHeightSign]
  rw [b.height_sub hjk, b.height_one_of_mem_support i.property, Int.negOnePow_sub]
  norm_num [Int.coe_negOnePow]
  simpa [geckHeightSign] using geckHeightSign_mul_self b (.inr k)

omit [IsDomain R] [P.IsCrystallographic] in
private theorem geckHeightMatrix_mul_self :
    geckHeightMatrix b * geckHeightMatrix b = 1 := by
  rw [geckHeightMatrix, diagonal_mul_diagonal]
  ext i j
  simp [geckHeightSign_mul_self]

/-- Conjugation by the height-parity matrix. This is kept private; the public construction is its
composition with Geck's opposition involution. -/
private def geckHeightConj :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R ≃ₗ⁅R⁆
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) R where
  toFun x := geckHeightMatrix b * x * geckHeightMatrix b
  invFun x := geckHeightMatrix b * x * geckHeightMatrix b
  map_add' x y := by noncomm_ring
  map_smul' t x := by simp
  map_lie' {x y} := by
    simp only [Ring.lie_def]
    nth_rw 1 [← mul_one x]
    nth_rw 2 [← one_mul x]
    simp only [← geckHeightMatrix_mul_self b]
    noncomm_ring
  left_inv x := by
    calc
      geckHeightMatrix b * (geckHeightMatrix b * x * geckHeightMatrix b) *
          geckHeightMatrix b =
          (geckHeightMatrix b * geckHeightMatrix b) * x *
            (geckHeightMatrix b * geckHeightMatrix b) := by noncomm_ring
      _ = x := by rw [geckHeightMatrix_mul_self]; simp
  right_inv x := by
    calc
      geckHeightMatrix b * (geckHeightMatrix b * x * geckHeightMatrix b) *
          geckHeightMatrix b =
          (geckHeightMatrix b * geckHeightMatrix b) * x *
            (geckHeightMatrix b * geckHeightMatrix b) := by noncomm_ring
      _ = x := by rw [geckHeightMatrix_mul_self]; simp

omit [IsDomain R] [P.IsCrystallographic] in
private theorem geckHeightConj_apply (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)
    (i j : b.support ⊕ ι) :
    geckHeightConj b A i j = geckHeightSign b i * A i j * geckHeightSign b j := by
  change (geckHeightMatrix b * A * geckHeightMatrix b) i j = _
  simp [geckHeightMatrix]

omit [IsDomain R] in
private theorem geckHeightConj_h (i : b.support) :
    geckHeightConj b (h i) = h i := by
  rw [h_eq_diagonal]
  let d : b.support ⊕ ι → R :=
    Sum.elim (fun _ => 0) (fun j => (P.pairingIn ℤ j i : R))
  change geckHeightConj b (diagonal d) = diagonal d
  ext j k
  rw [geckHeightConj_apply]
  by_cases hjk : j = k
  · subst k
    rw [Matrix.diagonal_apply_eq]
    calc
      geckHeightSign b j * d j * geckHeightSign b j =
          (geckHeightSign b j * geckHeightSign b j) *
            d j := by ring
      _ = d j := by rw [geckHeightSign_mul_self]; simp
  · rw [Matrix.diagonal_apply_ne _ hjk]
    simp

private theorem geckHeightConj_e (i : b.support) :
    geckHeightConj b (e i) = -e i := by
  let _ := P.indexNeg
  classical
  ext (j | j) (k | k)
  · simp [geckHeightConj_apply, geckHeightSign, e]
  · simp only [geckHeightConj_apply, e, Matrix.fromBlocks_apply₁₂,
      Matrix.of_apply, Matrix.neg_apply]
    split_ifs with hjk
    · rw [hjk.1, hjk.2, geckHeightSign_neg_simple]
      simp [geckHeightSign]
    · simp [geckHeightSign]
  · simp only [geckHeightConj_apply, e, Matrix.fromBlocks_apply₂₁,
      Matrix.of_apply, Matrix.neg_apply]
    split_ifs with hj
    · rw [hj, geckHeightSign_simple]
      simp [geckHeightSign]
    · simp [geckHeightSign]
  · simp only [geckHeightConj_apply, e, Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply, Matrix.neg_apply]
    split_ifs with hjk
    · have hs := geckHeightSign_mul_eq_neg_one_of_add b hjk
      calc
        geckHeightSign b (.inr j) * (↑(P.chainBotCoeff i k) + 1) *
              geckHeightSign b (.inr k) =
            (geckHeightSign b (.inr j) * geckHeightSign b (.inr k)) *
              (↑(P.chainBotCoeff i k) + 1) := by ring
        _ = -(↑(P.chainBotCoeff i k) + 1) := by rw [hs]; ring
    · simp [geckHeightSign]

private theorem geckHeightConj_f (i : b.support) :
    geckHeightConj b (f i) = -f i := by
  let _ := P.indexNeg
  classical
  ext (j | j) (k | k)
  · simp [geckHeightConj_apply, geckHeightSign, f]
  · simp only [geckHeightConj_apply, f, Matrix.fromBlocks_apply₁₂,
      Matrix.of_apply, Matrix.neg_apply]
    split_ifs with hjk
    · rw [hjk.1, hjk.2, geckHeightSign_simple]
      simp [geckHeightSign]
    · simp [geckHeightSign]
  · simp only [geckHeightConj_apply, f, Matrix.fromBlocks_apply₂₁,
      Matrix.of_apply, Matrix.neg_apply]
    split_ifs with hj
    · rw [hj, geckHeightSign_neg_simple]
      simp [geckHeightSign]
    · simp [geckHeightSign]
  · simp only [geckHeightConj_apply, f, Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply, Matrix.neg_apply]
    split_ifs with hjk
    · have hs := geckHeightSign_mul_eq_neg_one_of_sub b hjk
      calc
        geckHeightSign b (.inr j) * (↑(P.chainTopCoeff i k) + 1) *
              geckHeightSign b (.inr k) =
            (geckHeightSign b (.inr j) * geckHeightSign b (.inr k)) *
              (↑(P.chainTopCoeff i k) + 1) := by ring
        _ = -(↑(P.chainTopCoeff i k) + 1) := by rw [hs]; ring
    · simp [geckHeightSign]

private theorem geckHeightConj_mem_lieAlgebra {x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hx : x ∈ lieAlgebra b) : geckHeightConj b x ∈ lieAlgebra b := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
      obtain (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩) :
          (∃ i, h i = x) ∨ (∃ i, e i = x) ∨ (∃ i, f i = x) := by
        simpa only [mem_union, mem_range, or_assoc] using hx
      · rw [geckHeightConj_h]
        exact LieSubalgebra.subset_lieSpan (by simp)
      · rw [geckHeightConj_e]
        exact neg_mem (LieSubalgebra.subset_lieSpan (by simp))
      · rw [geckHeightConj_f]
        exact neg_mem (LieSubalgebra.subset_lieSpan (by simp))
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using SMulMemClass.smul_mem c hx
  | lie x y _ _ hx hy =>
      rw [LieEquiv.map_lie]
      exact LieSubalgebra.lie_mem _ hx hy

private theorem geckHeightConj_map_lieAlgebra :
    (lieAlgebra b).map (geckHeightConj b) = lieAlgebra b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact geckHeightConj_mem_lieAlgebra b hy
  · intro hx
    refine ⟨geckHeightConj b x, geckHeightConj_mem_lieAlgebra b hx, ?_⟩
    exact (geckHeightConj b).apply_symm_apply x

private def geckHeightInvolution : lieAlgebra b ≃ₗ⁅R⁆ lieAlgebra b :=
  (geckHeightConj b).ofSubalgebras _ _ (geckHeightConj_map_lieAlgebra b)

/-! ## The signed Chevalley involution -/

private theorem geckOpposition_map_lieAlgebra :
    (lieAlgebra b).map (ωConj b) = lieAlgebra b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ωConj_mem_of_mem hy
  · intro hx
    refine ⟨ωConj b x, ωConj_mem_of_mem hx, ?_⟩
    exact (ωConj b).apply_symm_apply x

private def geckOppositionInvolution : lieAlgebra b ≃ₗ⁅R⁆ lieAlgebra b :=
  (ωConj b).ofSubalgebras _ _ (geckOpposition_map_lieAlgebra b)

private theorem geckHeightInvolution_h (i : b.support) :
    geckHeightInvolution b ⟨h i, h_mem_lieAlgebra i⟩ =
      ⟨h i, h_mem_lieAlgebra i⟩ := by
  apply Subtype.ext
  exact geckHeightConj_h b i

private theorem geckHeightInvolution_e (i : b.support) :
    geckHeightInvolution b ⟨e i, e_mem_lieAlgebra i⟩ =
      -⟨e i, e_mem_lieAlgebra i⟩ := by
  apply Subtype.ext
  exact geckHeightConj_e b i

private theorem geckHeightInvolution_f (i : b.support) :
    geckHeightInvolution b ⟨f i, f_mem_lieAlgebra i⟩ =
      -⟨f i, f_mem_lieAlgebra i⟩ := by
  apply Subtype.ext
  exact geckHeightConj_f b i

private theorem geckOppositionInvolution_h (i : b.support) :
    geckOppositionInvolution b ⟨h i, h_mem_lieAlgebra i⟩ =
      -⟨h i, h_mem_lieAlgebra i⟩ := by
  apply Subtype.ext
  change ωConj b (h i) = -h i
  change ω b * h i * ω b = -h i
  rw [ω_mul_h]
  rw [mul_assoc, ω_mul_ω]
  simp

private theorem geckOppositionInvolution_e (i : b.support) :
    geckOppositionInvolution b ⟨e i, e_mem_lieAlgebra i⟩ =
      ⟨f i, f_mem_lieAlgebra i⟩ := by
  apply Subtype.ext
  change ωConj b (e i) = f i
  change ω b * e i * ω b = f i
  rw [ω_mul_e, mul_assoc, ω_mul_ω]
  simp

private theorem geckOppositionInvolution_f (i : b.support) :
    geckOppositionInvolution b ⟨f i, f_mem_lieAlgebra i⟩ =
      ⟨e i, e_mem_lieAlgebra i⟩ := by
  apply Subtype.ext
  change ωConj b (f i) = e i
  change ω b * f i * ω b = e i
  rw [ω_mul_f, mul_assoc, ω_mul_ω]
  simp

/-- The Chevalley involution of Geck's matrix Lie algebra. It is the composition of the opposition
involution with the height-parity involution, and therefore sends the simple generators by
`hᵢ ↦ -hᵢ`, `eᵢ ↦ -fᵢ`, and `fᵢ ↦ -eᵢ`. -/
noncomputable def geckChevalleyInvolution : lieAlgebra b ≃ₗ⁅R⁆ lieAlgebra b :=
  (geckOppositionInvolution b).trans (geckHeightInvolution b)

/-- The Chevalley involution sends a simple Cartan generator to its negative. -/
@[simp]
theorem geckChevalleyInvolution_h (i : b.support) :
    geckChevalleyInvolution b ⟨h i, h_mem_lieAlgebra i⟩ =
      -⟨h i, h_mem_lieAlgebra i⟩ := by
  rw [geckChevalleyInvolution, LieEquiv.trans_apply, geckOppositionInvolution_h,
    map_neg, geckHeightInvolution_h]

/-- The Chevalley involution sends a simple raising generator to the negative lowering
generator. -/
@[simp]
theorem geckChevalleyInvolution_e (i : b.support) :
    geckChevalleyInvolution b ⟨e i, e_mem_lieAlgebra i⟩ =
      -⟨f i, f_mem_lieAlgebra i⟩ := by
  rw [geckChevalleyInvolution, LieEquiv.trans_apply, geckOppositionInvolution_e,
    geckHeightInvolution_f]

/-- The Chevalley involution sends a simple lowering generator to the negative raising
generator. -/
@[simp]
theorem geckChevalleyInvolution_f (i : b.support) :
    geckChevalleyInvolution b ⟨f i, f_mem_lieAlgebra i⟩ =
      -⟨e i, e_mem_lieAlgebra i⟩ := by
  rw [geckChevalleyInvolution, LieEquiv.trans_apply, geckOppositionInvolution_f,
    geckHeightInvolution_e]

private theorem geckLieHom_ext {g k : lieAlgebra b →ₗ⁅R⁆ lieAlgebra b}
    (hh : ∀ i, g ⟨h i, h_mem_lieAlgebra i⟩ = k ⟨h i, h_mem_lieAlgebra i⟩)
    (he : ∀ i, g ⟨e i, e_mem_lieAlgebra i⟩ = k ⟨e i, e_mem_lieAlgebra i⟩)
    (hf : ∀ i, g ⟨f i, f_mem_lieAlgebra i⟩ = k ⟨f i, f_mem_lieAlgebra i⟩) : g = k := by
  apply LieHom.ext
  intro x
  have hx : x ∈ LieSubalgebra.lieSpan R (lieAlgebra b)
      (((↑) : lieAlgebra b → Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) ⁻¹'
        (range h ∪ range e ∪ range f)) := by
    change x ∈ LieSubalgebra.lieSpan R
      (LieSubalgebra.lieSpan R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)
        (range h ∪ range e ∪ range f))
      (Subtype.val ⁻¹' (range h ∪ range e ∪ range f))
    rw [LieSubalgebra.lieSpan_lieSpan_coe_preimage]
    trivial
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
      change (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) ∈
        range h ∪ range e ∪ range f at hx
      obtain (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩) :
          (∃ i, h i = x) ∨ (∃ i, e i = x) ∨ (∃ i, f i = x) := by
        simpa only [mem_union, mem_range, or_assoc] using hx
      · have : x = ⟨h i, h_mem_lieAlgebra i⟩ := Subtype.ext hi.symm
        subst x
        exact hh i
      · have : x = ⟨e i, e_mem_lieAlgebra i⟩ := Subtype.ext hi.symm
        subst x
        exact he i
      · have : x = ⟨f i, f_mem_lieAlgebra i⟩ := Subtype.ext hi.symm
        subst x
        exact hf i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]
  | lie x y _ _ hx hy => simp [hx, hy]

/-- `TauCeti.geckChevalleyInvolution` is the unique Lie homomorphism with the signed formulas on
Geck's simple Cartan, raising, and lowering generators. -/
theorem eq_geckChevalleyInvolution {g : lieAlgebra b →ₗ⁅R⁆ lieAlgebra b}
    (hh : ∀ i, g ⟨h i, h_mem_lieAlgebra i⟩ = -⟨h i, h_mem_lieAlgebra i⟩)
    (he : ∀ i, g ⟨e i, e_mem_lieAlgebra i⟩ = -⟨f i, f_mem_lieAlgebra i⟩)
    (hf : ∀ i, g ⟨f i, f_mem_lieAlgebra i⟩ = -⟨e i, e_mem_lieAlgebra i⟩) :
    g = (geckChevalleyInvolution b : lieAlgebra b →ₗ⁅R⁆ lieAlgebra b) := by
  apply geckLieHom_ext b
  · intro i
    rw [hh i]
    exact (geckChevalleyInvolution_h b i).symm
  · intro i
    rw [he i]
    exact (geckChevalleyInvolution_e b i).symm
  · intro i
    rw [hf i]
    exact (geckChevalleyInvolution_f b i).symm

/-- Applying Geck's Chevalley involution twice returns the original element. -/
@[simp]
theorem geckChevalleyInvolution_geckChevalleyInvolution (x : lieAlgebra b) :
    geckChevalleyInvolution b (geckChevalleyInvolution b x) = x := by
  have hcomp : (geckChevalleyInvolution b).trans (geckChevalleyInvolution b) =
      (LieEquiv.refl : lieAlgebra b ≃ₗ⁅R⁆ lieAlgebra b) := by
    apply LieEquiv.ext
    intro y
    exact DFunLike.congr_fun (geckLieHom_ext b (fun i => by simp) (fun i => by simp)
      fun i => by simp) y
  exact DFunLike.congr_fun hcomp x

/-- Geck's Chevalley involution is an involution. -/
theorem geckChevalleyInvolution_involutive :
    Function.Involutive (geckChevalleyInvolution b) :=
  geckChevalleyInvolution_geckChevalleyInvolution b

/-- Geck's Chevalley involution is its own inverse. -/
@[simp]
theorem geckChevalleyInvolution_symm :
    (geckChevalleyInvolution b).symm = geckChevalleyInvolution b := by
  apply DFunLike.ext _ _
  intro x
  apply (geckChevalleyInvolution b).injective
  calc
    geckChevalleyInvolution b ((geckChevalleyInvolution b).symm x) = x :=
      (geckChevalleyInvolution b).apply_symm_apply x
    _ = geckChevalleyInvolution b (geckChevalleyInvolution b x) :=
      (geckChevalleyInvolution_geckChevalleyInvolution b x).symm

end

end TauCeti

end
