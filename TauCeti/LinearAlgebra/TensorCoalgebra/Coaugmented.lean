/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import TauCeti.LinearAlgebra.TensorCoalgebra.Basic

/-!
# The coaugmented tensor coalgebra

For an `R`-module `M`, the tensor words `⨁_{n ≥ 0} M^{⊗n}` carry the deconcatenation coproduct
`Δ (x₁ ⋯ x_n) = ∑_{c = 0}^{n} (x₁ ⋯ x_c) ⊗ (x_{c+1} ⋯ x_n)`, whose outer two summands use the
empty word.  Together with the counit that reads off the length-zero coefficient this makes the
tensor words a genuine `Coalgebra` in Mathlib's sense, coaugmented by `r ↦ r · 1`, where the empty
word `1` is group-like.

This is the counital (coaugmented) extension of the reduced tensor coalgebra
`TauCeti.ReducedTensorWords`, which only admits the nontrivial cuts and is therefore not
counital.  The comparison is
`TauCeti.TensorWords.deconcatenation_comp_reducedInclusion`: the coproduct of a word `x` of
positive length is `1 ⊗ x + x ⊗ 1` together with the reduced coproduct of `x`, and the reduced
words map onto exactly the kernel `ker ε` of the counit. Both facts are what makes the two
presentations interchangeable downstream: an `A∞` structure is a square-zero coderivation of the
reduced coalgebra, while an `A∞` morphism is a morphism of the coaugmented ones.

The combinatorics is the same as in the reduced case and is again organised through blocks of
consecutive letters, `TauCeti.TensorWords.subword`.  In both cases the two iterated coproducts are
indexed by the triangle `0 ≤ d ≤ c ≤ n` of nested cuts and are compared after extending them to
the full square.  The one difference is that an empty block is now the empty word rather than
zero, so the degenerate summands outside the triangle no longer vanish: the extension is not free
as it is in the reduced case, and it is carried out by `Finset.sum_filter`, which keeps the
constraint `d ≤ c` as an explicit `if`.  Coassociativity is then `Finset.sum_comm` all the same.

## Main definitions

* `TauCeti.TensorWords`: the direct sum of all tensor powers, the empty one included.
* `TauCeti.TensorWords.deconcatenation`: the sum over every cut of a tensor word.
* `TauCeti.TensorWords.counit`: the length-zero coefficient.
* `TauCeti.TensorWords.coaugmentation`: the algebra map, bundled as a coalgebra morphism.
* `TauCeti.TensorWords.reducedInclusion` and `TauCeti.TensorWords.reducedProjection`: the
  positive-length words as a direct summand.

## Main results

* `TauCeti.TensorWords.instCoalgebra`: tensor words are a coalgebra.
* `TauCeti.TensorWords.isGroupLikeElem_one`: the empty word is group-like.
* `TauCeti.TensorWords.deconcatenation_comp_reducedInclusion`: on a word of positive length the
  coproduct is the reduced coproduct together with its two degenerate cuts.
* `TauCeti.TensorWords.ker_counit`: the kernel of the counit is the image of the positive-length
  words under `TauCeti.TensorWords.reducedInclusion`.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN

namespace TauCeti

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The module of tensor words, the empty word included. -/
abbrev TensorWords : Type _ := ⨁ n : ℕ, TensorPower R n M

namespace TensorWords

/-- Include a tensor power into tensor words. -/
noncomputable def of (n : ℕ) : TensorPower R n M →ₗ[R] TensorWords R M :=
  DirectSum.lof R ℕ (fun n ↦ TensorPower R n M) n

/-- Inclusion into tensor words is the direct-sum inclusion. -/
theorem of_def (n : ℕ) :
    of R M n = DirectSum.lof R ℕ (fun n ↦ TensorPower R n M) n := by
  rw [of]

/-- Pure tensor words with pointwise equal letters are equal. -/
theorem of_tprod_congr {n : ℕ} {x y : Fin n → M} (h : ∀ i, x i = y i) :
    of R M n (PiTensorProduct.tprod R x) = of R M n (PiTensorProduct.tprod R y) := by
  exact congrArg _ (congrArg _ (funext h))

/-- Two linear maps out of tensor words agree if they agree on pure tensor words. -/
theorem linearMap_ext {N : Type uN} [AddCommMonoid N] [Module R N]
    {f g : TensorWords R M →ₗ[R] N}
    (h : ∀ (n : ℕ) (x : Fin n → M),
      f (of R M n (PiTensorProduct.tprod R x)) =
        g (of R M n (PiTensorProduct.tprod R x))) : f = g := by
  apply DirectSum.linearMap_ext R
  intro n
  apply PiTensorProduct.ext
  ext x
  exact h n x

/-- Project tensor words to a fixed tensor length. -/
noncomputable def component (n : ℕ) : TensorWords R M →ₗ[R] TensorPower R n M :=
  DirectSum.component R ℕ (fun n ↦ TensorPower R n M) n

/-- The component of an included tensor power at its own length is that tensor power. -/
@[simp]
theorem component_of (n : ℕ) (x : TensorPower R n M) :
    component R M n (of R M n x) = x := by
  simp [component, of]

/-- Projecting an included tensor power vanishes when the two lengths differ. -/
@[simp]
theorem component_of_of_ne {m n : ℕ} (h : m ≠ n) (x : TensorPower R m M) :
    component R M n (of R M m x) = 0 := by
  simp [component, of, DirectSum.component.of, h]

/-- A linear map assembled from its length components is that component on a tensor word of that
length. -/
@[simp]
theorem toModule_of {N : Type uN} [AddCommMonoid N] [Module R N]
    (φ : ∀ n : ℕ, TensorPower R n M →ₗ[R] N) (n : ℕ) (z : TensorPower R n M) :
    DirectSum.toModule R ℕ N φ (of R M n z) = φ n z := by
  simp [of]

/-! ## The counit -/

/-- The counit of the tensor coalgebra reads off the coefficient of the empty word. -/
noncomputable def counit : TensorWords R M →ₗ[R] R :=
  (TensorPower.algebraMap₀ (R := R) (M := M)).symm.toLinearMap ∘ₗ component R M 0

/-- On the empty length the counit is the canonical identification with the ground ring. -/
@[simp]
theorem counit_of_zero (z : TensorPower R 0 M) :
    counit R M (of R M 0 z) = (TensorPower.algebraMap₀ (R := R) (M := M)).symm z := by
  simp [counit]

/-- The counit annihilates every word of positive length. -/
@[simp]
theorem counit_of_of_ne_zero {n : ℕ} (hn : n ≠ 0) (z : TensorPower R n M) :
    counit R M (of R M n z) = 0 := by
  simp [counit, component_of_of_ne R M hn]

/-- The algebra map is inclusion into tensor length zero. -/
theorem algebraMap_apply (r : R) :
    algebraMap R (TensorWords R M) r =
      of R M 0 (TensorPower.algebraMap₀ (R := R) (M := M) r) := by
  rw [DirectSum.algebraMap_apply, TensorPower.galgebra_toFun_def,
    ← DirectSum.lof_eq_of R ℕ (fun n ↦ TensorPower R n M), of_def]

/-- The algebra unit is the empty pure tensor in tensor length zero. -/
theorem one_eq_of_zero :
    (1 : TensorWords R M) =
      of R M 0 (PiTensorProduct.tprod R fun i : Fin 0 ↦ (i.elim0 : M)) := by
  rw [DirectSum.one_def, TensorPower.gOne_def, of_def, DirectSum.lof_eq_of]

/-- The counit is a retraction of the coaugmentation given by the algebra map. -/
@[simp]
theorem counit_comp_algebraMap :
    counit R M ∘ₗ Algebra.linearMap R (TensorWords R M) = LinearMap.id := by
  refine LinearMap.ext_ring ?_
  rw [LinearMap.comp_apply, Algebra.linearMap_apply, algebraMap_apply]
  rw [counit_of_zero, LinearEquiv.symm_apply_apply, LinearMap.id_apply]

/-- The counit retracts the coaugmentation on every scalar. -/
@[simp]
theorem counit_algebraMap (r : R) :
    counit R M (algebraMap R (TensorWords R M) r) = r := by
  rw [← Algebra.linearMap_apply, ← LinearMap.comp_apply, counit_comp_algebraMap,
    LinearMap.id_apply]

/-- The empty word has counit one. -/
@[simp]
theorem counit_one : counit R M (1 : TensorWords R M) = 1 := by
  have h := LinearMap.congr_fun (counit_comp_algebraMap R M) (1 : R)
  simpa only [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] using h

/-! ## Deconcatenation -/

/-- Deconcatenation on words of one fixed length, summed over all cuts, the two outer ones
included. -/
noncomputable def deconcatenationComponent (n : ℕ) :
    TensorPower R n M →ₗ[R] TensorWords R M ⊗[R] TensorWords R M :=
  ∑ i : Fin (n + 1),
    TensorProduct.map (of R M i.1) (of R M (n - i.1)) ∘ₗ
      TensorPower.splitAt R M n i.1 (by have := i.isLt; omega)

/-- On a pure tensor, deconcatenation is the sum of its prefix--suffix cuts. -/
@[simp]
theorem deconcatenationComponent_tprod (n : ℕ) (x : Fin n → M) :
    deconcatenationComponent R M n (PiTensorProduct.tprod R x) =
      ∑ i : Fin (n + 1),
        of R M i.1
            (PiTensorProduct.tprod R
              (fun j : Fin i.1 ↦ x (Fin.castLE (by have := i.isLt; omega) j))) ⊗ₜ[R]
          of R M (n - i.1)
            (PiTensorProduct.tprod R
              (fun j : Fin (n - i.1) ↦ x ⟨i.1 + j.1, by have := j.isLt; omega⟩)) := by
  simp only [deconcatenationComponent, LinearMap.sum_apply, LinearMap.comp_apply,
    TensorPower.splitAt_tprod, TensorProduct.map_tmul]

/-- Deconcatenation cuts a tensor word at every position, the two outer positions included. -/
noncomputable def deconcatenation :
    TensorWords R M →ₗ[R] TensorWords R M ⊗[R] TensorWords R M :=
  DirectSum.toModule R ℕ _ (deconcatenationComponent R M)

/-- Deconcatenation is computed length by length. -/
@[simp]
theorem deconcatenation_of (n : ℕ) (x : TensorPower R n M) :
    deconcatenation R M (of R M n x) = deconcatenationComponent R M n x := by
  simp [deconcatenation, of]

section Subword

variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- The tensor word `x a ⊗ ⋯ ⊗ x (a + b - 1)`, of length `b` and starting at position `a`.

It is zero when the requested block runs past the end of `x`, and is `1` when the block is empty
and starts inside the tuple (`a ≤ n`); the intended range of the definition is `a + b ≤ n`. -/
noncomputable def subword {n : ℕ} (x : Fin n → M) (a b : ℕ) : TensorWords R M :=
  if h : a + b ≤ n then
    of R M b (PiTensorProduct.tprod R fun j : Fin b ↦ x ⟨a + j.1, by have := j.isLt; omega⟩)
  else 0

/-- On its intended range, a subword is the pure tensor of the selected block of letters. -/
theorem subword_eq_of_tprod {n : ℕ} (x : Fin n → M) {a b : ℕ} (hab : a + b ≤ n) :
    subword R x a b =
      of R M b
        (PiTensorProduct.tprod R fun j : Fin b ↦ x ⟨a + j.1, by have := j.isLt; omega⟩) := by
  rw [subword, dite_eq_left hab]

/-- A block running past the end of the tuple is zero. -/
@[simp]
theorem subword_eq_zero_of_lt_add {n : ℕ} (x : Fin n → M) {a b : ℕ} (hab : n < a + b) :
    subword R x a b = 0 := by
  rw [subword, dite_eq_right (by omega)]

/-- An empty block inside a tuple is the empty word. -/
@[simp]
theorem subword_length_zero {n : ℕ} (x : Fin n → M) {a : ℕ} (ha : a ≤ n) :
    subword R x a 0 = (1 : TensorWords R M) := by
  rw [subword_eq_of_tprod R x (by omega)]
  rw [one_eq_of_zero]
  exact of_tprod_congr R M fun j ↦ j.elim0

/-- A whole tuple is the subword of full length starting at its beginning. -/
theorem of_tprod_eq_subword {n : ℕ} (x : Fin n → M) :
    of R M n (PiTensorProduct.tprod R x) = subword R x 0 n := by
  rw [subword_eq_of_tprod R x (by omega)]
  exact of_tprod_congr R M fun j ↦ (congrArg x (Fin.ext (Nat.zero_add j.1))).symm

/-- A nonempty block is annihilated by the counit. -/
@[simp]
theorem counit_subword_of_pos {n : ℕ} (x : Fin n → M) {a b : ℕ} (hb : 0 < b) :
    counit R M (subword R x a b) = 0 := by
  by_cases hab : a + b ≤ n
  · rw [subword_eq_of_tprod R x hab, counit_of_of_ne_zero R M (by omega)]
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]

/-- Deconcatenating a block cuts it at each of its positions, the two outer ones included. -/
theorem deconcatenation_subword {n : ℕ} (x : Fin n → M) {a b : ℕ} :
    deconcatenation R M (subword R x a b) =
      ∑ c ∈ Finset.range (b + 1), subword R x a c ⊗ₜ[R] subword R x (a + c) (b - c) := by
  by_cases hab : a + b ≤ n
  · rw [subword_eq_of_tprod R x hab, deconcatenation_of, deconcatenationComponent_tprod]
    let g := fun c ↦ subword R x a c ⊗ₜ[R] subword R x (a + c) (b - c)
    calc
      _ = ∑ i : Fin (b + 1), g i.1 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hi := i.isLt
        dsimp only [g]
        rw [subword_eq_of_tprod R x (a := a) (b := i.1) (by omega),
          subword_eq_of_tprod R x (a := a + i.1) (b := b - i.1) (by omega)]
        congr 1
        exact of_tprod_congr R M fun j ↦
          congrArg x (Fin.ext (Nat.add_assoc a i.1 j.1).symm)
      _ = _ := Fin.sum_univ_eq_sum_range g (b + 1)
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
    symm
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    simp only [Finset.mem_range] at hc
    by_cases hac : a + c ≤ n
    · rw [subword_eq_zero_of_lt_add R x (a := a + c) (b := b - c) (by omega),
        TensorProduct.tmul_zero]
    · rw [subword_eq_zero_of_lt_add R x (a := a) (b := c) (by omega),
        TensorProduct.zero_tmul]

end Subword

/-! ## Coassociativity and counitality -/

section Coassoc

variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- Cutting the left block again gives the sum over all earlier cut positions, written over the
full range of cut positions. -/
private theorem rTensor_deconcatenation_subword {n : ℕ} (y : Fin n → M) (a b : ℕ) {c : ℕ}
    (hc : c ∈ Finset.range (b + 1)) :
    TensorProduct.assoc R (TensorWords R M) (TensorWords R M) (TensorWords R M)
        (LinearMap.rTensor (TensorWords R M) (deconcatenation R M)
          (subword R y a c ⊗ₜ[R] subword R y (a + c) (b - c))) =
      ∑ d ∈ Finset.range (b + 1),
        if d ≤ c then
          subword R y a d ⊗ₜ[R]
            (subword R y (a + d) (c - d) ⊗ₜ[R] subword R y (a + c) (b - c))
        else 0 := by
  simp only [Finset.mem_range] at hc
  rw [LinearMap.rTensor_tmul, deconcatenation_subword R y (a := a) (b := c),
    TensorProduct.sum_tmul, map_sum]
  simp only [TensorProduct.assoc_tmul]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr (Finset.ext fun d ↦ ?_) fun d _ ↦ rfl
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- Cutting the right block again gives the sum over the absolute position `q` of the second cut,
written over the full range of cut positions. -/
private theorem lTensor_deconcatenation_subword {n : ℕ} (y : Fin n → M) (a b : ℕ) {c : ℕ}
    (hc : c ∈ Finset.range (b + 1)) :
    LinearMap.lTensor (TensorWords R M) (deconcatenation R M)
        (subword R y a c ⊗ₜ[R] subword R y (a + c) (b - c)) =
      ∑ q ∈ Finset.range (b + 1),
        if c ≤ q then
          subword R y a c ⊗ₜ[R]
            (subword R y (a + c) (q - c) ⊗ₜ[R] subword R y (a + q) (b - q))
        else 0 := by
  simp only [Finset.mem_range] at hc
  rw [LinearMap.lTensor_tmul, deconcatenation_subword R y (a := a + c) (b := b - c),
    TensorProduct.tmul_sum]
  let g := fun q ↦ subword R y a c ⊗ₜ[R]
    (subword R y (a + c) (q - c) ⊗ₜ[R] subword R y (a + q) (b - q))
  calc
    _ = ∑ e ∈ Finset.Ico 0 (b - c + 1), g (c + e) := by
      rw [Nat.Ico_zero_eq_range]
      refine Finset.sum_congr rfl fun e he ↦ ?_
      simp only [Finset.mem_range] at he
      dsimp only [g]
      have h1 : c + e - c = e := by omega
      have h2 : b - (c + e) = b - c - e := by omega
      rw [h1, h2, Nat.add_assoc]
    _ = ∑ q ∈ Finset.Ico (0 + c) (b - c + 1 + c), g q := Finset.sum_Ico_add g 0 (b - c + 1) c
    _ = ∑ q ∈ Finset.range (b + 1) with c ≤ q, g q := by
      refine Finset.sum_congr (Finset.ext fun q ↦ ?_) fun q _ ↦ rfl
      simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_filter]
      omega
    _ = _ := Finset.sum_filter _ _

/-- Both ways of iterating deconcatenation agree on every block of letters. -/
private theorem deconcatenation_coassoc_subword {n : ℕ} (y : Fin n → M) (a b : ℕ) :
    TensorProduct.assoc R (TensorWords R M) (TensorWords R M) (TensorWords R M)
        (LinearMap.rTensor (TensorWords R M) (deconcatenation R M)
          (deconcatenation R M (subword R y a b))) =
      LinearMap.lTensor (TensorWords R M) (deconcatenation R M)
        (deconcatenation R M (subword R y a b)) := by
  rw [deconcatenation_subword R y (a := a) (b := b)]
  simp only [map_sum]
  rw [Finset.sum_congr rfl fun c hc ↦ rTensor_deconcatenation_subword R y a b hc,
    Finset.sum_congr rfl fun c hc ↦ lTensor_deconcatenation_subword R y a b hc]
  exact Finset.sum_comm

variable (M)

/-- Deconcatenation is coassociative: cutting a tensor word twice gives the same sum of triples of
blocks whether the second cut is taken in the left or in the right factor of the first. -/
theorem deconcatenation_coassoc :
    (TensorProduct.assoc R (TensorWords R M) (TensorWords R M) (TensorWords R M)).toLinearMap ∘ₗ
        LinearMap.rTensor (TensorWords R M) (deconcatenation R M) ∘ₗ deconcatenation R M =
      LinearMap.lTensor (TensorWords R M) (deconcatenation R M) ∘ₗ deconcatenation R M := by
  apply linearMap_ext R M
  intro k y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [of_tprod_eq_subword R y]
  exact deconcatenation_coassoc_subword R y 0 k

/-- `counit` is a left counit for deconcatenation; only the cut with an empty left block
survives. -/
theorem rTensor_counit_comp_deconcatenation :
    LinearMap.rTensor (TensorWords R M) (counit R M) ∘ₗ deconcatenation R M =
      TensorProduct.mk R R (TensorWords R M) 1 := by
  apply linearMap_ext R M
  intro k y
  simp only [LinearMap.comp_apply]
  rw [of_tprod_eq_subword R y, deconcatenation_subword R y, map_sum]
  simp only [LinearMap.rTensor_tmul, Nat.zero_add]
  rw [Finset.sum_eq_single 0]
  · rw [subword_length_zero R y (by omega), counit_one, Nat.sub_zero]
    rfl
  · intro c _ hc
    rw [counit_subword_of_pos R y (Nat.pos_of_ne_zero hc), TensorProduct.zero_tmul]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- `counit` is a right counit for deconcatenation; only the cut with an empty right block
survives. -/
theorem lTensor_counit_comp_deconcatenation :
    LinearMap.lTensor (TensorWords R M) (counit R M) ∘ₗ deconcatenation R M =
      (TensorProduct.mk R (TensorWords R M) R).flip 1 := by
  apply linearMap_ext R M
  intro k y
  simp only [LinearMap.comp_apply]
  rw [of_tprod_eq_subword R y, deconcatenation_subword R y, map_sum]
  simp only [LinearMap.lTensor_tmul, Nat.zero_add]
  rw [Finset.sum_eq_single k]
  · rw [Nat.sub_self, subword_length_zero R y le_rfl, counit_one]
    rfl
  · intro c hc hck
    simp only [Finset.mem_range] at hc
    rw [counit_subword_of_pos R y (a := c) (b := k - c) (by omega), TensorProduct.tmul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- Deconcatenation and the length-zero coefficient are the coalgebra data of tensor words. -/
noncomputable instance instCoalgebraStruct : CoalgebraStruct R (TensorWords R M) where
  comul := deconcatenation R M
  counit := counit R M

/-- The comultiplication of the coalgebra structure is deconcatenation. -/
@[simp]
theorem comul_eq_deconcatenation :
    (CoalgebraStruct.comul : TensorWords R M →ₗ[R] TensorWords R M ⊗[R] TensorWords R M) =
      deconcatenation R M := rfl

/-- The counit of the coalgebra structure is the length-zero coefficient. -/
@[simp]
theorem counit_eq_counit :
    (CoalgebraStruct.counit : TensorWords R M →ₗ[R] R) = counit R M := rfl

/-- Tensor words form a coalgebra over the ground ring. -/
noncomputable instance instCoalgebra : Coalgebra R (TensorWords R M) where
  coassoc := deconcatenation_coassoc R M
  rTensor_counit_comp_comul := rTensor_counit_comp_deconcatenation R M
  lTensor_counit_comp_comul := lTensor_counit_comp_deconcatenation R M

end Coassoc

/-! ## The empty word is group-like -/

/-- Deconcatenating the empty word cuts it in the only way available. -/
@[simp]
theorem deconcatenation_one :
    deconcatenation R M (1 : TensorWords R M) =
      (1 : TensorWords R M) ⊗ₜ[R] (1 : TensorWords R M) := by
  have h0 : (1 : TensorWords R M) = subword R (fun j : Fin 0 ↦ (j.elim0 : M)) 0 0 :=
    (subword_length_zero R _ le_rfl).symm
  rw [h0, deconcatenation_subword]
  simp

/-- The empty word is a group-like element of the tensor coalgebra. -/
theorem isGroupLikeElem_one : IsGroupLikeElem R (1 : TensorWords R M) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp

/-- The canonical coaugmentation, bundling the algebra map as a coalgebra morphism. -/
noncomputable def coaugmentation : R →ₗc[R] TensorWords R M where
  toLinearMap := Algebra.linearMap R (TensorWords R M)
  counit_comp := by
    exact counit_comp_algebraMap R M
  map_comp_comul := by
    ext
    simp only [LinearMap.comp_apply, CommSemiring.comul_apply, TensorProduct.map_tmul,
      Algebra.linearMap_apply, map_one, comul_eq_deconcatenation, deconcatenation_one]

/-- The linear map underlying the canonical coaugmentation is the algebra map. -/
@[simp]
theorem coaugmentation_toLinearMap :
    (coaugmentation R M : R →ₗ[R] TensorWords R M) =
      Algebra.linearMap R (TensorWords R M) := by
  rw [coaugmentation]
  exact CoalgHom.coe_linearMap_mk _ _

/-- The canonical coaugmentation sends a scalar through the algebra map. -/
@[simp]
theorem coaugmentation_apply (r : R) :
    coaugmentation R M r = algebraMap R (TensorWords R M) r := by
  exact (LinearMap.congr_fun (coaugmentation_toLinearMap R M) r).trans
    (Algebra.linearMap_apply R (TensorWords R M) r)

/-! ## Comparison with the reduced tensor coalgebra -/

/-- The words of positive length inside all tensor words. -/
noncomputable def reducedInclusion : ReducedTensorWords R M →ₗ[R] TensorWords R M :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n ↦ of R M n.1

/-- The inclusion of the reduced tensor words keeps each length component. -/
@[simp]
theorem reducedInclusion_of (n : {n : ℕ // 0 < n}) (z : TensorPower R n.1 M) :
    reducedInclusion R M (ReducedTensorWords.of R M n z) = of R M n.1 z := by
  rw [reducedInclusion, ReducedTensorWords.toModule_of]

/-- The retraction of `TauCeti.TensorWords.reducedInclusion` that deletes the empty word. -/
noncomputable def reducedProjection : TensorWords R M →ₗ[R] ReducedTensorWords R M :=
  DirectSum.toModule R ℕ _ fun n ↦
    if h : 0 < n then ReducedTensorWords.of R M ⟨n, h⟩ else 0

/-- The projection keeps every component of positive length. -/
@[simp]
theorem reducedProjection_of_of_pos {n : ℕ} (hn : 0 < n) (z : TensorPower R n M) :
    reducedProjection R M (of R M n z) = ReducedTensorWords.of R M ⟨n, hn⟩ z := by
  rw [reducedProjection, toModule_of, dite_eq_left hn]

/-- The projection deletes the length-zero component. -/
@[simp]
theorem reducedProjection_of_zero (z : TensorPower R 0 M) :
    reducedProjection R M (of R M 0 z) = 0 := by
  rw [reducedProjection, toModule_of, dite_eq_right (by omega), LinearMap.zero_apply]

/-- The projection deletes the empty word. -/
@[simp]
theorem reducedProjection_one : reducedProjection R M (1 : TensorWords R M) = 0 := by
  rw [one_eq_of_zero, reducedProjection_of_zero]

/-- The projection is a retraction of the inclusion. -/
@[simp]
theorem reducedProjection_comp_reducedInclusion :
    reducedProjection R M ∘ₗ reducedInclusion R M = LinearMap.id := by
  apply ReducedTensorWords.linearMap_ext R M
  intro n x
  simp [reducedProjection_of_of_pos R M n.2]

/-- Projecting an included positive-length word returns that word. -/
@[simp]
theorem reducedProjection_reducedInclusion (w : ReducedTensorWords R M) :
    reducedProjection R M (reducedInclusion R M w) = w := by
  rw [← LinearMap.comp_apply, reducedProjection_comp_reducedInclusion, LinearMap.id_apply]

/-- The reduced tensor words inject into all tensor words. -/
theorem reducedInclusion_injective : Function.Injective (reducedInclusion R M) :=
  Function.LeftInverse.injective (g := reducedProjection R M) fun w ↦
    LinearMap.congr_fun (reducedProjection_comp_reducedInclusion R M) w

/-- Every word of positive length lies in the augmentation coideal. -/
@[simp]
theorem counit_comp_reducedInclusion : counit R M ∘ₗ reducedInclusion R M = 0 := by
  apply ReducedTensorWords.linearMap_ext R M
  intro n x
  rw [LinearMap.comp_apply, reducedInclusion_of, counit_of_of_ne_zero R M n.2.ne',
    LinearMap.zero_apply]

/-- The counit vanishes on every positive-length word. -/
@[simp]
theorem counit_reducedInclusion (w : ReducedTensorWords R M) :
    counit R M (reducedInclusion R M w) = 0 := by
  rw [← LinearMap.comp_apply, counit_comp_reducedInclusion, LinearMap.zero_apply]

/-- Tensor words are the empty word together with the words of positive length. -/
theorem reducedInclusion_comp_reducedProjection_add_algebraMap_comp_counit :
    reducedInclusion R M ∘ₗ reducedProjection R M +
        Algebra.linearMap R (TensorWords R M) ∘ₗ counit R M = LinearMap.id := by
  apply linearMap_ext R M
  intro n x
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply,
      reducedProjection_of_zero, map_zero, zero_add, counit_of_zero, Algebra.linearMap_apply,
      algebraMap_apply, LinearEquiv.apply_symm_apply]
  · rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      reducedProjection_of_of_pos R M hn, counit_of_of_ne_zero R M hn.ne', map_zero, add_zero,
      reducedInclusion_of, LinearMap.id_apply]

/-- Every tensor word is the sum of its positive-length part and its length-zero part. -/
@[simp]
theorem reducedInclusion_reducedProjection_add_algebraMap_counit (w : TensorWords R M) :
    reducedInclusion R M (reducedProjection R M w) +
        algebraMap R (TensorWords R M) (counit R M w) = w := by
  have h := LinearMap.congr_fun
    (reducedInclusion_comp_reducedProjection_add_algebraMap_comp_counit R M) w
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Algebra.linearMap_apply] using h

/-- The kernel of the counit is exactly the image of the positive-length words under
`TauCeti.TensorWords.reducedInclusion`. -/
theorem ker_counit :
    LinearMap.ker (counit R M) = LinearMap.range (reducedInclusion R M) := by
  apply le_antisymm
  · intro w hw
    refine ⟨reducedProjection R M w, ?_⟩
    have h := LinearMap.congr_fun
      (reducedInclusion_comp_reducedProjection_add_algebraMap_comp_counit R M) w
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [LinearMap.mem_ker] at hw
    rw [hw, map_zero, add_zero] at h
    exact h
  · rintro _ ⟨w, rfl⟩
    exact LinearMap.mem_ker.2
      (by rw [← LinearMap.comp_apply, counit_comp_reducedInclusion, LinearMap.zero_apply])

section Reduced

variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- A nonempty block is the same word read in either presentation. -/
@[simp]
theorem reducedInclusion_subword {n : ℕ} (x : Fin n → M) {a b : ℕ} (hb : 0 < b) :
    reducedInclusion R M (ReducedTensorWords.subword R x a b) = subword R x a b := by
  by_cases hab : a + b ≤ n
  · rw [ReducedTensorWords.subword_eq_of_tprod R x hb hab, reducedInclusion_of,
      subword_eq_of_tprod R x hab]
  · rw [ReducedTensorWords.subword_eq_zero_of_lt_add R x (by omega),
      subword_eq_zero_of_lt_add R x (by omega), map_zero]

end Reduced

/-- On a word of positive length the coproduct is the reduced coproduct together with the two
degenerate cuts. -/
theorem deconcatenation_comp_reducedInclusion :
    deconcatenation R M ∘ₗ reducedInclusion R M =
      TensorProduct.mk R (TensorWords R M) (TensorWords R M) (1 : TensorWords R M) ∘ₗ
          reducedInclusion R M +
        (TensorProduct.mk R (TensorWords R M) (TensorWords R M)).flip (1 : TensorWords R M) ∘ₗ
          reducedInclusion R M +
        TensorProduct.map (reducedInclusion R M) (reducedInclusion R M) ∘ₗ
          ReducedTensorWords.deconcatenation R M := by
  apply ReducedTensorWords.linearMap_ext R M
  intro n x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
    LinearMap.flip_apply]
  rw [reducedInclusion_of, of_tprod_eq_subword R x,
    ReducedTensorWords.of_tprod_eq_subword R n.2 x, deconcatenation_subword R x,
    ReducedTensorWords.deconcatenation_subword R x, map_sum]
  have hn := n.2
  have hsplit : Finset.range (n.1 + 1) = insert 0 (insert n.1 (Finset.Ioo 0 n.1)) := by
    ext c
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  have h0 : (0 : ℕ) ∉ insert n.1 (Finset.Ioo 0 n.1) := by
    simp only [Finset.mem_insert, Finset.mem_Ioo]
    omega
  have h1 : n.1 ∉ Finset.Ioo 0 n.1 := by simp
  rw [hsplit, Finset.sum_insert h0, Finset.sum_insert h1]
  simp only [Nat.zero_add, Nat.sub_zero, Nat.sub_self]
  rw [subword_length_zero R x (a := 0) (Nat.zero_le _),
    subword_length_zero R x (a := n.1) le_rfl, ← add_assoc]
  congr 1
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  simp only [Finset.mem_Ioo] at hc
  rw [TensorProduct.map_tmul, reducedInclusion_subword R x hc.1,
    reducedInclusion_subword R x (b := n.1 - c) (by omega)]

/-- The coproduct of an included positive-length word is its two degenerate cuts together with the
included reduced coproduct. -/
theorem deconcatenation_comp_reducedInclusion_apply (w : ReducedTensorWords R M) :
    deconcatenation R M (reducedInclusion R M w) =
      (1 : TensorWords R M) ⊗ₜ[R] reducedInclusion R M w
        + reducedInclusion R M w ⊗ₜ[R] (1 : TensorWords R M)
        + TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
            (ReducedTensorWords.deconcatenation R M w) := by
  have h := LinearMap.congr_fun (deconcatenation_comp_reducedInclusion R M) w
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
    LinearMap.flip_apply] at h
  exact h

/-- Projecting both factors of the coproduct of a positive-length word recovers reduced
deconcatenation. -/
@[simp]
theorem map_reducedProjection_deconcatenation_reducedInclusion (w : ReducedTensorWords R M) :
    TensorProduct.map (reducedProjection R M) (reducedProjection R M)
        (deconcatenation R M (reducedInclusion R M w)) =
      ReducedTensorWords.deconcatenation R M w := by
  rw [deconcatenation_comp_reducedInclusion_apply, map_add, map_add]
  simp only [TensorProduct.map_tmul, reducedProjection_one,
    reducedProjection_reducedInclusion, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    zero_add, TensorProduct.map_map, reducedProjection_comp_reducedInclusion,
    TensorProduct.map_id, LinearMap.id_apply]

/-- Projecting both factors after deconcatenating an included positive-length word is reduced
deconcatenation. -/
@[simp]
theorem map_reducedProjection_comp_deconcatenation_comp_reducedInclusion :
    TensorProduct.map (reducedProjection R M) (reducedProjection R M) ∘ₗ
        deconcatenation R M ∘ₗ reducedInclusion R M =
      ReducedTensorWords.deconcatenation R M := by
  apply LinearMap.ext
  exact map_reducedProjection_deconcatenation_reducedInclusion R M

/-- The letters of a tensor word are primitive.

This fires ahead of `TauCeti.TensorWords.deconcatenation_of`, whose right-hand side
`deconcatenationComponent` has no computation rule for an abstract tensor power. -/
@[simp high]
theorem deconcatenation_of_length_one (z : TensorPower R 1 M) :
    deconcatenation R M (of R M 1 z) =
      (1 : TensorWords R M) ⊗ₜ[R] of R M 1 z +
        of R M 1 z ⊗ₜ[R] (1 : TensorWords R M) := by
  have h := deconcatenation_comp_reducedInclusion_apply R M
    (ReducedTensorWords.of R M ⟨1, Nat.one_pos⟩ z)
  rw [reducedInclusion_of, ReducedTensorWords.deconcatenation_of_length_one R M z,
    map_zero, add_zero] at h
  exact h

end TensorWords

end TauCeti
