/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.Range
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coderivation
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Graded coderivations of the reduced tensor coalgebra

Let `M` carry an internal integer grading `G`, and let `T = ⨁_{n ≥ 1} M^{⊗ n}` be the reduced
tensor coalgebra of `TauCeti.ReducedTensorWords`.  The ungraded correspondence of
`TauCeti.ReducedTensorWords.coderivEquivTaylor` matches coderivations with their Taylor components,
but an operation of degree `q` assembles into a *`q`-twisted* coderivation: it satisfies the
co-Leibniz rule with a Koszul sign, cutting its value giving the cut halves with `b` applied to
one half, scaled by the sign `(-1)^(q * |w₁|)` when `b` is applied to the right half `w₂`.  This
file packages that signed correspondence. Homogeneity of degree `q` is separate, and is recorded
by `isHomogeneous_gradedCoderiv`.

The sign is not carried by hand.  The Koszul twist `TauCeti.InternalGrading.koszulTwist G q`
scales each homogeneous element of degree `e` by `(-1)^(q * e)`, and the letterwise extension
`ReducedTensorWords.map` lifts it to words.  Precomposing each Taylor summand with the twist of the
letters preceding its collapsed block produces exactly the signs
`(-1)^(q * (|x₀| + ⋯ + |x_{p - 1}|))` of the classical suspended formula (0-based positions; `p` is
the number of letters preceding the collapsed block), and the twisted co-Leibniz identity takes
the sign-free shape

`Δ ∘ b = (b ⊗ 1) ∘ Δ + (1 ⊗ b) ∘ (τ ⊗ 1) ∘ Δ`

in which `τ = ReducedTensorWords.map (InternalGrading.koszulTwist G q)` acts on the left half of
every cut.  For
`q = 0` this reduces term by term to the ungraded theory: the twist of parameter zero is the
identity, so a `0`-twisted graded coderivation is exactly an ungraded coderivation.  The predicate
`IsGradedCoderivation G q` is this `q`-twisted co-Leibniz condition; it does not include
homogeneity of `b`, and it depends only on the parity of `q`.  Homogeneity is recorded separately
by `isHomogeneous_gradedCoderiv` and `IsGradedCoderivation.isHomogeneous`.

## Main definitions

* `TauCeti.ReducedTensorWords.gradedCoderiv`: the graded Taylor expansion of a linear map `F` from
  words to letters, at twist parameter `q`.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation`: the `q`-twisted co-Leibniz identity of an
  endomorphism of words.
* `TauCeti.ReducedTensorWords.gradedPiece`: the words whose letters have total degree `D`.
* `TauCeti.ReducedTensorWords.gradedCoderivations`: the submodule of `q`-twisted coderivations.

## Main results

* `TauCeti.ReducedTensorWords.isGradedCoderivation_gradedCoderiv`,
  `TauCeti.ReducedTensorWords.letter_comp_gradedCoderiv`: `gradedCoderiv G F q` is a `q`-twisted
  coderivation with letter component `F`.
* `TauCeti.ReducedTensorWords.IsGradedCoderivation.eq_of_letter_comp_eq`: a graded coderivation is
  determined by its letter component.
* `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderiv`: if `F` raises degrees by `r` then so
  does `gradedCoderiv G F q`, independently of the twist parameter.
* `TauCeti.ReducedTensorWords.gradedCoderivEquivTaylor`: the `q`-twisted coderivations form a
  submodule identified, through the letter components, with the maps from tensor words to letters.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/
public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti



section GradedCoderiv

open ReducedTensorWords InternalGrading

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The endomorphism of length-`n` tensor words twisting the first `p` letters: precomposing the
ungraded Taylor summand at position `p` with it produces the graded, Koszul-signed summand. -/
private noncomputable def ReducedTensorWords.gradedTwistFirst (G : InternalGrading R M) (q : ℤ)
    (n p : ℕ) :
    TensorPower R n M →ₗ[R] TensorPower R n M :=
  PiTensorProduct.map (s := fun _ : Fin n => M) (t := fun _ : Fin n => M)
    fun i => if i.val < p then koszulTwist G q else LinearMap.id

/-- The `(p, d)` summand of the graded Taylor expansion of `F` at twist parameter `q`: the ungraded
summand, precomposed with the twist of the letters preceding the collapsed block. -/
private noncomputable def ReducedTensorWords.gradedCoderivSummand (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) (n p d : ℕ) :
    TensorPower R n M →ₗ[R] ReducedTensorWords R M :=
  coderivSummand R F n p d ∘ₗ gradedTwistFirst G q n p

/-- On a pure tensor word, the graded Taylor summand splices the value of `F` on the collapsed
block into the tuple whose first `p` letters carry the Koszul twist. -/
private theorem ReducedTensorWords.gradedCoderivSummand_tprod (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n p d : ℕ} (hd : 0 < d) (hpd : p + d ≤ n)
    (x : Fin n → M) :
    gradedCoderivSummand G F q n p d (PiTensorProduct.tprod R x)
      = splice R (twistedTuple G q x 0 p) 0 n p d (F (subword R x p d)) := by
  have hsub : subword R
      (fun i => (if i.val < p then koszulTwist G q else LinearMap.id) (x i)) p d =
      subword R x p d :=
    subword_congr R _ _ (by omega) (by omega) fun j hj ↦ by
      simp [show ¬(p + j < p) from by omega]
  rw [gradedCoderivSummand, LinearMap.coe_comp, Function.comp_apply, gradedTwistFirst,
    PiTensorProduct.map_tprod, coderivSummand_tprod R F hd hpd, hsub]
  refine splice_congr R _ _ _ (by omega) (by omega) fun j hj ↦ ?_
  simp only [twistedTuple_apply, Nat.zero_le, true_and]
  by_cases hj' : j < p <;> simp [hj']

/-- The graded Taylor expansion of a map `F` from words to single letters, at twist parameter `q`:
on a tensor word it collapses each block to the letter that `F` produces from it, composed with the
twist of the letters preceding the block.

If the inputs are homogeneous of degrees `𝒟 i`, the collapse at position `p` thus carries the
Koszul sign `(-1)^(q * (𝒟 0 + ⋯ + 𝒟 (p - 1)))`, because the Koszul twist scales each of those
letters by its own sign factor; see `gradedCoderiv_of_tprod_of_homogeneous`. -/
noncomputable def ReducedTensorWords.gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M :=
  DirectSum.toModule R {n : ℕ // 0 < n} _ fun n =>
    ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), gradedCoderivSummand G F q n.1 p d

private theorem gradedCoderiv_of (G : InternalGrading R M) (F : ReducedTensorWords R M →ₗ[R] M)
    (q : ℤ) (n : {n : ℕ // 0 < n}) (z : TensorPower R n.1 M) :
    gradedCoderiv G F q (of R M n z)
      = ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          gradedCoderivSummand G F q n.1 p d z := by
  rw [gradedCoderiv, toModule_of]
  simp only [LinearMap.sum_apply]

/-- Evaluation of the graded Taylor expansion on a pure tensor word: every summand collapses one
block and twists the letters preceding it. -/
theorem ReducedTensorWords.gradedCoderiv_of_tprod (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n : ℕ} (hn : 0 < n) (x : Fin n → M) :
    gradedCoderiv G F q (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x))
      = ∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1),
          splice R (twistedTuple G q x 0 p) 0 n p d (F (subword R x p d)) := by
  rw [gradedCoderiv_of]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases h : 0 < d ∧ p + d ≤ n
  · rw [gradedCoderivSummand_tprod G F q h.1 h.2 x]
  · rw [gradedCoderivSummand, coderivSummand_eq_zero R F (by tauto), LinearMap.zero_comp,
      LinearMap.zero_apply]
    exact (splice_eq_zero R (twistedTuple G q x 0 p) _ (by tauto)).symm

private theorem negOnePow_sum_range {R : Type uR} [CommRing R] (q : ℤ) (deg : ℕ → ℤ) (p : ℕ) :
    (((q * ∑ j ∈ Finset.range p, deg j).negOnePow : ℤ) : R) =
      ∏ j ∈ Finset.range p, (((q * deg j).negOnePow : ℤ) : R) := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ, mul_add, Int.negOnePow_add,
        Units.val_mul, Int.cast_mul, ih]

/-- Splicing a Koszul-twisted prefix of a homogeneous tuple produces the Koszul sign of that
prefix times the untwisted splice. -/
theorem ReducedTensorWords.splice_twistedTuple_smul (G : InternalGrading R M) (q : ℤ)
    {n : ℕ} (x : Fin n → M) (𝒟 : Fin n → ℤ) (hx : ∀ i, x i ∈ G.piece (𝒟 i))
    (p d : ℕ) (e : M) :
    splice R (twistedTuple G q x 0 p) 0 n p d e =
      (((q * ∑ j ∈ Finset.range p, if h : j < n then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
        splice R x 0 n p d e := by
  by_cases hfit : 0 < d ∧ p + d ≤ n
  · have hp : p ≤ n := by omega
    rw [splice_eq_of_tprod R (twistedTuple G q x 0 p) e hfit.1 hfit.2 (by omega),
      splice_eq_of_tprod R x e hfit.1 hfit.2 (by omega)]
    let deg : ℕ → ℤ := fun j => if h : j < n then 𝒟 ⟨j, h⟩ else 0
    let c : Fin (n + 1 - d) → R := fun j =>
      if j.val < p then (((q * deg j.val).negOnePow : ℤ) : R) else 1
    have hletters :
        (fun j : Fin (n + 1 - d) =>
          if _ : j.val < p then twistedTuple G q x 0 p ⟨0 + j.val, by omega⟩
          else if _ : j.val = p then e
          else twistedTuple G q x 0 p ⟨0 + (j.val + d - 1), by omega⟩) =
          fun j => c j •
            (if _ : j.val < p then x ⟨0 + j.val, by omega⟩
            else if _ : j.val = p then e
            else x ⟨0 + (j.val + d - 1), by omega⟩) := by
      funext j
      by_cases hjp : j.val < p
      · rw [dite_eq_left hjp, dite_eq_left hjp]
        simp only [c, hjp, ite_true, twistedTuple_apply, Nat.zero_add, and_true]
        rw [ite_eq_left (Nat.zero_le j.val),
          koszulTwist_apply_of_mem G (hx ⟨j.val, by omega⟩) q]
        simp [deg, show j.val < n from by omega]
      · rw [dite_eq_right hjp, dite_eq_right hjp]
        simp only [c, hjp, ite_false, one_smul, twistedTuple_apply, Nat.zero_add]
        by_cases hje : j.val = p
        · simp [hje]
        · rw [dite_eq_right hje, dite_eq_right hje,
            ite_eq_right (show ¬(0 ≤ j.val + d - 1 ∧ j.val + d - 1 < p) from by omega)]
    rw [hletters, (PiTensorProduct.tprod R).map_smul_univ, map_smul]
    congr 1
    have hprod : ∏ j : Fin (n + 1 - d), c j =
        (((q * ∑ j ∈ Finset.range p, deg j).negOnePow : ℤ) : R) := by
      rw [Fin.prod_univ_eq_prod_range (f := fun k : ℕ =>
          if k < p then (((q * deg k).negOnePow : ℤ) : R) else 1),
        show n + 1 - d = p + (1 + (n - p - d)) from by omega,
        Finset.prod_range_add, Finset.prod_range_add, Finset.prod_range_one]
      have s1 : ∏ x ∈ Finset.range p,
          (if x < p then (((q * deg x).negOnePow : ℤ) : R) else 1) =
          ∏ x ∈ Finset.range p, (((q * deg x).negOnePow : ℤ) : R) :=
        Finset.prod_congr rfl fun j hj ↦ by simp [Finset.mem_range.mp hj]
      have s2 : ∏ x ∈ Finset.range (n - p - d),
          (if p + (1 + x) < p then (((q * deg (p + (1 + x))).negOnePow : ℤ) : R) else 1) = 1 :=
        Finset.prod_eq_one fun j _ ↦ by simp
      have s3 : (if p + 0 < p then (((q * deg (p + 0)).negOnePow : ℤ) : R) else 1) = 1 := by simp
      rw [s1, s2, s3, mul_one, mul_one, negOnePow_sum_range]
    simpa [deg] using hprod
  · rw [splice_eq_zero R _ e (by tauto), splice_eq_zero R x e (by tauto), smul_zero]

/-- Evaluation of the graded Taylor expansion on a pure tensor of homogeneous letters: each
summand is the corresponding untwisted splice, scaled by the Koszul sign
`(-1)^(q * (𝒟 0 + ⋯ + 𝒟 (p - 1)))` of the letters preceding the collapsed block. -/
theorem ReducedTensorWords.gradedCoderiv_of_tprod_of_homogeneous (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n : ℕ} (hn : 0 < n) (x : Fin n → M)
    (𝒟 : Fin n → ℤ) (hx : ∀ i, x i ∈ G.piece (𝒟 i)) :
    gradedCoderiv G F q (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)) =
      ∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1),
        (((q * ∑ j ∈ Finset.range p, if h : j < n then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          splice R x 0 n p d (F (subword R x p d)) := by
  rw [gradedCoderiv_of_tprod]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun d _ ↦
    splice_twistedTuple_smul G q x 𝒟 hx p d _

/-- Evaluation of a Taylor summand on a block read out of a longer tuple: the same transport as
for the ungraded summands, with the twisted tuple carried along. -/
private theorem ReducedTensorWords.gradedCoderivSummand_tprod_of_eq (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n b : ℕ} (x : Fin n → M) (y : Fin b → M)
    {a : ℕ} (hab : a + b ≤ n)
    (hy : ∀ j : Fin b, y j = x ⟨a + j.val, by omega⟩)
    (p d : ℕ) :
    gradedCoderivSummand G F q b p d (PiTensorProduct.tprod R y)
      = splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) := by
  by_cases h : 0 < d ∧ p + d ≤ b
  · have hy' : ∀ (j : ℕ) (hj : j < b),
        (if (⟨j, hj⟩ : Fin b).val < p then koszulTwist G q else LinearMap.id) (y ⟨j, hj⟩) =
          twistedTuple G q x a p ⟨a + j, by omega⟩ := by
      intro j hj
      have hyj := hy ⟨j, hj⟩
      by_cases hj' : j < p
      · simp [hj', hyj, show a ≤ a + j from by omega,
          show a + j < a + p from by omega]
      · simp [hj', hyj, show ¬(a + j < a + p) from by omega]
    have hsub : subword R (twistedTuple G q x a p) (a + p) d = subword R x (a + p) d :=
      subword_congr R _ _ (by omega) (by omega) fun j hj ↦ by
        simp
    rw [gradedCoderivSummand, LinearMap.coe_comp, Function.comp_apply, gradedTwistFirst,
      PiTensorProduct.map_tprod,
      coderivSummand_tprod_of_eq R F (twistedTuple G q x a p) _ hab hy' p d, hsub]
  · rw [gradedCoderivSummand, coderivSummand_eq_zero R F (by tauto), LinearMap.zero_comp,
      LinearMap.zero_apply, splice_eq_zero_of_not_fits R _ _ (by tauto)]

/-- Evaluation of the graded Taylor expansion on a block of a pure tensor word: the same sums as
for the ungraded `coderiv_subword`, with each spliced tuple twisted before the block that
collapses.  The two ranges may be taken as large as convenient, since a summand whose collapsed
block does not fit vanishes. -/
theorem ReducedTensorWords.gradedCoderiv_subword (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n : ℕ} (x : Fin n → M) {a b K : ℕ}
    (hK : b ≤ K) :
    gradedCoderiv G F q (subword R x a b)
      = ∑ p ∈ Finset.range K, ∑ d ∈ Finset.range (K + 1),
          splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) := by
  by_cases hab : a + b ≤ n
  · have hvanish : ∀ p d : ℕ, b ≤ p ∨ b < d →
        splice R (twistedTuple G q x a p) a b p d (F (subword R x (a + p) d)) = 0 :=
      fun p d h ↦ splice_eq_zero_of_not_fits R (twistedTuple G q x a p) _ (by omega)
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [subword_length_zero, map_zero]
      exact (Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
        hvanish p d (Or.inl (Nat.zero_le p))).symm
    rw [subword_eq_of_tprod R x hb hab, gradedCoderiv_of,
      ← sum_sum_range_eq_of_eq_zero_right hK _ hvanish]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun d _ ↦
      gradedCoderivSummand_tprod_of_eq G F q x (fun j : Fin b => x ⟨a + j, by omega⟩) hab
        (fun j ↦ rfl) p d
  · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero]
    symm
    exact Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
      splice_eq_zero_of_length_lt_add R (twistedTuple G q x a p)
        (F (subword R x (a + p) d)) (by omega)


/-! ### The grading by total letter degree -/

/-- The words of total degree `D`: the span of the pure tensor words whose letters lie in
homogeneous pieces the degrees of which add up to `D`. -/
noncomputable def ReducedTensorWords.gradedPiece (G : InternalGrading R M) (D : ℤ) :
    Submodule R (ReducedTensorWords R M) :=
  Submodule.span R {z | ∃ (n : ℕ) (_hn : 0 < n) (𝒟 : Fin n → ℤ) (x : Fin n → M),
    (∀ i, x i ∈ G.piece (𝒟 i)) ∧ (∑ i, 𝒟 i) = D ∧
      z = of R M ⟨n, _hn⟩ (PiTensorProduct.tprod R x)}

/-- Induction on membership in `gradedPiece`: a consumer may apply this in place of
`Submodule.span_induction`, whose span is sealed behind the definition. -/
theorem ReducedTensorWords.gradedPiece_induction {G : InternalGrading R M} {D : ℤ}
    {motive : ReducedTensorWords R M → Prop} {z : ReducedTensorWords R M}
    (hz : z ∈ gradedPiece G D)
    (mem : ∀ (n : ℕ) (hn : 0 < n) (𝒟 : Fin n → ℤ) (x : Fin n → M),
      (∀ i, x i ∈ G.piece (𝒟 i)) → (∑ i, 𝒟 i) = D →
        motive (of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x)))
    (zero : motive 0)
    (add : ∀ u v, u ∈ gradedPiece G D → v ∈ gradedPiece G D → motive u → motive v →
      motive (u + v))
    (smul : ∀ (a : R) u, u ∈ gradedPiece G D → motive u → motive (a • u)) :
    motive z := by
  induction hz using Submodule.span_induction with
  | mem _ hw =>
    obtain ⟨n, hn, 𝒟, x, hx, hD, rfl⟩ := hw
    exact mem n hn 𝒟 x hx hD
  | zero => exact zero
  | add u v hu hv ihu ihv => exact add u v hu hv ihu ihv
  | smul a u hu ih => exact smul a u hu ih

/-- A pure tensor word of homogeneous letters of degrees `𝒟 i` lies in the graded piece of total
degree `∑ i, 𝒟 i`. -/
theorem ReducedTensorWords.mem_gradedPiece_of_tprod (G : InternalGrading R M) {n : ℕ} (hn : 0 < n)
    (x : Fin n → M) (𝒟 : Fin n → ℤ) (h𝒟 : ∀ i, x i ∈ G.piece (𝒟 i)) :
    of R M ⟨n, hn⟩ (PiTensorProduct.tprod R x) ∈ gradedPiece G (∑ i, 𝒟 i) :=
  Submodule.subset_span ⟨n, hn, 𝒟, x, h𝒟, rfl, rfl⟩

/-- Splicing one homogeneous letter into a word of homogeneous letters stays inside the graded
piece: the total degree is that of the untouched prefix and suffix plus the degree of the new
letter.  The degree family is indexed by absolute positions, since splicing shifts them. -/
theorem ReducedTensorWords.splice_mem_gradedPiece (G : InternalGrading R M) {n : ℕ}
    (x : Fin n → M) (𝒟 : ℕ → ℤ) (h𝒟 : ∀ i : Fin n, x i ∈ G.piece (𝒟 i))
    (p d : ℕ) {E : ℤ} {e : M} (he : e ∈ G.piece E) (hpd : p + d ≤ n) :
    splice R x 0 n p d e ∈ gradedPiece G
      ((∑ j ∈ Finset.range p, 𝒟 j) + E +
        ∑ j ∈ Finset.range (n - p - d), 𝒟 (p + d + j)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [splice_zero_length]
    exact Submodule.zero_mem _
  · have hidx : ∑ i : Fin (n + 1 - d),
        (fun j : Fin (n + 1 - d) =>
          if j.val < p then 𝒟 j.val else if j.val = p then E else 𝒟 (j.val + d - 1)) i =
        (∑ j ∈ Finset.range p, 𝒟 j) + E +
          ∑ j ∈ Finset.range (n - p - d), 𝒟 (p + d + j) := by
      rw [Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ => if k < p then 𝒟 k else if k = p then E else 𝒟 (k + d - 1)),
        show n + 1 - d = p + (1 + (n - p - d)) from by omega, Finset.sum_range_add,
        Finset.sum_range_add, Finset.sum_range_one]
      have s1 : ∑ x ∈ Finset.range p,
          (if x < p then 𝒟 x else if x = p then E else 𝒟 (x + d - 1))
          = ∑ x ∈ Finset.range p, 𝒟 x :=
        Finset.sum_congr rfl fun j hj ↦ by simp [Finset.mem_range.mp hj]
      have s2 : ∑ x ∈ Finset.range (n - p - d),
          (if p + (1 + x) < p then 𝒟 (p + (1 + x))
            else if p + (1 + x) = p then E else 𝒟 (p + (1 + x) + d - 1))
          = ∑ x ∈ Finset.range (n - p - d), 𝒟 (p + d + x) :=
        Finset.sum_congr rfl fun j _ ↦ by
          simp [show p + (1 + j) + d - 1 = p + d + j from by omega]
      rw [s1, s2,
        show (if p + 0 < p then 𝒟 (p + 0)
            else if p + 0 = p then E else 𝒟 (p + 0 + d - 1)) = E from by simp]
      abel
    rw [splice_eq_of_tprod R x e hd hpd (by omega)]
    have step := mem_gradedPiece_of_tprod G (by omega)
      (fun j : Fin (n + 1 - d) =>
        dite (j.val < p) (fun _ => x ⟨(0 : ℕ) + j.val, by have := j.isLt; omega⟩)
          (fun _ =>
            dite (j.val = p) (fun _ => e)
              (fun _ => x ⟨(0 : ℕ) + (j.val + d - 1), by have := j.isLt; have := hpd; omega⟩)))
      (fun j : Fin (n + 1 - d) =>
        if j.val < p then 𝒟 j.val else if j.val = p then E else 𝒟 (j.val + d - 1))
      (by
        intro j
        split_ifs with h₁ h₂
        · have h := h𝒟 ⟨j.val, by have := j.isLt; omega⟩
          simpa using h
        · exact he
        · have h := h𝒟 ⟨j.val + d - 1, by have := j.isLt; have := hpd; omega⟩
          simpa using h)
    rw [hidx] at step
    exact step

/-- If `F` raises total degrees by `r`, so does its graded Taylor expansion, independently of
the twist parameter `q`: for every `D`, the map `gradedCoderiv G F q` sends `gradedPiece G D`
into `gradedPiece G (D + r)`. The twist preserves each homogeneous piece. -/
theorem ReducedTensorWords.isHomogeneous_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q r : ℤ)
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (fun e => G.piece e) r) :
    LinearMap.IsHomogeneous (gradedCoderiv G F q) (gradedPiece G) (gradedPiece G) r := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, hn, 𝒟, x, hx, hD, rfl⟩ := hw
    rw [← hD, gradedCoderiv_of_tprod G F q hn x]
    refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun d _ => ?_
    by_cases hfit : 0 < d ∧ p + d ≤ n
    · -- extend the degree family to all absolute positions, so that splicing can shift it
      set g : ℕ → ℤ := fun k => if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hgdef
      have hg : ∀ i : Fin n, g i.val = 𝒟 i := fun i => by simp [hgdef]
      -- the twist keeps every letter inside its original piece
      have ht : ∀ i : Fin n, twistedTuple G q x 0 p i ∈ G.piece (g i.val) := fun i => by
        rw [hg i]
        simp only [twistedTuple_apply, Nat.zero_le, true_and, Nat.zero_add]
        by_cases hi : i.val < p
        · simp only [hi, ite_true]
          exact koszulTwist_mem_piece G (hx i) q
        · simp only [hi, ite_false]
          exact hx i
      -- the collapsed block is a word of total degree ∑_{j < d} g (p + j)
      have hsub : subword R x p d ∈ gradedPiece G (∑ j ∈ Finset.range d, g (p + j)) := by
        have h := mem_gradedPiece_of_tprod G hfit.1
          (fun j : Fin d => x ⟨p + j.val, by omega⟩)
          (fun j : Fin d => g (p + j.val))
          (fun j => by rw [hg ⟨p + j.val, by omega⟩]; exact hx _)
        rw [subword_eq_of_tprod R x hfit.1 hfit.2]
        rw [Fin.sum_univ_eq_sum_range (f := fun k : ℕ => g (p + k))] at h
        exact h
      have hFe : F (subword R x p d) ∈ G.piece ((∑ j ∈ Finset.range d, g (p + j)) + r) :=
        hF.map_mem hsub
      have idx : (∑ j ∈ Finset.range p, g j) +
          ((∑ j ∈ Finset.range d, g (p + j)) + r) +
          ∑ j ∈ Finset.range (n - p - d), g (p + d + j) = (∑ i, 𝒟 i) + r := by
        have hgsum : (∑ i, 𝒟 i) = ∑ j ∈ Finset.range n, g j := by
          rw [← Fin.sum_univ_eq_sum_range (f := g)]
          exact Finset.sum_congr rfl fun i _ => (hg i).symm
        rw [hgsum, sum_range_add_add g hfit.2]
        abel
      have step := splice_mem_gradedPiece G (twistedTuple G q x 0 p) g ht p d hFe hfit.2
      rwa [idx] at step
    · rw [splice_eq_zero R (twistedTuple G q x 0 p) _ (by tauto)]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a u _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih

/-! ### Graded coderivations -/

section Predicate

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- A *graded coderivation* of twist parameter `q` of the reduced tensor coalgebra: an
endomorphism `b` satisfying the co-Leibniz rule with the Koszul sign of the left cut half,

`Δ ∘ b = (b ⊗ 1) ∘ Δ + (1 ⊗ b) ∘ (τ ⊗ 1) ∘ Δ`,

in which `τ = ReducedTensorWords.map (InternalGrading.koszulTwist G q)` is the letterwise
extension of the Koszul twist and acts on the left half of every cut.  This is only the twisted
co-Leibniz condition, not a homogeneity requirement on `b`; it depends only on the parity of `q`.
On a word `z` of homogeneous letters, summing over cuts `w₁ ⊗ w₂` of `z`,

`Δ (b z) = ∑ (b w₁ ⊗ w₂ + (-1)^(q * |w₁|) • (w₁ ⊗ b w₂))`,

the classical signed co-Leibniz rule.  For `q = 0` the twist is the identity and this is plain
`IsCoderivation`. Homogeneity of degree `r` is recorded by
`IsGradedCoderivation.isHomogeneous`. -/
def ReducedTensorWords.IsGradedCoderivation (G : InternalGrading R M) (q : ℤ)
    (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) : Prop :=
  deconcatenation R M ∘ₗ b =
    LinearMap.rTensor (ReducedTensorWords R M) b ∘ₗ deconcatenation R M +
      (LinearMap.lTensor (ReducedTensorWords R M) b ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q))) ∘ₗ
        deconcatenation R M

variable {G}

/-- The co-Leibniz identity of a graded coderivation, applied to an element. -/
theorem ReducedTensorWords.IsGradedCoderivation.deconcatenation_apply {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G q b) (z : ReducedTensorWords R M) :
    deconcatenation R M (b z) =
      LinearMap.rTensor (ReducedTensorWords R M) b (deconcatenation R M z) +
        LinearMap.lTensor (ReducedTensorWords R M) b
          (LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q))
            (deconcatenation R M z)) := by
  have h := congrArg (fun f : _ →ₗ[_] _ => f z) hb
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] using h

/-- The co-Leibniz identity of a graded coderivation, as a reusable `Iff`: this exposes the body
of the predicate to consumers in other modules, for which the definition's body is not exposed. -/
theorem ReducedTensorWords.isGradedCoderivation_iff {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    IsGradedCoderivation G q b ↔
      (deconcatenation R M ∘ₗ b =
        LinearMap.rTensor (ReducedTensorWords R M) b ∘ₗ deconcatenation R M +
          (LinearMap.lTensor (ReducedTensorWords R M) b ∘ₗ
              LinearMap.rTensor (ReducedTensorWords R M)
                (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q))) ∘ₗ
            deconcatenation R M) :=
  Iff.rfl

/-- On a block of a pure tensor word, twisting letterwise is the twisted tuple read in place. -/
private theorem map_twist_subword (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) {a b : ℕ} (hab : a + b ≤ n) :
    ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q) (subword R x a b) =
      subword R (twistedTuple G q x a b) a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [subword_length_zero, map_zero, subword_length_zero]
  · rw [subword_eq_of_tprod R x hb hab, map_of_tprod,
      subword_eq_of_tprod R (twistedTuple G q x a b) hb hab]
    refine of_tprod_congr R M _ rfl fun j => ?_
    have hj := j.isLt
    simp only [twistedTuple_apply, Fin.val_cast]
    rw [ite_eq_left (show a ≤ a + j.val ∧ a + j.val < a + b from by omega)]

/-- A `q`-twisted graded coderivation of the reduced tensor coalgebra is determined by its letter
component, that is by its composite with the projection onto single letters: two such coderivations
whose letter components agree are equal.  This is the signed analogue of
`TauCeti.ReducedTensorWords.IsCoderivation.eq_of_letter_comp_eq`. -/
theorem ReducedTensorWords.IsGradedCoderivation.eq_of_letter_comp_eq {q : ℤ}
    {b₁ b₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (h₁ : IsGradedCoderivation G q b₁) (h₂ : IsGradedCoderivation G q b₂)
    (hl : letter R M ∘ₗ b₁ = letter R M ∘ₗ b₂) : b₁ = b₂ :=
  eq_of_letter_comp_eq_of_twist h₁ h₂ hl

end Predicate


/-- The words `twistedTuple G q x 0 m` and `twistedTuple G q x 0 c` agree on their first `c`
letters whenever `c ≤ m ≤ n`, since twisting only affects positions below the twist length. -/
private theorem subword_twistedTuple_congr (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) {m c : ℕ} (hcm : c ≤ m) (hm : m ≤ n) :
    subword R (twistedTuple G q x 0 m) 0 c = subword R (twistedTuple G q x 0 c) 0 c := by
  refine subword_congr R (twistedTuple G q x 0 m) (twistedTuple G q x 0 c)
    (by omega) (by omega) fun j hj ↦ ?_
  simp only [twistedTuple_apply, Nat.zero_le, true_and, Nat.zero_add]
  rw [ite_eq_left (show j < m from by omega), ite_eq_left hj]

/-- The tuples `twistedTuple G q x 0 (c + p)` and `twistedTuple G q x c p` agree on every letter
from position `c` onward, so splices acting on the letters at and after position `c` coincide. -/
private theorem splice_twistedTuple_congr (G : InternalGrading R M) (q : ℤ) {n : ℕ}
    (x : Fin n → M) {b c p d : ℕ} (hab : c + b ≤ n) (e : M) :
    splice R (twistedTuple G q x 0 (c + p)) c b p d e =
      splice R (twistedTuple G q x c p) c b p d e := by
  refine splice_congr R _ _ _ hab hab fun j hj ↦ ?_
  simp only [twistedTuple_apply, Nat.zero_le, true_and, Nat.zero_add]
  by_cases hj' : j < p
  · have e2 : c ≤ c + j ∧ c + j < c + p := by omega
    rw [ite_eq_left (show c + j < c + p from by omega), ite_eq_left e2]
  · have e2 : ¬(c ≤ c + j ∧ c + j < c + p) := by omega
    rw [ite_eq_right (show ¬(c + j < c + p) from by omega), ite_eq_right e2]

/-- The graded Taylor expansion of any linear map `F` from tensor words to letters is a
`q`-twisted coderivation: the signed analogue of `isCoderivation_coderiv`.  The twist of the
letters preceding each collapsed block produces exactly the Koszul sign `(-1)^(q * |left half|)`
of the co-Leibniz rule, so the identity holds for an arbitrary `F`, homogeneous or not. -/
@[simp]
theorem ReducedTensorWords.isGradedCoderivation_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    IsGradedCoderivation G q (gradedCoderiv G F q) := by
  refine linearMap_ext R M fun n x ↦ ?_
  have hn : 0 < n.1 := n.2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
  rw [of_tprod_eq_subword R hn x]
  -- Both sides expand as triple sums over a cut, a collapsed-block start, and a block length.
  have hLHS : deconcatenation R M (gradedCoderiv G F q (subword R x 0 n.1)) =
      (∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range (p + 1),
          subword R (twistedTuple G q x 0 p) 0 c ⊗ₜ[R]
            splice R (twistedTuple G q x 0 p) c (n.1 - c) (p - c) d (F (subword R x p d))) +
        ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range n.1,
          splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
            subword R (twistedTuple G q x 0 p) c (n.1 - c) := by
    rw [gradedCoderiv_subword G F q x (K := n.1) (le_refl n.1), map_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [deconcatenation_splice R (twistedTuple G q x 0 p)]
    simp only [Nat.zero_add]
  have hdelta : deconcatenation R M (subword R x 0 n.1) =
      ∑ c ∈ Finset.range n.1, subword R x 0 c ⊗ₜ[R] subword R x c (n.1 - c) := by
    rw [deconcatenation_subword R x (a := 0) (b := n.1)]
    simp only [Nat.zero_add]
    exact sum_Ioo_eq_sum_range n.1 _ (by rw [subword_length_zero, TensorProduct.zero_tmul])
  have hRHS : LinearMap.rTensor (ReducedTensorWords R M) (gradedCoderiv G F q)
        (deconcatenation R M (subword R x 0 n.1)) +
      LinearMap.lTensor (ReducedTensorWords R M) (gradedCoderiv G F q)
        (LinearMap.rTensor (ReducedTensorWords R M)
          (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q))
          (deconcatenation R M (subword R x 0 n.1))) =
      (∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
            subword R x c (n.1 - c)) +
        ∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
          subword R (twistedTuple G q x 0 c) 0 c ⊗ₜ[R]
            splice R (twistedTuple G q x c p) c (n.1 - c) p d
              (F (subword R x (c + p) d)) := by
    rw [hdelta, map_sum, map_sum, map_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun c hc ↦ ?_ <;>
      simp only [Finset.mem_range] at hc
    · rw [LinearMap.rTensor_tmul,
        gradedCoderiv_subword G F q x (a := 0) (b := c) (K := n.1) (by omega),
        TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun p _ ↦ by
        rw [TensorProduct.sum_tmul]
        simp only [Nat.zero_add]
    · rw [LinearMap.rTensor_tmul, map_twist_subword G q x (hab := by omega),
        LinearMap.lTensor_tmul,
        gradedCoderiv_subword G F q x (a := c) (b := n.1 - c) (K := n.1) (by omega)]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [TensorProduct.tmul_sum]
  rw [hLHS]
  rw [hRHS]
  -- Blocks collapsed in the left half match the plain co-Leibniz term.
  have hA2 : ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1), ∑ c ∈ Finset.range n.1,
      splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
        subword R (twistedTuple G q x 0 p) c (n.1 - c) =
    ∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
      splice R (twistedTuple G q x 0 p) 0 c p d (F (subword R x p d)) ⊗ₜ[R]
        subword R x c (n.1 - c) := by
    refine Eq.trans (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm) ?_
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun c hc ↦ Finset.sum_congr rfl fun p _ ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [Finset.mem_range] at hc
    by_cases hpc : p + d ≤ c
    · have hrw : subword R (twistedTuple G q x 0 p) c (n.1 - c) = subword R x c (n.1 - c) :=
        subword_congr R _ _ (by omega) (by omega) fun j hj ↦ by
          have h2 : ¬((0:ℕ) ≤ c + j ∧ c + j < 0 + p) := by omega
          simp only [twistedTuple_apply, h2, ite_false]
      simp only [hrw]
    · rw [splice_eq_zero_of_block_lt_add R (twistedTuple G q x 0 p)
        (F (subword R x p d)) (by omega), TensorProduct.zero_tmul,
        TensorProduct.zero_tmul]
  -- Blocks collapsed in the right half match the twisted co-Leibniz term, after reindexing the
  -- absolute block position through the triangle identity.
  have hA1 : ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
      ∑ c ∈ Finset.range (p + 1),
        subword R (twistedTuple G q x 0 p) 0 c ⊗ₜ[R]
          splice R (twistedTuple G q x 0 p) c (n.1 - c) (p - c) d (F (subword R x p d)) =
    ∑ c ∈ Finset.range n.1, ∑ p ∈ Finset.range n.1, ∑ d ∈ Finset.range (n.1 + 1),
      subword R (twistedTuple G q x 0 c) 0 c ⊗ₜ[R]
        splice R (twistedTuple G q x c p) c (n.1 - c) p d
          (F (subword R x (c + p) d)) := by
    have hg : ∀ c p : ℕ, n.1 ≤ c + p →
        (∑ d ∈ Finset.range (n.1 + 1),
            subword R (twistedTuple G q x 0 c) 0 c ⊗ₜ[R]
              splice R (twistedTuple G q x c p) c (n.1 - c) p d
                (F (subword R x (c + p) d))) = 0 :=
      fun c p hp ↦ sum_tmul_splice_eq_zero R (twistedTuple G q x c p)
        (subword R (twistedTuple G q x 0 c) 0 c) (fun d => F (subword R x (c + p) d)) hp
    rw [(sum_range_triangle n.1 _ hg).symm]
    rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.range n.1) ↦ Finset.sum_comm]
    refine Finset.sum_congr rfl fun P hP ↦ Finset.sum_congr rfl fun c hc ↦
      Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [Finset.mem_range] at hP hc
    have hcp : c + (P - c) = P := by omega
    have hl := subword_twistedTuple_congr (G := G) (q := q) (x := x) (m := P) (c := c)
      (by omega) (by omega)
    have hbF : subword R x (c + (P - c)) d = subword R x P d := by
      rw [hcp]
    have hr := splice_twistedTuple_congr (G := G) (q := q) (x := x) (b := n.1 - c) (c := c)
      (p := P - c) (d := d) (hab := by omega)
    rw [hcp] at hr
    rw [← hbF, hl, hr]
  rw [add_comm, hA2, hA1]


/-! ### Determinedness and the correspondence -/

section Letter

open ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- The Taylor components of the graded Taylor expansion are the given map: the only summand
leaving a single letter is the one collapsing the whole word, whose preceding twist is empty. -/
@[simp]
theorem ReducedTensorWords.letter_comp_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) :
    letter R M ∘ₗ gradedCoderiv G F q = F := by
  refine linearMap_ext R M fun n x ↦ ?_
  have hn : 0 < n.1 := n.2
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [of_tprod_eq_subword R hn x,
    gradedCoderiv_subword G F q x (K := n.1) (le_refl n.1)]
  simp only [map_sum]
  refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
  · intro p _ hp
    refine Finset.sum_eq_zero fun d hd ↦
      letter_splice_eq_zero_of_not_whole R (twistedTuple G q x 0 p) _ (by omega)
  · intro hp
    exact absurd hp (by simp [hn])
  · refine (Finset.sum_eq_single n.1 ?_ ?_).trans ?_
    · intro d hd hd'
      exact letter_splice_eq_zero_of_not_whole R (twistedTuple G q x 0 0) _ (by omega)
    · intro hcon
      exact absurd hcon (by simp)
    · exact letter_splice_self R (twistedTuple G q x 0 0)
        (F (subword R x 0 n)) hn (by omega)

/-- A graded coderivation whose letter component raises degrees by `r` raises degrees by `r`:
being determined by its letter component, it inherits homogeneity from it. The twist parameter
`q` of the co-Leibniz identity is independent of this shift. -/
theorem ReducedTensorWords.IsGradedCoderivation.isHomogeneous {G : InternalGrading R M}
    {q r : ℤ} {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G q b)
    (hhom : LinearMap.IsHomogeneous (letter R M ∘ₗ b) (gradedPiece G) (fun e => G.piece e) r) :
    LinearMap.IsHomogeneous b (gradedPiece G) (gradedPiece G) r := by
  rw [IsGradedCoderivation.eq_of_letter_comp_eq hb (isGradedCoderivation_gradedCoderiv G
    (letter R M ∘ₗ b) q) (letter_comp_gradedCoderiv G (letter R M ∘ₗ b) q).symm]
  exact isHomogeneous_gradedCoderiv G (letter R M ∘ₗ b) q r hhom

end Letter

/-! ### Twist parameter zero -/

/-- A `0`-twisted graded coderivation is a coderivation: the twist of parameter zero is the
identity, so the Koszul sign drops out of the co-Leibniz rule. -/
theorem ReducedTensorWords.IsGradedCoderivation.isCoderivation {G : InternalGrading R M}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsGradedCoderivation G 0 b) : IsCoderivation R b := by
  rw [isCoderivation_iff]
  have heq := hb
  simp only [IsGradedCoderivation] at heq
  rw [InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id,
    LinearMap.comp_id, ← LinearMap.add_comp] at heq
  exact heq

/-- A coderivation is a `0`-twisted graded coderivation. -/
theorem ReducedTensorWords.IsCoderivation.isGradedCoderivation (G : InternalGrading R M)
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hb : IsCoderivation R b) : IsGradedCoderivation G 0 b := by
  rw [isCoderivation_iff] at hb
  simp only [IsGradedCoderivation]
  rw [hb, InternalGrading.koszulTwist_zero, ReducedTensorWords.map_id, LinearMap.rTensor_id,
    LinearMap.comp_id, ← LinearMap.add_comp]

/-- At twist parameter zero the graded Taylor expansion is the ungraded one. -/
@[simp]
theorem ReducedTensorWords.gradedCoderiv_zero (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) :
    gradedCoderiv G F 0 = coderiv R F :=
  IsCoderivation.eq_of_letter_comp_eq
    (isGradedCoderivation_gradedCoderiv G F 0).isCoderivation
    (isCoderivation_coderiv R F)
    (by rw [letter_comp_gradedCoderiv, letter_comp_coderiv])



/-! ### The submodule of graded coderivations -/

/-- The `q`-twisted coderivations of the reduced tensor coalgebra form an `R`-submodule of its
endomorphisms: both sides of the twisted co-Leibniz identity depend linearly on the
endomorphism `b`. Membership is the co-Leibniz condition only; it does not include homogeneity,
and it depends only on the parity of `q`. See `isHomogeneous_gradedCoderiv` and
`IsGradedCoderivation.isHomogeneous` for the degree statement. -/
noncomputable def ReducedTensorWords.gradedCoderivations (G : InternalGrading R M) (q : ℤ) :
    Submodule R (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) where
  carrier := {b | IsGradedCoderivation G q b}
  add_mem' {b₁ b₂} hb₁ hb₂ := by
    -- membership in the carrier unfolds to the predicate, which the iff then exposes
    change IsGradedCoderivation G q (b₁ + b₂)
    rw [isGradedCoderivation_iff]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
    rw [map_add, hb₁.deconcatenation_apply, hb₂.deconcatenation_apply,
      LinearMap.rTensor_add, LinearMap.lTensor_add]
    simp only [LinearMap.add_apply]
    abel
  zero_mem' := by
    -- membership in the carrier unfolds to the predicate, which the iff then exposes
    change IsGradedCoderivation G q 0
    rw [isGradedCoderivation_iff]
    simp [LinearMap.zero_comp]
  smul_mem' r x hx := by
    -- membership in the carrier unfolds to the predicate, which the iff then exposes
    change IsGradedCoderivation G q (r • x)
    rw [isGradedCoderivation_iff]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, LinearMap.smul_apply]
    rw [map_smul, hx.deconcatenation_apply, smul_add]

/-- Membership in `gradedCoderivations` is, by definition, being a graded coderivation. -/
@[simp]
theorem ReducedTensorWords.mem_gradedCoderivations (G : InternalGrading R M) {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} :
    b ∈ gradedCoderivations G q ↔ IsGradedCoderivation G q b :=
  Iff.rfl

/-- The graded coderivation/Taylor correspondence: a `q`-twisted coderivation (the co-Leibniz
condition, not a homogeneity hypothesis) is determined by its letter component, and every linear
map from tensor words to letters is the letter component of exactly one such coderivation, namely
its graded Taylor expansion `gradedCoderiv G F q`. The carrier depends only on the parity of `q`.
This is the signed analogue of `ReducedTensorWords.coderivEquivTaylor`. -/
noncomputable def ReducedTensorWords.gradedCoderivEquivTaylor (G : InternalGrading R M) (q : ℤ) :
    gradedCoderivations G q ≃ₗ[R] (ReducedTensorWords R M →ₗ[R] M) where
  toFun b := letter R M ∘ₗ (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
  invFun F := ⟨gradedCoderiv G F q, (mem_gradedCoderivations G).2
    (isGradedCoderivation_gradedCoderiv G F q)⟩
  left_inv b := by
    have hb : IsGradedCoderivation G q
        (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :=
      (mem_gradedCoderivations G).1 b.property
    have key : (gradedCoderiv G (letter R M ∘ₗ (b : _)) q :
        ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) =
          (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :=
      IsGradedCoderivation.eq_of_letter_comp_eq
        (isGradedCoderivation_gradedCoderiv G (letter R M ∘ₗ (b : _)) q) hb
        (by rw [letter_comp_gradedCoderiv])
    exact Subtype.ext key
  right_inv F := letter_comp_gradedCoderiv G F q
  map_add' b₁ b₂ := LinearMap.comp_add _ _ _
  map_smul' r b := LinearMap.comp_smul _ _ _

/-- The graded coderivation/Taylor equivalence sends a coderivation to its letter component. -/
@[simp]
theorem ReducedTensorWords.gradedCoderivEquivTaylor_apply (G : InternalGrading R M) (q : ℤ)
    (b : gradedCoderivations G q) :
    gradedCoderivEquivTaylor G q b =
      letter R M ∘ₗ (b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :=
  by rfl

/-- The inverse of the graded coderivation/Taylor equivalence is the graded Taylor expansion. -/
@[simp]
theorem ReducedTensorWords.gradedCoderivEquivTaylor_symm_apply (G : InternalGrading R M) (q : ℤ)
    (F : ReducedTensorWords R M →ₗ[R] M) :
    (gradedCoderivEquivTaylor G q).symm F =
      ⟨gradedCoderiv G F q, (mem_gradedCoderivations G).2
        (isGradedCoderivation_gradedCoderiv G F q)⟩ :=
  by rfl

end GradedCoderiv

end TauCeti
