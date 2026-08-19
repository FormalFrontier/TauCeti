/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Borel
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Dominant weights and highest weight vectors for `gl n`

Weights of `gl n R` for the diagonal Cartan subalgebra are tuples `μ : n → R`
(`TauCeti.glWeightEquiv`). This file adds the two predicates that highest weight theory for
`gl n` is stated against, both in the matrix unit positive system of
`TauCeti/Algebra/Lie/GeneralLinear/Borel.lean`.

The first is **dominance**. For `gl n` it is a condition on *differences*, not on the entries
themselves: a tuple `μ : Fin n → R` over a ring of characteristic zero is dominant integral when
each consecutive difference `μ i - μ (i+1)` is a natural number — characteristic zero is what makes
"is a natural number" a real condition, since over `ZMod p` every element is a natural number cast
and every tuple would qualify. The entries are unconstrained, and that slack is exactly the
central direction: adding a constant tuple `c · (1, …, 1)` — the weight of the centre of `gl n` —
preserves dominance for every `c : R`. The staircase `(N - 1/2, N - 3/2, …, 1/2)` over `ℚ` is
dominant with no integer entry at all, which is what makes the slack visible, and the weakly
decreasing *integer* tuples sit inside the dominant ones as the weights of the rational
representations of the group.

The second is being a **highest weight vector** of weight `μ`: a nonzero vector which the diagonal
matrix units `Eᵢᵢ` scale by `μ i` and which the raising matrix units `Eᵢⱼ`, `i < j`, annihilate.
Those two families are coordinates for the diagonal Cartan subalgebra and generators of the
positive nilpotent ideal `𝔫⁺`, so the elementwise conditions are equivalent to the two
coordinate-free ones: the whole Cartan acts by the weight `TauCeti.glWeightEquiv R n μ`, and the
whole of `𝔫⁺` annihilates (`TauCeti.isGlHighestWeightVector_iff_forall_mem`).

## Main definitions

* `TauCeti.IsGlDominantIntegral μ`: the consecutive differences of `μ : Fin n → R` are natural
  numbers, for `R` of characteristic zero.
* `TauCeti.glStaircase N`: the staircase tuple `(N - 1/2, N - 3/2, …, 1/2) : Fin N → ℚ`.
* `TauCeti.IsGlHighestWeightVector μ v`: `v` is nonzero, the diagonal matrix unit `Eᵢᵢ` acts on it
  by `μ i`, and every raising matrix unit `Eᵢⱼ` with `i < j` annihilates it.

## Main results

* `TauCeti.IsGlDominantIntegral.exists_natCast_sub_of_le`: dominance propagates from consecutive
  indices to all pairs, `μ i - μ j ∈ ℕ` whenever `i ≤ j`, and
  `TauCeti.isGlDominantIntegral_iff_forall_le` records the two forms as equivalent.
* `TauCeti.isGlDominantIntegral_intCast`: an antitone integer tuple is dominant — the weights of
  the group level sit inside the dominant ones.
* `TauCeti.IsGlDominantIntegral.add_const`: dominance is invariant under the central direction.
* `TauCeti.isGlDominantIntegral_glStaircase` and `TauCeti.glStaircase_ne_intCast`: the staircase is
  dominant and no entry of it is an integer, so dominance genuinely does not force integrality.
* `TauCeti.IsGlHighestWeightVector.lie_eq_glWeightEquiv_smul` and
  `TauCeti.IsGlHighestWeightVector.lie_eq_zero_of_mem_strictUpperTriangular`: the whole diagonal
  Cartan subalgebra acts by the weight, and the whole positive nilpotent ideal annihilates.
* `TauCeti.isGlHighestWeightVector_iff_forall_mem`: those two conditions characterise a highest
  weight vector, so the elementwise definition loses nothing.
* `TauCeti.IsGlHighestWeightVector.weight_eq`: a vector is a highest weight vector for at most one
  weight.
* `TauCeti.isGlHighestWeightVector_single_bot_top`: the highest root vector `E_{⊥⊤}` is a highest
  weight vector of the adjoint module, of weight `ε_⊥ - ε_⊤`, so the predicate is not vacuous.

## Implementation notes

Both predicates are stated as the conjunctions pinned by the roadmap rather than as structures, so
that they are definitionally the classical conditions; because the bodies are not exposed, the
`Iff` restatements `TauCeti.isGlDominantIntegral_iff` and
`TauCeti.isGlHighestWeightVector_iff` are how they are introduced and eliminated downstream, with
`TauCeti.IsGlHighestWeightVector.ne_zero`,
`TauCeti.IsGlHighestWeightVector.lie_single_self_eq_smul` and
`TauCeti.IsGlHighestWeightVector.lie_single_eq_zero` as the projections.

Dominance is stated for `Fin n`, since "consecutive" refers to the successor on the indices, while
the highest weight condition needs only a linearly ordered index type and is stated for one, as
`TauCeti.strictUpperTriangular` is. Neither needs a field or an algebraically closed field, so both
are over a commutative ring and the roadmap's field case is the instance `R = K`; dominance
additionally asks for `CharZero R`, because "the difference is a natural number" is a condition on
`R` only when the cast `ℕ → R` is injective — in characteristic `p` every element of `ZMod p` is
such a cast and the predicate would be satisfied by every tuple. That hypothesis is used in the
definition itself, through the injective `Nat.castEmbedding` rather than the bare `Nat.cast`, so
that no shape of the predicate can drift away from it; `TauCeti.isGlDominantIntegral_iff` puts the
condition back in the plain form `∃ k : ℕ, μ i - μ j = k`. The two statements that read a scalar
back off a vector — uniqueness of the weight, and that rescaling preserves the predicate — are the
ones needing more, namely the hypotheses `IsCancelMulZero R` and `Module.IsTorsionFree R M` of
Mathlib's `smul_left_injective`, without which a torsion vector could carry several weights at
once.

As in `TauCeti/Algebra/Lie/GeneralLinear/Basic.lean`, `LieRing.ofAssociativeRing` is a local
instance, Mathlib not registering it globally; the Lie module hypotheses on `M` are stated against
it, so a downstream file must install it too before mentioning `IsGlHighestWeightVector`.

## References

This implements the two predicates of the "diagonal Cartan and `gl_n` weights" item of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: *"dominance is a condition on
differences (`IsGlDominantIntegral`: consecutive differences in `ℕ`, entries free in `K`), and a
highest weight vector is a simultaneous eigenvector of the diagonal killed by the strict upper
triangle (`IsGlHighestWeightVector`)"*, together with the staircase example that item names and the
integral points of that layer's "dictionary to the group level". The classification statements
made against them are not proved here.

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991), §15.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Dominant integral weights of `gl n` -/

section Dominant

variable {R : Type*} [CommRing R] [CharZero R] {n : ℕ}

/-- A tuple `μ : Fin n → R` is **dominant integral** for `gl n` when each consecutive difference
`μ i - μ j`, `j` the successor of `i`, is a natural number.

The scalars are required to have characteristic zero: that is what makes the condition say what it
reads as. In characteristic `p` the cast `ℕ → R` is not injective — over `ZMod p` every element is
the cast of a natural number — so every tuple would be dominant and the notion would be vacuous.
Accordingly the cast is spelled through `Nat.castEmbedding`, which is `Nat.cast` bundled with its
injectivity, so that the hypothesis is used by the statement itself;
`TauCeti.isGlDominantIntegral_iff` restates the condition with the plain cast and is how the
predicate is introduced and eliminated.

The entries themselves are unconstrained: dominance is a condition on differences only, so it is
invariant under the central direction `μ ↦ μ + c · (1, …, 1)`
(`TauCeti.IsGlDominantIntegral.add_const`) and does not force integrality
(`TauCeti.glStaircase_ne_intCast`). -/
def IsGlDominantIntegral (mu : Fin n → R) : Prop :=
  ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → ∃ k : ℕ, mu i - mu j = Nat.castEmbedding k

/-- `TauCeti.IsGlDominantIntegral` unfolded. The predicate is not exposed, so this is how it is
introduced and eliminated outside this file. -/
theorem isGlDominantIntegral_iff {mu : Fin n → R} :
    IsGlDominantIntegral mu ↔
      ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → ∃ k : ℕ, mu i - mu j = (k : R) :=
  Iff.rfl

variable {mu nu : Fin n → R}

/-- **Dominance propagates along a chain of consecutive steps**: if `i` is `d` steps below `j` then
`μ i - μ j` is a natural number, by adding up the `d` consecutive differences. -/
theorem IsGlDominantIntegral.exists_natCast_sub_of_add_eq (h : IsGlDominantIntegral mu) :
    ∀ (d : ℕ) (i j : Fin n), (i : ℕ) + d = (j : ℕ) → ∃ k : ℕ, mu i - mu j = (k : R) := by
  rw [isGlDominantIntegral_iff] at h
  intro d
  induction d with
  | zero =>
    intro i j hij
    obtain rfl : i = j := Fin.ext (by simpa using hij)
    exact ⟨0, by simp⟩
  | succ d ih =>
    intro i j hij
    have hlt : (i : ℕ) + 1 < n := by have := j.isLt; omega
    obtain ⟨k₁, hk₁⟩ := h i ⟨(i : ℕ) + 1, hlt⟩ rfl
    obtain ⟨k₂, hk₂⟩ := ih ⟨(i : ℕ) + 1, hlt⟩ j (by simpa using by omega)
    exact ⟨k₁ + k₂, by push_cast [← hk₁, ← hk₂]; ring⟩

/-- **Dominance is a condition on all differences, not just the consecutive ones**: for a dominant
`μ` and `i ≤ j`, the difference `μ i - μ j` is a natural number. -/
theorem IsGlDominantIntegral.exists_natCast_sub_of_le (h : IsGlDominantIntegral mu) {i j : Fin n}
    (hij : i ≤ j) : ∃ k : ℕ, mu i - mu j = (k : R) := by
  rw [Fin.le_def] at hij
  exact h.exists_natCast_sub_of_add_eq ((j : ℕ) - (i : ℕ)) i j (by omega)

/-- Dominance in its two equivalent forms: consecutive differences, or all differences along the
order. -/
theorem isGlDominantIntegral_iff_forall_le :
    IsGlDominantIntegral mu ↔ ∀ i j : Fin n, i ≤ j → ∃ k : ℕ, mu i - mu j = (k : R) :=
  ⟨fun h _ _ hij => h.exists_natCast_sub_of_le hij,
    fun h i j hij => h i j (Fin.le_def.mpr (by omega))⟩

/-- A constant tuple is dominant: this is the weight by which the centre of `gl n` acts. -/
theorem isGlDominantIntegral_const (c : R) : IsGlDominantIntegral (fun _ : Fin n => c) :=
  fun _ _ _ => ⟨0, by simp⟩

/-- Dominance is closed under addition. -/
theorem IsGlDominantIntegral.add (h : IsGlDominantIntegral mu) (h' : IsGlDominantIntegral nu) :
    IsGlDominantIntegral (mu + nu) := by
  rw [isGlDominantIntegral_iff] at h h' ⊢
  intro i j hij
  obtain ⟨k₁, hk₁⟩ := h i j hij
  obtain ⟨k₂, hk₂⟩ := h' i j hij
  exact ⟨k₁ + k₂, by simp only [Pi.add_apply]; push_cast [← hk₁, ← hk₂]; ring⟩

/-- **Dominance is invariant under the central direction.** Adding the constant tuple
`c · (1, …, 1)` — the weight of the centre of `gl n`, which is invisible to the differences — takes
dominant weights to dominant weights. -/
theorem IsGlDominantIntegral.add_const (h : IsGlDominantIntegral mu) (c : R) :
    IsGlDominantIntegral (fun i => mu i + c) :=
  h.add (isGlDominantIntegral_const c)

/-- **The integral points.** An antitone tuple of integers is dominant: the weakly decreasing
integer tuples that index the rational representations of the group `GL n` sit inside the dominant
weights of `gl n`, the extra directions being the non-integral ones. -/
theorem isGlDominantIntegral_intCast {a : Fin n → ℤ} (ha : Antitone a) :
    IsGlDominantIntegral (fun i => (a i : R)) := by
  rw [isGlDominantIntegral_iff]
  intro i j hij
  have hle : i ≤ j := Fin.le_def.mpr (by omega)
  have h0 : (0 : ℤ) ≤ a i - a j := sub_nonneg.mpr (ha hle)
  refine ⟨(a i - a j).toNat, ?_⟩
  rw [← Int.cast_natCast (R := R), Int.toNat_of_nonneg h0, Int.cast_sub]

/-- Over an index type with at most one element there is no consecutive pair, so every tuple is
dominant. -/
theorem isGlDominantIntegral_of_le_one (hn : n ≤ 1) (mu : Fin n → R) : IsGlDominantIntegral mu :=
  fun _ j hij => absurd (j.isLt) (by omega)

/-! ### The staircase weight -/

/-- The **staircase** weight `(N - 1/2, N - 3/2, …, 1/2) : Fin N → ℚ`, the standard witness that
dominance for `gl n` does not force the entries to be integers: it is dominant
(`TauCeti.isGlDominantIntegral_glStaircase`) and none of its entries is an integer
(`TauCeti.glStaircase_ne_intCast`). Its consecutive differences are all `1`, so it is the half-shift
of the integral weight `(N - 1, N - 2, …, 0)` by the central direction `-1/2 · (1, …, 1)`. -/
def glStaircase (N : ℕ) : Fin N → ℚ := fun i => (N : ℚ) - 1 / 2 - (i : ℕ)

@[simp]
theorem glStaircase_apply (N : ℕ) (i : Fin N) :
    glStaircase N i = (N : ℚ) - 1 / 2 - (i : ℕ) := (rfl)

/-- The staircase weight is dominant: its consecutive differences are all `1`. -/
theorem isGlDominantIntegral_glStaircase (N : ℕ) : IsGlDominantIntegral (glStaircase N) := by
  rw [isGlDominantIntegral_iff]
  intro i j hij
  have hji : ((j : ℕ) : ℚ) = ((i : ℕ) : ℚ) + 1 := by exact_mod_cast hij.symm
  exact ⟨1, by rw [glStaircase_apply, glStaircase_apply, hji]; push_cast; ring⟩

/-- **No entry of the staircase weight is an integer.** Together with
`TauCeti.isGlDominantIntegral_glStaircase` this pins the difference between dominance for `gl n`
and dominance for a semisimple Lie algebra: the entries of a dominant `gl n` weight are free, only
their differences are constrained. -/
theorem glStaircase_ne_intCast {N : ℕ} (i : Fin N) (m : ℤ) : glStaircase N i ≠ (m : ℚ) := by
  intro h
  rw [glStaircase_apply] at h
  have h2 : ((2 * (N : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℚ) = ((2 * m : ℤ) : ℚ) := by
    push_cast
    linarith
  have := Int.cast_injective (α := ℚ) h2
  omega

end Dominant

/-! ### Highest weight vectors for `gl n` -/

section Diagonal

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- A diagonal matrix is the combination of the diagonal matrix units with its own diagonal entries
as coefficients. -/
private theorem eq_sum_smul_single_self {A : Matrix n n R} (hA : A ∈ diagonalCartan R n) :
    A = ∑ i : n, A i i • single i i (1 : R) := by
  have h : ∑ i : n, A i i • single i i (1 : R) = ∑ i : n, single i i (A i i) :=
    Finset.sum_congr rfl fun i _ => by rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  ext a b
  rw [Matrix.sum_apply]
  simp only [single_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [mem_diagonalCartan_iff.mp hA a b hab]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right fun hi => hab (hi.1.symm.trans hi.2)).symm

end Diagonal

section HighestWeight

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule (Matrix n n R) M]
variable {mu nu : n → R} {v : M}

/-- A vector `v` of a `gl n R`-module is a **highest weight vector of weight `μ`** for the matrix
unit positive system when it is nonzero, the diagonal matrix unit `Eᵢᵢ` acts on it by the scalar
`μ i`, and every raising matrix unit `Eᵢⱼ` with `i < j` annihilates it.

The two elementwise families are coordinates for the diagonal Cartan subalgebra and generators of
the positive nilpotent ideal `𝔫⁺`, so this says exactly that `v` is a `𝔫⁺`-annihilated weight
vector of weight `TauCeti.glWeightEquiv R n μ`; see
`TauCeti.isGlHighestWeightVector_iff_forall_mem`. -/
def IsGlHighestWeightVector (mu : n → R) (v : M) : Prop :=
  v ≠ 0 ∧ (∀ i : n, ⁅(single i i 1 : Matrix n n R), v⁆ = mu i • v) ∧
    ∀ i j : n, i < j → ⁅(single i j 1 : Matrix n n R), v⁆ = 0

/-- `TauCeti.IsGlHighestWeightVector` unfolded. The predicate is not exposed, so this is how it is
introduced outside this file; the three projections below are its elimination API. -/
theorem isGlHighestWeightVector_iff :
    IsGlHighestWeightVector mu v ↔
      v ≠ 0 ∧ (∀ i : n, ⁅(single i i 1 : Matrix n n R), v⁆ = mu i • v) ∧
        ∀ i j : n, i < j → ⁅(single i j 1 : Matrix n n R), v⁆ = 0 :=
  Iff.rfl

namespace IsGlHighestWeightVector

/-- A highest weight vector is nonzero. -/
theorem ne_zero (hv : IsGlHighestWeightVector mu v) : v ≠ 0 := hv.1

/-- The diagonal matrix unit `Eᵢᵢ` scales a highest weight vector by the `i`-th entry of its
weight. -/
theorem lie_single_self_eq_smul (hv : IsGlHighestWeightVector mu v) (i : n) :
    ⁅(single i i 1 : Matrix n n R), v⁆ = mu i • v := hv.2.1 i

/-- The raising matrix units annihilate a highest weight vector. -/
theorem lie_single_eq_zero (hv : IsGlHighestWeightVector mu v) {i j : n} (hij : i < j) :
    ⁅(single i j 1 : Matrix n n R), v⁆ = 0 := hv.2.2 i j hij

end IsGlHighestWeightVector

/-- **Transport along an equivalence of `gl n R`-modules.** -/
theorem IsGlHighestWeightVector.map {M' : Type*} [AddCommGroup M'] [Module R M']
    [LieRingModule (Matrix n n R) M']
    (e : M ≃ₗ⁅R,Matrix n n R⁆ M') (hv : IsGlHighestWeightVector mu v) :
    IsGlHighestWeightVector mu (e v) := by
  have hmap : ∀ (x : Matrix n n R) (m : M), e ⁅x, m⁆ = ⁅x, e m⁆ := fun x m =>
    LieModuleHom.map_lie (e : M →ₗ⁅R,Matrix n n R⁆ M') x m
  refine isGlHighestWeightVector_iff.mpr
    ⟨fun h => hv.ne_zero (e.injective (by rw [h, map_zero])), fun i => ?_, fun i j hij => ?_⟩
  · rw [← hmap, hv.lie_single_self_eq_smul, map_smul]
  · rw [← hmap, hv.lie_single_eq_zero hij, map_zero]

/-- **A vector is a highest weight vector for at most one weight.** The diagonal matrix units read
the weight off the vector, so two weights of the same nonzero vector agree entry by entry. -/
theorem IsGlHighestWeightVector.weight_eq [IsCancelMulZero R] [Module.IsTorsionFree R M]
    (hv : IsGlHighestWeightVector mu v) (hv' : IsGlHighestWeightVector nu v) : mu = nu := by
  funext i
  refine smul_left_injective R hv.ne_zero ?_
  change mu i • v = nu i • v
  rw [← hv.lie_single_self_eq_smul i, hv'.lie_single_self_eq_smul i]

variable [LieModule R (Matrix n n R) M]

namespace IsGlHighestWeightVector

/-- **The whole diagonal Cartan subalgebra acts on a highest weight vector by its weight**, not
just the diagonal matrix units: `⁅A, v⁆ = (∑ i, μ i · Aᵢᵢ) • v` for every diagonal `A`. -/
theorem lie_eq_smul_of_mem_diagonalCartan (hv : IsGlHighestWeightVector mu v) {A : Matrix n n R}
    (hA : A ∈ diagonalCartan R n) : ⁅A, v⁆ = (∑ i : n, mu i * A i i) • v := by
  conv_lhs => rw [eq_sum_smul_single_self hA]
  rw [sum_lie, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_lie, hv.lie_single_self_eq_smul, smul_smul, mul_comm]

/-- The coordinate-free form of `TauCeti.IsGlHighestWeightVector.lie_eq_smul_of_mem_diagonalCartan`:
an element of the diagonal Cartan subalgebra acts on a highest weight vector by the value of the
weight `TauCeti.glWeightEquiv R n μ` on it. -/
theorem lie_eq_glWeightEquiv_smul (hv : IsGlHighestWeightVector mu v) (A : diagonalCartan R n) :
    ⁅(A : Matrix n n R), v⁆ = glWeightEquiv R n mu A • v := by
  rw [glWeightEquiv_apply]
  exact hv.lie_eq_smul_of_mem_diagonalCartan A.2

/-- **The whole positive nilpotent ideal `𝔫⁺` annihilates a highest weight vector**, not just the
raising matrix units that span it. -/
theorem lie_eq_zero_of_mem_strictUpperTriangular (hv : IsGlHighestWeightVector mu v)
    {A : Matrix n n R} (hA : A ∈ strictUpperTriangular R n) : ⁅A, v⁆ = 0 := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [sum_lie]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sum_lie]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases lt_or_ge i j with hij | hij
  · have hsmul : single i j (A i j) = A i j • single i j (1 : R) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hsmul, smul_lie, hv.lie_single_eq_zero hij, smul_zero]
  · rw [mem_strictUpperTriangular_iff.mp hA i j hij, Matrix.single_zero, zero_lie]

end IsGlHighestWeightVector

/-- **The subalgebra form of the definition**: a highest weight vector is exactly a nonzero vector
on which the diagonal Cartan subalgebra acts by the weight `TauCeti.glWeightEquiv R n μ` and which
the positive nilpotent ideal `𝔫⁺` annihilates. The elementwise definition therefore loses
nothing. -/
theorem isGlHighestWeightVector_iff_forall_mem :
    IsGlHighestWeightVector mu v ↔ v ≠ 0 ∧
      (∀ A : diagonalCartan R n, ⁅(A : Matrix n n R), v⁆ = glWeightEquiv R n mu A • v) ∧
        ∀ A ∈ strictUpperTriangular R n, ⁅A, v⁆ = 0 := by
  refine ⟨fun hv => ⟨hv.ne_zero, fun A => hv.lie_eq_glWeightEquiv_smul A, fun _ hA =>
    hv.lie_eq_zero_of_mem_strictUpperTriangular hA⟩, fun ⟨hne, hcartan, hnil⟩ => ?_⟩
  refine ⟨hne, fun i => ?_, fun i j hij => hnil _ (single_mem_strictUpperTriangular hij 1)⟩
  have h := hcartan ⟨single i i 1, single_self_mem_diagonalCartan i 1⟩
  rwa [glWeightEquiv_apply, show ∑ j : n, mu j * (single i i (1 : R)) j j = mu i by
    simp [single_apply, Finset.sum_ite_eq]] at h

section TorsionFree

variable [IsCancelMulZero R] [Module.IsTorsionFree R M]

/-- Rescaling a highest weight vector by a nonzero scalar gives a highest weight vector of the same
weight. -/
theorem IsGlHighestWeightVector.smul (hv : IsGlHighestWeightVector mu v) {c : R} (hc : c ≠ 0) :
    IsGlHighestWeightVector mu (c • v) := by
  refine isGlHighestWeightVector_iff.mpr
    ⟨fun h => hc ((smul_eq_zero_iff_left hv.ne_zero).mp h), fun i => ?_, fun i j hij => ?_⟩
  · rw [lie_smul, hv.lie_single_self_eq_smul, smul_comm]
  · rw [lie_smul, hv.lie_single_eq_zero hij, smul_zero]

end TorsionFree

end HighestWeight

/-! ### The highest root vector of the adjoint module -/

section Adjoint

variable {R : Type*} [CommRing R] [Nontrivial R] {n : Type*} [DecidableEq n] [Fintype n]
  [LinearOrder n] [OrderBot n] [OrderTop n]

/-- **The highest root vector is a highest weight vector**, for the adjoint action of `gl n R` on
itself: the matrix unit `E_{⊥⊤}` in the corner is nonzero, the diagonal acts on it by
`ε_⊥ - ε_⊤`, and every raising matrix unit annihilates it, since `E_{ij} E_{⊥⊤}` needs `j = ⊥` and
`E_{⊥⊤} E_{ij}` needs `i = ⊤`, both impossible for `i < j`.

`TauCeti.IsGlHighestWeightVector` is therefore not vacuous. For an index type with more than one
element the weight `ε_⊥ - ε_⊤` is the highest root, the tuple `(1, 0, …, 0, -1)`; for a singleton
one the two matrix units coincide, the weight degenerates to `0`, and the statement is the (still
true) assertion that `E_{⊥⊥}` is a highest weight vector of weight `0` of the abelian `gl 1`. -/
theorem isGlHighestWeightVector_single_bot_top :
    IsGlHighestWeightVector
      ((Pi.single (⊥ : n) 1 - Pi.single (⊤ : n) 1 : n → R))
      (single (⊥ : n) (⊤ : n) (1 : R)) := by
  refine isGlHighestWeightVector_iff.mpr ⟨?_, fun k => ?_, fun i j hij => ?_⟩
  · intro hz
    have := congrArg (fun A : Matrix n n R => A ⊥ ⊤) hz
    simp at this
  · rw [lie_single_of_mem_diagonalCartan (single_self_mem_diagonalCartan k 1) ⊥ ⊤ 1]
    congr 1
    simp [single_apply, Pi.single_apply]
  · have hjb : j ≠ (⊥ : n) := (bot_le.trans_lt hij).ne'
    have hti : (⊤ : n) ≠ i := (hij.trans_le le_top).ne'
    have h₁ : (single i j 1 : Matrix n n R) * single ⊥ ⊤ 1 = 0 :=
      Matrix.single_mul_single_of_ne 1 i j ⊥ hjb 1
    have h₂ : (single (⊥ : n) ⊤ 1 : Matrix n n R) * single i j 1 = 0 :=
      Matrix.single_mul_single_of_ne 1 ⊥ ⊤ i hti 1
    rw [LieRing.of_associative_ring_bracket, h₁, h₂, sub_zero]

end Adjoint

end TauCeti
