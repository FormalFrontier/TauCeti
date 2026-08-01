/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# The centre and the derived ideal of `gl n R`

The general linear Lie algebra `gl n R` is `Matrix n n R` with the commutator bracket. It is the
basic *reductive* — as opposed to semisimple — example: it splits as its centre plus its derived
ideal as soon as `Fintype.card n` is invertible in `R`. This file identifies both pieces.

The centre of `gl n R` is the scalar matrices, for any commutative ring `R` and any finite index
type. The derived ideal `⁅gl n R, gl n R⁆` is the trace-zero ideal `sl n R`, again over any
commutative ring and any finite index type: one inclusion is the vanishing of the trace of a
commutator, and the other writes a trace-zero matrix as a combination of the commutators
`Eᵢⱼ = ⁅Eᵢᵢ, Eᵢⱼ⁆` (for `i ≠ j`) and `Eᵢᵢ - Eⱼⱼ = ⁅Eᵢⱼ, Eⱼᵢ⁆`.

The two pieces are complementary whenever the size of the matrices is invertible in `R`: the
intersection is cut out by `Fintype.card n * r = 0`, and the projection onto the centre divides the
trace by `Fintype.card n`. Under that hypothesis `gl n R` is the direct sum of its centre and its
derived ideal, which is the linear half of the reductivity criterion `radical = center`. Only this
sufficiency is proved here; the hypothesis is not necessary in general, since for an empty index
type `gl n R` is the zero Lie algebra and the decomposition is vacuous. It cannot simply be dropped
either: over `ZMod p` the identity matrix of `gl p (ZMod p)` has trace zero, so there the centre
sits *inside* the derived ideal and the two are not complementary.

## Main definitions

* `TauCeti.slIdeal R n`: the trace-zero matrices, as a `LieIdeal R (Matrix n n R)`. Mathlib's
  `LieAlgebra.SpecialLinear.sl n R` is the same subspace packaged only as a Lie subalgebra, and
  `TauCeti.slIdeal_toLieSubalgebra_eq_sl` identifies the two.

## Main results

* `TauCeti.mem_center_matrix_iff`: an element of `gl n R` is central exactly when it is a scalar
  matrix, and `TauCeti.center_matrix_toSubmodule_eq_span_one` records the centre as the span of `1`.
* `TauCeti.derivedSeries_one_eq_slIdeal`: the derived ideal of `gl n R` is `TauCeti.slIdeal R n`, so
  by `TauCeti.mem_slIdeal_iff` it consists of the trace-zero matrices, and
  `TauCeti.derivedSeries_one_toLieSubalgebra_eq_sl` reads this as `LieAlgebra.SpecialLinear.sl n R`.
* `TauCeti.isCompl_center_derivedSeries_one_matrix`: when `Fintype.card n` is invertible in `R`,
  the centre and the derived ideal are complementary submodules of `gl n R`.
* `TauCeti.derivedSeries_one_matrix_ne_top`: for nonempty `n` over a nontrivial `R`, `gl n R` is
  not perfect.
* `TauCeti.not_hasTrivialRadical_matrix`: for nonempty `n` over a nontrivial `R`, `gl n R` is not
  semisimple, since its centre is then a nonzero abelian ideal (`TauCeti.center_matrix_ne_bot`).

## Implementation notes

Every result about `gl n R` is stated over an arbitrary commutative ring `R`; no field,
characteristic, or algebraic closure hypothesis is used, and the invertibility of `Fintype.card n`
is carried as an `Invertible` hypothesis only on the one result that needs it. Two groups of
declarations ask for less: the matrix-unit bracket identities need only a ring, and the
decomposition of a trace-zero matrix into matrix units needs only an additive commutative group,
no multiplication at all.

Mathlib does not register `LieRing.ofAssociativeRing` as a global instance, so, as in
`Mathlib/Algebra/Lie/Matrix.lean`, it is a local instance here.

## References

This implements the concrete `gl n` half of the opening "structure of reductive Lie algebras"
target of Layer 9 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: *"Concretely
for `gl_n`: the centre is the scalar matrices, the derived ideal is `sl n`"*, together with the
direct-sum statement into which the reductivity criterion quoted there splits.
-/

public section

namespace TauCeti

open Matrix LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} {n : Type*} [DecidableEq n] [Fintype n]

/-! ### Trace-zero matrices as sums of matrix units -/

section AddCommGroup

variable [AddCommGroup R]

/-- **A trace-zero matrix as a sum of commutator-shaped matrix units.** Every matrix is the sum of
its matrix units `Eₚq (Aₚq)`; subtracting `E₀₀ (Aₚₚ)` from each diagonal one changes the total by
`E₀₀ (trace A)`, so for a trace-zero `A` the corrected sum is still `A`.

The correction is what puts each summand in commutator form: the membership helper below exhibits
an explicit bracket for every one of them. Only the additive structure of `R` is involved here. -/
private lemma eq_sum_sum_ite_single_sub_of_trace_eq_zero (i₀ : n) {A : Matrix n n R}
    (hA : A.trace = 0) :
    A = ∑ p : n, ∑ q : n,
      (if p = q then single p p (A p q) - single i₀ i₀ (A p q) else single p q (A p q)) := by
  have hsplit : ∀ p q : n,
      (if p = q then single p p (A p q) - single i₀ i₀ (A p q) else single p q (A p q))
        = single p q (A p q) - (if p = q then single i₀ i₀ (A p q) else 0) := fun p q => by
    by_cases hpq : p = q <;> simp [hpq]
  have hrow : ∀ p : n, (∑ q : n, if p = q then single i₀ i₀ (A p q) else (0 : Matrix n n R))
      = single i₀ i₀ (A p p) := fun p => by simp
  have hsingle_sum : ∀ f : n → R, ∑ p : n, single i₀ i₀ (f p) = single i₀ i₀ (∑ p : n, f p) :=
    fun f => (map_sum (Matrix.singleAddMonoidHom i₀ i₀) f Finset.univ).symm
  have hcorr : ∑ p : n, ∑ q : n, (if p = q then single i₀ i₀ (A p q) else 0)
      = single i₀ i₀ A.trace := by
    rw [Finset.sum_congr rfl fun p _ => hrow p, hsingle_sum]
    -- `Matrix.trace` is by definition the sum of the diagonal entries.
    rfl
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hsplit p q]
  simp only [Finset.sum_sub_distrib, hcorr, hA, Matrix.single_zero, sub_zero]
  exact Matrix.matrix_eq_sum_single A

end AddCommGroup

/-! ### Matrix units as commutators -/

section Ring

variable [Ring R]

/-- An off-diagonal matrix unit is a commutator: `Eᵢⱼ = ⁅Eᵢᵢ, Eᵢⱼ⁆` when `i ≠ j`. -/
theorem lie_single_self_single_of_ne {i j : n} (hij : i ≠ j) (c : R) :
    ⁅single i i (1 : R), single i j c⁆ = single i j c := by
  rw [LieRing.of_associative_ring_bracket, single_mul_single_same,
    single_mul_single_of_ne (h := Ne.symm hij), one_mul, sub_zero]

/-- A difference of diagonal matrix units is a commutator: `Eᵢᵢ - Eⱼⱼ = ⁅Eᵢⱼ, Eⱼᵢ⁆`. -/
theorem lie_single_single_eq_sub (i j : n) (c : R) :
    ⁅single i j c, single j i (1 : R)⁆ = single i i c - single j j c := by
  rw [LieRing.of_associative_ring_bracket, single_mul_single_same, single_mul_single_same, mul_one,
    one_mul]

end Ring

variable [CommRing R]

/-! ### The centre of `gl n R` -/

/-- The centre of `gl n R` is the scalar matrices. The Lie centre and the ring centre agree here,
since a commutator vanishes exactly when the two factors commute.

This is deliberately not a `simp` lemma: `simp` rewrites the left-hand side with
`LieModule.mem_maxTrivSubmodule` to `∀ X, ⁅X, A⁆ = 0`, so tagging it `@[simp]` violates `simpNF`. -/
theorem mem_center_matrix_iff {A : Matrix n n R} :
    A ∈ LieAlgebra.center R (Matrix n n R) ↔ ∃ r : R, A = r • (1 : Matrix n n R) := by
  have key : (∀ B : Matrix n n R, ⁅B, A⁆ = 0) ↔ A ∈ Set.center (Matrix n n R) := by
    rw [Semigroup.mem_center_iff]
    exact forall_congr' fun B => by rw [LieRing.of_associative_ring_bracket, sub_eq_zero]
  rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule, key, Matrix.center_eq_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

variable (R n) in
/-- The centre of `gl n R` is the `R`-span of the identity matrix. -/
theorem center_matrix_toSubmodule_eq_span_one :
    (LieAlgebra.center R (Matrix n n R)).toSubmodule = R ∙ (1 : Matrix n n R) := by
  ext A
  rw [LieSubmodule.mem_toSubmodule, mem_center_matrix_iff, Submodule.mem_span_singleton]
  exact exists_congr fun r => eq_comm

/-! ### The special linear ideal -/

variable (R n) in
/-- The trace-zero matrices, as a Lie ideal of `gl n R`.

Mathlib's `LieAlgebra.SpecialLinear.sl n R` is the same subspace, packaged only as a Lie
subalgebra; `TauCeti.slIdeal_toLieSubalgebra_eq_sl` identifies the two. The ideal packaging is what
the derived series of `gl n R` lives in. -/
def slIdeal : LieIdeal R (Matrix n n R) where
  carrier := {A | A.trace = 0}
  add_mem' hA hB := by simp_all
  zero_mem' := by simp
  smul_mem' c _ hA := by simp_all
  lie_mem {X A} _ := matrix_trace_commutator_zero n R X A

@[simp]
theorem mem_slIdeal_iff {A : Matrix n n R} : A ∈ slIdeal R n ↔ A.trace = 0 := Iff.rfl

variable (R n) in
/-- The special linear ideal of `gl n R` is Mathlib's special linear subalgebra. -/
theorem slIdeal_toLieSubalgebra_eq_sl :
    (slIdeal R n : LieSubalgebra R (Matrix n n R)) = LieAlgebra.SpecialLinear.sl n R :=
  SetLike.ext fun _ => (mem_slIdeal_iff (R := R) (n := n)).trans
    (LinearMap.mem_ker (f := Matrix.traceLinearMap n R R)).symm

/-! ### The derived ideal of `gl n R` -/

/-- Each summand of the corrected double sum above lies in the derived ideal of `gl n R`, being a
commutator: an off-diagonal unit by `TauCeti.lie_single_self_single_of_ne`, and a corrected diagonal
one by `TauCeti.lie_single_single_eq_sub`. -/
private lemma ite_single_sub_mem_derivedSeries_one (i₀ : n) (c : R) (p q : n) :
    (if p = q then single p p c - single i₀ i₀ c else single p q c)
      ∈ derivedSeries R (Matrix n n R) 1 := by
  classical
  have hcomm : ∀ X Y : Matrix n n R, ⁅X, Y⁆ ∈ derivedSeries R (Matrix n n R) 1 := fun X Y => by
    have hmem : ⁅X, Y⁆ ∈ Submodule.span R {⁅x, y⁆ | (x : Matrix n n R) (y : Matrix n n R)} :=
      Submodule.subset_span ⟨X, Y, rfl⟩
    rwa [← coe_derivedSeries_one_eq] at hmem
  by_cases hpq : p = q
  · subst hpq
    simpa [lie_single_single_eq_sub p i₀ c] using hcomm (single p i₀ c) (single i₀ p 1)
  · simpa [hpq, lie_single_self_single_of_ne hpq c] using
      hcomm (single p p (1 : R)) (single p q c)

variable (R n) in
/-- The derived ideal of `gl n R` is the special linear ideal: `⁅gl n R, gl n R⁆ = sl n R`.

One inclusion is the vanishing of the trace of a commutator. For the other, a trace-zero matrix is
the sum of its off-diagonal matrix units `Eᵢⱼ (Aᵢⱼ)`, commutators by
`TauCeti.lie_single_self_single_of_ne`, and of the differences `Eᵢᵢ (Aᵢᵢ) - E₀₀ (Aᵢᵢ)`, commutators
by `TauCeti.lie_single_single_eq_sub`; the discrepancy between the two sums is `E₀₀ (trace A)`,
which vanishes. For an empty index type both sides are the zero ideal. -/
theorem derivedSeries_one_eq_slIdeal :
    derivedSeries R (Matrix n n R) 1 = slIdeal R n := by
  classical
  refine le_antisymm ?_ fun A hA => ?_
  · have hspan : Submodule.span R {⁅X, Y⁆ | (X : Matrix n n R) (Y : Matrix n n R)}
        ≤ (slIdeal R n : Submodule R (Matrix n n R)) := by
      rw [Submodule.span_le]
      rintro - ⟨X, Y, rfl⟩
      exact mem_slIdeal_iff.mpr (matrix_trace_commutator_zero n R X Y)
    rw [← coe_derivedSeries_one_eq] at hspan
    exact hspan
  -- With no indices at all the only matrix is `0`, which lies in every ideal.
  rcases isEmpty_or_nonempty n with hn | hne
  · haveI := hn
    rw [Subsingleton.elim A 0]
    exact zero_mem _
  obtain ⟨i₀⟩ := hne
  rw [eq_sum_sum_ite_single_sub_of_trace_eq_zero i₀ (mem_slIdeal_iff.mp hA)]
  exact Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
    ite_single_sub_mem_derivedSeries_one i₀ (A p q) p q

variable (R n) in
/-- The derived ideal of `gl n R` is Mathlib's special linear Lie algebra `sl n R`. -/
theorem derivedSeries_one_toLieSubalgebra_eq_sl :
    (derivedSeries R (Matrix n n R) 1 : LieSubalgebra R (Matrix n n R))
      = LieAlgebra.SpecialLinear.sl n R := by
  rw [derivedSeries_one_eq_slIdeal R n, slIdeal_toLieSubalgebra_eq_sl R n]

/-! ### `gl n R` is the direct sum of its centre and its derived ideal -/

variable (R n) in
/-- When the size of the matrices is invertible in `R`, the centre and the derived ideal of
`gl n R` are complementary: `gl n R = R·1 ⊕ sl n R`. This is the linear half of the reductivity
criterion `radical = center`, made concrete for `gl n R`.

The invertibility hypothesis cannot simply be dropped: in `gl p (ZMod p)` the identity matrix has
trace `0`, so there the centre is contained in the derived ideal and the two are not complementary.
It is not necessary either, since for an empty index type `gl n R` is the zero Lie algebra. -/
theorem isCompl_center_derivedSeries_one_matrix [Invertible (Fintype.card n : R)] :
    IsCompl (LieAlgebra.center R (Matrix n n R)).toSubmodule
      (derivedSeries R (Matrix n n R) 1).toSubmodule := by
  constructor
  · rw [Submodule.disjoint_def]
    intro A hA hA'
    obtain ⟨r, rfl⟩ := mem_center_matrix_iff.mp hA
    rw [derivedSeries_one_eq_slIdeal R n, LieSubmodule.mem_toSubmodule, mem_slIdeal_iff] at hA'
    have hr : (Fintype.card n : R) * r = 0 := by
      simpa [Matrix.trace_smul, Matrix.trace_one, mul_comm] using hA'
    have hr0 : r = 0 := by
      simpa [← mul_assoc, invOf_mul_self] using congrArg (⅟(Fintype.card n : R) * ·) hr
    rw [hr0, zero_smul]
  · rw [codisjoint_iff_le_sup]
    intro A _
    set r : R := ⅟(Fintype.card n : R) * A.trace with hr
    refine Submodule.mem_sup.mpr ⟨r • (1 : Matrix n n R), mem_center_matrix_iff.mpr ⟨r, rfl⟩,
      A - r • (1 : Matrix n n R), ?_, by abel⟩
    have htr : (r • (1 : Matrix n n R)).trace = A.trace := by
      rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hr, mul_assoc, mul_comm A.trace,
        ← mul_assoc, invOf_mul_self, one_mul]
    rw [derivedSeries_one_eq_slIdeal R n, LieSubmodule.mem_toSubmodule, mem_slIdeal_iff,
      Matrix.trace_sub, htr, sub_self]

variable (R n) in
/-- `gl n R` is not perfect: for nonempty `n` over a nontrivial ring its derived ideal misses the
diagonal matrix unit `Eᵢᵢ`, whose trace is `1`. -/
theorem derivedSeries_one_matrix_ne_top [Nonempty n] [Nontrivial R] :
    derivedSeries R (Matrix n n R) 1 ≠ ⊤ := by
  obtain ⟨i⟩ := ‹Nonempty n›
  intro h
  have h1 : single i i (1 : R) ∈ slIdeal R n := by
    rw [← derivedSeries_one_eq_slIdeal R n, h]; exact LieSubmodule.mem_top _
  rw [mem_slIdeal_iff, Matrix.trace_single_eq_same] at h1
  exact one_ne_zero h1

/-! ### `gl n R` is not semisimple, for nonempty `n` over a nontrivial ring -/

variable (R n) in
/-- The centre of `gl n R` is nonzero: it contains the identity matrix. -/
theorem center_matrix_ne_bot [Nonempty n] [Nontrivial R] :
    LieAlgebra.center R (Matrix n n R) ≠ ⊥ := by
  intro h
  have h1 : (1 : Matrix n n R) = 0 := by
    rw [← LieSubmodule.mem_bot (R := R) (L := Matrix n n R), ← h]
    exact mem_center_matrix_iff.mpr ⟨1, (one_smul R _).symm⟩
  exact one_ne_zero h1

variable (R n) in
/-- For nonempty `n` over a nontrivial ring, `gl n R` is not semisimple: its centre is then a
nonzero abelian ideal, so its radical is nonzero. This is why the highest-weight theory of `gl n R`
cannot be read off Mathlib's `IsKilling` machinery, and has to be developed through the reductive
decomposition instead. -/
theorem not_hasTrivialRadical_matrix [Nonempty n] [Nontrivial R] :
    ¬ LieAlgebra.HasTrivialRadical R (Matrix n n R) := by
  intro h
  letI := h
  exact center_matrix_ne_bot R n (LieAlgebra.center_eq_bot R (Matrix n n R))

end TauCeti
