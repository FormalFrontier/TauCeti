/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.RingTheory.Finiteness.Subalgebra

/-!
# The degree filtration of a Clifford algebra

A Clifford algebra carries two entirely different gradings, and it is worth keeping them apart.
Mathlib already has the `ℤ/2`-grading `CliffordAlgebra.evenOdd`, which is a genuine
`GradedAlgebra`: the Clifford relation `ι Q m * ι Q m = Q m` preserves the parity of the number of
generators, so parity descends to the quotient. It does *not* preserve the number of generators, so
there is no `ℕ`-grading; what survives is an increasing **filtration** by the number of generators
needed to write an element.

This file builds that filtration. `TauCeti.CliffordAlgebra.filtration Q k` is the `R`-submodule
spanned by the products `ι Q v₁ * ⋯ * ι Q vₙ` with `n ≤ k`, the empty product `1` included, so that
`filtration Q 0` is the module of scalars and `filtration Q 1` adjoins the generators. It is
increasing, multiplicative (`filtration Q i * filtration Q j ≤ filtration Q (i + j)`), exhausts the
algebra, and is preserved by the grade involution, by reversal, and by the functoriality of the
Clifford algebra in the quadratic form.

Following the roadmap, the filtration is *not* the submodule power `LinearMap.range (ι Q) ^ k`:
powers of a submodule of a noncommutative algebra collect the products of *exactly* `k` generators.
The relation between the two is `TauCeti.CliffordAlgebra.filtration_eq_iSup_pow`, which writes
`filtration Q k` as the supremum of those powers over `i ≤ k`; this is the sense in which the
filtration is the "at most `k`" companion of Mathlib's `evenOdd`, whose definition is the analogous
supremum over the `i` of a fixed parity.

## Main definitions

* `TauCeti.CliffordAlgebra.filtration Q k`: the span of the products of at most `k` generators.

## Main results

* `TauCeti.CliffordAlgebra.filtration_zero` and
  `TauCeti.CliffordAlgebra.filtration_one` compute the first two steps, as the scalars and the
  scalars together with `LinearMap.range (ι Q)`.
* `TauCeti.CliffordAlgebra.filtration_mul_le`: the filtration is multiplicative. This is the
  statement that makes the associated graded object an algebra, and it is the prerequisite the
  roadmap asks for before anything downstream.
* `TauCeti.CliffordAlgebra.filtration_succ_eq_sup` and
  `TauCeti.CliffordAlgebra.filtration_one_mul_filtration`: two recursions for the successor step,
  additive and multiplicative.
* `TauCeti.CliffordAlgebra.filtration_eq_iSup_pow`: the comparison with the submodule powers of
  `LinearMap.range (ι Q)`.
* `TauCeti.CliffordAlgebra.iSup_filtration_eq_top` and
  `TauCeti.CliffordAlgebra.exists_mem_filtration`: the filtration is exhaustive.
* `TauCeti.CliffordAlgebra.involute_mem_filtration`,
  `TauCeti.CliffordAlgebra.reverse_mem_filtration` and
  `TauCeti.CliffordAlgebra.map_mem_filtration`: the filtration is preserved by the grade
  involution, by reversal, and by an isometry of quadratic forms.
* `TauCeti.CliffordAlgebra.filtration_fg`: each step is a finitely generated module when `M` is.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 0, "The degree filtration".
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I.
-/

public section

open CliffordAlgebra

universe u v w

namespace TauCeti

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The degree filtration of a Clifford algebra: `filtration Q k` is the `R`-submodule spanned by
the products `ι Q v₁ * ⋯ * ι Q vₙ` of at most `k` generators, the empty product `1` included.

This is deliberately not the submodule power `LinearMap.range (ι Q) ^ k`, which spans the products
of exactly `k` generators; see `filtration_eq_iSup_pow` for the comparison. -/
@[expose] def filtration (Q : QuadraticForm R M) (k : ℕ) : Submodule R (CliffordAlgebra Q) :=
  Submodule.span R {x | ∃ l : List M, l.length ≤ k ∧ (l.map (ι Q)).prod = x}

variable (Q : QuadraticForm R M)

/-- The defining span, restated so that `Submodule.span_le` can be used on `filtration`. -/
theorem filtration_eq_span (k : ℕ) :
    filtration Q k = Submodule.span R {x | ∃ l : List M, l.length ≤ k ∧ (l.map (ι Q)).prod = x} :=
  rfl

/-- A product of at most `k` generators lies in the `k`-th step of the filtration. This is the
generating family, so most `filtration` memberships reduce to it. -/
theorem prod_map_ι_mem_filtration {k : ℕ} {l : List M} (hl : l.length ≤ k) :
    (l.map (ι Q)).prod ∈ filtration Q k :=
  Submodule.subset_span ⟨l, hl, rfl⟩

/-- The filtration is increasing: a product of at most `i` generators is a product of at most `j`
of them whenever `i ≤ j`. -/
theorem filtration_mono : Monotone (filtration Q) := fun _ _ hij =>
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans hij, hx⟩

/-- The zeroth step of the filtration is the module of scalars, the span of the empty product. -/
theorem filtration_zero : filtration Q 0 = 1 := by
  rw [filtration_eq_span, Submodule.one_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]
    simp
  · rintro rfl
    exact ⟨[], le_rfl, rfl⟩

theorem one_mem_filtration (k : ℕ) : (1 : CliffordAlgebra Q) ∈ filtration Q k := by
  simpa using prod_map_ι_mem_filtration Q (l := []) (Nat.zero_le k)

theorem one_le_filtration (k : ℕ) : 1 ≤ filtration Q k :=
  Submodule.one_le.2 (one_mem_filtration Q k)

theorem algebraMap_mem_filtration (r : R) (k : ℕ) :
    algebraMap R (CliffordAlgebra Q) r ∈ filtration Q k := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (one_mem_filtration Q k)

theorem ι_mem_filtration_one (m : M) : ι Q m ∈ filtration Q 1 := by
  simpa using prod_map_ι_mem_filtration Q (l := [m]) le_rfl

theorem range_ι_le_filtration_one : LinearMap.range (ι Q) ≤ filtration Q 1 := by
  rintro _ ⟨m, rfl⟩
  exact ι_mem_filtration_one Q m

theorem ι_mul_ι_mem_filtration_two (a b : M) : ι Q a * ι Q b ∈ filtration Q 2 := by
  simpa using prod_map_ι_mem_filtration Q (l := [a, b]) le_rfl

/-- **The filtration is multiplicative.** Concatenating a product of at most `i` generators with a
product of at most `j` generators gives a product of at most `i + j` of them, so the associated
graded object of the filtration is an algebra. -/
theorem filtration_mul_le (i j : ℕ) :
    filtration Q i * filtration Q j ≤ filtration Q (i + j) := by
  rw [filtration_eq_span, filtration_eq_span, Submodule.span_mul_span, Submodule.span_le,
    Set.mul_subset_iff]
  rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩
  rw [← List.prod_append, ← List.map_append]
  exact prod_map_ι_mem_filtration Q (by simpa using Nat.add_le_add h₁ h₂)

/-- Iterating `filtration_mul_le`: the `n`-th submodule power of the `i`-th step lands in the
`i * n`-th step. -/
theorem filtration_pow_le (i n : ℕ) : filtration Q i ^ n ≤ filtration Q (i * n) := by
  induction n with
  | zero => rw [pow_zero, Nat.mul_zero, filtration_zero]
  | succ n ih =>
    calc filtration Q i ^ (n + 1)
        = filtration Q i ^ n * filtration Q i := pow_succ _ _
      _ ≤ filtration Q (i * n) * filtration Q i := mul_le_mul' ih le_rfl
      _ ≤ filtration Q (i * n + i) := filtration_mul_le Q _ _
      _ = filtration Q (i * (n + 1)) := by rw [Nat.mul_succ]

/-- A product of exactly `n` generators lies in the `n`-th submodule power of
`LinearMap.range (ι Q)`. -/
theorem prod_map_ι_mem_pow (l : List M) :
    (l.map (ι Q)).prod ∈ LinearMap.range (ι Q) ^ l.length := by
  induction l with
  | nil => exact Submodule.one_le.1 le_rfl
  | cons m t ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) ih

/-- The products of exactly `n` generators are among the products of at most `n` of them. -/
theorem pow_range_ι_le_filtration (n : ℕ) : LinearMap.range (ι Q) ^ n ≤ filtration Q n := by
  induction n with
  | zero => rw [pow_zero, filtration_zero]
  | succ n ih =>
    calc LinearMap.range (ι Q) ^ (n + 1)
        = LinearMap.range (ι Q) ^ n * LinearMap.range (ι Q) := pow_succ _ _
      _ ≤ filtration Q n * filtration Q 1 := mul_le_mul' ih (range_ι_le_filtration_one Q)
      _ ≤ filtration Q (n + 1) := filtration_mul_le Q n 1

/-- The comparison between the filtration and the submodule powers of `LinearMap.range (ι Q)`:
`filtration Q k` collects the products of at most `k` generators, so it is the supremum of the
powers up to `k`. Compare `CliffordAlgebra.evenOdd`, the supremum of the powers whose exponent has
a fixed parity. -/
theorem filtration_eq_iSup_pow (k : ℕ) :
    filtration Q k = ⨆ i : {i : ℕ // i ≤ k}, LinearMap.range (ι Q) ^ (i : ℕ) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun i => ?_)
  · rintro _ ⟨l, hl, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨l.length, hl⟩ (prod_map_ι_mem_pow Q l)
  · exact (pow_range_ι_le_filtration Q i).trans (filtration_mono Q i.2)

/-- The successor step of the filtration adjoins the products of exactly `k + 1` generators. -/
theorem filtration_succ_eq_sup (k : ℕ) :
    filtration Q (k + 1) = filtration Q k ⊔ LinearMap.range (ι Q) ^ (k + 1) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (sup_le (filtration_mono Q (Nat.le_succ k)) (pow_range_ι_le_filtration Q (k + 1)))
  rintro _ ⟨l, hl, rfl⟩
  rcases eq_or_lt_of_le hl with h | h
  · exact Submodule.mem_sup_right (h ▸ prod_map_ι_mem_pow Q l)
  · exact Submodule.mem_sup_left (prod_map_ι_mem_filtration Q (Nat.lt_succ_iff.1 h))

/-- The first step of the filtration is the scalars together with the generators. -/
theorem filtration_one : filtration Q 1 = 1 ⊔ LinearMap.range (ι Q) := by
  simpa [filtration_zero] using filtration_succ_eq_sup Q 0

/-- The multiplicative form of the successor recursion: each step is the first step times the
previous one. -/
theorem filtration_one_mul_filtration (k : ℕ) :
    filtration Q 1 * filtration Q k = filtration Q (k + 1) := by
  refine le_antisymm (by simpa [Nat.add_comm] using filtration_mul_le Q 1 k) ?_
  rw [filtration_succ_eq_sup]
  refine sup_le ?_ ?_
  · calc filtration Q k = 1 * filtration Q k := (one_mul _).symm
      _ ≤ filtration Q 1 * filtration Q k := mul_le_mul' (one_le_filtration Q 1) le_rfl
  · rw [pow_succ']
    exact mul_le_mul' (range_ι_le_filtration_one Q) (pow_range_ι_le_filtration Q k)

/-- **The filtration is exhaustive.** Every element of the Clifford algebra is a combination of
products of generators, so it lies in some step. -/
theorem iSup_filtration_eq_top : ⨆ k, filtration Q k = ⊤ := by
  rw [eq_top_iff, ← iSup_ι_range_eq_top Q]
  exact iSup_mono' fun i => ⟨i, pow_range_ι_le_filtration Q i⟩

/-- The pointwise form of `iSup_filtration_eq_top`, available because the filtration is a directed
family. -/
theorem exists_mem_filtration (x : CliffordAlgebra Q) : ∃ k, x ∈ filtration Q k := by
  have hx : x ∈ ⨆ k, filtration Q k := by rw [iSup_filtration_eq_top]; exact Submodule.mem_top
  rwa [Submodule.mem_iSup_of_directed _ (filtration_mono Q).directed_le] at hx

/-- The generators of a Clifford algebra commute up to the polarization of `Q`, which is a scalar:
the associated graded algebra of the filtration is commutative in degree one. -/
theorem ι_mul_ι_add_swap_mem_filtration_zero (a b : M) :
    ι Q a * ι Q b + ι Q b * ι Q a ∈ filtration Q 0 := by
  rw [ι_mul_ι_add_swap]
  exact algebraMap_mem_filtration Q _ 0

section Conjugation

/-- The grade involution preserves each step of the filtration: it multiplies a product of `n`
generators by `(-1) ^ n`. -/
theorem involute_mem_filtration {k : ℕ} {x : CliffordAlgebra Q} (hx : x ∈ filtration Q k) :
    involute x ∈ filtration Q k := by
  have h : filtration Q k ≤ (filtration Q k).comap (involute (Q := Q)).toLinearMap := by
    rw [filtration_eq_span, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    change involute (l.map (ι Q)).prod ∈ filtration Q k
    rw [involute_prod_map_ι]
    exact Submodule.smul_mem _ _ (prod_map_ι_mem_filtration Q hl)
  exact h hx

/-- Reversal preserves each step of the filtration: it reverses the list of generators. -/
theorem reverse_mem_filtration {k : ℕ} {x : CliffordAlgebra Q} (hx : x ∈ filtration Q k) :
    reverse x ∈ filtration Q k := by
  have h : filtration Q k ≤ (filtration Q k).comap (reverse (Q := Q)) := by
    rw [filtration_eq_span, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    change reverse (l.map (ι Q)).prod ∈ filtration Q k
    rw [reverse_prod_map_ι, ← List.map_reverse]
    exact prod_map_ι_mem_filtration Q (by simpa using hl)
  exact h hx

end Conjugation

section Map

variable {N : Type w} [AddCommGroup N] [Module R N] {Q' : QuadraticForm R N}

/-- The functoriality of the Clifford algebra in the quadratic form takes a product of generators
to a product of the same length. -/
theorem map_prod_map_ι (f : Q →qᵢ Q') (l : List M) :
    CliffordAlgebra.map f (l.map (ι Q)).prod = ((l.map f).map (ι Q')).prod := by
  induction l with
  | nil => simp
  | cons m t ih => simp [ih]

/-- An isometry of quadratic forms respects the degree filtration. -/
theorem map_mem_filtration (f : Q →qᵢ Q') {k : ℕ} {x : CliffordAlgebra Q}
    (hx : x ∈ filtration Q k) : CliffordAlgebra.map f x ∈ filtration Q' k := by
  have h : filtration Q k ≤ (filtration Q' k).comap (CliffordAlgebra.map f).toLinearMap := by
    rw [filtration_eq_span, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    change CliffordAlgebra.map f (l.map (ι Q)).prod ∈ filtration Q' k
    rw [map_prod_map_ι]
    exact prod_map_ι_mem_filtration Q' (by simpa using hl)
  exact h hx

end Map

/-- Every step of the filtration is a finitely generated module as soon as `M` is: the `k`-th step
is generated by the products of at most `k` elements of a generating family of `M`. -/
theorem filtration_fg [Module.Finite R M] (k : ℕ) : (filtration Q k).FG := by
  have hι : (LinearMap.range (ι Q)).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.finite_def.1 ‹Module.Finite R M›).map _
  induction k with
  | zero =>
    rw [filtration_zero, Submodule.one_eq_span]
    exact Submodule.fg_span_singleton 1
  | succ k ih =>
    rw [filtration_succ_eq_sup]
    exact ih.sup (hι.pow _)

end CliffordAlgebra

end TauCeti
