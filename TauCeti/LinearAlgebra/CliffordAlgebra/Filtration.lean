/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import TauCeti.Algebra.WordFiltration

/-!
# The degree filtration of a Clifford algebra

A Clifford algebra carries two different degree structures, one grading and one filtration, and it
is worth keeping them apart. Mathlib already has the `ℤ/2`-grading `CliffordAlgebra.evenOdd`, which
is a genuine `GradedAlgebra`: the Clifford relation `ι Q m * ι Q m = Q m` preserves the parity of
the number of generators, so parity descends to the quotient. It does *not* preserve the number of
generators, so there is no `ℕ`-grading; what survives is an increasing **filtration** by the number
of generators needed to write an element.

This file builds that filtration. `TauCeti.CliffordAlgebra.filtration Q k` is the `R`-submodule
spanned by the products `ι Q v₁ * ⋯ * ι Q vₙ` with `n ≤ k`, the empty product `1` included, so that
`filtration Q 0` is the module of scalars and `filtration Q 1` adjoins the generators. It is
increasing, multiplicative (`filtration Q i * filtration Q j = filtration Q (i + j)`), exhausts the
algebra, and is preserved by the grade involution, by reversal, and by the functoriality of the
Clifford algebra in the quadratic form.

The construction itself is not special to Clifford algebras: `filtration` and `filtrationPrevious`
are `TauCeti.Algebra.wordFiltration` and `TauCeti.Algebra.wordFiltrationPrevious` of
`TauCeti/Algebra/WordFiltration.lean`, specialized to `ι Q`, and the lemmas below that do not use
the Clifford relation are specializations of the generic ones. The universal enveloping algebra
carries the same construction as its PBW filtration.

Following the roadmap, the filtration is *not* the submodule power `LinearMap.range (ι Q) ^ k`:
powers of a submodule of a noncommutative algebra collect the products of *exactly* `k` generators.
The relation between the two is `TauCeti.CliffordAlgebra.filtration_eq_iSup_pow`, which writes
`filtration Q k` as the supremum of those powers over `i ≤ k`; this is the sense in which the
filtration is the "at most `k`" companion of Mathlib's `evenOdd`, whose definition is the analogous
supremum over the `i` of a fixed parity.

## Main definitions

* `TauCeti.CliffordAlgebra.filtration Q k`: the span of the products of at most `k` generators.
* `TauCeti.CliffordAlgebra.FiltrationGradedPiece Q k`: the degree-`k` successive quotient.

## Main results

* `TauCeti.CliffordAlgebra.prod_map_ι_mem_filtration` and
  `TauCeti.CliffordAlgebra.filtration_le_iff`: the products of at most `k` generators lie in the
  `k`-th step and generate it, which is how memberships and bounds are proved.
* `TauCeti.CliffordAlgebra.filtration_eq_pow`: the defining equation, as the `k`-th power of the
  scalars together with `LinearMap.range (ι Q)`.
* `TauCeti.CliffordAlgebra.filtration_zero` and
  `TauCeti.CliffordAlgebra.filtration_one` compute the first two steps, as the scalars and the
  scalars together with `LinearMap.range (ι Q)`.
* `TauCeti.CliffordAlgebra.filtration_mul`: the filtration is multiplicative, and in fact exactly
  so: `filtration Q i * filtration Q j = filtration Q (i + j)`. This is the statement that makes
  the associated graded object an algebra, and it is the prerequisite the roadmap asks for before
  anything downstream; `TauCeti.CliffordAlgebra.filtration_pow` is its iterate and
  `TauCeti.CliffordAlgebra.mul_mem_filtration` its elementwise form.
* `TauCeti.CliffordAlgebra.filtration_succ_eq_sup`: the recursion for the successor step.
* `TauCeti.CliffordAlgebra.filtration_eq_iSup_pow`: the comparison with the submodule powers of
  `LinearMap.range (ι Q)`.
* `TauCeti.CliffordAlgebra.filtrationLeadingTerm` and
  `TauCeti.CliffordAlgebra.filtrationLeadingTerm_surjective`: the exterior-power leading-term map
  onto each successive filtration quotient. It is surjective over any `CommRing`; when `2` is
  invertible `TauCeti.CliffordAlgebra.filtrationGradedEquiv_comp_filtrationLeadingTerm` identifies
  it with the inverse of the graded equivalence.
* `TauCeti.CliffordAlgebra.iSup_filtration_eq_top`: the filtration is exhaustive.
* `TauCeti.CliffordAlgebra.involute_mem_filtration`,
  `TauCeti.CliffordAlgebra.reverse_mem_filtration` and
  `TauCeti.CliffordAlgebra.map_mem_filtration`: the filtration is preserved by the grade
  involution, by reversal, and by an isometry of quadratic forms.
* `TauCeti.CliffordAlgebra.contractLeft_mem_filtration_succ` and
  `TauCeti.CliffordAlgebra.contractLeft_mem_filtration`,
  `TauCeti.CliffordAlgebra.changeForm_mem_filtration`, and
  `TauCeti.CliffordAlgebra.changeFormEquiv_map_filtration` and
  `TauCeti.CliffordAlgebra.changeForm_mem_filtration_iff`: contraction and change of
  quadratic form respect the filtration, contraction lowers every positive step by one, and the
  change-form equivalence transports every step exactly.
* `TauCeti.CliffordAlgebra.changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration`: change of form
  has identity symbol, that is, it moves a word of generators only by terms two filtration degrees
  lower.
* `TauCeti.CliffordAlgebra.fg_filtration`: each step is a finitely generated module when `M` is.

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
of exactly `k` generators; see `filtration_eq_iSup_pow` for the comparison.

This is `TauCeti.Algebra.wordFiltration` specialized to `ι Q`; the shared API is in
`TauCeti/Algebra/WordFiltration.lean`. -/
def filtration (Q : QuadraticForm R M) (k : ℕ) : Submodule R (CliffordAlgebra Q) :=
  TauCeti.Algebra.wordFiltration (ι Q) k

/-- The defining equation of the filtration: degree `k` is the `k`-th submodule power of the
scalars together with `LinearMap.range (ι Q)`. Contrast `filtration_eq_iSup_pow`, the comparison
with the powers of `LinearMap.range (ι Q)` alone. -/
theorem filtration_eq_pow (Q : QuadraticForm R M) (k : ℕ) :
    filtration Q k = (1 ⊔ LinearMap.range (ι Q)) ^ k :=
  TauCeti.Algebra.wordFiltration_eq_pow (ι Q) k

/-- The filtration step preceding degree `k`, that is `TauCeti.Algebra.wordFiltrationPrevious`
specialized to `ι Q`. At degree zero it is bottom, so the degree-zero piece remains the scalar
filtration step rather than a zero quotient. -/
def filtrationPrevious (Q : QuadraticForm R M) : ℕ → Submodule R (CliffordAlgebra Q) :=
  TauCeti.Algebra.wordFiltrationPrevious (ι Q)

@[simp]
theorem filtrationPrevious_zero (Q : QuadraticForm R M) : filtrationPrevious Q 0 = ⊥ :=
  TauCeti.Algebra.wordFiltrationPrevious_zero (ι Q)

@[simp]
theorem filtrationPrevious_succ (Q : QuadraticForm R M) (k : ℕ) :
    filtrationPrevious Q (k + 1) = filtration Q k :=
  TauCeti.Algebra.wordFiltrationPrevious_succ (ι Q) k

/-- The Clifford filtration carries Mathlib's bundled ring-filtration structure. -/
instance instIsRingFiltration (Q : QuadraticForm R M) :
    IsRingFiltration (filtration Q) (filtrationPrevious Q) :=
  TauCeti.Algebra.wordFiltration.instIsRingFiltration (ι Q)

/-- The filtration step preceding degree `k`, viewed inside the degree-`k` filtration step. This is
the relation defining the degree-`k` associated-graded quotient. -/
def filtrationPreviousRestricted (Q : QuadraticForm R M) (k : ℕ) :
    Submodule R (filtration Q k) :=
  (filtrationPrevious Q k).submoduleOf (filtration Q k)

/-- Membership in the restricted preceding filtration is ambient membership in the preceding
filtration step. -/
@[simp]
theorem mem_filtrationPreviousRestricted_iff (Q : QuadraticForm R M) (k : ℕ)
    (x : filtration Q k) :
    x ∈ filtrationPreviousRestricted Q k ↔
      (x : CliffordAlgebra Q) ∈ filtrationPrevious Q k :=
  Iff.rfl

/-- The restricted preceding filtration is trivial in degree zero. -/
@[simp]
theorem filtrationPreviousRestricted_zero (Q : QuadraticForm R M) :
    filtrationPreviousRestricted Q 0 = ⊥ := by
  ext x
  simp [filtrationPreviousRestricted, Submodule.submoduleOf]

/-- In successor degree, the restricted preceding filtration is the preceding filtration step
viewed inside the successor step. -/
@[simp]
theorem filtrationPreviousRestricted_succ (Q : QuadraticForm R M) (k : ℕ) :
    filtrationPreviousRestricted Q (k + 1) =
      Submodule.comap (filtration Q (k + 1)).subtype (filtration Q k) := by
  simp only [filtrationPreviousRestricted, Submodule.submoduleOf, filtrationPrevious_succ]

/-- The degree-`k` piece of the associated graded Clifford filtration. -/
abbrev FiltrationGradedPiece (Q : QuadraticForm R M) (k : ℕ) : Type max u v :=
  filtration Q k ⧸ filtrationPreviousRestricted Q k

variable (Q : QuadraticForm R M)

/-- A product of at most `k` generators lies in the `k`-th step of the filtration. This is the
generating family, so most `filtration` memberships reduce to it. -/
theorem prod_map_ι_mem_filtration {k : ℕ} {l : List M} (hl : l.length ≤ k) :
    (l.map (ι Q)).prod ∈ filtration Q k :=
  TauCeti.Algebra.prod_map_mem_wordFiltration (ι Q) hl

/-- The `k`-th step of the filtration is spanned by the products of at most `k` generators, so a
submodule contains it exactly when it contains those products. This is `Submodule.span_le` in the
form in which it applies to `filtration`. -/
theorem filtration_le_iff {k : ℕ} {p : Submodule R (CliffordAlgebra Q)} :
    filtration Q k ≤ p ↔ ∀ l : List M, l.length ≤ k → (l.map (ι Q)).prod ∈ p :=
  TauCeti.Algebra.wordFiltration_le_iff (ι Q)

/-- The filtration is increasing: a product of at most `i` generators is a product of at most `j`
of them whenever `i ≤ j`. -/
theorem filtration_mono : Monotone (filtration Q) :=
  TauCeti.Algebra.wordFiltration_mono (ι Q)

/-- The zeroth step of the filtration is the module of scalars, the span of the empty product. -/
@[simp]
theorem filtration_zero : filtration Q 0 = 1 :=
  TauCeti.Algebra.wordFiltration_zero (ι Q)

/-- `1` is the empty product of generators, so it lies in every step of the filtration. -/
theorem one_mem_filtration (k : ℕ) : (1 : CliffordAlgebra Q) ∈ filtration Q k :=
  TauCeti.Algebra.one_mem_wordFiltration (ι Q) k

/-- Scalars lie in every step of the filtration, being multiples of the empty product. -/
theorem algebraMap_mem_filtration (r : R) (k : ℕ) :
    algebraMap R (CliffordAlgebra Q) r ∈ filtration Q k :=
  TauCeti.Algebra.algebraMap_mem_wordFiltration (ι Q) r k

/-- A generator is a product of one generator, so it lies in the first step. -/
theorem ι_mem_filtration_one (m : M) : ι Q m ∈ filtration Q 1 :=
  TauCeti.Algebra.apply_mem_wordFiltration_one (ι Q) m

/-- The submodule form of `ι_mem_filtration_one`: all of `LinearMap.range (ι Q)` lies in the first
step. -/
theorem ι_range_le_filtration_one : LinearMap.range (ι Q) ≤ filtration Q 1 :=
  TauCeti.Algebra.range_le_wordFiltration_one (ι Q)

/-- A product of two generators lies in the second step. This is the membership the roadmap's
bivectors use. -/
theorem ι_mul_ι_mem_filtration_two (a b : M) : ι Q a * ι Q b ∈ filtration Q 2 := by
  simpa using prod_map_ι_mem_filtration Q (l := [a, b]) le_rfl

/-- **The filtration is multiplicative**, and exactly so. Concatenating a product of at most `i`
generators with a product of at most `j` generators gives a product of at most `i + j` of them, and
conversely a product of at most `i + j` generators splits after its `i`-th factor. In particular the
associated graded object of the filtration is an algebra. -/
theorem filtration_mul (i j : ℕ) :
    filtration Q i * filtration Q j = filtration Q (i + j) :=
  TauCeti.Algebra.wordFiltration_mul (ι Q) i j

/-- The elementwise form of `filtration_mul`: a product of an element of the `i`-th step and an
element of the `j`-th step lies in the `i + j`-th step. -/
theorem mul_mem_filtration {i j : ℕ} {x y : CliffordAlgebra Q} (hx : x ∈ filtration Q i)
    (hy : y ∈ filtration Q j) : x * y ∈ filtration Q (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltration (ι Q) hx hy

/-- Multiplication preserves a strict degree drop in the left factor of the Clifford filtration. -/
theorem mul_mem_filtrationPrevious_left {i j : ℕ} {x y : CliffordAlgebra Q}
    (hx : x ∈ filtrationPrevious Q i) (hy : y ∈ filtration Q j) :
    x * y ∈ filtrationPrevious Q (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltrationPrevious_left (ι Q) hx hy

/-- Multiplication preserves a strict degree drop in the right factor of the Clifford filtration. -/
theorem mul_mem_filtrationPrevious_right {i j : ℕ} {x y : CliffordAlgebra Q}
    (hx : x ∈ filtration Q i) (hy : y ∈ filtrationPrevious Q j) :
    x * y ∈ filtrationPrevious Q (i + j) :=
  TauCeti.Algebra.mul_mem_wordFiltrationPrevious_right (ι Q) hx hy

/-- Iterating `filtration_mul`: the `n`-th submodule power of the `i`-th step is the `i * n`-th
step. -/
theorem filtration_pow (i n : ℕ) : filtration Q i ^ n = filtration Q (i * n) :=
  TauCeti.Algebra.wordFiltration_pow (ι Q) i n

/-- A product of exactly `n` generators lies in the `n`-th submodule power of
`LinearMap.range (ι Q)`. -/
theorem prod_map_ι_mem_pow (l : List M) :
    (l.map (ι Q)).prod ∈ LinearMap.range (ι Q) ^ l.length :=
  TauCeti.Algebra.prod_map_mem_range_pow (ι Q) l

/-- The products of exactly `n` generators are among the products of at most `n` of them. -/
theorem ι_range_pow_le_filtration (n : ℕ) : LinearMap.range (ι Q) ^ n ≤ filtration Q n :=
  TauCeti.Algebra.range_pow_le_wordFiltration (ι Q) n

/-- The comparison between the filtration and the submodule powers of `LinearMap.range (ι Q)`:
`filtration Q k` collects the products of at most `k` generators, so it is the supremum of the
powers up to `k`. Compare `CliffordAlgebra.evenOdd`, the supremum of the powers whose exponent has
a fixed parity. -/
theorem filtration_eq_iSup_pow (k : ℕ) :
    filtration Q k = ⨆ i : {i : ℕ // i ≤ k}, LinearMap.range (ι Q) ^ (i : ℕ) :=
  TauCeti.Algebra.wordFiltration_eq_iSup_pow (ι Q) k

/-- The successor step of the filtration adjoins the products of exactly `k + 1` generators. -/
theorem filtration_succ_eq_sup (k : ℕ) :
    filtration Q (k + 1) = filtration Q k ⊔ LinearMap.range (ι Q) ^ (k + 1) :=
  TauCeti.Algebra.wordFiltration_succ_eq_sup (ι Q) k

/-- The first step of the filtration is the scalars together with the generators. -/
@[simp]
theorem filtration_one : filtration Q 1 = 1 ⊔ LinearMap.range (ι Q) :=
  TauCeti.Algebra.wordFiltration_one (ι Q)

/-- **The filtration is exhaustive.** Every element of the Clifford algebra is a combination of
products of generators, so it lies in some step. -/
theorem iSup_filtration_eq_top : ⨆ k, filtration Q k = ⊤ := by
  rw [eq_top_iff, ← iSup_ι_range_eq_top Q]
  exact iSup_mono' fun i => ⟨i, ι_range_pow_le_filtration Q i⟩

private theorem repeat_product_mem_filtration (a : M) :
    ∀ middle : List M,
      ((a :: (middle ++ [a])).map (ι Q)).prod ∈ filtration Q (middle.length + 1) := by
  intro middle
  induction middle with
  | nil =>
      -- Expose the singleton word so the Clifford square relation sees its adjacent generators.
      change ι Q a * (ι Q a * 1) ∈ filtration Q 1
      rw [mul_one]
      rw [ι_sq_scalar]
      exact filtration_mono Q (Nat.zero_le _) (algebraMap_mem_filtration Q _ 0)
  | cons b middle ih =>
      -- Expose the list product so `ι_mul_ι_comm` can rewrite the first adjacent pair.
      change ι Q a * (ι Q b * ((middle ++ [a]).map (ι Q)).prod) ∈
        filtration Q (middle.length + 1 + 1)
      rw [← mul_assoc, ι_mul_ι_comm, sub_mul, mul_assoc]
      refine Submodule.sub_mem _ ?_ ?_
      · have htail : ((middle ++ [a]).map (ι Q)).prod ∈ filtration Q (middle.length + 1) :=
          prod_map_ι_mem_filtration Q (l := middle ++ [a]) (by simp)
        have hscalar :
            algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a b) *
                ((middle ++ [a]).map (ι Q)).prod ∈
              filtration Q (middle.length + 1) := by
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ htail
        exact filtration_mono Q (by omega) hscalar
      · have hinner : ι Q a * ((middle ++ [a]).map (ι Q)).prod ∈
            filtration Q (middle.length + 1) := by
          simpa only [List.map_cons, List.prod_cons] using ih
        have hmul := Submodule.mul_mem_mul (ι_mem_filtration_one Q b) hinner
        rw [filtration_mul] at hmul
        simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul

private theorem prod_map_ι_mem_filtration_pred_of_not_nodup :
    ∀ l : List M, ¬l.Nodup →
      (l.map (ι Q)).prod ∈ filtration Q (l.length - 1) := by
  intro l hl
  induction l with
  | nil => simp at hl
  | cons a tail ih =>
      by_cases ha : a ∈ tail
      · obtain ⟨pre, suf, rfl⟩ := List.mem_iff_append.1 ha
        have hcore := repeat_product_mem_filtration Q a pre
        have hsuffix : (suf.map (ι Q)).prod ∈ filtration Q suf.length :=
          prod_map_ι_mem_filtration Q le_rfl
        have hmul := Submodule.mul_mem_mul hcore hsuffix
        rw [filtration_mul] at hmul
        -- Restore the expanded repeated word to match the filtered product above.
        change ((a :: (pre ++ a :: suf)).map (ι Q)).prod ∈
          filtration Q ((a :: (pre ++ a :: suf)).length - 1)
        have hindex : (a :: (pre ++ a :: suf)).length - 1 = pre.length + 1 + suf.length := by
          simp
          omega
        rw [hindex]
        simpa [List.map_append, List.prod_append, mul_assoc] using hmul
      · have htail : ¬tail.Nodup := by
          intro htail
          exact hl (List.nodup_cons.2 ⟨ha, htail⟩)
        have hpositive : 0 < tail.length := by
          by_contra hnot
          have hzero : tail.length = 0 := Nat.eq_zero_of_not_pos hnot
          have hempty : tail = [] := List.eq_nil_of_length_eq_zero hzero
          subst tail
          simp at htail
        have hmul := Submodule.mul_mem_mul (ι_mem_filtration_one Q a) (ih htail)
        rw [filtration_mul] at hmul
        have hindex : 1 + (tail.length - 1) = tail.length := by omega
        rw [hindex] at hmul
        -- Expose the cons product after normalizing the filtration degree.
        change ι Q a * (tail.map (ι Q)).prod ∈ filtration Q tail.length
        exact hmul

private noncomputable def filtrationLeadingTermRaw (k : ℕ) :
    MultilinearMap R (fun _ : Fin (k + 1) => M) (CliffordAlgebra Q) :=
  (MultilinearMap.mkPiAlgebraFin R (k + 1) (CliffordAlgebra Q)).compLinearMap fun _ => ι Q

private theorem filtrationLeadingTermRaw_mem (k : ℕ) (v : Fin (k + 1) → M) :
    filtrationLeadingTermRaw Q k v ∈ filtration Q (k + 1) := by
  -- Expose the multilinear product as a list word, then as `map` for the filtration lemma.
  change (List.ofFn fun i => ι Q (v i)).prod ∈ filtration Q (k + 1)
  change (List.ofFn ((ι Q) ∘ v)).prod ∈ filtration Q (k + 1)
  rw [← List.map_ofFn]
  exact prod_map_ι_mem_filtration Q (l := List.ofFn v) (by simp)

private theorem filtrationLeadingTermRaw_mem_previous (k : ℕ) (v : Fin (k + 1) → M)
    {i j : Fin (k + 1)} (hij : v i = v j) (hijne : i ≠ j) :
    filtrationLeadingTermRaw Q k v ∈ filtration Q k := by
  -- Expose the raw multilinear product as the list word used by the repeated-word lemma.
  change (List.ofFn ((ι Q) ∘ v)).prod ∈ filtration Q k
  rw [← List.map_ofFn]
  have hnot : ¬(List.ofFn v).Nodup := by
    rw [List.nodup_ofFn]
    exact fun hinj => hijne (hinj hij)
  simpa only [List.length_ofFn, Nat.add_sub_cancel] using
    prod_map_ι_mem_filtration_pred_of_not_nodup Q (List.ofFn v) hnot

private noncomputable def filtrationLeadingTermAlternating (k : ℕ) :
    M [⋀^Fin (k + 1)]→ₗ[R] FiltrationGradedPiece Q (k + 1) :=
  let P := filtrationPreviousRestricted Q (k + 1)
  { toMultilinearMap :=
      P.mkQ.compMultilinearMap
        ((filtrationLeadingTermRaw Q k).codRestrict (filtration Q (k + 1))
          (filtrationLeadingTermRaw_mem Q k))
    map_eq_zero_of_eq' := by
      intro v i j hij hijne
      -- Expose the quotient/subtype wrapper so zero is membership in the lower filtration.
      change P.mkQ ⟨filtrationLeadingTermRaw Q k v, filtrationLeadingTermRaw_mem Q k v⟩ = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change filtrationLeadingTermRaw Q k v ∈ filtrationPrevious Q (k + 1)
      simpa only [filtrationPrevious_succ] using
        filtrationLeadingTermRaw_mem_previous Q k v hij hijne }

/-- The degree-`k + 1` leading-term map from the exterior power to the corresponding Clifford
filtration quotient. A repeated generator becomes a lower-filtration term under the Clifford
relation, so the product descends to an alternating map.

This is the `CommRing`-level half of the Layer 0 `filtrationGradedEquiv` target in the
[spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean#L62-L68). -/
noncomputable def filtrationLeadingTerm (k : ℕ) : ExteriorAlgebra.exteriorPower R (k + 1) M →ₗ[R]
    FiltrationGradedPiece Q (k + 1) :=
  exteriorPower.alternatingMapLinearEquiv (filtrationLeadingTermAlternating Q k)

/-- The leading-term map sends an exterior product to the class of the corresponding product of
Clifford generators. -/
@[simp]
theorem filtrationLeadingTerm_apply_ιMulti (k : ℕ) (v : Fin (k + 1) → M) :
    filtrationLeadingTerm Q k (exteriorPower.ιMulti R (k + 1) v) =
      Submodule.Quotient.mk ⟨(List.ofFn ((ι Q) ∘ v)).prod,
        by
          rw [← List.map_ofFn]
          exact prod_map_ι_mem_filtration Q (l := List.ofFn v) (by simp)⟩ := by
  simp only [filtrationLeadingTerm, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    filtrationLeadingTermAlternating]
  rfl

/-- The pullback along the filtration quotient of the range of the degree-`k + 1` leading-term map.
An element of `filtration Q (k + 1)` lies in its image under the inclusion exactly when its class
modulo `filtration Q k` is a leading term. -/
private noncomputable def leadingTermPreimage (k : ℕ) : Submodule R (filtration Q (k + 1)) :=
  (LinearMap.range (filtrationLeadingTerm Q k)).comap
    (filtrationPreviousRestricted Q (k + 1)).mkQ

/-- **The lower filtration consists of leading terms, trivially.** An element of `filtration Q k`
has zero class modulo `filtration Q k`, and zero is a leading term. -/
private theorem filtration_le_map_leadingTermPreimage (k : ℕ) :
    filtration Q k ≤ (leadingTermPreimage Q k).map (filtration Q (k + 1)).subtype := by
  intro z hz
  have hz' : z ∈ filtration Q (k + 1) := filtration_mono Q (by omega) hz
  refine Submodule.mem_map.2 ⟨⟨z, hz'⟩, ?_, rfl⟩
  have hzero :
      (filtrationPreviousRestricted Q (k + 1)).mkQ ⟨z, hz'⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (by
      rw [mem_filtrationPreviousRestricted_iff, filtrationPrevious_succ]
      exact hz)
  simp [leadingTermPreimage, hzero]

/-- **A product of `k + 1` generators is a leading term**, namely of the corresponding exterior
product, so the top piece of the successor filtration also consists of leading terms. -/
private theorem ι_range_pow_le_map_leadingTermPreimage (k : ℕ) :
    LinearMap.range (ι Q) ^ (k + 1) ≤
      (leadingTermPreimage Q k).map (filtration Q (k + 1)).subtype := by
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_le]
  rintro x hx
  obtain ⟨f, rfl⟩ := Set.mem_pow.1 hx
  choose v hv using fun i => LinearMap.mem_range.1 (f i).property
  have hprod : (List.ofFn fun i => (f i : CliffordAlgebra Q)).prod =
      (List.ofFn ((ι Q) ∘ v)).prod := by
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    exact (hv i).symm
  rw [hprod]
  refine Submodule.mem_map.2 ⟨⟨(List.ofFn ((ι Q) ∘ v)).prod, ?_⟩, ?_, rfl⟩
  · rw [← List.map_ofFn]
    exact prod_map_ι_mem_filtration Q (l := List.ofFn v) (by simp)
  · simpa [leadingTermPreimage] using LinearMap.mem_range.2
      ⟨exteriorPower.ιMulti R (k + 1) v, filtrationLeadingTerm_apply_ιMulti Q k v⟩

/-- Every element of the degree-`k + 1` Clifford filtration quotient is the leading term of an
element of the degree-`k + 1` exterior power. -/
theorem filtrationLeadingTerm_surjective (k : ℕ) :
    Function.Surjective (filtrationLeadingTerm Q k) := by
  -- Both pieces of the successor filtration split consist of leading terms.
  have hle : filtration Q (k + 1) ≤
      (leadingTermPreimage Q k).map (filtration Q (k + 1)).subtype :=
    (filtration_succ_eq_sup Q k).le.trans
      (sup_le (filtration_le_map_leadingTermPreimage Q k)
        (ι_range_pow_le_map_leadingTermPreimage Q k))
  intro z
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (filtrationPreviousRestricted Q (k + 1)) z
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 (hle x.property)
  obtain rfl : y = x := Subtype.ext hxy
  simpa [leadingTermPreimage] using hy

section Conjugation

/-- The grade involution preserves each step of the filtration: it multiplies a product of `n`
generators by `(-1) ^ n`. -/
theorem involute_mem_filtration {k : ℕ} {x : CliffordAlgebra Q} (hx : x ∈ filtration Q k) :
    involute x ∈ filtration Q k := by
  have h : filtration Q k ≤ (filtration Q k).comap (involute (Q := Q)).toLinearMap :=
    (filtration_le_iff Q).2 fun l hl => by
      rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, involute_prod_map_ι]
      exact Submodule.smul_mem _ _ (prod_map_ι_mem_filtration Q hl)
  exact h hx

/-- Reversal preserves each step of the filtration: it reverses the list of generators. -/
theorem reverse_mem_filtration {k : ℕ} {x : CliffordAlgebra Q} (hx : x ∈ filtration Q k) :
    reverse x ∈ filtration Q k := by
  have h : filtration Q k ≤ (filtration Q k).comap (reverse (Q := Q)) :=
    (filtration_le_iff Q).2 fun l hl => by
      rw [Submodule.mem_comap, reverse_prod_map_ι, ← List.map_reverse]
      exact prod_map_ι_mem_filtration Q (by simpa using hl)
  exact h hx

end Conjugation

section Map

variable {N : Type w} [AddCommGroup N] [Module R N] {Q' : QuadraticForm R N}

/-- An isometry of quadratic forms respects the degree filtration: it takes a product of generators
to a product of the same length. -/
theorem map_mem_filtration (f : Q →qᵢ Q') {k : ℕ} {x : CliffordAlgebra Q}
    (hx : x ∈ filtration Q k) : CliffordAlgebra.map f x ∈ filtration Q' k := by
  apply TauCeti.Algebra.map_mem_wordFiltration (ι Q) (CliffordAlgebra.map f) (ι Q') _ hx
  intro m
  rw [CliffordAlgebra.map_apply_ι]
  exact TauCeti.Algebra.apply_mem_wordFiltration_one (ι Q') (f m)

end Map

section ChangeForm

variable {Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M}

private theorem contractLeft_prod_map_ι_mem_filtration_pred (d : Module.Dual R M) :
    ∀ l : List M, contractLeft d (l.map (ι Q)).prod ∈ filtration Q (l.length - 1)
  | [] => by simp
  | [m] => by simp
  | m :: n :: l => by
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul]
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (by
        simpa using prod_map_ι_mem_filtration Q (l := n :: l) le_rfl)
    · have hmul :=
        Submodule.mul_mem_mul (ι_mem_filtration_one Q m)
          (contractLeft_prod_map_ι_mem_filtration_pred d (n :: l))
      rw [filtration_mul Q 1 ((n :: l).length - 1)] at hmul
      simpa [Nat.add_comm] using hmul

/-- Left contraction lowers every positive filtration step by one. -/
theorem contractLeft_mem_filtration_succ (d : Module.Dual R M) {k : ℕ}
    {x : CliffordAlgebra Q} (hx : x ∈ filtration Q (k + 1)) :
    contractLeft d x ∈ filtration Q k := by
  have h : filtration Q (k + 1) ≤ (filtration Q k).comap (contractLeft d) :=
    (filtration_le_iff Q).2 fun l hl => by
      rw [Submodule.mem_comap]
      exact filtration_mono Q (by omega)
        (contractLeft_prod_map_ι_mem_filtration_pred Q d l)
  exact h hx

/-- Left contraction preserves each filtration step. -/
theorem contractLeft_mem_filtration (d : Module.Dual R M) {k : ℕ} {x : CliffordAlgebra Q}
    (hx : x ∈ filtration Q k) : contractLeft d x ∈ filtration Q k :=
  contractLeft_mem_filtration_succ Q d (filtration_mono Q (Nat.le_succ k) hx)

/-- **Change of form has identity symbol, and its correction is even.** Transporting a word of at
most `k + 2` generators along `changeForm` changes it only by terms of filtration degree at most
`k`: the difference between the word in the `ι Q` and the same word in the `ι Q'` drops *two*
steps. It corrects by left contractions, and each contraction removes a pair of generators, so a
one-step bound would not be sharp. Mathlib's `changeForm_ι_mul_ι` is the first instance: a
two-generator word is corrected by the scalar `B m₁ m₂`, which lies in `filtration Q' 0`.

Where `changeForm_mem_filtration` says `changeForm` is a filtered map, this says its associated
graded map is the identity. -/
theorem changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration (h : B.toQuadraticMap = Q' - Q) :
    ∀ (l : List M) {k : ℕ}, l.length ≤ k + 2 →
      changeForm h (l.map (ι Q)).prod - (l.map (ι Q')).prod ∈ filtration Q' k
  | [], _, _ => by simp
  | [m], _, _ => by simp
  | m :: n :: l, 0, hk => by
      have hl : l = [] := List.length_eq_zero_iff.mp (by simpa using hk)
      subst hl
      simp [changeForm_ι_mul_ι]
  | m :: n :: l, k + 1, hk => by
      have hl : (n :: l).length ≤ k + 2 := by simpa using hk
      have hIH := changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration h (n :: l) hl
      -- The tail's transport is its own word plus a lower-degree correction, so it stays in range.
      have htail : changeForm h ((n :: l).map (ι Q)).prod ∈ filtration Q' (k + 2) := by
        simpa using Submodule.add_mem _ (filtration_mono Q' (by omega) hIH)
          (prod_map_ι_mem_filtration Q' hl)
      simp only [List.map_cons, List.prod_cons] at hIH htail ⊢
      rw [changeForm_ι_mul, sub_right_comm, ← mul_sub]
      refine Submodule.sub_mem _ ?_ ?_
      · simpa [Nat.add_comm] using mul_mem_filtration Q' (ι_mem_filtration_one Q' m) hIH
      · exact contractLeft_mem_filtration_succ Q' (B m) htail

private theorem changeForm_prod_map_ι_mem_filtration (h : B.toQuadraticMap = Q' - Q)
    (l : List M) : changeForm h (l.map (ι Q)).prod ∈ filtration Q' l.length := by
  have hdiff := changeForm_prod_map_ι_sub_prod_map_ι_mem_filtration Q h l
    (k := l.length) (by omega)
  simpa using Submodule.add_mem _ hdiff (prod_map_ι_mem_filtration Q' (le_refl l.length))

/-- Changing quadratic form by a bilinear form preserves each filtration step. -/
theorem changeForm_mem_filtration (h : B.toQuadraticMap = Q' - Q) {k : ℕ}
    {x : CliffordAlgebra Q} (hx : x ∈ filtration Q k) : changeForm h x ∈ filtration Q' k := by
  have hmap : filtration Q k ≤ (filtration Q' k).comap (changeForm h) :=
    (filtration_le_iff Q).2 fun l hl => by
      rw [Submodule.mem_comap]
      exact filtration_mono Q' hl (changeForm_prod_map_ι_mem_filtration Q h l)
  exact hmap hx

/-- The change-form equivalence transports every Clifford filtration step exactly. -/
@[simp]
theorem changeFormEquiv_map_filtration (h : B.toQuadraticMap = Q' - Q) (k : ℕ) :
    (filtration Q k).map (changeFormEquiv h).toLinearMap = filtration Q' k := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact changeForm_mem_filtration Q h hy
  · intro x hx
    refine ⟨(changeFormEquiv h).symm x, ?_, (changeFormEquiv h).apply_symm_apply x⟩
    rw [changeFormEquiv_symm]
    exact changeForm_mem_filtration Q' (changeForm.neg_proof h) hx

private theorem changeFormEquiv_mem_filtration_iff_aux
    (h : B.toQuadraticMap = Q' - Q) (k : ℕ)
    (x : CliffordAlgebra Q) : (changeFormEquiv h) x ∈ filtration Q' k ↔ x ∈ filtration Q k := by
  rw [← changeFormEquiv_map_filtration Q h k, Submodule.mem_map_equiv]
  rw [(changeFormEquiv h).symm_apply_apply]

/-- Membership in the filtration is invariant under the change-form equivalence. The statement
uses `changeForm`, the simplifier's normal form for applying `changeFormEquiv`. -/
@[simp]
theorem changeForm_mem_filtration_iff (h : B.toQuadraticMap = Q' - Q) (k : ℕ)
    (x : CliffordAlgebra Q) : changeForm h x ∈ filtration Q' k ↔ x ∈ filtration Q k := by
  simpa only [changeFormEquiv_apply] using changeFormEquiv_mem_filtration_iff_aux Q h k x

end ChangeForm

/-- Every step of the filtration is a finitely generated module as soon as `M` is: the `k`-th step
is generated by the products of at most `k` elements of a generating family of `M`. -/
theorem fg_filtration [Module.Finite R M] (k : ℕ) : (filtration Q k).FG := by
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
