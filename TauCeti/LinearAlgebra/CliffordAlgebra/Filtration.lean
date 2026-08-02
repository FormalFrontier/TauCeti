/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Finiteness.Subalgebra

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

Following the roadmap, the filtration is *not* the submodule power `LinearMap.range (ι Q) ^ k`:
powers of a submodule of a noncommutative algebra collect the products of *exactly* `k` generators.
The relation between the two is `TauCeti.CliffordAlgebra.filtration_eq_iSup_pow`, which writes
`filtration Q k` as the supremum of those powers over `i ≤ k`; this is the sense in which the
filtration is the "at most `k`" companion of Mathlib's `evenOdd`, whose definition is the analogous
supremum over the `i` of a fixed parity.

## Main definitions

* `TauCeti.CliffordAlgebra.filtration Q k`: the span of the products of at most `k` generators.

## Main results

* `TauCeti.CliffordAlgebra.prod_map_ι_mem_filtration` and
  `TauCeti.CliffordAlgebra.filtration_le_iff`: the products of at most `k` generators lie in the
  `k`-th step and generate it, which is how memberships and bounds are proved.
* `TauCeti.CliffordAlgebra.filtration_zero` and
  `TauCeti.CliffordAlgebra.filtration_one` compute the first two steps, as the scalars and the
  scalars together with `LinearMap.range (ι Q)`.
* `TauCeti.CliffordAlgebra.filtration_mul`: the filtration is multiplicative, and in fact exactly
  so: `filtration Q i * filtration Q j = filtration Q (i + j)`. This is the statement that makes
  the associated graded object an algebra, and it is the prerequisite the roadmap asks for before
  anything downstream; `TauCeti.CliffordAlgebra.filtration_pow` is its iterate.
* `TauCeti.CliffordAlgebra.filtration_succ_eq_sup`: the recursion for the successor step.
* `TauCeti.CliffordAlgebra.filtration_eq_iSup_pow`: the comparison with the submodule powers of
  `LinearMap.range (ι Q)`.
* `TauCeti.CliffordAlgebra.filtrationLeadingTerm` and
  `TauCeti.CliffordAlgebra.filtrationLeadingTerm_surjective`: the exterior-power leading-term map
  onto each successive filtration quotient, the surjectivity half of the associated-graded bridge.
* `TauCeti.CliffordAlgebra.iSup_filtration_eq_top` and
  `TauCeti.CliffordAlgebra.exists_mem_filtration`: the filtration is exhaustive.
* `TauCeti.CliffordAlgebra.involute_mem_filtration`,
  `TauCeti.CliffordAlgebra.reverse_mem_filtration` and
  `TauCeti.CliffordAlgebra.map_mem_filtration`: the filtration is preserved by the grade
  involution, by reversal, and by an isometry of quadratic forms.
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
of exactly `k` generators; see `filtration_eq_iSup_pow` for the comparison. -/
def filtration (Q : QuadraticForm R M) (k : ℕ) : Submodule R (CliffordAlgebra Q) :=
  Submodule.span R {x | ∃ l : List M, l.length ≤ k ∧ (l.map (ι Q)).prod = x}

variable (Q : QuadraticForm R M)

/-- A product of at most `k` generators lies in the `k`-th step of the filtration. This is the
generating family, so most `filtration` memberships reduce to it. -/
theorem prod_map_ι_mem_filtration {k : ℕ} {l : List M} (hl : l.length ≤ k) :
    (l.map (ι Q)).prod ∈ filtration Q k :=
  Submodule.subset_span ⟨l, hl, rfl⟩

/-- The `k`-th step of the filtration is spanned by the products of at most `k` generators, so a
submodule contains it exactly when it contains those products. This is `Submodule.span_le` in the
form in which it applies to `filtration`. -/
theorem filtration_le_iff {k : ℕ} {p : Submodule R (CliffordAlgebra Q)} :
    filtration Q k ≤ p ↔ ∀ l : List M, l.length ≤ k → (l.map (ι Q)).prod ∈ p := by
  rw [filtration, Submodule.span_le]
  constructor
  · intro h l hl
    exact h ⟨l, hl, rfl⟩
  · rintro h _ ⟨l, hl, rfl⟩
    exact h l hl

/-- The filtration is increasing: a product of at most `i` generators is a product of at most `j`
of them whenever `i ≤ j`. -/
theorem filtration_mono : Monotone (filtration Q) := fun _ _ hij =>
  (filtration_le_iff Q).2 fun _ hl => prod_map_ι_mem_filtration Q (hl.trans hij)

/-- The zeroth step of the filtration is the module of scalars, the span of the empty product. -/
@[simp]
theorem filtration_zero : filtration Q 0 = 1 := by
  rw [filtration, Submodule.one_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]
    simp
  · rintro rfl
    exact ⟨[], le_rfl, rfl⟩

/-- `1` is the empty product of generators, so it lies in every step of the filtration. -/
theorem one_mem_filtration (k : ℕ) : (1 : CliffordAlgebra Q) ∈ filtration Q k := by
  simpa using prod_map_ι_mem_filtration Q (l := []) (Nat.zero_le k)

/-- The submodule form of `one_mem_filtration`: the scalars sit inside every step. -/
theorem one_le_filtration (k : ℕ) : 1 ≤ filtration Q k :=
  Submodule.one_le.2 (one_mem_filtration Q k)

/-- Scalars lie in every step of the filtration, being multiples of the empty product. -/
theorem algebraMap_mem_filtration (r : R) (k : ℕ) :
    algebraMap R (CliffordAlgebra Q) r ∈ filtration Q k := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (one_mem_filtration Q k)

/-- A generator is a product of one generator, so it lies in the first step. -/
theorem ι_mem_filtration_one (m : M) : ι Q m ∈ filtration Q 1 := by
  simpa using prod_map_ι_mem_filtration Q (l := [m]) le_rfl

/-- The submodule form of `ι_mem_filtration_one`: all of `LinearMap.range (ι Q)` lies in the first
step. -/
theorem ι_range_le_filtration_one : LinearMap.range (ι Q) ≤ filtration Q 1 := by
  rintro _ ⟨m, rfl⟩
  exact ι_mem_filtration_one Q m

/-- A product of two generators lies in the second step. This is the membership the roadmap's
bivectors use. -/
theorem ι_mul_ι_mem_filtration_two (a b : M) : ι Q a * ι Q b ∈ filtration Q 2 := by
  simpa using prod_map_ι_mem_filtration Q (l := [a, b]) le_rfl

/-- **The filtration is multiplicative**, and exactly so. Concatenating a product of at most `i`
generators with a product of at most `j` generators gives a product of at most `i + j` of them, and
conversely a product of at most `i + j` generators splits after its `i`-th factor. In particular the
associated graded object of the filtration is an algebra. -/
theorem filtration_mul (i j : ℕ) :
    filtration Q i * filtration Q j = filtration Q (i + j) := by
  refine le_antisymm ?_ ?_
  · rw [filtration, filtration, Submodule.span_mul_span, Submodule.span_le, Set.mul_subset_iff]
    rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩
    rw [← List.prod_append, ← List.map_append]
    exact prod_map_ι_mem_filtration Q (by simpa using Nat.add_le_add h₁ h₂)
  · refine (filtration_le_iff Q).2 fun l hl => ?_
    rw [← List.take_append_drop i l, List.map_append, List.prod_append]
    refine Submodule.mul_mem_mul (prod_map_ι_mem_filtration Q (List.length_take_le i l))
      (prod_map_ι_mem_filtration Q ?_)
    rw [List.length_drop]
    omega

/-- Iterating `filtration_mul`: the `n`-th submodule power of the `i`-th step is the `i * n`-th
step. -/
theorem filtration_pow (i n : ℕ) : filtration Q i ^ n = filtration Q (i * n) := by
  induction n with
  | zero => rw [pow_zero, Nat.mul_zero, filtration_zero]
  | succ n ih => rw [pow_succ, ih, filtration_mul, Nat.mul_succ]

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
theorem ι_range_pow_le_filtration (n : ℕ) : LinearMap.range (ι Q) ^ n ≤ filtration Q n := by
  induction n with
  | zero => rw [pow_zero, filtration_zero]
  | succ n ih =>
    calc LinearMap.range (ι Q) ^ (n + 1)
        = LinearMap.range (ι Q) ^ n * LinearMap.range (ι Q) := pow_succ _ _
      _ ≤ filtration Q n * filtration Q 1 := mul_le_mul' ih (ι_range_le_filtration_one Q)
      _ = filtration Q (n + 1) := filtration_mul Q n 1

/-- The comparison between the filtration and the submodule powers of `LinearMap.range (ι Q)`:
`filtration Q k` collects the products of at most `k` generators, so it is the supremum of the
powers up to `k`. Compare `CliffordAlgebra.evenOdd`, the supremum of the powers whose exponent has
a fixed parity. -/
theorem filtration_eq_iSup_pow (k : ℕ) :
    filtration Q k = ⨆ i : {i : ℕ // i ≤ k}, LinearMap.range (ι Q) ^ (i : ℕ) := by
  refine le_antisymm ((filtration_le_iff Q).2 fun l hl => ?_) (iSup_le fun i => ?_)
  · exact Submodule.mem_iSup_of_mem ⟨l.length, hl⟩ (prod_map_ι_mem_pow Q l)
  · exact (ι_range_pow_le_filtration Q i).trans (filtration_mono Q i.2)

/-- The successor step of the filtration adjoins the products of exactly `k + 1` generators. -/
theorem filtration_succ_eq_sup (k : ℕ) :
    filtration Q (k + 1) = filtration Q k ⊔ LinearMap.range (ι Q) ^ (k + 1) := by
  refine le_antisymm ((filtration_le_iff Q).2 fun l hl => ?_)
    (sup_le (filtration_mono Q (Nat.le_succ k)) (ι_range_pow_le_filtration Q (k + 1)))
  rcases eq_or_lt_of_le hl with h | h
  · exact Submodule.mem_sup_right (h ▸ prod_map_ι_mem_pow Q l)
  · exact Submodule.mem_sup_left (prod_map_ι_mem_filtration Q (Nat.lt_succ_iff.1 h))

/-- The first step of the filtration is the scalars together with the generators. -/
@[simp]
theorem filtration_one : filtration Q 1 = 1 ⊔ LinearMap.range (ι Q) := by
  simpa [filtration_zero] using filtration_succ_eq_sup Q 0

/-- **The filtration is exhaustive.** Every element of the Clifford algebra is a combination of
products of generators, so it lies in some step. -/
theorem iSup_filtration_eq_top : ⨆ k, filtration Q k = ⊤ := by
  rw [eq_top_iff, ← iSup_ι_range_eq_top Q]
  exact iSup_mono' fun i => ⟨i, ι_range_pow_le_filtration Q i⟩

/-- The pointwise form of `iSup_filtration_eq_top`, available because the filtration is a directed
family. -/
theorem exists_mem_filtration (x : CliffordAlgebra Q) : ∃ k, x ∈ filtration Q k := by
  have hx : x ∈ ⨆ k, filtration Q k := by rw [iSup_filtration_eq_top]; exact Submodule.mem_top
  rwa [Submodule.mem_iSup_of_directed _ (filtration_mono Q).directed_le] at hx

/-- The generators of a Clifford algebra anticommute up to the polarization of `Q`, which is a
scalar: the associated graded algebra of the filtration is graded-commutative in degree one, the
symmetric sum `ι Q a * ι Q b + ι Q b * ι Q a` dropping to the previous step of the filtration. -/
theorem ι_mul_ι_add_swap_mem_filtration_zero (a b : M) :
    ι Q a * ι Q b + ι Q b * ι Q a ∈ filtration Q 0 := by
  rw [ι_mul_ι_add_swap]
  exact algebraMap_mem_filtration Q _ 0

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

private noncomputable def filtrationLeadingTermAlternating (k : ℕ) : M [⋀^Fin (k + 1)]→ₗ[R]
    (filtration Q (k + 1) ⧸ (filtration Q k).comap (filtration Q (k + 1)).subtype) :=
  let P : Submodule R (filtration Q (k + 1)) :=
    (filtration Q k).comap (filtration Q (k + 1)).subtype
  { toMultilinearMap :=
      P.mkQ.compMultilinearMap
        ((filtrationLeadingTermRaw Q k).codRestrict (filtration Q (k + 1))
          (filtrationLeadingTermRaw_mem Q k))
    map_eq_zero_of_eq' := by
      intro v i j hij hijne
      -- Expose the quotient/subtype wrapper so zero is membership in the lower filtration.
      change P.mkQ ⟨filtrationLeadingTermRaw Q k v, filtrationLeadingTermRaw_mem Q k v⟩ = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact filtrationLeadingTermRaw_mem_previous Q k v hij hijne }

/-- The degree-`k + 1` leading-term map from the exterior power to the corresponding Clifford
filtration quotient. A repeated generator becomes a lower-filtration term under the Clifford
relation, so the product descends to an alternating map.

This is the surjectivity half of the Layer 0 `filtrationGradedEquiv` target in the
[spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean#L62-L68). -/
noncomputable def filtrationLeadingTerm (k : ℕ) : ExteriorAlgebra.exteriorPower R (k + 1) M →ₗ[R]
    (filtration Q (k + 1) ⧸ (filtration Q k).comap (filtration Q (k + 1)).subtype) :=
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

/-- Every element of the degree-`k + 1` Clifford filtration quotient is the leading term of an
element of the degree-`k + 1` exterior power. -/
theorem filtrationLeadingTerm_surjective (k : ℕ) :
    Function.Surjective (filtrationLeadingTerm Q k) := by
  -- Pull the leading-term range back along the quotient, then use the successor filtration split.
  let P : Submodule R (filtration Q (k + 1)) :=
    (filtration Q k).comap (filtration Q (k + 1)).subtype
  let q : filtration Q (k + 1) →ₗ[R] (filtration Q (k + 1) ⧸ P) := P.mkQ
  let T : Submodule R (filtration Q (k + 1)) :=
    (LinearMap.range (filtrationLeadingTerm Q k)).comap q
  have hle : filtration Q (k + 1) ≤ T.map (filtration Q (k + 1)).subtype := by
    calc
      filtration Q (k + 1) = filtration Q k ⊔ LinearMap.range (ι Q) ^ (k + 1) :=
        filtration_succ_eq_sup Q k
      _ ≤ T.map (filtration Q (k + 1)).subtype := sup_le (by
        intro z hz
        have hz' : z ∈ filtration Q (k + 1) := filtration_mono Q (by omega) hz
        let z' : filtration Q (k + 1) := ⟨z, hz'⟩
        refine Submodule.mem_map.2 ⟨z', ?_, rfl⟩
        -- Unfold the range comap and quotient map before proving a lower-filtration class is zero.
        change q z' ∈ LinearMap.range (filtrationLeadingTerm Q k)
        change P.mkQ z' ∈ LinearMap.range (filtrationLeadingTerm Q k)
        have hzP : z' ∈ P := by
          -- Membership in the comap is exactly the original lower-filtration membership.
          change z ∈ filtration Q k
          exact hz
        have hzero : P.mkQ z' = 0 := by
          rw [Submodule.mkQ_apply]
          exact (Submodule.Quotient.mk_eq_zero P).mpr hzP
        rw [hzero]
        exact LinearMap.mem_range.2 ⟨0, map_zero _⟩) (by
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
        · change q ⟨(List.ofFn ((ι Q) ∘ v)).prod, ?_⟩ ∈
            LinearMap.range (filtrationLeadingTerm Q k)
          -- Expose the quotient map after the subtype witness is constructed.
          change P.mkQ ⟨(List.ofFn ((ι Q) ∘ v)).prod, ?_⟩ ∈
            LinearMap.range (filtrationLeadingTerm Q k)
          rw [Submodule.mkQ_apply]
          exact LinearMap.mem_range.2 ⟨exteriorPower.ιMulti R (k + 1) v,
            filtrationLeadingTerm_apply_ιMulti Q k v⟩)
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P z
  have hx : (x : CliffordAlgebra Q) ∈ T.map (filtration Q (k + 1)).subtype := hle x.property
  rcases Submodule.mem_map.1 hx with ⟨y, hy, hxy⟩
  have hxy' : y = x := Subtype.ext hxy
  subst x
  -- Unfold the range comap one final time to extract an exterior-power preimage.
  change q y ∈ LinearMap.range (filtrationLeadingTerm Q k) at hy
  change P.mkQ y ∈ LinearMap.range (filtrationLeadingTerm Q k) at hy
  exact LinearMap.mem_range.1 hy

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
  have h : filtration Q k ≤ (filtration Q' k).comap (CliffordAlgebra.map f).toLinearMap :=
    (filtration_le_iff Q).2 fun l hl => by
      rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_list_prod, List.map_map]
      simpa [Function.comp_def] using
        prod_map_ι_mem_filtration Q' (l := l.map f) (by simpa using hl)
  exact h hx

end Map

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
