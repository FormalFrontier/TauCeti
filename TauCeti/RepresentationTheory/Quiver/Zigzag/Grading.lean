/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedQuotient
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Relations
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis

/-!
# The zigzag relations are homogeneous

Every zigzag relator of a simple graph is homogeneous for the path-length grading of the path
algebra of the doubled quiver: the two quadratic families sit in degree two, and each long
generator is a single path, homogeneous of its own length. Consequently both relation ideals of
`TauCeti.RepresentationTheory.Quiver.Zigzag.Relations` are homogeneous ideals.

## Main results

* `TauCeti.IsZigzagRelator.isHomogeneousElem` and
  `TauCeti.IsQuadraticZigzagRelator.mem_grade_two`: the relators are homogeneous, the quadratic
  ones in degree two.
* `TauCeti.isHomogeneous_zigzagIdeal` and `TauCeti.isHomogeneous_quadraticZigzagIdeal`: **the
  relation ideals are homogeneous.**
* `TauCeti.zigzagGrade`: the induced degree-`n` piece on the relation quotient, the descent of
  `TauCeti.PathAlgebra.grade` along the quotient map.
* `TauCeti.isInternal_zigzagGrade`: **the quotient is the internal direct sum of its graded
  pieces**, the comparison of the direct-sum graded algebra with the ungraded quotient asked for
  by the roadmap.
* `TauCeti.zigzagGrade_zero_eq_span_range_vertexIdempotent`,
  `TauCeti.zigzagGrade_one_eq_span_range_dart` and
  `TauCeti.zigzagGrade_two_eq_span_range_zigzagVolume`: the concrete pieces, spanned by the
  vertex idempotent classes, the arrow classes, and the volume classes respectively.
* `TauCeti.zigzagGrade_eq_bot_of_three_le`: every piece of degree at least three vanishes.

## References

This is the grading clause of Layer 0 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which
asks for the relation ideal to be homogeneous for the path-length grading and for the induced
nonnegative grading on the quotient to be compared with the ungraded quotient rather than
postulated as an unrelated graded copy. See Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3.
-/

public section

namespace TauCeti

open PathAlgebra

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-- **The quadratic zigzag relators sit in degree two**: a non-returning length-two path is a
single basis path of length two, and a difference of two length-two backtracks is a difference of
two such. -/
theorem IsQuadraticZigzagRelator.mem_grade_two {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsQuadraticZigzagRelator k G x) : x ∈ grade k (DoubledQuiver G) 2 := by
  cases hx with
  | nonreturn p hp _ => exact ofPath_mem_grade_of_length hp
  | equal_backtracks p q hp hq =>
    exact Submodule.sub_mem _ (ofPath_mem_grade_of_length hp) (ofPath_mem_grade_of_length hq)

/-- The quadratic zigzag relators are homogeneous. -/
theorem IsQuadraticZigzagRelator.isHomogeneousElem {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsQuadraticZigzagRelator k G x) :
    SetLike.IsHomogeneousElem (grade k (DoubledQuiver G)) x :=
  ⟨2, IsQuadraticZigzagRelator.mem_grade_two k G hx⟩

/-- **The uniform zigzag relators are homogeneous**: the quadratic ones in degree two, and each
long generator in the degree its own length names. -/
theorem IsZigzagRelator.isHomogeneousElem {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) : SetLike.IsHomogeneousElem (grade k (DoubledQuiver G)) x := by
  cases hx with
  | quadratic h => exact IsQuadraticZigzagRelator.isHomogeneousElem k G h
  | long_path y _ => exact ⟨y.2.2.length, ofPath_mem_grade y⟩

variable [Finite V]

/-- **The quadratic relation ideal is homogeneous** for the path-length grading. -/
theorem isHomogeneous_quadraticZigzagIdeal :
    (quadraticZigzagIdeal k G).asIdeal.IsHomogeneous (grade k (DoubledQuiver G)) := by
  rw [quadraticZigzagIdeal_eq_span]
  exact TwoSidedIdeal.homogeneous_span _ fun _ hx =>
    IsQuadraticZigzagRelator.isHomogeneousElem k G hx

/-- **The uniform relation ideal is homogeneous** for the path-length grading. This is the
condition needed to descend the grading to the zigzag quotient. -/
theorem isHomogeneous_zigzagIdeal :
    (zigzagIdeal k G).asIdeal.IsHomogeneous (grade k (DoubledQuiver G)) := by
  rw [zigzagIdeal_eq_span]
  exact TwoSidedIdeal.homogeneous_span _ fun _ hx => IsZigzagRelator.isHomogeneousElem k G hx

/-! ### The induced grading on the relation quotient -/

open DoubledQuiver

/-- **The induced grading on the zigzag relation quotient**: the degree-`n` piece is the image of
the degree-`n` piece of the path-length grading of the path algebra of the doubled quiver under
the quotient map. Because the relation ideal is homogeneous
(`TauCeti.isHomogeneous_zigzagIdeal`), this is a genuine grading: multiplication adds degrees
(`PathAlgebra.gradeQuot_mul_gradeQuot_le`) and `TauCeti.isInternal_zigzagGrade` compares the
direct sum of the pieces with the quotient itself rather than with a separate graded copy. -/
@[expose]
noncomputable def zigzagGrade (n : ℕ) : Submodule k (nonisolatedZigzagQuotient k G) :=
  PathAlgebra.gradeQuot k (zigzagIdeal k G) n

/-- Membership in the induced degree-`n` piece is being the class of a homogeneous element. -/
theorem mem_zigzagGrade_iff {n : ℕ} {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagGrade k G n ↔
      ∃ y ∈ PathAlgebra.grade k (DoubledQuiver G) n, zigzagMk k G y = x := by
  refine ⟨fun hx => ?_, fun h => ?_⟩
  · obtain ⟨y, hy, hEq⟩ := (PathAlgebra.mem_gradeQuot_iff (k := k)).mp hx
    exact ⟨y, hy, (zigzagMk_apply k G y).trans hEq⟩
  · obtain ⟨y, hy, hEq⟩ := h
    refine (PathAlgebra.mem_gradeQuot_iff (k := k)).mpr ⟨y, hy, ?_⟩
    rwa [zigzagMk_apply k G] at hEq

/-- A homogeneous element lands in the piece its degree names. -/
theorem zigzagMk_mem_zigzagGrade {n : ℕ} {y : pathAlgebra k (DoubledQuiver G)}
    (hy : y ∈ PathAlgebra.grade k (DoubledQuiver G) n) :
    zigzagMk k G y ∈ zigzagGrade k G n :=
  (mem_zigzagGrade_iff k G).mpr ⟨y, hy, rfl⟩

/-- **The quotient is the internal direct sum of its graded pieces**: this is the comparison of
the direct-sum graded algebra with the ungraded quotient asked for by the roadmap, in the
internal sense in which the pieces are submodules of the quotient itself rather than a separate
graded copy. -/
theorem isInternal_zigzagGrade :
    DirectSum.IsInternal (zigzagGrade k G) :=
  PathAlgebra.isInternal_gradeQuot k (zigzagIdeal k G) (isHomogeneous_zigzagIdeal k G)

/-- The multiplicative structure of the induced pieces: multiplication adds degrees and the unit
is homogeneous of degree zero. -/
theorem zigzagGradedMonoid : SetLike.GradedMonoid (zigzagGrade k G) :=
  PathAlgebra.gradedMonoidGradeQuot k (zigzagIdeal k G)

/-- **The zigzag relation quotient is a graded algebra** for the induced path-length grading.
This is kept as a definition rather than an instance so that callers choose when to introduce it
locally; see `TauCeti.PathAlgebra.gradedAlgebraGradeQuot`. -/
@[instance_reducible]
noncomputable def zigzagGradedAlgebra : GradedAlgebra (zigzagGrade k G) :=
  PathAlgebra.gradedAlgebraGradeQuot k (zigzagIdeal k G) (isHomogeneous_zigzagIdeal k G)

/-- **Degree zero is spanned by the vertex idempotent classes. -/
theorem zigzagGrade_zero_eq_span_range_vertexIdempotent :
    zigzagGrade k G 0 =
      Submodule.span k
        (Set.range fun i : V => zigzagMk k G (vertexIdempotent k (vertex G i))) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_zigzagGrade_iff k G).mp hx
    clear hx
    rw [PathAlgebra.grade_zero_eq_span_range_vertexIdempotent] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      refine Submodule.subset_span ⟨(vertexEquiv G).symm v, ?_⟩
      simp
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
        rw [map_add]
        exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
        rw [map_smul]
        exact Submodule.smul_mem _ c ih
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)

/-- **Degree one is spanned by the arrow classes**, one for each dart of the graph. -/
theorem zigzagGrade_one_eq_span_range_dart :
    zigzagGrade k G 1 =
      Submodule.span k (Set.range fun d : G.Dart =>
        zigzagMk k G (ofArrow (arrow G d.adj))) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_zigzagGrade_iff k G).mp hx
    clear hx
    rw [PathAlgebra.grade_one_eq_span_range_ofArrow] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨a, b, e⟩, rfl⟩ := hw
      obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
        ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
      obtain ⟨j, rfl⟩ : ∃ j, b = vertex G j :=
        ⟨(vertexEquiv G).symm b, (vertexEquiv_symm_apply G b).symm⟩
      have hadj : G.Adj i j := (DoubledQuiver.nonempty_hom_iff G).mp ⟨e⟩
      have heq : arrow G (⟨(i, j), hadj⟩ : G.Dart).adj = e :=
        Subsingleton.elim _ _
      refine Submodule.subset_span ⟨⟨(i, j), hadj⟩, ?_⟩
      change zigzagMk k G (ofArrow (arrow G (⟨(i, j), hadj⟩ : G.Dart).adj))
          = zigzagMk k G (ofArrow e)
      rw [heq]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
        rw [map_add]
        exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
        rw [map_smul]
        exact Submodule.smul_mem _ c ih
  · rw [Submodule.span_le]
    rintro e ⟨d, rfl⟩
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.ofArrow_mem_grade_one _)

/-- **Degree two is spanned by the volume classes**: every length-two path either does not return,
and dies, or returns to its source, and equals a backtrack there. -/
theorem zigzagGrade_two_eq_span_range_zigzagVolume :
    zigzagGrade k G 2 =
      Submodule.span k (Set.range fun i : V => zigzagVolume k G i) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_zigzagGrade_iff k G).mp hx
    clear hx
    simp only [PathAlgebra.grade] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t, ht, rfl⟩ := hw
      obtain ⟨a, b, p⟩ := t
      have ht' : p.length = 2 := ht
      obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
        ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
      rcases eq_or_ne b (vertex G i) with rfl | hne
      · obtain ⟨m, h, hp⟩ := exists_eq_backtrackPath G p ht'
        change zigzagMk k G (ofPath ⟨vertex G i, vertex G i, p⟩) ∈ _
        rw [hp, ← backtrackElem_eq_ofPath, zigzagMk_backtrackElem_eq_zigzagVolume]
        exact Submodule.subset_span ⟨i, rfl⟩
      · rw [zigzagMk_ofPath_eq_zero_of_ne k G p ht' (Ne.symm hne)]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
        rw [map_add]
        exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
        rw [map_smul]
        exact Submodule.smul_mem _ c ih
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    change zigzagVolume k G i ∈ zigzagGrade k G 2
    by_cases hi : ∃ j, G.Adj i j
    · obtain ⟨j, hj⟩ := hi
      rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj]
      refine zigzagMk_mem_zigzagGrade k G ?_
      rw [backtrackElem_eq_ofPath]
      exact PathAlgebra.ofPath_mem_grade_of_length (length_backtrackPath G hj)
    · have hiso : G.IsIsolated i := fun w hw => hi ⟨w, hw⟩
      rw [zigzagVolume_eq_zero_of_isIsolated k G hiso]
      exact Submodule.zero_mem _

/-- Every piece of degree at least three vanishes: all long paths are relations. -/
theorem zigzagGrade_eq_bot_of_three_le {n : ℕ} (hn : 3 ≤ n) : zigzagGrade k G n = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, hy, hEq⟩ := (mem_zigzagGrade_iff k G).mp hx
  subst hEq
  clear hx
  have hy' : y ∈ (zigzagIdeal k G).asIdeal := by
    simp only [PathAlgebra.grade] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t, ht', rfl⟩ := hw
      have hlen : t.snd.snd.length = n := ht'
      refine TwoSidedIdeal.mem_asIdeal.mpr
        (mem_zigzagIdeal_of_isZigzagRelator k G
          (IsZigzagRelator.long_path t (hn.trans ht'.symm.le)))
    | zero => exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ ih
  rw [(zigzagMk_eq_zero_iff k G).mpr hy']
  exact (Submodule.mem_bot k).mp rfl

end TauCeti
