/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis

/-!
# The zigzag relations are homogeneous and the induced grading

Every zigzag relator of a simple graph is homogeneous for the path-length grading of the path
algebra of the doubled quiver: the two quadratic families sit in degree two, and each long
generator is a single path, homogeneous of its own length. Consequently both relation ideals of
`TauCeti.RepresentationTheory.Quiver.Zigzag.Relations` are homogeneous ideals.

Because the relation ideals are homogeneous, the generic descent
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient` applies to them: the relation quotient
carries the induced grading `TauCeti.zigzagGrade`, this file packages its graded-algebra
structure, and it computes the concrete pieces.

## Main definitions

* `TauCeti.zigzagGrade`: the induced degree-`n` piece on the relation quotient, the descent of
  `TauCeti.PathAlgebra.grade` along the quotient map.
* `TauCeti.zigzagGradedAlgebra`: **the zigzag relation quotient is a graded algebra** for the
  induced path-length grading.

## Main results

* `TauCeti.IsZigzagRelator.isHomogeneousElem` and
  `TauCeti.IsQuadraticZigzagRelator.mem_grade_two`: the relators are homogeneous, the quadratic
  ones in degree two.
* `TauCeti.isHomogeneous_zigzagIdeal` and `TauCeti.isHomogeneous_quadraticZigzagIdeal`: **the
  relation ideals are homogeneous.**
* `TauCeti.isInternal_zigzagGrade`: **the quotient is the internal direct sum of its graded
  pieces**, the comparison of the direct-sum graded algebra with the ungraded quotient asked for
  by the roadmap.
* `TauCeti.zigzagGrade_zero_eq_span_range_vertexIdempotent`,
  `TauCeti.zigzagGrade_one_eq_span_range_ofArrow` and
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
the quotient map. Multiplication adds degrees for any relation ideal
(`TauCeti.GradedAlgebra.gradeQuot_mul_gradeQuot_le`); because the relation ideal is homogeneous
(`TauCeti.isHomogeneous_zigzagIdeal`), `TauCeti.isInternal_zigzagGrade` also holds, comparing the
direct sum of the pieces with the quotient itself rather than with a separate graded copy. -/
noncomputable def zigzagGrade (n : ℕ) : Submodule k (nonisolatedZigzagQuotient k G) :=
  TauCeti.GradedAlgebra.gradeQuot (grade k (DoubledQuiver G)) (zigzagIdeal k G).asIdeal n

/-- A homogeneous element lands in the piece its degree names. -/
@[simp]
theorem zigzagMk_mem_zigzagGrade {n : ℕ} {y : pathAlgebra k (DoubledQuiver G)}
    (hy : y ∈ grade k (DoubledQuiver G) n) : zigzagMk k G y ∈ zigzagGrade k G n := by
  rw [zigzagGrade, zigzagMk_apply]
  exact TauCeti.GradedAlgebra.mk_mem_gradeQuot _ _ hy

/-- **The quotient is the internal direct sum of its graded pieces**: this is the comparison of
the direct-sum graded algebra with the ungraded quotient asked for by the roadmap, in the
internal sense in which the pieces are submodules of the quotient itself rather than a separate
graded copy. -/
theorem isInternal_zigzagGrade :
    DirectSum.IsInternal (zigzagGrade k G) :=
  TauCeti.GradedAlgebra.isInternal_gradeQuot (grade k (DoubledQuiver G))
    (zigzagIdeal k G).asIdeal (isHomogeneous_zigzagIdeal k G)

/-- Multiplication adds degrees in the induced grading: the product of a degree-`m` class and a
degree-`n` class lies in degree `m + n`. -/
theorem mul_mem_zigzagGrade {m n : ℕ} {x y : nonisolatedZigzagQuotient k G}
    (hx : x ∈ zigzagGrade k G m) (hy : y ∈ zigzagGrade k G n) :
    x * y ∈ zigzagGrade k G (m + n) :=
  TauCeti.GradedAlgebra.mul_mem_gradeQuot _ _ hx hy

/-- **The zigzag relation quotient is a graded algebra** for the induced path-length grading.
This is kept as a definition rather than an instance so that callers choose when to introduce it
locally; see `TauCeti.GradedAlgebra.gradedAlgebraGradeQuot`. -/
@[instance_reducible]
noncomputable def zigzagGradedAlgebra : GradedAlgebra (zigzagGrade k G) :=
  TauCeti.GradedAlgebra.gradedAlgebraGradeQuot (grade k (DoubledQuiver G))
    (zigzagIdeal k G).asIdeal (isHomogeneous_zigzagIdeal k G)

/-- The descended piece is spanned by the images of any spanning family of the original piece:
a member of the descended degree-`n` piece lies in the span of `T` as soon as the image under
`zigzagMk` of every generator of the original piece does. Private helper for the computations of
the concrete pieces below. -/
private theorem mem_span_of_mem_zigzagGrade {n : ℕ}
    {S : Set (pathAlgebra k (DoubledQuiver G))}
    (hs : grade k (DoubledQuiver G) n = Submodule.span k S)
    {T : Set (nonisolatedZigzagQuotient k G)}
    (hmem : ∀ z ∈ S, Ideal.Quotient.mk (zigzagIdeal k G).asIdeal z ∈ Submodule.span k T)
    {w : nonisolatedZigzagQuotient k G} (hw : w ∈ zigzagGrade k G n) :
    w ∈ Submodule.span k T := by
  have heq := TauCeti.GradedAlgebra.gradeQuot_eq_span_image
    (grade k (DoubledQuiver G)) (zigzagIdeal k G).asIdeal (i := n) hs
  rw [zigzagGrade, heq] at hw
  refine (Submodule.span_le.2 ?_) hw
  rintro u ⟨z, hz, rfl⟩
  exact hmem z hz

/-- **Degree zero is spanned by the vertex idempotent classes.** -/
theorem zigzagGrade_zero_eq_span_range_vertexIdempotent :
    zigzagGrade k G 0 =
      Submodule.span k
        (Set.range fun i : V => zigzagMk k G (vertexIdempotent k (vertex G i))) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine mem_span_of_mem_zigzagGrade k G
      (PathAlgebra.grade_zero_eq_span_range_vertexIdempotent k (DoubledQuiver G)) ?_ hw
    rintro z ⟨v, rfl⟩
    rw [← zigzagMk_apply k G]
    exact Submodule.subset_span ⟨(vertexEquiv G).symm v, by simp⟩
  · rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)

/-- **Degree one is spanned by the arrow classes**, one for each dart of the graph. -/
theorem zigzagGrade_one_eq_span_range_ofArrow :
    zigzagGrade k G 1 =
      Submodule.span k (Set.range fun d : G.Dart =>
        zigzagMk k G (ofArrow (arrow G d.adj))) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine mem_span_of_mem_zigzagGrade k G
      (PathAlgebra.grade_one_eq_span_range_ofArrow) ?_ hw
    rintro z ⟨⟨a, b, e⟩, rfl⟩
    rw [← zigzagMk_apply k G]
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
      ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = vertex G j :=
      ⟨(vertexEquiv G).symm b, (vertexEquiv_symm_apply G b).symm⟩
    have hadj : G.Adj i j := (nonempty_hom_iff G).mp ⟨e⟩
    have heq : arrow G (⟨(i, j), hadj⟩ : G.Dart).adj = e := Subsingleton.elim _ _
    -- the spanning-family element is a beta-redex; reduce it to `zigzagMk k G (ofArrow e)`
    dsimp only
    exact Submodule.subset_span ⟨⟨(i, j), hadj⟩, by dsimp only; rw [heq]⟩
  · rw [Submodule.span_le]
    rintro e ⟨d, rfl⟩
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.ofArrow_mem_grade_one _)

/-- **Degree two is spanned by the volume classes**: every length-two path either does not return,
and dies, or returns to its source, and equals a backtrack there. -/
theorem zigzagGrade_two_eq_span_range_zigzagVolume :
    zigzagGrade k G 2 =
      Submodule.span k (Set.range fun i : V => zigzagVolume k G i) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine mem_span_of_mem_zigzagGrade k G
      (PathAlgebra.grade_eq_span_image_basis k (DoubledQuiver G) 2) ?_ hw
    rintro z ⟨t, ht, rfl⟩
    rw [← zigzagMk_apply k G]
    simp only [coe_pathAlgebraBasis]
    obtain ⟨a, b, p⟩ := t
    have ht' : p.length = 2 := ht
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
      ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
    rcases eq_or_ne b (vertex G i) with rfl | hne
    · obtain ⟨m, h, hp⟩ := exists_eq_backtrackPath G p ht'
      rw [hp, ← backtrackElem_eq_ofPath, zigzagMk_backtrackElem_eq_zigzagVolume]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [zigzagMk_ofPath_eq_zero_of_ne k G p ht' (Ne.symm hne)]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    -- membership in the spanned range only needs beta reduction here
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
  have hle : PathAlgebra.grade k (DoubledQuiver G) n ≤
      Submodule.restrictScalars k ((zigzagIdeal k G).asIdeal) := by
    rw [PathAlgebra.grade_eq_span_image_basis, Submodule.span_le]
    rintro z ⟨t, ht, rfl⟩
    have ht' : t.2.2.length = n := ht
    simp only [coe_pathAlgebraBasis]
    exact TwoSidedIdeal.mem_asIdeal.mpr
      (mem_zigzagIdeal_of_isZigzagRelator k G (IsZigzagRelator.long_path t (hn.trans ht'.symm.le)))
  refine TauCeti.GradedAlgebra.gradeQuot_eq_bot_of_le (grade k (DoubledQuiver G))
    (zigzagIdeal k G).asIdeal fun y hy => ?_
  exact hle hy

end TauCeti
