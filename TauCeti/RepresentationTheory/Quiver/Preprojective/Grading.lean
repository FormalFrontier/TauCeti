/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# The path-length grading of the preprojective algebra

Every preprojective relator of a quiver is homogeneous for the path-length grading of the path
algebra of the doubled quiver: the head backtrack and the tail backtrack of an arrow are the
basis elements of single length-two paths, so the local relator at a vertex and the global
relator are differences of sums of degree-two elements. Consequently the preprojective relation
ideal is homogeneous.

Because the relation ideal is homogeneous, the generic descent
`TauCeti.GradedAlgebra.gradeQuot` applies to it: the preprojective algebra `Pi_k(Q)` carries the
induced path-length grading `TauCeti.preprojectiveGrade`, in which the vertex idempotents have
degree `0`, the doubled arrows degree `1`, and the relator degree `2`. This file packages the
graded-algebra structure and computes the concrete pieces.

## Main definitions

* `TauCeti.preprojectiveGrade`: the induced degree-`n` piece on the preprojective algebra, the
  descent of `TauCeti.PathAlgebra.grade` along the quotient map `TauCeti.preprojectiveMk`.
* `TauCeti.preprojectiveGradedAlgebra`: **the preprojective algebra is a graded algebra** for the
  induced path-length grading.

## Main results

* `TauCeti.headBacktrackElem_mem_grade_two` and `TauCeti.tailBacktrackElem_mem_grade_two`: the
  two backtracks of an arrow have degree two.
* `TauCeti.localPreprojectiveRelator_mem_grade_two` and
  `TauCeti.preprojectiveRelator_mem_grade_two`: the local and global relators have degree two.
* `TauCeti.isHomogeneous_preprojectiveIdeal`: **the preprojective relation ideal is
  homogeneous.**
* `TauCeti.isInternal_preprojectiveGrade`: **the preprojective algebra is the internal direct
  sum of its graded pieces**, the comparison of the direct-sum graded algebra with the ungraded
  quotient rather than with a separate graded copy.
* `TauCeti.preprojectiveGrade_zero_eq_span_range_vertexIdempotent` and
  `TauCeti.preprojectiveGrade_one_eq_span_range_ofArrow`: degree `0` is spanned by the vertex
  idempotent classes and degree `1` by the doubled arrow classes.
* `TauCeti.preprojectiveGrade_eq_span_range_ofPath`: every piece is spanned by the classes of the
  paths of its degree.

## References

This is the grading clause of the first bullet of Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks for the additive preprojective
algebra to carry path length with every doubled arrow in degree `1`. The descent construction is
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient`, instantiated for the zigzag relation
quotient in `TauCeti.RepresentationTheory.Quiver.Zigzag.Grading`. See Crawley-Boevey, *Quiver
algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-! ### The generators of the doubled path algebra are homogeneous -/

section Generators

variable (k : Type w) {Q : Type u} [Semiring k] [Quiver.{v + 1} Q]

/-- **The head backtrack of an arrow has degree two**: it is the basis element of a single
length-two path of the doubled quiver. -/
theorem headBacktrackElem_mem_grade_two {i j : Q} (a : i ⟶ j) :
    headBacktrackElem k a ∈ grade k (Symmetrify Q) 2 := by
  rw [headBacktrackElem_def k a]
  refine ofPath_mem_grade_of_length ?_
  simp only [Path.length_comp, Quiver.Path.length_toPath]

/-- **The tail backtrack of an arrow has degree two**: it is the basis element of a single
length-two path of the doubled quiver. -/
theorem tailBacktrackElem_mem_grade_two {i j : Q} (a : i ⟶ j) :
    tailBacktrackElem k a ∈ grade k (Symmetrify Q) 2 := by
  rw [tailBacktrackElem_def k a]
  refine ofPath_mem_grade_of_length ?_
  simp only [Path.length_comp, Quiver.Path.length_toPath]

end Generators

/-! ### The relators have degree two -/

section Relators

variable (k : Type w) {Q : Type u} [Ring k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **The local preprojective relator has degree two**: it is a difference of sums of head and
tail backtracks, each of degree two. -/
theorem localPreprojectiveRelator_mem_grade_two (v : Q) :
    localPreprojectiveRelator k v ∈ grade k (Symmetrify Q) 2 := by
  rw [localPreprojectiveRelator_def k v]
  exact Submodule.sub_mem _
    (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun a _ =>
      headBacktrackElem_mem_grade_two k a)
    (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun a _ =>
      tailBacktrackElem_mem_grade_two k a)

variable (Q)

/-- **The global preprojective relator has degree two**. -/
theorem preprojectiveRelator_mem_grade_two :
    preprojectiveRelator k Q ∈ grade k (Symmetrify Q) 2 := by
  rw [preprojectiveRelator_def k Q]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.sum_mem _ fun a _ => Submodule.sub_mem _
      (headBacktrackElem_mem_grade_two k a) (tailBacktrackElem_mem_grade_two k a)

end Relators

/-! ### The relation ideal is homogeneous -/

section Ideal

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

variable (Q)

/-- **The preprojective relation ideal is homogeneous** for the path-length grading. This is the
condition needed to descend the grading to the preprojective algebra. -/
theorem isHomogeneous_preprojectiveIdeal :
    (preprojectiveIdeal k Q).asIdeal.IsHomogeneous (grade k (Symmetrify Q)) := by
  rw [preprojectiveIdeal_eq_span k Q]
  refine TwoSidedIdeal.homogeneous_span _ fun x hx => ?_
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨2, preprojectiveRelator_mem_grade_two k Q⟩

end Ideal

/-! ### The induced grading on the preprojective algebra -/

section Grade

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v + 1} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

variable (Q)

/-- **The induced path-length grading on the preprojective algebra**: the degree-`n` piece is the
image of the degree-`n` piece of the doubled path algebra under the quotient map. Multiplication
adds degrees for any relation ideal (`TauCeti.GradedAlgebra.mul_mem_gradeQuot`); because the
relation ideal is homogeneous (`TauCeti.isHomogeneous_preprojectiveIdeal`),
`TauCeti.isInternal_preprojectiveGrade` also holds, comparing the direct sum of the pieces with
the preprojective algebra itself rather than with a separate graded copy. -/
noncomputable def preprojectiveGrade (n : ℕ) : Submodule k (preprojectiveAlgebra k Q) :=
  TauCeti.GradedAlgebra.gradeQuot (grade k (Symmetrify Q)) (preprojectiveIdeal k Q).asIdeal n

/-- A homogeneous element lands in the piece its degree names. -/
theorem preprojectiveMk_mem_preprojectiveGrade {n : ℕ} {y : pathAlgebra k (Symmetrify Q)}
    (hy : y ∈ grade k (Symmetrify Q) n) :
    preprojectiveMk k Q y ∈ preprojectiveGrade k Q n := by
  rw [preprojectiveGrade, preprojectiveMk_apply k Q]
  exact TauCeti.GradedAlgebra.mk_mem_gradeQuot _ _ hy

/-- Membership in the induced degree-`n` piece is being the class of a degree-`n` element of the
doubled path algebra. -/
@[simp]
theorem mem_preprojectiveGrade_iff {n : ℕ} {x : preprojectiveAlgebra k Q} :
    x ∈ preprojectiveGrade k Q n ↔
      ∃ y ∈ grade k (Symmetrify Q) n, preprojectiveMk k Q y = x := by
  rw [preprojectiveGrade, TauCeti.GradedAlgebra.mem_gradeQuot_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, preprojectiveMk_apply k Q y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (preprojectiveMk_apply k Q y).symm⟩

/-- **The preprojective algebra is the internal direct sum of its graded pieces**: this is the
comparison of the direct-sum graded algebra with the ungraded quotient asked for by the roadmap,
in the internal sense in which the pieces are submodules of the algebra itself. -/
theorem isInternal_preprojectiveGrade :
    DirectSum.IsInternal (preprojectiveGrade k Q) :=
  TauCeti.GradedAlgebra.isInternal_gradeQuot (grade k (Symmetrify Q))
    (preprojectiveIdeal k Q).asIdeal (isHomogeneous_preprojectiveIdeal k Q)

/-- Multiplication adds degrees in the induced grading: the product of a degree-`m` class and a
degree-`n` class lies in degree `m + n`. -/
theorem mul_mem_preprojectiveGrade {m n : ℕ} {x y : preprojectiveAlgebra k Q}
    (hx : x ∈ preprojectiveGrade k Q m) (hy : y ∈ preprojectiveGrade k Q n) :
    x * y ∈ preprojectiveGrade k Q (m + n) :=
  TauCeti.GradedAlgebra.mul_mem_gradeQuot _ _ hx hy

/-- **The preprojective algebra is a graded algebra** for the induced path-length grading. This
is kept as a definition rather than an instance so that callers choose when to introduce it
locally; see `TauCeti.GradedAlgebra.gradedAlgebraGradeQuot`. -/
@[instance_reducible]
noncomputable def preprojectiveGradedAlgebra : GradedAlgebra (preprojectiveGrade k Q) :=
  TauCeti.GradedAlgebra.gradedAlgebraGradeQuot (grade k (Symmetrify Q))
    (preprojectiveIdeal k Q).asIdeal (isHomogeneous_preprojectiveIdeal k Q)

/-! ### The concrete pieces -/

/-- **Degree zero is spanned by the vertex idempotent classes**: the images under `preprojectiveMk`
of the vertex idempotents of the doubled quiver, that is, of the `TauCeti.doubledVertexIdempotent`s
at the vertices of `Q`. -/
theorem preprojectiveGrade_zero_eq_span_range_vertexIdempotent :
    preprojectiveGrade k Q 0 =
      Submodule.span k (Set.range fun v : Symmetrify Q =>
        preprojectiveMk k Q (vertexIdempotent k v)) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine TauCeti.GradedAlgebra.mem_span_of_mem_gradeQuot
      (grade k (Symmetrify Q)) (preprojectiveIdeal k Q).asIdeal (i := 0)
      (PathAlgebra.grade_zero_eq_span_range_vertexIdempotent k (Symmetrify Q)) ?_ hw
    rintro z ⟨v, rfl⟩
    rw [← preprojectiveMk_apply k Q]
    exact Submodule.subset_span ⟨v, rfl⟩
  · rw [Submodule.span_le]
    rintro z ⟨v, rfl⟩
    exact preprojectiveMk_mem_preprojectiveGrade k Q
      (PathAlgebra.vertexIdempotent_mem_grade_zero v)

/-- **Degree one is spanned by the doubled arrow classes**, one for each arrow of the doubled
quiver `Quiver.Symmetrify Q`. -/
theorem preprojectiveGrade_one_eq_span_range_ofArrow :
    preprojectiveGrade k Q 1 =
      Submodule.span k (Set.range fun e : Σ a b : Symmetrify Q, (a ⟶ b) =>
        preprojectiveMk k Q (PathAlgebra.ofArrow e.2.2)) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine TauCeti.GradedAlgebra.mem_span_of_mem_gradeQuot
      (grade k (Symmetrify Q)) (preprojectiveIdeal k Q).asIdeal (i := 1)
      PathAlgebra.grade_one_eq_span_range_ofArrow ?_ hw
    rintro z ⟨⟨a, b, e⟩, rfl⟩
    rw [← preprojectiveMk_apply k Q]
    exact Submodule.subset_span
      ⟨(⟨a, b, e⟩ : Σ a' b' : Symmetrify Q, (a' ⟶ b')), rfl⟩
  · rw [Submodule.span_le]
    rintro z ⟨e, rfl⟩
    exact preprojectiveMk_mem_preprojectiveGrade k Q (PathAlgebra.ofArrow_mem_grade_one e.2.2)

/-- **Every graded piece is spanned by the classes of the paths of that length**: the degree-`n`
piece of the preprojective algebra is the span of the images, under the quotient map, of the
length-`n` paths of the doubled quiver. -/
theorem preprojectiveGrade_eq_span_range_ofPath (n : ℕ) :
    preprojectiveGrade k Q n =
      Submodule.span k (Set.range fun x :
          {x : Quiver.TotalPath (Symmetrify Q) // x.2.2.length = n} =>
          preprojectiveMk k Q (PathAlgebra.ofPath x.1)) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine TauCeti.GradedAlgebra.mem_span_of_mem_gradeQuot
      (grade k (Symmetrify Q)) (preprojectiveIdeal k Q).asIdeal (i := n)
      (PathAlgebra.grade_eq_span_range k (Symmetrify Q) n) ?_ hw
    rintro z ⟨x, rfl⟩
    rw [← preprojectiveMk_apply k Q]
    exact Submodule.subset_span ⟨x, rfl⟩
  · rw [Submodule.span_le]
    rintro z ⟨x, rfl⟩
    exact preprojectiveMk_mem_preprojectiveGrade k Q
      (PathAlgebra.ofPath_mem_grade_of_length x.2)

end Grade

end TauCeti
