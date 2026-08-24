/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# The path-length grading on a quotient of a path algebra

A homogeneous two-sided relation ideal `I` in the path-length graded algebra `kQ` descends to a
grading of the quotient `kQ / I`: the degree-`n` piece of the quotient is the image of the
degree-`n` piece of `kQ` under the quotient map. This file carries out that descent once and for
all, in the internal sense used throughout Tau Ceti: the graded pieces are submodules of the
quotient itself, and the direct sum of the pieces is compared with the quotient itself, not with a
separate graded copy.

The input is `TauCeti.PathAlgebra.gradeQuot k I n`, the image of `TauCeti.PathAlgebra.grade k Q n`
under `Ideal.Quotient.mk I.asIdeal`. Because the relation ideal is homogeneous, distinct degrees
cannot cancel against each other modulo `I`: a finite sum of homogeneous elements of pairwise
different degrees dies in the quotient only componentwise, since projecting onto any one degree
reads off that summand. That observation proves independence of the pieces, and together with the
surjectivity of the quotient map it proves that the pieces form an internal decomposition.

## Main definitions

* `TauCeti.PathAlgebra.gradeQuot`: the degree-`n` piece of the quotient, the image of the
  degree-`n` piece of `kQ`.
* `TauCeti.PathAlgebra.gradedMonoidGradeQuot`: the multiplicative structure of the pieces,
  supplied as the `SetLike.GradedMonoid` instance data.
* `TauCeti.PathAlgebra.gradedAlgebraGradeQuot`: the resulting `GradedAlgebra` structure.

## Main results

* `TauCeti.PathAlgebra.mul_mem_gradeQuot` and `TauCeti.PathAlgebra.gradeQuot_mul_gradeQuot_le`:
  multiplication adds degrees.
* `TauCeti.PathAlgebra.iSupIndep_gradeQuot`, `TauCeti.PathAlgebra.iSup_gradeQuot_eq_top`, and
  `TauCeti.PathAlgebra.isInternal_gradeQuot`: **the quotient is the internal direct sum of its
  graded pieces.**
* `TauCeti.PathAlgebra.gradedAlgebraGradeQuot`: the induced `GradedAlgebra` structure.

## Implementation notes

The `GradedAlgebra` structure is a definition rather than an instance: it depends on the relation
ideal `I` through its homogeneity proof, and registering it globally would attach a competing
grading to every quotient of every path algebra at once. Callers introduce it locally with
`letI` where an instance is needed.

Mathlib's graded structure on a quotient by a homogeneous ideal is the open PR
[#36501](https://github.com/leanprover-community/mathlib4/pull/36501) and is not pinned here;
when it lands this construction should be replaced by it.

## References

This is the descent clause of the grading bullet of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, phrased for an arbitrary finite quiver because the
preprojective constructions of Layer 4 descend along the same map. See
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Ch. II.
-/

public section

namespace TauCeti

namespace PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Finite Q]

/-- The degree-`n` piece of the quotient of `kQ` by a two-sided relation ideal `I`: the image of
the degree-`n` piece of the path-length grading of `kQ` under the quotient map. Homogeneity of
`I`, which is what makes this family a grading, is needed only for the results below, not for the
definition. It is exposed so that instantiations of this construction may unfold it. -/
@[expose]
noncomputable def gradeQuot (I : TwoSidedIdeal (pathAlgebra k Q)) (n : ℕ) :
    Submodule k (pathAlgebra k Q ⧸ I.asIdeal) :=
  (grade k Q n).map (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap

/-- Membership in the descended degree-`n` piece is being the class of a homogeneous element. -/
theorem mem_gradeQuot_iff {I : TwoSidedIdeal (pathAlgebra k Q)} {n : ℕ}
    {x : pathAlgebra k Q ⧸ I.asIdeal} :
    x ∈ gradeQuot k I n ↔ ∃ y ∈ grade k Q n, Ideal.Quotient.mk I.asIdeal y = x :=
  Submodule.mem_map

/-- A homogeneous element lands in the degree-`n` piece of the quotient. -/
@[simp]
theorem mk_mem_gradeQuot {I : TwoSidedIdeal (pathAlgebra k Q)} {n : ℕ} {y : pathAlgebra k Q}
    (hy : y ∈ grade k Q n) : Ideal.Quotient.mk I.asIdeal y ∈ gradeQuot k I n :=
  Submodule.mem_map.2 ⟨y, hy, rfl⟩

/-- **Multiplication adds degrees** in the quotient: the product of a degree-`m` class and a
degree-`n` class lies in degree `m + n`. -/
theorem mul_mem_gradeQuot {I : TwoSidedIdeal (pathAlgebra k Q)} {m n : ℕ}
    {x y : pathAlgebra k Q ⧸ I.asIdeal} (hx : x ∈ gradeQuot k I m)
    (hy : y ∈ gradeQuot k I n) : x * y ∈ gradeQuot k I (m + n) := by
  obtain ⟨a, ha, rfl⟩ := (mem_gradeQuot_iff k).mp hx
  obtain ⟨b, hb, rfl⟩ := (mem_gradeQuot_iff k).mp hy
  rw [← map_mul]
  refine mk_mem_gradeQuot k ?_
  exact grade_mul_grade_le m n (Submodule.mul_mem_mul ha hb)

/-- Multiplication adds degrees, as an inclusion of products of pieces. -/
theorem gradeQuot_mul_gradeQuot_le (I : TwoSidedIdeal (pathAlgebra k Q)) (m n : ℕ) :
    gradeQuot k I m * gradeQuot k I n ≤ gradeQuot k I (m + n) :=
  Submodule.mul_le.2 fun _ hx _ hy => mul_mem_gradeQuot k hx hy

section Internal

variable (I : TwoSidedIdeal (pathAlgebra k Q))

/-- Projecting a homogeneous element onto any degree picks out the element itself in its own
degree and zero elsewhere. Private: it packages three standard rewriting steps. -/
private theorem proj_of_mem_grade (j n : ℕ) {x : pathAlgebra k Q} (hx : x ∈ grade k Q n) :
    GradedRing.proj (grade k Q) j x = if j = n then x else 0 := by
  by_cases h : j = n
  · subst h
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem _ hx]
    simp
  · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem _ hx, DirectSum.of_apply,
      dite_eq_right (Ne.symm h), ite_eq_right h]
    rfl

/-- A finite sum whose `i`-th summand lies in the `i`-th piece lies in the supremum of the
pieces. Private: the usual induction over the index finset. -/
private theorem sum_mem_iSup_gradeQuot (s : Finset ℕ)
    (g : ℕ → pathAlgebra k Q ⧸ I.asIdeal) (hg : ∀ i ∈ s, g i ∈ gradeQuot k I i) :
    ∑ i ∈ s, g i ∈ ⨆ i, gradeQuot k I i := by
  classical
  have key : ∀ t : Finset ℕ, ∀ g : ℕ → pathAlgebra k Q ⧸ I.asIdeal,
      (∀ i ∈ t, g i ∈ gradeQuot k I i) → ∑ i ∈ t, g i ∈ ⨆ i, gradeQuot k I i := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro g _; simp
    | insert a t ha ih =>
      intro g hg
      obtain ⟨hga, hgt⟩ := (Finset.forall_mem_insert a t _).mp hg
      rw [Finset.sum_insert ha]
      exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem a hga) (ih g hgt)
  exact key s g hg

/-- **Independence of the descended pieces**: a finite sum of classes which vanishes in the
quotient vanishes termwise. Homogeneity of `I` is what licenses reading off each summand by
projecting the lifted relation onto its degree; without it, degrees could cancel modulo `I`. -/
theorem iSupIndep_gradeQuot (hI : I.asIdeal.IsHomogeneous (grade k Q)) :
    iSupIndep (gradeQuot k I) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  classical
  intro s v hv hv0 j hj
  have hall : ∀ i : ℕ, ∃ y, y ∈ grade k Q i ∧
      (i ∈ s → Ideal.Quotient.mk I.asIdeal y = v i) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨y, hy, hq⟩ := (mem_gradeQuot_iff k).mp (hv i hi)
      exact ⟨y, hy, fun _ => hq⟩
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd h hi⟩
  choose a hav ha using hall
  have hzero : Ideal.Quotient.mk I.asIdeal (∑ i ∈ s, a i) = 0 := by
    rw [map_sum]
    exact (Finset.sum_congr rfl fun i hi => ha i hi).trans hv0
  have hmember : ∑ i ∈ s, a i ∈ I.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hzero
  have hjmem : a j ∈ I.asIdeal := by
    have hproj := hI.mem_iff.mp hmember j
    have hsing : GradedRing.proj (grade k Q) j (∑ l ∈ s, a l) = a j := by
      have key := Finset.sum_eq_single_of_mem j hj
        (f := fun l => GradedRing.proj (grade k Q) j (a l))
        (fun i _ hne => by rw [proj_of_mem_grade k j i (hav i), ite_eq_right (Ne.symm hne)])
      rw [map_sum, key, proj_of_mem_grade k j j (hav j), ite_eq_left rfl]
    rw [← hsing]
    exact hproj
  rw [← ha j hj, Ideal.Quotient.eq_zero_iff_mem]
  exact hjmem

/-- The descended pieces span the whole quotient, because the quotient map does. -/
theorem iSup_gradeQuot_eq_top : ⨆ n, gradeQuot k I n = ⊤ := by
  classical
  refine eq_top_iff.2 ?_
  intro x _
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hsplit : Ideal.Quotient.mk I.asIdeal (∑ i ∈ (DirectSum.decompose (grade k Q) f).support,
      ((DirectSum.decompose (grade k Q) f i : pathAlgebra k Q)))
      = ∑ i ∈ (DirectSum.decompose (grade k Q) f).support,
        Ideal.Quotient.mk I.asIdeal ((DirectSum.decompose (grade k Q) f i : pathAlgebra k Q)) :=
    map_sum _ _ _
  rw [← DirectSum.sum_support_decompose (grade k Q) f, hsplit]
  refine sum_mem_iSup_gradeQuot k I (DirectSum.decompose (grade k Q) f).support
    (fun i => Ideal.Quotient.mk I.asIdeal
      ((DirectSum.decompose (grade k Q) f i : pathAlgebra k Q))) ?_
  intro i _
  exact mk_mem_gradeQuot k (DirectSum.decompose (grade k Q) f i).2

/-- **The quotient is the internal direct sum of its descended pieces**: this is the comparison of
the direct-sum graded algebra with the ungraded quotient asked for by the roadmap, in the internal
sense in which the pieces live inside the quotient itself. -/
theorem isInternal_gradeQuot (hI : I.asIdeal.IsHomogeneous (grade k Q)) :
    DirectSum.IsInternal (gradeQuot k I) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_gradeQuot k I hI)
    (iSup_gradeQuot_eq_top k I)

/-- The multiplicative structure of the descended pieces: the unit lies in degree `0`, being the
class of the sum of the vertex idempotents, and multiplication adds degrees. This supplies the
instance data for downstream `GradedAlgebra` constructions. -/
theorem gradedMonoidGradeQuot : SetLike.GradedMonoid (gradeQuot k I) where
  one_mem := by
    let _ := Fintype.ofFinite Q
    have h1 : (1 : pathAlgebra k Q ⧸ I.asIdeal) = Ideal.Quotient.mk I.asIdeal 1 := rfl
    rw [h1]
    refine mk_mem_gradeQuot k ?_
    rw [one_def]
    exact Submodule.sum_mem _ fun v _ => vertexIdempotent_mem_grade_zero v
  mul_mem _ _ _ _ hx hy := mul_mem_gradeQuot k hx hy

/-- **The induced grading on the quotient**: the descended pieces form a graded algebra. This is
kept as a definition rather than an instance because it depends on the relation ideal `I`; see
the implementation notes. -/
@[instance_reducible]
noncomputable def gradedAlgebraGradeQuot (hI : I.asIdeal.IsHomogeneous (grade k Q)) :
    GradedAlgebra (gradeQuot k I) :=
  letI := gradedMonoidGradeQuot k I
  DirectSum.IsInternal.gradedAlgebra (isInternal_gradeQuot k I hI)

end Internal

end PathAlgebra

end TauCeti
