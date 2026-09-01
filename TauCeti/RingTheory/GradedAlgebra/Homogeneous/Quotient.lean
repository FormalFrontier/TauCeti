/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The grading induced on a quotient by a homogeneous ideal

A homogeneous two-sided ideal `I` in an `R`-algebra `A` graded by `𝒜` descends that grading to
the quotient `A ⧸ I`: the degree-`i` piece of the quotient is the image of the degree-`i` piece of
`A` under the quotient map. This file carries out the descent once and for all, in the internal
sense used throughout Tau Ceti: the graded pieces are submodules of the quotient itself, and the
direct sum of the pieces is compared with the quotient itself, not with a separate graded copy.

The input is `TauCeti.GradedAlgebra.gradeQuot 𝒜 I i`, the image of `𝒜 i` under
`Ideal.Quotient.mkₐ R I`. Because the ideal is homogeneous, distinct degrees cannot cancel against
each other modulo `I`: a finite sum of homogeneous elements of pairwise different degrees dies in
the quotient only componentwise, since projecting onto any one degree reads off that summand. That
observation proves independence of the pieces, and together with the surjectivity of the quotient
map it proves that the pieces form an internal decomposition.

## Main definitions

* `TauCeti.GradedAlgebra.gradeQuot`: the degree-`i` piece of the quotient, the image of the
  degree-`i` piece of `A`.
* `TauCeti.GradedAlgebra.gradedAlgebraGradeQuot`: the resulting `GradedAlgebra` structure.

## Main results

* `TauCeti.GradedAlgebra.mul_mem_gradeQuot` and
  `TauCeti.GradedAlgebra.gradeQuot_mul_gradeQuot_le`: multiplication adds degrees.
* `TauCeti.GradedAlgebra.gradeQuot_eq_span_image`: the descended piece is the span of the images
  of any spanning family of the original piece.
* `TauCeti.GradedAlgebra.mem_span_of_mem_gradeQuot`: a spanning result for the original piece
  descends to the quotient.
* `TauCeti.GradedAlgebra.gradeQuot_eq_bot_of_le`: a piece whose original grading lies in `I`
  vanishes.
* `TauCeti.GradedAlgebra.iSupIndep_gradeQuot`, `TauCeti.GradedAlgebra.iSup_gradeQuot_eq_top`, and
  `TauCeti.GradedAlgebra.isInternal_gradeQuot`: **the quotient is the internal direct sum of its
  graded pieces.**

## Implementation notes

The multiplicative structure of the descended pieces is registered as a global
`SetLike.GradedMonoid` instance; that class is `Prop`-valued, so attaching it to every descended
grading at once is harmless. The `GradedAlgebra` structure itself is a definition rather than an
instance: it depends on the homogeneity of `I`, and registering it globally would attach a
competing grading to every quotient of every graded algebra at once. Callers introduce it locally
with `letI` where an instance is needed.

Mathlib's graded structure on a quotient by a homogeneous ideal is the open PR
[#36501](https://github.com/leanprover-community/mathlib4/pull/36501) by Antoine Chambert-Loir,
and the shape of this construction follows it: the degree-`i` piece as the image of `𝒜 i` under
the quotient map, independence of the pieces via `GradedRing.proj`, and the induced
`GradedAlgebra` assembled from `DirectSum.IsInternal`. That PR is not pinned here; when it lands
this construction should be replaced by it.

## References

This construction states for an arbitrary graded algebra the descent clause of the grading bullet
of Layer 0 of `TauCetiRoadmap/ZigzagPreprojective/README.md`; see Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

namespace GradedAlgebra

universe u v w

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (I : Ideal A) [I.IsTwoSided]

/-- The degree-`i` piece of the quotient of `A` by a two-sided ideal `I`: the image of the
degree-`i` piece `𝒜 i` under the quotient map. Homogeneity of `I`, which is what makes this family
a grading, is needed only for the results below, not for the definition. -/
noncomputable def gradeQuot (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R I).toLinearMap

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- Membership in the descended degree-`i` piece is being the class of a homogeneous element. -/
theorem mem_gradeQuot_iff {i : ι} {x : A ⧸ I} :
    x ∈ gradeQuot 𝒜 I i ↔ ∃ y ∈ 𝒜 i, Ideal.Quotient.mk I y = x :=
  Submodule.mem_map

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- A homogeneous element lands in the degree-`i` piece of the quotient. -/
@[simp]
theorem mk_mem_gradeQuot {i : ι} {y : A} (hy : y ∈ 𝒜 i) :
    Ideal.Quotient.mk I y ∈ gradeQuot 𝒜 I i :=
  Submodule.mem_map.2 ⟨y, hy, rfl⟩

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- The descended degree-`i` piece is the span of the images of any spanning family of the
original piece: descending commutes with spanning. -/
theorem gradeQuot_eq_span_image {i : ι} {s : Set A} (hs : 𝒜 i = Submodule.span R s) :
    gradeQuot 𝒜 I i = Submodule.span R ((Ideal.Quotient.mk I) '' s) := by
  rw [gradeQuot, hs, Submodule.map_span]
  rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- A member of a descended piece lies in the span of `t` if the images of a spanning family of
the original piece lie in that span. -/
theorem mem_span_of_mem_gradeQuot {i : ι} {s : Set A} (hs : 𝒜 i = Submodule.span R s)
    {t : Set (A ⧸ I)}
    (hmem : ∀ z ∈ s, Ideal.Quotient.mk I z ∈ Submodule.span R t)
    {w : A ⧸ I} (hw : w ∈ gradeQuot 𝒜 I i) :
    w ∈ Submodule.span R t := by
  have heq := gradeQuot_eq_span_image 𝒜 I (i := i) hs
  rw [heq] at hw
  refine (Submodule.span_le.2 ?_) hw
  rintro u ⟨z, hz, rfl⟩
  exact hmem z hz

omit [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] in
/-- A piece whose original grading lies in `I` vanishes in the quotient. -/
theorem gradeQuot_eq_bot_of_le {i : ι} (hle : ∀ y ∈ 𝒜 i, y ∈ I) : gradeQuot 𝒜 I i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hle y hy)

/-- Multiplication adds degrees, as an inclusion of products of pieces. -/
theorem gradeQuot_mul_gradeQuot_le (m n : ι) :
    gradeQuot 𝒜 I m * gradeQuot 𝒜 I n ≤ gradeQuot 𝒜 I (m + n) := by
  simp only [gradeQuot, ← Submodule.map_mul (𝒜 m) (𝒜 n) (Ideal.Quotient.mkₐ R I)]
  exact Submodule.map_mono (Submodule.mul_le.2 fun _ hx _ hy => SetLike.mul_mem_graded hx hy)

/-- **Multiplication adds degrees** in the quotient: the product of a degree-`m` class and a
degree-`n` class lies in degree `m + n`. -/
theorem mul_mem_gradeQuot {m n : ι} {x y : A ⧸ I}
    (hx : x ∈ gradeQuot 𝒜 I m) (hy : y ∈ gradeQuot 𝒜 I n) : x * y ∈ gradeQuot 𝒜 I (m + n) :=
  gradeQuot_mul_gradeQuot_le 𝒜 I m n (Submodule.mul_mem_mul hx hy)

section Internal

/-- Projecting a homogeneous element onto any degree picks out the element itself in its own
degree and zero elsewhere. Private: it packages two standard rewriting steps. -/
private theorem proj_of_mem_grade (j n : ι) {x : A} (hx : x ∈ 𝒜 n) :
    GradedRing.proj 𝒜 j x = if j = n then x else 0 := by
  by_cases h : j = n
  · subst h
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]
    simp
  · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hx (Ne.symm h),
      ite_eq_right h]

/-- **Independence of the descended pieces**: a finite sum of classes which vanishes in the
quotient vanishes termwise. Homogeneity of `I` is what licenses reading off each summand by
projecting the lifted relation onto its degree; without it, degrees could cancel modulo `I`. -/
theorem iSupIndep_gradeQuot (hI : I.IsHomogeneous 𝒜) : iSupIndep (gradeQuot 𝒜 I) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  classical
  intro s v hv hv0 j hj
  have hall : ∀ i : ι, ∃ y, y ∈ 𝒜 i ∧ (i ∈ s → Ideal.Quotient.mk I y = v i) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨y, hy, hq⟩ := (mem_gradeQuot_iff 𝒜 I).mp (hv i hi)
      exact ⟨y, hy, fun _ => hq⟩
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd h hi⟩
  choose a hav ha using hall
  have hzero : Ideal.Quotient.mk I (∑ i ∈ s, a i) = 0 := by
    rw [map_sum]
    exact (Finset.sum_congr rfl fun i hi => ha i hi).trans hv0
  have hmember : ∑ i ∈ s, a i ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hzero
  have hjmem : a j ∈ I := by
    have hproj := hI.mem_iff.mp hmember j
    have hsing : GradedRing.proj 𝒜 j (∑ l ∈ s, a l) = a j := by
      have key := Finset.sum_eq_single_of_mem j hj
        (f := fun l => GradedRing.proj 𝒜 j (a l))
        (fun i _ hne => by rw [proj_of_mem_grade 𝒜 j i (hav i), ite_eq_right (Ne.symm hne)])
      rw [map_sum, key, proj_of_mem_grade 𝒜 j j (hav j), ite_eq_left rfl]
    rw [← hsing]
    exact hproj
  rw [← ha j hj, Ideal.Quotient.eq_zero_iff_mem]
  exact hjmem

/-- The descended pieces span the whole quotient, because the quotient map does. -/
theorem iSup_gradeQuot_eq_top : ⨆ i, gradeQuot 𝒜 I i = ⊤ := by
  simp only [gradeQuot]
  rw [← Submodule.map_iSup (Ideal.Quotient.mkₐ R I).toLinearMap,
    DirectSum.IsInternal.submodule_iSup_eq_top (DirectSum.Decomposition.isInternal 𝒜)]
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I x
  exact ⟨a, trivial, rfl⟩

/-- **The quotient is the internal direct sum of its descended pieces**: this is the comparison of
the direct-sum graded algebra with the ungraded quotient asked for by the roadmap, in the internal
sense in which the pieces live inside the quotient itself. -/
theorem isInternal_gradeQuot (hI : I.IsHomogeneous 𝒜) :
    DirectSum.IsInternal (gradeQuot 𝒜 I) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_gradeQuot 𝒜 I hI)
    (iSup_gradeQuot_eq_top 𝒜 I)

/-- The multiplicative structure of the descended pieces: the unit lies in degree `0` and
multiplication adds degrees. This supplies the instance data for downstream `GradedAlgebra`
constructions. Since `SetLike.GradedMonoid` is a `Prop`-valued class, this can be registered
globally without attaching data to unrelated quotients. -/
instance : SetLike.GradedMonoid (gradeQuot 𝒜 I) where
  one_mem := mk_mem_gradeQuot 𝒜 I SetLike.GradedOne.one_mem
  mul_mem _ _ _ _ hx hy := mul_mem_gradeQuot 𝒜 I hx hy

/-- **The induced grading on the quotient**: the descended pieces form a graded algebra. This is
kept as a definition rather than an instance because it depends on the homogeneity of `I`; see
the implementation notes. -/
@[instance_reducible]
noncomputable def gradedAlgebraGradeQuot (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (gradeQuot 𝒜 I) :=
  DirectSum.IsInternal.gradedAlgebra (isInternal_gradeQuot 𝒜 I hI)

end Internal

end GradedAlgebra

end TauCeti
