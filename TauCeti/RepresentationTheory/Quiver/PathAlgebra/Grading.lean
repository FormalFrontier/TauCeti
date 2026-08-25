/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.RepresentationTheory.Quiver.Radical

/-!
# The path-length grading of a path algebra

The path algebra `kQ` is free on the paths of `Q`, and concatenating paths adds their lengths, so
the span `TauCeti.PathAlgebra.grade k Q n` of the paths of length `n` makes `kQ` an `ℕ`-graded
`k`-algebra. This file constructs that grading in the internal sense: the graded pieces are
submodules of `kQ` itself and the decomposition compares them with `kQ`, rather than with a
separate graded copy of it.

Degree `0` is the span of the vertex idempotents and degree `1` is the span of the arrows. Each
piece is free on the paths of that length, and each sits inside the corresponding step
`TauCeti.pathSpan k Q n` of the length filtration of
`TauCeti.RepresentationTheory.Quiver.Radical`, which spans the paths of length *at least* `n`.

## Main definitions

* `TauCeti.PathAlgebra.grade`: the degree-`n` piece, the span of the paths of length `n`.
* `TauCeti.PathAlgebra.gradeBasis`: the paths of length `n` as a `k`-basis of that piece.
* `TauCeti.PathAlgebra.decomposeAlgHom`: the algebra homomorphism to the direct sum decomposing
  elements by path length, which is `DirectSum.decompose` for the grading below.

## Main results

* `TauCeti.PathAlgebra.gradedAlgebra`: **the path-length grading**, the `GradedAlgebra` instance
  on `TauCeti.PathAlgebra.grade`. Its multiplicative half,
  `TauCeti.PathAlgebra.grade_mul_grade_le`, is the statement that multiplication adds degrees, and
  `TauCeti.PathAlgebra.isInternal_grade` is the comparison of the direct sum of the pieces with
  `kQ` itself.
* `TauCeti.PathAlgebra.mem_grade_iff`: an element is homogeneous of degree `n` exactly when its
  path coordinates are supported on the paths of length `n`.
* `TauCeti.PathAlgebra.grade_zero_eq_span_range_vertexIdempotent` and
  `TauCeti.PathAlgebra.grade_one_eq_span_range_ofArrow`: the vertex idempotents span degree `0`
  and the arrows span degree `1`.
* `TauCeti.PathAlgebra.grade_le_pathSpan`: the degree-`n` piece lies in the `n`-th step of the
  length filtration.
* `TauCeti.PathAlgebra.decompose_ofPath`: `DirectSum.decompose` sends a basis path to the summand
  indexed by its length.

## Implementation notes

The grading is constructed from `TauCeti.PathAlgebra.decomposeAlgHom`, built from the universal
property `TauCeti.PathAlgebra.liftAlgHom` in the same way as
`AddMonoidAlgebra.gradeBy.gradedAlgebra` is built from the universal property of an additive monoid
algebra: an assignment of a homogeneous summand to each basis path is an algebra map to the direct
sum as soon as it respects the three defining products of `kQ`. It is what
`GradedAlgebra.ofAlgHom` installs as `DirectSum.decompose`; the two maps are definitionally equal.

The unit of `kQ` is the sum of the vertex idempotents, which exists only for a finite vertex type,
so the graded *pieces* are defined for every quiver while the grading itself asks for `[Finite Q]`.

## References

This is the grading clause of Layer 0 of `TauCetiRoadmap/ZigzagPreprojective/README.md`:
"Construct the induced nonnegative grading. Prove that the relation ideal is homogeneous and that
multiplication adds degrees. Compare the direct-sum graded algebra with the ungraded quotient
rather than postulating an unrelated graded copy." This file discharges the nonnegative grading and
"multiplication adds degrees" for `kQ`, and makes the comparison internal to `kQ` rather than to a
separate graded copy: the pieces are submodules of `kQ` and `TauCeti.PathAlgebra.isInternal_grade`
exhibits `kQ` as their direct sum. Homogeneity of the zigzag relation ideals is
`TauCeti.RepresentationTheory.Quiver.Zigzag.Grading`; the descent of the grading along the quotient
map — the comparison with the ungraded *quotient* — is not proved here. See
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Ch. II.
-/

public section

namespace TauCeti

open DirectSum

universe u v w

namespace PathAlgebra

section Grade

variable (k : Type w) (Q : Type u) [Semiring k] [Quiver.{v} Q]

/-- The degree-`n` piece of the path-length grading of the path algebra: the `k`-span of the paths
of length `n`. -/
noncomputable def grade (n : ℕ) : Submodule k (pathAlgebra k Q) :=
  Submodule.span k
    ((fun x : Quiver.TotalPath Q => (ofPath x : pathAlgebra k Q)) ''
      {x : Quiver.TotalPath Q | x.2.2.length = n})

/-- The degree-`n` piece is the span of the image of the length-`n` paths under the path basis.
This is the form the `Module.Basis` API reads. -/
theorem grade_eq_span_image_basis (n : ℕ) :
    grade k Q n = Submodule.span k
      (⇑(pathAlgebraBasis k Q) '' {x : Quiver.TotalPath Q | x.2.2.length = n}) := by
  simp only [grade, coe_pathAlgebraBasis]

/-- The degree-`n` piece is the span of the length-`n` paths, indexed by the subtype they form. -/
theorem grade_eq_span_range (n : ℕ) :
    grade k Q n = Submodule.span k
      (Set.range fun x : {x : Quiver.TotalPath Q // x.2.2.length = n} =>
        (ofPath x.1 : pathAlgebra k Q)) := by
  simp only [grade, Set.image_eq_range]
  -- `↥{x | x.2.2.length = n}` and `{x // x.2.2.length = n}` are the same type by definition.
  rfl

variable {k Q}

/-- **Homogeneity is a condition on path coordinates**: an element has degree `n` exactly when
every path carrying a nonzero coordinate has length `n`. -/
theorem mem_grade_iff {n : ℕ} {f : pathAlgebra k Q} :
    f ∈ grade k Q n ↔ ∀ x ∈ ((pathAlgebraBasis k Q).repr f).support, x.2.2.length = n := by
  rw [grade_eq_span_image_basis, Module.Basis.mem_span_image]
  exact ⟨fun h _ hx => h hx, fun h _ hx => h _ hx⟩

/-- A basis path is homogeneous of its own length. -/
theorem ofPath_mem_grade (x : Quiver.TotalPath Q) :
    (ofPath x : pathAlgebra k Q) ∈ grade k Q x.2.2.length :=
  Submodule.subset_span ⟨x, rfl, rfl⟩

/-- A path of length `n` is homogeneous of degree `n`. -/
theorem ofPath_mem_grade_of_length {n : ℕ} {x : Quiver.TotalPath Q} (hx : x.2.2.length = n) :
    (ofPath x : pathAlgebra k Q) ∈ grade k Q n :=
  hx ▸ ofPath_mem_grade x

/-- **A basis path has degree `n` exactly when its length is `n`.** -/
@[simp]
theorem ofPath_mem_grade_iff [Nontrivial k] {n : ℕ} {x : Quiver.TotalPath Q} :
    (ofPath x : pathAlgebra k Q) ∈ grade k Q n ↔ x.2.2.length = n := by
  refine ⟨fun hx => mem_grade_iff.1 hx x ?_, ofPath_mem_grade_of_length⟩
  rw [ofPath_eq_single, pathAlgebraBasis_repr_single, Finsupp.mem_support_iff,
    Finsupp.single_eq_same]
  exact one_ne_zero

/-- A scaled basis path is homogeneous of the length of that path. -/
theorem single_mem_grade_of_length {n : ℕ} {x : Quiver.TotalPath Q} (hx : x.2.2.length = n)
    (c : k) : (single x c : pathAlgebra k Q) ∈ grade k Q n := by
  rw [single_eq_smul_ofPath]
  exact Submodule.smul_mem _ c (ofPath_mem_grade_of_length hx)

/-- A vertex idempotent is homogeneous of degree `0`. -/
theorem vertexIdempotent_mem_grade_zero (v : Q) :
    (vertexIdempotent k v : pathAlgebra k Q) ∈ grade k Q 0 := by
  rw [vertexIdempotent_eq_ofPath]
  exact ofPath_mem_grade_of_length rfl

/-- **Two paths multiply in the sum of their degrees**, whether or not they are composable. -/
theorem ofPath_mul_ofPath_mem_grade (x y : Quiver.TotalPath Q) :
    (ofPath x * ofPath y : pathAlgebra k Q) ∈ grade k Q (x.2.2.length + y.2.2.length) := by
  rw [ofPath_mul_ofPath]
  cases hxy : x.mul? y with
  | none => exact Submodule.zero_mem _
  | some z =>
    exact ofPath_mem_grade_of_length
      (Quiver.TotalPath.length_eq_add_of_mul?_eq_some (Q := Q) hxy)

variable (k Q)

/-- The paths of length `n` are a `k`-basis of the degree-`n` piece: every graded piece is free. -/
noncomputable def gradeBasis (n : ℕ) :
    Module.Basis {x : Quiver.TotalPath Q // x.2.2.length = n} k (grade k Q n) :=
  (Module.Basis.span
      (linearIndependent_ofPath k Q fun x : Quiver.TotalPath Q => x.2.2.length = n)).map
    (LinearEquiv.ofEq _ _ (grade_eq_span_range k Q n).symm)

variable {k Q}

/-- The basis of the degree-`n` piece consists of the paths of length `n`. -/
@[simp]
theorem coe_gradeBasis_apply {n : ℕ} (x : {x : Quiver.TotalPath Q // x.2.2.length = n}) :
    (gradeBasis k Q n x : pathAlgebra k Q) = ofPath x.1 := by
  rw [gradeBasis, Module.Basis.map_apply, Module.Basis.span_apply, LinearEquiv.coe_ofEq_apply]

variable (k Q)

/-- **Degree `0` is the span of the vertex idempotents**: the trivial paths are exactly the paths
of length zero. -/
theorem grade_zero_eq_span_range_vertexIdempotent : grade k Q 0
    = Submodule.span k (Set.range (vertexIdempotent k)) := by
  rw [grade]
  refine congrArg (Submodule.span k) (Set.ext fun f => ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b, p⟩, hp, rfl⟩
    replace hp : p.length = 0 := hp
    obtain rfl := p.eq_of_length_zero hp
    obtain rfl := p.eq_nil_of_length_zero hp
    exact ⟨a, vertexIdempotent_eq_ofPath k a⟩
  · rintro ⟨v, rfl⟩
    exact ⟨⟨v, v, _root_.Quiver.Path.nil⟩, rfl, (vertexIdempotent_eq_ofPath k v).symm⟩

/-- **The degree-`n` piece lies in the `n`-th step of the length filtration**: a path of length
exactly `n` is in particular a path of length at least `n`. -/
theorem grade_le_pathSpan (n : ℕ) : grade k Q n ≤ pathSpan k Q n := by
  rw [grade]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ofPath_mem_pathSpan hx.ge

variable {k Q}

/-- An arrow is homogeneous of degree `1`. -/
theorem ofArrow_mem_grade_one {a b : Q} (e : a ⟶ b) :
    (ofArrow e : pathAlgebra k Q) ∈ grade k Q 1 := by
  rw [ofArrow_eq_ofPath]
  exact ofPath_mem_grade_of_length rfl

/-- **Degree `1` is the span of the arrows**: the length-one paths are exactly the arrows. -/
theorem grade_one_eq_span_range_ofArrow : grade k Q 1 = Submodule.span k
    (Set.range fun e : Σ a b : Q, a ⟶ b => (ofArrow e.2.2 : pathAlgebra k Q)) := by
  rw [grade]
  refine congrArg (Submodule.span k) (Set.ext fun f => ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b, p⟩, hp, rfl⟩
    obtain ⟨c, e, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ (n := 0) (by simpa using hp)
    obtain rfl := q.eq_of_length_zero hq
    obtain rfl := q.eq_nil_of_length_zero hq
    exact ⟨⟨a, c, e⟩, ofArrow_eq_ofPath e⟩
  · rintro ⟨⟨a, b, e⟩, rfl⟩
    exact ⟨⟨a, b, e.toPath⟩, rfl, (ofArrow_eq_ofPath e).symm⟩

end Grade

section GradeComm

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q]

/-- **Multiplication adds degrees.** -/
theorem grade_mul_grade_le [Finite Q] (i j : ℕ) :
    grade k Q i * grade k Q j ≤ grade k Q (i + j) := by
  simp only [grade, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  replace hx : x.2.2.length = i := hx
  replace hy : y.2.2.length = j := hy
  subst hx
  subst hy
  exact SetLike.mem_coe.2 (ofPath_mul_ofPath_mem_grade x y)

end GradeComm

/-! ### The graded algebra structure -/

section GradedAlgebra

variable (k : Type w) (Q : Type u) [CommSemiring k] [Quiver.{v} Q] [Finite Q]

/-- The graded pieces form a graded monoid: the unit is the degree-zero sum of the vertex
idempotents, and multiplication adds degrees. -/
noncomputable instance gradedMonoid : SetLike.GradedMonoid (grade k Q) where
  one_mem := by
    let _ := Fintype.ofFinite Q
    rw [one_def]
    exact Submodule.sum_mem _ fun v _ => vertexIdempotent_mem_grade_zero v
  mul_mem _ _ _ _ hf hg := grade_mul_grade_le _ _ (Submodule.mul_mem_mul hf hg)

omit [Finite Q] in
/-- Two graded-monoid points of the graded pieces agree once their degrees and their underlying
path-algebra elements do. Private: it only removes the dependent rewriting from the products
below. -/
private theorem gradedMonoid_mk_eq {i j : ℕ} {f : grade k Q i} {g : grade k Q j} (hij : i = j)
    (hfg : (f : pathAlgebra k Q) = g) :
    GradedMonoid.mk (A := fun n => grade k Q n) i f = GradedMonoid.mk j g := by
  subst hij
  exact congrArg _ (Subtype.ext hfg)

/-- The summand of the direct sum attached to a basis path: the path itself, in the degree its
length names. This is the assignment the decomposition map lifts. -/
private noncomputable def gradeSummand (x : Quiver.TotalPath Q) : ⨁ n, grade k Q n :=
  DirectSum.of (fun n => grade k Q n) x.2.2.length ⟨ofPath x, ofPath_mem_grade x⟩

private theorem gradeSummand_mul_gradeSummand {a b c : Q} (p : _root_.Quiver.Path a b)
    (q : _root_.Quiver.Path c a) :
    gradeSummand k Q ⟨a, b, p⟩ * gradeSummand k Q ⟨c, a, q⟩
      = gradeSummand k Q ⟨c, b, q.comp p⟩ := by
  rw [gradeSummand, gradeSummand, gradeSummand, DirectSum.of_mul_of]
  refine DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_eq k Q ?_ ?_)
  · rw [_root_.Quiver.Path.length_comp]
    exact Nat.add_comm _ _
  · exact ofPath_mul_ofPath_of_comp p q

private theorem gradeSummand_mul_gradeSummand_of_not_composable
    {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    gradeSummand k Q x * gradeSummand k Q y = 0 := by
  rw [gradeSummand, gradeSummand, DirectSum.of_mul_of]
  refine (DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_eq k Q (j := x.2.2.length +
    y.2.2.length) (g := 0) rfl ?_)).trans (map_zero _)
  exact ofPath_mul_ofPath_of_not_composable h

private theorem sum_gradeSummand_nil :
    letI := Fintype.ofFinite Q
    ∑ v : Q, gradeSummand k Q ⟨v, v, _root_.Quiver.Path.nil⟩ = 1 := by
  let _ := Fintype.ofFinite Q
  have hv : ∀ v : Q, gradeSummand k Q ⟨v, v, _root_.Quiver.Path.nil⟩
      = DirectSum.of (fun n => grade k Q n) 0
        ⟨vertexIdempotent k v, vertexIdempotent_mem_grade_zero v⟩ := fun v =>
    congrArg (DirectSum.of (fun n => grade k Q n) 0)
      (Subtype.ext (vertexIdempotent_eq_ofPath k v).symm)
  have hsum : ∑ v : Q, DirectSum.of (fun n => grade k Q n) 0
        ⟨vertexIdempotent k v, vertexIdempotent_mem_grade_zero v⟩
      = DirectSum.of (fun n => grade k Q n) 0
        (∑ v : Q, ⟨vertexIdempotent k v, vertexIdempotent_mem_grade_zero v⟩) :=
    (map_sum _ _ _).symm
  rw [Finset.sum_congr rfl fun v _ => hv v, hsum, DirectSum.one_def]
  refine congrArg _ (Subtype.ext ?_)
  rw [AddSubmonoidClass.coe_finsetSum]
  exact (one_def (k := k) (Q := Q)).symm

/-- The algebra homomorphism into the direct sum of graded pieces that decomposes elements by path
length. This is the map `GradedAlgebra.ofAlgHom` installs as `DirectSum.decompose` for the grading
below, as `AddMonoidAlgebra.decomposeAux` is for the grading of a monoid algebra; the two maps are
definitionally equal. -/
noncomputable def decomposeAlgHom : pathAlgebra k Q →ₐ[k] ⨁ n, grade k Q n :=
  liftAlgHom k (gradeSummand k Q) (gradeSummand_mul_gradeSummand k Q)
    (gradeSummand_mul_gradeSummand_of_not_composable k Q) (sum_gradeSummand_nil k Q)

/-- The decomposition map sends a basis path to the summand its length names. -/
theorem decomposeAlgHom_ofPath (x : Quiver.TotalPath Q) :
    decomposeAlgHom k Q (ofPath x)
      = DirectSum.of (fun n => grade k Q n) x.2.2.length ⟨ofPath x, ofPath_mem_grade x⟩ := by
  rw [decomposeAlgHom, liftAlgHom_ofPath, gradeSummand]

/-- The span induction behind `decomposeAlgHom_of_mem`: on the span of the length-`n` paths the
decomposition map is the inclusion of the degree-`n` summand. The membership hypothesis is
quantified inside the conclusion so that the motive of the induction does not mention a fixed
membership proof; each step supplies its own. -/
private theorem decomposeAlgHom_apply_aux {n : ℕ} {f : pathAlgebra k Q}
    (hf : f ∈ Submodule.span k (Set.range fun x : {x : Quiver.TotalPath Q // x.2.2.length = n} =>
      (ofPath x.1 : pathAlgebra k Q))) :
    ∀ h : f ∈ grade k Q n,
      decomposeAlgHom k Q f = DirectSum.of (fun m => grade k Q m) n ⟨f, h⟩ := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hg
    subst hx
    exact fun _ => decomposeAlgHom_ofPath k Q x
  | zero => exact fun _ => (map_zero _).trans (map_zero _).symm
  | add g g' hg hg' ihg ihg' =>
    refine fun _ => ?_
    rw [map_add, ihg ((grade_eq_span_range k Q n).ge hg), ihg' ((grade_eq_span_range k Q n).ge hg'),
      ← map_add, AddMemClass.mk_add_mk]
  | smul c g hg ih =>
    refine fun _ => ?_
    rw [map_smul, ih ((grade_eq_span_range k Q n).ge hg), ← DirectSum.of_smul,
      SetLike.mk_smul_mk]

/-- The decomposition map is the identity on a homogeneous element, placing it in the summand its
degree names. -/
theorem decomposeAlgHom_of_mem {n : ℕ} {f : pathAlgebra k Q}
    (hf : f ∈ grade k Q n) :
    decomposeAlgHom k Q f = DirectSum.of (fun m => grade k Q m) n ⟨f, hf⟩ :=
  decomposeAlgHom_apply_aux k Q ((grade_eq_span_range k Q n).le hf) hf

/-- **The path-length grading**: the path algebra of a finite quiver is `ℕ`-graded by path length,
with the span of the paths of length `n` in degree `n`. -/
noncomputable instance gradedAlgebra : GradedAlgebra (grade k Q) :=
  .ofAlgHom _ (decomposeAlgHom k Q)
    (AlgHom.toLinearMap_injective <| (pathAlgebraBasis k Q).ext fun x => by
      simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, coe_pathAlgebraBasis, decomposeAlgHom_ofPath,
        DirectSum.coeAlgHom_of, AlgHom.coe_id, id_eq])
    fun _ f => decomposeAlgHom_of_mem k Q f.2

/-- **The path algebra is the internal direct sum of its graded pieces**: the direct-sum graded
algebra is compared with `kQ` itself, not with a separate graded copy. -/
theorem isInternal_grade : DirectSum.IsInternal (grade k Q) :=
  DirectSum.Decomposition.isInternal _

/-- The decomposition sends a basis path to the summand its length names. -/
@[simp]
theorem decompose_ofPath (x : Quiver.TotalPath Q) :
    DirectSum.decompose (grade k Q) (ofPath x : pathAlgebra k Q)
      = DirectSum.of (fun n => grade k Q n) x.2.2.length ⟨ofPath x, ofPath_mem_grade x⟩ :=
  DirectSum.decompose_of_mem _ (ofPath_mem_grade x)

end GradedAlgebra

end PathAlgebra

end TauCeti
