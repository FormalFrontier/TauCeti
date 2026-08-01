/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# The root space decomposition of `gl n R`

Let `gl n R = Matrix n n R` carry the commutator bracket and let `diagonalCartan R n` be its
diagonal Cartan subalgebra. This file computes the weight spaces of `gl n R` for that Cartan
subalgebra: *over a domain*, a matrix lies in the root space of a functional `χ` exactly when it is
supported on the pairs `(a, b)` with `εₐ - ε_b = χ`. Since the matrix unit `Eₐ_b` lies in the root
space of `εₐ - ε_b` and every matrix is a sum of matrix units, those root spaces span `gl n R`
(`TauCeti.iSup_rootSpace_glRoot_eq_top`), and hence so do all the root spaces
(`TauCeti.iSup_rootSpace_eq_top`); those two spanning statements need no hypothesis on `R` beyond
commutativity. Over a domain Mathlib's `LieModule.iSupIndep_genWeightSpace` makes the latter
supremum direct, exhibiting `gl n R` as the direct sum of its root spaces.

The pairs `(a, b)` do *not* index those root spaces injectively, so the finer decomposition of
`gl n R` into the matrix-unit lines `R · Eₐ_b` is not the root space decomposition. Every
`εₐ - ε_a` is the zero functional, and the zero root space contains every diagonal matrix rather
than just the line `R · Eₐ_a`: that is `TauCeti.glRoot_self` together with
`TauCeti.single_mem_rootSpace`, and over a Noetherian base Mathlib's
`LieAlgebra.rootSpace_zero_eq` identifies the zero root space with the whole diagonal Cartan
subalgebra, as it does for any Cartan subalgebra. In characteristic two `εᵢ - εⱼ = εⱼ - εᵢ`, so the
pairs `(i, j)` and `(j, i)` share a root space as well. Only for `i ≠ j`, over a domain, and away
from characteristic two, is a root space the line spanned by a single matrix unit
(`TauCeti.rootSpace_glRoot_eq_span`).

Everything rests on one computation, `TauCeti.lie_apply_of_mem_diagonalCartan`: the adjoint action
of a diagonal matrix scales the `(a, b)` entry by `A a a - A b b`. Equivalently `ad A` is the
diagonal operator on the matrix-unit basis with entries `A a a - A b b`
(`TauCeti.toEnd_diagonalCartan_eq_toLin_diagonal`), which is what puts Mathlib's theory of diagonal
operators at our disposal: over a domain the generalized weight spaces are honest simultaneous
eigenspaces (`TauCeti.rootSpace_diagonalCartan_eq_weightSpace`), and the diagonal Cartan is *split*,
so triangularizability holds over an arbitrary commutative ring with no algebraic closure hypothesis
(`TauCeti.instIsTriangularizableMatrixDiagonalCartan`).

## Main results

* `TauCeti.toEnd_diagonalCartan_eq_toLin_diagonal`: `ad A` is a diagonal operator in the matrix-unit
  basis, for `A` in the diagonal Cartan subalgebra.
* `TauCeti.rootSpace_diagonalCartan_eq_weightSpace`: over a domain, the generalized weight spaces
  are honest simultaneous eigenspaces.
* `TauCeti.mem_rootSpace_diagonalCartan_iff`: over a domain, a matrix lies in the root space of `χ`
  exactly when its `(a, b)` entry vanishes for every pair with `εₐ - ε_b ≠ χ`.
* `TauCeti.iSup_rootSpace_glRoot_eq_top`: over any commutative ring, `gl n R` is spanned by the root
  spaces of the weights `εₐ - ε_b`; `TauCeti.iSup_rootSpace_eq_top` is the same spanning statement
  indexed by the weights themselves, where each root space occurs once and the supremum is the root
  space decomposition.
* `TauCeti.instIsTriangularizableMatrixDiagonalCartan`: over any commutative ring, `gl n R` is
  triangularizable over its diagonal Cartan subalgebra, so Mathlib's weight space machinery applies
  over any field, not only an algebraically closed one.
* `TauCeti.rootSpace_glRoot_eq_span`: over a domain and away from characteristic two the root space
  of `εᵢ - εⱼ`, for `i ≠ j`, is the line spanned by the matrix unit `Eᵢⱼ`, and
  `TauCeti.finrank_rootSpace_glRoot_eq_one` records the resulting dimension over a field.
* `TauCeti.rootSpace_diagonalCartan_eq_bot`: over a domain, a functional that is not one of the
  `εₐ - ε_b` has trivial root space, so the roots of `gl n R` are exactly the `εᵢ - εⱼ` with `i ≠ j`
  (`TauCeti.exists_glRoot_eq_of_rootSpace_ne_bot`).

## Implementation notes

The spanning statements `TauCeti.iSup_rootSpace_glRoot_eq_top` and `TauCeti.iSup_rootSpace_eq_top`,
the diagonal-operator identification `TauCeti.toEnd_diagonalCartan_eq_toLin_diagonal` and
triangularizability hold over an arbitrary commutative ring. Everything that computes a root space
rather than merely placing an element in one assumes `[IsDomain R]`, since that is the hypothesis
under which Mathlib's `Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace` collapses a generalized
eigenspace of a diagonal operator to the eigenspace.

The hypothesis `(2 : R) ≠ 0` in `TauCeti.rootSpace_glRoot_eq_span` is not an artefact. In
characteristic two `εᵢ - εⱼ = εⱼ - εᵢ`, so `Eᵢⱼ` and `Eⱼᵢ` share a root space and that root space
is a plane rather than a line. The statements that do not separate `εᵢ - εⱼ` from `εⱼ - εᵢ`, in
particular `TauCeti.mem_rootSpace_diagonalCartan_iff` and `TauCeti.iSup_rootSpace_glRoot_eq_top`,
need no such hypothesis.

Since the Killing form of `gl n R` is degenerate, `LieAlgebra.IsKilling` is unavailable and with it
all of Mathlib's `LieAlgebra.IsKilling.rootSystem` machinery, including `finrank_rootSpace_eq_one`;
the analogues here are proved from scratch. See the module documentation of
`TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan`.

## References

This implements the root space decomposition of `gl n` supporting the diagonal Cartan targets of
Layer 9 (and the Layer 1 root space vocabulary, transported to the reductive case) of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-! ### The adjoint action of the diagonal Cartan as a diagonal operator -/

/-- **`ad A` is a diagonal operator** for `A` in the diagonal Cartan subalgebra: in the matrix-unit
basis it is the diagonal matrix whose `(a, b)` entry is `A a a - A b b`. This identification is what
makes Mathlib's theory of diagonal operators, in particular
`Matrix.iSup_eigenspace_toLin_diagonal_eq_top` and
`Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace`, available for the adjoint action. -/
theorem toEnd_diagonalCartan_eq_toLin_diagonal (A : diagonalCartan R n) :
    LieModule.toEnd R (diagonalCartan R n) (Matrix n n R) A
      = toLin (stdBasis R n n) (stdBasis R n n)
          (diagonal fun p : n × n => (A : Matrix n n R) p.1 p.1 - (A : Matrix n n R) p.2 p.2) := by
  refine (stdBasis R n n).ext fun p => ?_
  rw [LieModule.toEnd_apply_apply, LieSubalgebra.coe_bracket_of_module, toLin_self,
    Finset.sum_eq_single p (fun q _ hq => by rw [diagonal_apply_ne _ hq, zero_smul]) (by simp),
    diagonal_apply_eq, stdBasis_eq_single, lie_single_of_mem_diagonalCartan A.2]

/-! ### Triangularizability: the diagonal Cartan of `gl n R` is split -/

/-- `gl n R` is triangularizable over its diagonal Cartan subalgebra: the matrix units are a
simultaneous eigenbasis. No field, characteristic or algebraic closure hypothesis is needed, so
this is the statement that the diagonal Cartan subalgebra is *split*. -/
instance instIsTriangularizableMatrixDiagonalCartan :
    LieModule.IsTriangularizable R (diagonalCartan R n) (Matrix n n R) where
  maxGenEigenspace_eq_top A := by
    rw [toEnd_diagonalCartan_eq_toLin_diagonal, eq_top_iff,
      ← iSup_eigenspace_toLin_diagonal_eq_top (M := Matrix n n R) _ (stdBasis R n n)]
    exact iSup_mono fun _ => Module.End.eigenspace_le_maxGenEigenspace

/-! ### The weight spaces of `gl n R` -/

/-- **Over a domain the weight spaces of `gl n R` are honest simultaneous eigenspaces**, not merely
generalized ones: the diagonal Cartan subalgebra acts diagonally on the matrix units, so no
nilpotent part survives. For a Killing-semisimple Lie algebra the corresponding statement is the
abstract Jordan decomposition; here it is Mathlib's
`Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace` applied to
`TauCeti.toEnd_diagonalCartan_eq_toLin_diagonal`, one operator at a time. The hypothesis
`[IsDomain R]` is the one that Mathlib lemma needs, and it is not decorative: over a ring with
nilpotents a generalized eigenspace of a diagonal operator can be strictly larger than the
eigenspace. -/
theorem rootSpace_diagonalCartan_eq_weightSpace [IsDomain R]
    (χ : Module.Dual R (diagonalCartan R n)) :
    LieAlgebra.rootSpace (diagonalCartan R n) χ
      = LieModule.weightSpace (Matrix n n R) (χ : diagonalCartan R n → R) := by
  refine le_antisymm (fun B hB => ?_) (LieModule.weightSpace_le_genWeightSpace _ _)
  rw [LieModule.mem_weightSpace]
  intro A
  have hB' : B ∈ Module.End.maxGenEigenspace
      (LieModule.toEnd R (diagonalCartan R n) (Matrix n n R) A) (χ A) := by
    have := LieModule.genWeightSpace_le_genWeightSpaceOf (Matrix n n R) A _ hB
    rwa [LieModule.mem_genWeightSpaceOf, ← Module.End.mem_maxGenEigenspace] at this
  rw [toEnd_diagonalCartan_eq_toLin_diagonal, maxGenEigenspace_toLin_diagonal_eq_eigenspace,
    Module.End.mem_eigenspace_iff, ← toEnd_diagonalCartan_eq_toLin_diagonal,
    LieModule.toEnd_apply_apply] at hB'
  exact hB'

/-- A matrix supported on the pairs `(a, b)` with `εₐ - ε_b = χ` lies in the root space of `χ`. It
lies in the honest weight space, in fact: the matrix units are eigenvectors of the diagonal Cartan
subalgebra. -/
theorem mem_rootSpace_diagonalCartan_of_forall {χ : Module.Dual R (diagonalCartan R n)}
    {B : Matrix n n R} (h : ∀ a b, glRoot R n a b ≠ χ → B a b = 0) :
    B ∈ LieAlgebra.rootSpace (diagonalCartan R n) χ := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  intro A
  ext a b
  rw [LieSubalgebra.coe_bracket_of_module, lie_apply_of_mem_diagonalCartan A.2,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hab : glRoot R n a b = χ
  · rw [← glRoot_apply a b A, hab]
  · rw [h a b hab, mul_zero, mul_zero]

/-- **The weight spaces of `gl n R`, over a domain**: for `[IsDomain R]`, a matrix lies in the root
space of a functional `χ` on the diagonal Cartan subalgebra exactly when its `(a, b)` entry vanishes
for every pair with `εₐ - ε_b ≠ χ`. The domain hypothesis is used only for the forward implication,
through `TauCeti.rootSpace_diagonalCartan_eq_weightSpace`; the converse is
`TauCeti.mem_rootSpace_diagonalCartan_of_forall`, which holds over any commutative ring. No
hypothesis on the characteristic is needed, since the statement does not separate `εᵢ - εⱼ` from
`εⱼ - εᵢ`. -/
@[simp]
theorem mem_rootSpace_diagonalCartan_iff [IsDomain R] (χ : Module.Dual R (diagonalCartan R n))
    (B : Matrix n n R) :
    B ∈ LieAlgebra.rootSpace (diagonalCartan R n) χ ↔ ∀ a b, glRoot R n a b ≠ χ → B a b = 0 := by
  refine ⟨fun hB a b hab => ?_, mem_rootSpace_diagonalCartan_of_forall⟩
  obtain ⟨k, hk⟩ : ∃ k, glRoot R n a b (diagonalCartanBasis R n k)
      ≠ χ (diagonalCartanBasis R n k) := by
    by_contra hcon
    push Not at hcon
    exact hab ((diagonalCartanBasis R n).ext hcon)
  rw [rootSpace_diagonalCartan_eq_weightSpace, LieModule.mem_weightSpace] at hB
  set A := diagonalCartanBasis R n k
  have hentry := congrFun (congrFun (hB A) a) b
  rw [LieSubalgebra.coe_bracket_of_module, lie_apply_of_mem_diagonalCartan A.2, Matrix.smul_apply,
    smul_eq_mul, ← glRoot_apply a b A] at hentry
  exact (mul_eq_zero.mp (by linear_combination hentry)).resolve_left (sub_ne_zero.mpr hk)

/-! ### The root space decomposition -/

/-- The root spaces of the weights `εₐ - ε_b` span `gl n R`, because the matrix unit `Eₐ_b` lies in
the root space of `εₐ - ε_b`.

This is a spanning statement only. The pairs `(a, b)` repeat root spaces: every `εₐ - ε_a` is the
zero functional, whose root space contains the whole diagonal Cartan subalgebra, and in
characteristic two `εᵢ - εⱼ = εⱼ - εᵢ`. So this supremum is not direct; for the supremum over the
weights themselves, which over a domain is, see `TauCeti.iSup_rootSpace_eq_top`. -/
theorem iSup_rootSpace_glRoot_eq_top :
    ⨆ p : n × n, LieAlgebra.rootSpace (diagonalCartan R n) (glRoot R n p.1 p.2) = ⊤ := by
  refine top_le_iff.mp fun B _ => ?_
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.iSup_toSubmodule, matrix_eq_sum_single B]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  exact Submodule.mem_iSup_of_mem (a, b) (single_mem_rootSpace a b (B a b))

/-- **The root space decomposition of `gl n R`**: the root spaces span `gl n R`. Over a domain
Mathlib's `LieModule.iSupIndep_genWeightSpace` says the root spaces are independent, so this
supremum is direct and `gl n R` is the direct sum of its root spaces.

Mathlib's `LieModule.iSup_genWeightSpace_eq_top` proves the same spanning statement for a
triangularizable module, but only in finite dimensions over a field; here the diagonal Cartan
subalgebra is split, so no hypothesis on `R` is needed. -/
theorem iSup_rootSpace_eq_top :
    ⨆ χ : Module.Dual R (diagonalCartan R n), LieAlgebra.rootSpace (diagonalCartan R n) χ = ⊤ := by
  rw [eq_top_iff, ← iSup_rootSpace_glRoot_eq_top]
  exact iSup_le fun p =>
    le_iSup (fun χ : Module.Dual R (diagonalCartan R n) =>
      LieAlgebra.rootSpace (diagonalCartan R n) χ) (glRoot R n p.1 p.2)

/-! ### The roots of `gl n R`, and the root spaces as lines -/

/-- Away from characteristic two the weights `εᵢ - εⱼ`, for `i ≠ j`, are pairwise distinct. In
characteristic two `εᵢ - εⱼ = εⱼ - εᵢ`, and the statement fails. -/
@[simp]
theorem glRoot_eq_glRoot_iff (h2 : (2 : R) ≠ 0) {i j : n} (hij : i ≠ j) (a b : n) :
    glRoot R n a b = glRoot R n i j ↔ a = i ∧ b = j := by
  have : Nontrivial R := nontrivial_of_ne 2 0 h2
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  replace h : (Pi.single a 1 - Pi.single b 1 : n → R) = Pi.single i 1 - Pi.single j 1 := by
    funext k
    have hk := congrArg
      (fun χ : Module.Dual R (diagonalCartan R n) => χ (diagonalCartanBasis R n k)) h
    simpa [single_apply, Pi.single_apply] using hk
  have hi := congrFun h i
  have hj := congrFun h j
  rw [Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij] at hi
  rw [Pi.sub_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at hj
  refine ⟨?_, ?_⟩
  · by_contra hia
    rw [Pi.single_eq_of_ne (Ne.symm hia)] at hi
    by_cases hib : b = i
    · rw [hib, Pi.single_eq_same] at hi
      exact absurd (by linear_combination -hi) h2
    · rw [Pi.single_eq_of_ne (Ne.symm hib)] at hi
      have h10 : (1 : R) = 0 := by linear_combination -hi
      exact one_ne_zero h10
  · by_contra hjb
    rw [Pi.single_eq_of_ne (Ne.symm hjb)] at hj
    by_cases hja : a = j
    · rw [hja, Pi.single_eq_same] at hj
      exact absurd (by linear_combination hj) h2
    · rw [Pi.single_eq_of_ne (Ne.symm hja)] at hj
      have h10 : (1 : R) = 0 := by linear_combination hj
      exact one_ne_zero h10

/-- **The root spaces of `gl n R` are lines**: over a domain (`[IsDomain R]`), away from
characteristic two (`(2 : R) ≠ 0`), and for `i ≠ j`, the root space of `εᵢ - εⱼ` is spanned by the
matrix unit `Eᵢⱼ`. All three hypotheses are needed: for `i = j` the root space is the zero root
space, which contains the whole diagonal Cartan subalgebra, and in characteristic two `Eᵢⱼ` and
`Eⱼᵢ` share a root space, which is then a plane. This is the `gl n` analogue of Mathlib's
`LieAlgebra.IsKilling.finrank_rootSpace_eq_one`, which is unavailable here because the Killing form
of `gl n R` is degenerate. -/
theorem rootSpace_glRoot_eq_span [IsDomain R] (h2 : (2 : R) ≠ 0) {i j : n} (hij : i ≠ j) :
    (LieAlgebra.rootSpace (diagonalCartan R n) (glRoot R n i j)).toSubmodule
      = R ∙ single i j 1 := by
  refine le_antisymm (fun B hB => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    refine ⟨B i j, ?_⟩
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, single_apply]
    by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h, mul_zero]
      refine ((mem_rootSpace_diagonalCartan_iff _ _).mp hB a b fun hcon => h ?_).symm
      obtain ⟨rfl, rfl⟩ := (glRoot_eq_glRoot_iff h2 hij a b).mp hcon
      exact ⟨rfl, rfl⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact single_mem_rootSpace i j 1

/-- Over a field `K` of characteristic other than two (`(2 : K) ≠ 0`), the root space of `gl n K`
attached to the root `εᵢ - εⱼ` with `i ≠ j` is one-dimensional. This is
`TauCeti.rootSpace_glRoot_eq_span` counted, so it carries the same hypotheses. -/
theorem finrank_rootSpace_glRoot_eq_one {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {i j : n}
    (hij : i ≠ j) :
    Module.finrank K
      (LieAlgebra.rootSpace (diagonalCartan K n) (glRoot K n i j)).toSubmodule = 1 := by
  have hne : single i j (1 : K) ≠ 0 := by
    intro hcon
    simpa using congrFun (congrFun hcon i) j
  rw [rootSpace_glRoot_eq_span h2 hij]
  exact finrank_span_singleton hne

/-- Over a domain (`[IsDomain R]`), a functional on the diagonal Cartan subalgebra that is not one
of the `εₐ - ε_b` has trivial root space. -/
theorem rootSpace_diagonalCartan_eq_bot [IsDomain R] {χ : Module.Dual R (diagonalCartan R n)}
    (h : ∀ a b, glRoot R n a b ≠ χ) :
    LieAlgebra.rootSpace (diagonalCartan R n) χ = ⊥ := by
  refine le_antisymm (fun B hB => ?_) bot_le
  rw [LieSubmodule.mem_bot]
  ext a b
  rw [Matrix.zero_apply]
  exact (mem_rootSpace_diagonalCartan_iff _ _).mp hB a b (h a b)

/-- **The roots of `gl n R`**: over a domain (`[IsDomain R]`), a nonzero functional `χ` with a
nonzero root space is `εᵢ - εⱼ` for some `i ≠ j`. The hypothesis `χ ≠ 0` is what rules out the
diagonal pairs, since every `εₐ - ε_a` is the zero functional and the zero root space contains the
whole diagonal Cartan subalgebra. -/
theorem exists_glRoot_eq_of_rootSpace_ne_bot [IsDomain R]
    {χ : Module.Dual R (diagonalCartan R n)} (hχ : χ ≠ 0)
    (h : LieAlgebra.rootSpace (diagonalCartan R n) χ ≠ ⊥) :
    ∃ i j, i ≠ j ∧ glRoot R n i j = χ := by
  by_contra hcon
  push Not at hcon
  refine h (rootSpace_diagonalCartan_eq_bot fun a b hab => ?_)
  by_cases hab' : a = b
  · exact hχ (by rw [← hab, hab', glRoot_self])
  · exact hcon a b hab' hab

end TauCeti
