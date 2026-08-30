/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix
public import TauCeti.RingTheory.Idempotents.Hom

/-!
# The graded homomorphism spaces of the zigzag vertex projectives

For a finite simple graph without isolated vertices, `TauCeti.zigzagProjective` is the
indecomposable left projective `P_i = Z e_i` of the zigzag relation quotient and
`TauCeti.zigzagCorner` is the corner `e_i Z e_j`.  This file supplies the dictionary those two
files leave open, namely

`Hom_Z(P_i, P_j) ≅ e_i Z e_j`,

together with its refinement by the path-length grading.  The grading is extended by zero from
`ℕ` to `ℤ`, and the internal shift is `M{d}_p = M_{p-d}`, so `[M{1}] = q[M]`.  Thus the
degree-zero homomorphisms `P_i → P_j{d}` are the degree-`(-d)` part of the corner.  Equivalently,
the homomorphisms which raise degree by `n : ℕ` are `Hom(P_i{n}, P_j)`.

Combining the two identifications with the entrywise computation of the graded corners in
`TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix` turns the graded Cartan matrix into what
the roadmap asks it to be, a matrix of graded dimensions of homomorphism spaces,

`C_G(q)_{i,j} = ∑_d dim_k Hom(P_i{d}, P_j) q^d = (1 + q²) δ_{i,j} + q A_{i,j}`.

Moving the internal shift from source to target reverses its sign: intrinsically degree-`d` maps
are `Hom(P_i{d}, P_j)`, equivalently `Hom(P_i, P_j{-d})`, not `Hom(P_i, P_j{d})`.

## Main definitions

* `TauCeti.zigzagProjectiveHomEquivCorner`: **the dictionary `Hom_Z(P_i, P_j) ≃ₗ[k] e_i Z e_j`.**
* `TauCeti.zigzagProjectiveShiftGrade`: the grading of the shifted projective `P_i{d}`.
* `TauCeti.zigzagProjectiveTargetShiftHom`: the degree-zero homomorphisms
  `Hom(P_i, P_j{d})`, for every `d : ℤ`.
* `TauCeti.zigzagProjectiveHomOfDegree`: the homomorphisms `P_i → P_j` raising path degree by
  `d`, that is `Hom(P_i{d}, P_j)`.

## Main results

* `TauCeti.zigzagProjectiveHomOfDegreeEquivGradedCorner`: **the graded dictionary**
  `Hom(P_i{d}, P_j) ≃ₗ[k] (e_i Z e_j)_d`.
* `TauCeti.zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner`: **the signed target-shift
  dictionary**
  `Hom(P_i, P_j{d}) ≃ₗ[k] (e_i Z e_j)_{-d}` for every `d : ℤ`.
* `TauCeti.zigzagProjectiveHomOfDegree_eq_bot_of_three_le`: no homomorphism raises degree by three
  or more, so the graded homomorphism spaces are concentrated in degrees `0`, `1` and `2`.
* `TauCeti.id_mem_zigzagProjectiveHomOfDegree_zero` and
  `TauCeti.zigzagProjectiveHomEquivCorner_symm_apply_mem`: the identity has degree zero, and right
  multiplication by a homogeneous element of the corner has that element's degree.
* `TauCeti.finrank_zigzagProjectiveHomOfDegree_zero_self`,
  `TauCeti.finrank_zigzagProjectiveHomOfDegree_one_of_adj` and
  `TauCeti.finrank_zigzagProjectiveHomOfDegree_two_self_of_adj`: the three one-dimensional
  homogeneous homomorphism spaces — the identity of `P_i`, the map along an edge, and the map
  through the volume class — with the vanishing of all the others.
* `TauCeti.zigzagGradedCartanMatrix_eq_sum_finrank_zigzagProjectiveHomOfDegree`: **the graded
  Cartan entry is the graded dimension of the homomorphism spaces**, `∑_d dim Hom(P_i{d}, P_j) qᵈ`.

## Implementation notes

Both source- and target-shifted Hom spaces are defined by intrinsic homogeneity conditions,
quantified over every homogeneous element of `P_i`, rather than as preimages of graded corners.
The comparison with evaluation at the generator is then proved.  The shifted projectives retain
the same underlying module and change only their family of homogeneous submodules, so these Hom
spaces are `k`-submodules of the ungraded homomorphism space.

## References

This is the homomorphism half of Layer 3 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which
asks for `P_i` together with "all homogeneous `Hom(P_i,P_j{d})` spaces".  Under its pinned shift
convention, moving that target shift to the source reverses the sign; the nonnegative
degree-raising part formalized here is `Hom(P_i{d},P_j) = Hom(P_i,P_j{-d})`.  See
Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver Polynomial

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### The ungraded dictionary -/

private theorem zigzagProjective_eq_spanSingleton (i : V) :
    zigzagProjective k G i = Ideal.span {zigzagVertexIdempotent k G i} := by
  ext x
  rw [mem_zigzagProjective_iff,
    mem_span_singleton_iff_mul_eq_self (zigzagMk_vertexIdempotent_mul_self k G i)]

private theorem zigzagCorner_eq_cornerSubmodule (i j : V) :
    zigzagCorner k G i j =
      cornerSubmodule k (zigzagVertexIdempotent k G i) (zigzagVertexIdempotent k G j) := by
  ext x
  rw [mem_zigzagCorner_iff, mem_cornerSubmodule_iff k
    (zigzagMk_vertexIdempotent_mul_self k G i)
    (zigzagMk_vertexIdempotent_mul_self k G j)]

private noncomputable def zigzagProjectiveEquivSpanSingleton (i : V) :
    zigzagProjective k G i ≃ₗ[nonisolatedZigzagQuotient k G]
      (Ideal.span {zigzagVertexIdempotent k G i} :
        Ideal (nonisolatedZigzagQuotient k G)) :=
  LinearEquiv.ofEq _ _ (zigzagProjective_eq_spanSingleton k G i)

private noncomputable def zigzagProjectiveHomEquivSpanSingletonHom (i j : V) :
    (zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) ≃ₗ[k]
      ((Ideal.span {zigzagVertexIdempotent k G i} :
          Ideal (nonisolatedZigzagQuotient k G)) →ₗ[nonisolatedZigzagQuotient k G]
        (Ideal.span {zigzagVertexIdempotent k G j} :
          Ideal (nonisolatedZigzagQuotient k G))) :=
  (LinearEquiv.arrowCongrAddEquiv (zigzagProjectiveEquivSpanSingleton k G i)
    (zigzagProjectiveEquivSpanSingleton k G j)).toLinearEquiv (by
      intro c φ
      ext x
      simp only [LinearEquiv.arrowCongrAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply]
      exact congr_arg Subtype.val
        ((zigzagProjectiveEquivSpanSingleton k G j).toLinearMap.map_smul_of_tower c
          (φ ((zigzagProjectiveEquivSpanSingleton k G i).symm x))))

private noncomputable def zigzagCornerEquivCornerSubmodule (i j : V) :
    zigzagCorner k G i j ≃ₗ[k]
      cornerSubmodule k (zigzagVertexIdempotent k G i) (zigzagVertexIdempotent k G j) :=
  LinearEquiv.ofEq _ _ (zigzagCorner_eq_cornerSubmodule k G i j)

private theorem coe_zigzagProjectiveEquivSpanSingleton_apply (i : V)
    (x : zigzagProjective k G i) :
    (zigzagProjectiveEquivSpanSingleton k G i x : nonisolatedZigzagQuotient k G) = x := by
  simpa only [zigzagProjectiveEquivSpanSingleton] using
    LinearEquiv.coe_ofEq_apply (zigzagProjective_eq_spanSingleton k G i) x

private theorem coe_zigzagProjectiveEquivSpanSingleton_symm_apply (i : V)
    (x : (Ideal.span {zigzagVertexIdempotent k G i} :
      Ideal (nonisolatedZigzagQuotient k G))) :
    ((zigzagProjectiveEquivSpanSingleton k G i).symm x : nonisolatedZigzagQuotient k G) = x := by
  simpa only [zigzagProjectiveEquivSpanSingleton, LinearEquiv.ofEq_symm] using
    LinearEquiv.coe_ofEq_apply (zigzagProjective_eq_spanSingleton k G i).symm x

private theorem coe_zigzagCornerEquivCornerSubmodule_apply (i j : V)
    (x : zigzagCorner k G i j) :
    (zigzagCornerEquivCornerSubmodule k G i j x : nonisolatedZigzagQuotient k G) = x := by
  simpa only [zigzagCornerEquivCornerSubmodule] using
    LinearEquiv.coe_ofEq_apply (zigzagCorner_eq_cornerSubmodule k G i j) x

private theorem coe_zigzagCornerEquivCornerSubmodule_symm_apply (i j : V)
    (x : cornerSubmodule k (zigzagVertexIdempotent k G i) (zigzagVertexIdempotent k G j)) :
    ((zigzagCornerEquivCornerSubmodule k G i j).symm x :
      nonisolatedZigzagQuotient k G) = x := by
  simpa only [zigzagCornerEquivCornerSubmodule, LinearEquiv.ofEq_symm] using
    LinearEquiv.coe_ofEq_apply (zigzagCorner_eq_cornerSubmodule k G i j).symm x

private theorem coe_zigzagProjectiveHomEquivSpanSingletonHom_apply {i j : V}
    (φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G j) :
    ((zigzagProjectiveHomEquivSpanSingletonHom k G i j φ)
        (spanSingletonGenerator (zigzagVertexIdempotent k G i)) :
      nonisolatedZigzagQuotient k G) =
        (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) := by
  -- The arrow-congruence equivalence has no application theorem, so expose its composite once;
  -- the following rewrites use the explicit coercion lemmas for both transported projectives.
  change ((zigzagProjectiveEquivSpanSingleton k G j)
      (φ ((zigzagProjectiveEquivSpanSingleton k G i).symm
        (spanSingletonGenerator (zigzagVertexIdempotent k G i)))) :
    nonisolatedZigzagQuotient k G) = _
  rw [coe_zigzagProjectiveEquivSpanSingleton_apply]
  have harg : (zigzagProjectiveEquivSpanSingleton k G i).symm
      (spanSingletonGenerator (zigzagVertexIdempotent k G i)) =
        zigzagProjectiveGenerator k G i := by
    apply Subtype.ext
    rw [coe_zigzagProjectiveEquivSpanSingleton_symm_apply, coe_spanSingletonGenerator,
      coe_zigzagProjectiveGenerator]
  rw [harg]

private theorem coe_zigzagProjectiveHomEquivSpanSingletonHom_symm_apply {i j : V}
    (φ : (Ideal.span {zigzagVertexIdempotent k G i} :
        Ideal (nonisolatedZigzagQuotient k G)) →ₗ[nonisolatedZigzagQuotient k G]
      (Ideal.span {zigzagVertexIdempotent k G j} :
        Ideal (nonisolatedZigzagQuotient k G))) (y : zigzagProjective k G i) :
    (((zigzagProjectiveHomEquivSpanSingletonHom k G i j).symm φ) y :
      nonisolatedZigzagQuotient k G) =
        (φ (zigzagProjectiveEquivSpanSingleton k G i y) :
          nonisolatedZigzagQuotient k G) := by
  -- As above, expose the arrow-congruence application and immediately rewrite the transport.
  change ((zigzagProjectiveEquivSpanSingleton k G j).symm
      (φ (zigzagProjectiveEquivSpanSingleton k G i y)) :
    nonisolatedZigzagQuotient k G) = _
  rw [coe_zigzagProjectiveEquivSpanSingleton_symm_apply]

/-- **The homomorphisms `Z e_i → Z e_j` are the corner `e_i Z e_j`**, by evaluation at the
generator `e_i`.  This is the dictionary through which the corners computed by
`TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix` are homomorphism spaces of the vertex
projectives. -/
noncomputable def zigzagProjectiveHomEquivCorner (i j : V) :
    (zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) ≃ₗ[k]
      zigzagCorner k G i j :=
  (zigzagProjectiveHomEquivSpanSingletonHom k G i j).trans
    ((spanSingletonHomEquivCorner (zigzagMk_vertexIdempotent_mul_self k G i)
        (zigzagMk_vertexIdempotent_mul_self k G j)).trans
      (zigzagCornerEquivCornerSubmodule k G i j).symm)

@[simp]
theorem coe_zigzagProjectiveHomEquivCorner_apply {i j : V}
    (φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) :
    ((zigzagProjectiveHomEquivCorner k G i j φ : zigzagCorner k G i j) :
        nonisolatedZigzagQuotient k G) =
      (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) :=
  by
    -- Expose the composite equivalence; every step below is then an explicit coercion lemma.
    change ((zigzagCornerEquivCornerSubmodule k G i j).symm
      (spanSingletonHomEquivCorner (zigzagMk_vertexIdempotent_mul_self k G i)
        (zigzagMk_vertexIdempotent_mul_self k G j)
        (zigzagProjectiveHomEquivSpanSingletonHom k G i j φ)) :
          nonisolatedZigzagQuotient k G) = _
    calc
      _ = (spanSingletonHomEquivCorner (zigzagMk_vertexIdempotent_mul_self k G i)
          (zigzagMk_vertexIdempotent_mul_self k G j)
          (zigzagProjectiveHomEquivSpanSingletonHom k G i j φ) :
            nonisolatedZigzagQuotient k G) :=
        coe_zigzagCornerEquivCornerSubmodule_symm_apply k G i j _
      _ = ((zigzagProjectiveHomEquivSpanSingletonHom k G i j φ)
          (spanSingletonGenerator (zigzagVertexIdempotent k G i)) :
            nonisolatedZigzagQuotient k G) :=
        coe_spanSingletonHomEquivCorner_apply (zigzagMk_vertexIdempotent_mul_self k G i)
          (zigzagMk_vertexIdempotent_mul_self k G j) _
      _ = _ := coe_zigzagProjectiveHomEquivSpanSingletonHom_apply k G φ

@[simp]
theorem coe_zigzagProjectiveHomEquivCorner_symm_apply {i j : V} (x : zigzagCorner k G i j)
    (y : zigzagProjective k G i) :
    (((zigzagProjectiveHomEquivCorner k G i j).symm x) y : nonisolatedZigzagQuotient k G) =
      (y : nonisolatedZigzagQuotient k G) * (x : nonisolatedZigzagQuotient k G) :=
  by
    -- Expose the composite inverse; its factors are handled by their application lemmas.
    change (((zigzagProjectiveHomEquivSpanSingletonHom k G i j).symm
      ((spanSingletonHomEquivCorner (zigzagMk_vertexIdempotent_mul_self k G i)
        (zigzagMk_vertexIdempotent_mul_self k G j)).symm
          (zigzagCornerEquivCornerSubmodule k G i j x))) y :
            nonisolatedZigzagQuotient k G) = _
    calc
      _ = (((spanSingletonHomEquivCorner (zigzagMk_vertexIdempotent_mul_self k G i)
          (zigzagMk_vertexIdempotent_mul_self k G j)).symm
            (zigzagCornerEquivCornerSubmodule k G i j x))
              (zigzagProjectiveEquivSpanSingleton k G i y) :
                nonisolatedZigzagQuotient k G) :=
        coe_zigzagProjectiveHomEquivSpanSingletonHom_symm_apply k G _ _
      _ = (zigzagProjectiveEquivSpanSingleton k G i y :
            nonisolatedZigzagQuotient k G) *
          (zigzagCornerEquivCornerSubmodule k G i j x :
            nonisolatedZigzagQuotient k G) :=
        coe_spanSingletonHomEquivCorner_symm_apply
          (zigzagMk_vertexIdempotent_mul_self k G i)
          (zigzagMk_vertexIdempotent_mul_self k G j) _ _
      _ = _ := by
        rw [coe_zigzagProjectiveEquivSpanSingleton_apply,
          coe_zigzagCornerEquivCornerSubmodule_apply]

/-- A homomorphism `Z e_i → Z e_j` is right multiplication by its value at the generator. -/
theorem coe_zigzagProjectiveHom_apply {i j : V}
    (φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j)
    (x : zigzagProjective k G i) :
    (φ x : nonisolatedZigzagQuotient k G) =
      (x : nonisolatedZigzagQuotient k G) *
        (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) :=
  by
    calc
      (φ x : nonisolatedZigzagQuotient k G) =
          (((zigzagProjectiveHomEquivCorner k G i j).symm
            (zigzagProjectiveHomEquivCorner k G i j φ)) x :
              nonisolatedZigzagQuotient k G) := by
        rw [LinearEquiv.symm_apply_apply]
      _ = (x : nonisolatedZigzagQuotient k G) *
          (zigzagProjectiveHomEquivCorner k G i j φ :
            nonisolatedZigzagQuotient k G) :=
        coe_zigzagProjectiveHomEquivCorner_symm_apply k G _ _
      _ = (x : nonisolatedZigzagQuotient k G) *
          (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) := by
        rw [coe_zigzagProjectiveHomEquivCorner_apply]

/-! ### The graded dictionary -/

/-- The signed degree-`d` part of the corner `e_i Z e_j`. -/
noncomputable def zigzagIntegerGradedCorner (i j : V) (d : ℤ) :
    Submodule k (nonisolatedZigzagQuotient k G) :=
  zigzagCorner k G i j ⊓ zigzagIntegerGrade k G d

@[simp]
theorem mem_zigzagIntegerGradedCorner_iff {i j : V} {d : ℤ}
    {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagIntegerGradedCorner k G i j d ↔
      x ∈ zigzagCorner k G i j ∧ x ∈ zigzagIntegerGrade k G d :=
  Iff.rfl

@[simp]
theorem zigzagIntegerGradedCorner_ofNat (i j : V) (d : ℕ) :
    zigzagIntegerGradedCorner k G i j d = zigzagGradedCorner k G i j d := by
  ext x
  simp [zigzagIntegerGradedCorner]

/-- Signed corners vanish in negative degrees. -/
theorem zigzagIntegerGradedCorner_eq_bot_of_neg (i j : V) {d : ℤ} (hd : d < 0) :
    zigzagIntegerGradedCorner k G i j d = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  have h := ((mem_zigzagIntegerGradedCorner_iff k G).1 hx).2
  rw [zigzagIntegerGrade_eq_bot_of_neg k G hd, Submodule.mem_bot] at h
  exact h

/-- The graded homomorphism space `Hom(P_i, P_j{d})`: the `Z`-linear maps which are degree zero
from the grading of `P_i` to the shifted grading of `P_j{d}`.  The shift parameter is an arbitrary
integer, as required by the internal grading-shift action. -/
noncomputable def zigzagProjectiveTargetShiftHom (i j : V) (d : ℤ) :
    Submodule k
      (zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) :=
  LinearMap.homogeneousSubmodule (R := nonisolatedZigzagQuotient k G) (S := k)
    (zigzagProjectiveGrade k G i) (zigzagProjectiveShiftGrade k G j d) 0

/-- A map `P_i → P_j{d}` is degree zero precisely when its underlying map has signed degree
`-d`. -/
theorem mem_zigzagProjectiveTargetShiftHom_iff_isHomogeneous {i j : V} {d : ℤ}
    {φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G j} :
    φ ∈ zigzagProjectiveTargetShiftHom k G i j d ↔
      LinearMap.IsHomogeneous φ (zigzagProjectiveGrade k G i)
        (zigzagProjectiveGrade k G j) (-d) := by
  have hshift : zigzagProjectiveShiftGrade k G j d =
      Graded.shift (zigzagProjectiveGrade k G j) (-d) := by
    funext p
    simp [Graded.shift_apply, sub_eq_add_neg]
  rw [zigzagProjectiveTargetShiftHom, LinearMap.mem_homogeneousSubmodule, hshift,
    LinearMap.isHomogeneous_shift_target_iff]
  simp

/-- The path-length grading restricted to a vertex projective, indexed by natural degrees. -/
private noncomputable def zigzagProjectiveNatGrade (i : V) (d : ℕ) :
    Submodule k (zigzagProjective k G i) :=
  Submodule.comap ((zigzagProjective k G i).restrictScalars k).subtype (zigzagGrade k G d)

@[simp]
private theorem mem_zigzagProjectiveNatGrade_iff {i : V} {d : ℕ}
    {x : zigzagProjective k G i} :
    x ∈ zigzagProjectiveNatGrade k G i d ↔
      (x : nonisolatedZigzagQuotient k G) ∈ zigzagGrade k G d :=
  Iff.rfl

/-- **The homomorphisms `P_i{d} → P_j`**: those `Z`-linear maps `Z e_i → Z e_j` which send a
homogeneous element of degree `n` to a homogeneous element of degree `n + d`. -/
noncomputable def zigzagProjectiveHomOfDegree (i j : V) (d : ℕ) :
    Submodule k
      (zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) :=
  LinearMap.homogeneousSubmodule (R := nonisolatedZigzagQuotient k G) (S := k)
    (zigzagProjectiveNatGrade k G i) (zigzagProjectiveNatGrade k G j) d

/-- **A homomorphism raises degree by `d` exactly when its value at the generator is a degree-`d`
element of the corner.** The generator `e_i` has degree zero, which gives one direction, and
multiplication adds degrees, which gives the other. -/
@[simp]
theorem mem_zigzagProjectiveHomOfDegree_iff {i j : V} {d : ℕ}
    {φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j} :
    φ ∈ zigzagProjectiveHomOfDegree k G i j d ↔
      (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) ∈
        zigzagGradedCorner k G i j d := by
  rw [zigzagProjectiveHomOfDegree, LinearMap.mem_homogeneousSubmodule]
  have hgen : zigzagProjectiveGenerator k G i ∈ zigzagProjectiveNatGrade k G i 0 := by
    rw [mem_zigzagProjectiveNatGrade_iff, coe_zigzagProjectiveGenerator]
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)
  constructor
  · intro hφ
    refine (mem_zigzagGradedCorner_iff k G).2
      ⟨?_, ?_⟩
    · rw [← coe_zigzagProjectiveHomEquivCorner_apply]
      exact (zigzagProjectiveHomEquivCorner k G i j φ).2
    exact (mem_zigzagProjectiveNatGrade_iff k G).1
      (by simpa only [Nat.zero_add] using hφ.map_mem hgen)
  · intro hφ
    rw [LinearMap.isHomogeneous_def]
    intro n x hx
    rw [mem_zigzagProjectiveNatGrade_iff, coe_zigzagProjectiveHom_apply]
    exact mul_mem_zigzagGrade k G ((mem_zigzagProjectiveNatGrade_iff k G).1 hx)
      ((mem_zigzagGradedCorner_iff k G).1 hφ).2

/-- A homomorphism of vertex projectives has signed degree `d` exactly when its value at the
projective generator belongs to the signed degree-`d` corner. -/
theorem isHomogeneous_zigzagProjective_iff {i j : V} {d : ℤ}
    {φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G j} :
    LinearMap.IsHomogeneous φ (zigzagProjectiveGrade k G i)
        (zigzagProjectiveGrade k G j) d ↔
      (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) ∈
        zigzagIntegerGradedCorner k G i j d := by
  have hgen : zigzagProjectiveGenerator k G i ∈ zigzagProjectiveGrade k G i 0 := by
    have hzero : (0 : ℤ) = (0 : ℕ) := rfl
    rw [mem_zigzagProjectiveGrade_iff, hzero, zigzagIntegerGrade_ofNat,
      coe_zigzagProjectiveGenerator]
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)
  constructor
  · intro hφ
    refine (mem_zigzagIntegerGradedCorner_iff k G).2 ⟨?_, ?_⟩
    · rw [← coe_zigzagProjectiveHomEquivCorner_apply]
      exact (zigzagProjectiveHomEquivCorner k G i j φ).2
    · exact (mem_zigzagProjectiveGrade_iff k G).1
        (by simpa only [Int.zero_add] using hφ.map_mem hgen)
  · intro hφ
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    rw [mem_zigzagProjectiveGrade_iff, coe_zigzagProjectiveHom_apply]
    exact mul_mem_zigzagIntegerGrade k G
      ((mem_zigzagProjectiveGrade_iff k G).1 hx)
      ((mem_zigzagIntegerGradedCorner_iff k G).1 hφ).2

/-- **Target-shift membership by evaluation.** A map belongs to `Hom(P_i, P_j{d})` exactly when
its value at the generator belongs to the degree-`(-d)` corner. -/
@[simp]
theorem mem_zigzagProjectiveTargetShiftHom_iff {i j : V} {d : ℤ}
    {φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G j} :
    φ ∈ zigzagProjectiveTargetShiftHom k G i j d ↔
      (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) ∈
        zigzagIntegerGradedCorner k G i j (-d) := by
  rw [mem_zigzagProjectiveTargetShiftHom_iff_isHomogeneous,
    isHomogeneous_zigzagProjective_iff]

/-- The degree-`d` homomorphisms are the preimage of the degree-`d` corner under the ungraded
dictionary. -/
theorem zigzagProjectiveHomOfDegree_eq_comap (i j : V) (d : ℕ) :
    zigzagProjectiveHomOfDegree k G i j d =
      Submodule.comap (zigzagProjectiveHomEquivCorner k G i j).toLinearMap
        (Submodule.comap (zigzagCorner k G i j).subtype (zigzagGradedCorner k G i j d)) := by
  ext φ
  rw [mem_zigzagProjectiveHomOfDegree_iff, Submodule.mem_comap, Submodule.mem_comap]
  simp only [LinearEquiv.coe_coe, Submodule.subtype_apply,
    coe_zigzagProjectiveHomEquivCorner_apply]

/-- **The graded dictionary**: the homomorphisms `P_i{d} → P_j` are the degree-`d` part of the
corner `e_i Z e_j`. -/
noncomputable def zigzagProjectiveHomOfDegreeEquivGradedCorner (i j : V) (d : ℕ) :
    zigzagProjectiveHomOfDegree k G i j d ≃ₗ[k] zigzagGradedCorner k G i j d :=
  (LinearEquiv.ofEq _ _ (zigzagProjectiveHomOfDegree_eq_comap k G i j d)).trans
    (((zigzagProjectiveHomEquivCorner k G i j).ofSubmodules _ _
        (Submodule.map_comap_eq_of_surjective
          (zigzagProjectiveHomEquivCorner k G i j).surjective _)).trans
      (Submodule.comapSubtypeEquivOfLe (zigzagGradedCorner_le_zigzagCorner k G i j d)))

/-- The graded dictionary sends a homogeneous map to its value at the projective generator. -/
@[simp]
theorem coe_zigzagProjectiveHomOfDegreeEquivGradedCorner_apply {i j : V} {d : ℕ}
    (φ : zigzagProjectiveHomOfDegree k G i j d) :
    ((zigzagProjectiveHomOfDegreeEquivGradedCorner k G i j d φ :
        zigzagGradedCorner k G i j d) :
        nonisolatedZigzagQuotient k G) =
      ((φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
        zigzagProjective k G j) (zigzagProjectiveGenerator k G i) :
          nonisolatedZigzagQuotient k G) := by
  -- The standard submodule-restriction equivalences have no coercion theorem; expose their
  -- composite once, then use the public application lemma for the ungraded dictionary.
  change ((zigzagProjectiveHomEquivCorner k G i j
    (φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G j) : zigzagCorner k G i j) :
        nonisolatedZigzagQuotient k G) = _
  rw [coe_zigzagProjectiveHomEquivCorner_apply]

/-- The inverse graded dictionary is right multiplication by the corresponding homogeneous
corner element. -/
@[simp]
theorem coe_zigzagProjectiveHomOfDegreeEquivGradedCorner_symm_apply {i j : V} {d : ℕ}
    (x : zigzagGradedCorner k G i j d) (y : zigzagProjective k G i) :
    ((((zigzagProjectiveHomOfDegreeEquivGradedCorner k G i j d).symm x :
        zigzagProjectiveHomOfDegree k G i j d) :
          zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
            zigzagProjective k G j) y : nonisolatedZigzagQuotient k G) =
      (y : nonisolatedZigzagQuotient k G) *
        (x : nonisolatedZigzagQuotient k G) := by
  -- The inverse composite likewise reduces to the ungraded dictionary after inserting the
  -- explicit inclusion of the graded corner into the corner.
  change (((zigzagProjectiveHomEquivCorner k G i j).symm
    (⟨(x : nonisolatedZigzagQuotient k G),
      (zigzagGradedCorner_le_zigzagCorner k G i j d) x.2⟩ : zigzagCorner k G i j)) y :
        nonisolatedZigzagQuotient k G) = _
  rw [coe_zigzagProjectiveHomEquivCorner_symm_apply]

/-- The target-shifted homomorphisms are the preimage of the signed degree-`(-d)` corner under
the ungraded dictionary. -/
theorem zigzagProjectiveTargetShiftHom_eq_comap (i j : V) (d : ℤ) :
    zigzagProjectiveTargetShiftHom k G i j d =
      Submodule.comap (zigzagProjectiveHomEquivCorner k G i j).toLinearMap
        (Submodule.comap (zigzagCorner k G i j).subtype
          (zigzagIntegerGradedCorner k G i j (-d))) := by
  ext φ
  rw [mem_zigzagProjectiveTargetShiftHom_iff, Submodule.mem_comap, Submodule.mem_comap]
  simp only [LinearEquiv.coe_coe, Submodule.subtype_apply,
    coe_zigzagProjectiveHomEquivCorner_apply]

/-- **The signed target-shift dictionary**: for every `d : ℤ`, the degree-zero maps
`Hom(P_i, P_j{d})` are the degree-`(-d)` part of the corner `e_i Z e_j`. -/
noncomputable def zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner (i j : V) (d : ℤ) :
    zigzagProjectiveTargetShiftHom k G i j d ≃ₗ[k]
      zigzagIntegerGradedCorner k G i j (-d) :=
  (LinearEquiv.ofEq _ _ (zigzagProjectiveTargetShiftHom_eq_comap k G i j d)).trans
    (((zigzagProjectiveHomEquivCorner k G i j).ofSubmodules _ _
        (Submodule.map_comap_eq_of_surjective
          (zigzagProjectiveHomEquivCorner k G i j).surjective _)).trans
      (Submodule.comapSubtypeEquivOfLe fun _ hx =>
        ((mem_zigzagIntegerGradedCorner_iff k G).1 hx).1))

/-- The signed target-shift dictionary sends a homogeneous map to its value at the projective
generator. -/
@[simp]
theorem coe_zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner_apply {i j : V} {d : ℤ}
    (φ : zigzagProjectiveTargetShiftHom k G i j d) :
    ((zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner k G i j d φ :
        zigzagIntegerGradedCorner k G i j (-d)) : nonisolatedZigzagQuotient k G) =
      ((φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
        zigzagProjective k G j) (zigzagProjectiveGenerator k G i) :
          nonisolatedZigzagQuotient k G) := by
  -- The target-shift equivalence uses the same standard submodule restrictions, whose
  -- application is exposed here before invoking the ungraded dictionary lemma.
  change ((zigzagProjectiveHomEquivCorner k G i j
    (φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G j) : zigzagCorner k G i j) :
        nonisolatedZigzagQuotient k G) = _
  rw [coe_zigzagProjectiveHomEquivCorner_apply]

/-- The inverse signed target-shift dictionary is right multiplication by the corresponding
homogeneous corner element. -/
@[simp]
theorem coe_zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner_symm_apply {i j : V} {d : ℤ}
    (x : zigzagIntegerGradedCorner k G i j (-d)) (y : zigzagProjective k G i) :
    ((((zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner k G i j d).symm x :
        zigzagProjectiveTargetShiftHom k G i j d) :
          zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
            zigzagProjective k G j) y : nonisolatedZigzagQuotient k G) =
      (y : nonisolatedZigzagQuotient k G) *
        (x : nonisolatedZigzagQuotient k G) := by
  -- Expose the inverse submodule composite and then rewrite it through the public inverse
  -- application lemma for the ungraded dictionary.
  change (((zigzagProjectiveHomEquivCorner k G i j).symm
    (⟨(x : nonisolatedZigzagQuotient k G),
      ((mem_zigzagIntegerGradedCorner_iff k G).1 x.2).1⟩ : zigzagCorner k G i j)) y :
        nonisolatedZigzagQuotient k G) = _
  rw [coe_zigzagProjectiveHomEquivCorner_symm_apply]

/-- Moving a nonnegative source shift to the target reverses its sign. -/
theorem zigzagProjectiveTargetShiftHom_neg_ofNat (i j : V) (d : ℕ) :
    zigzagProjectiveTargetShiftHom k G i j (-(d : ℤ)) =
      zigzagProjectiveHomOfDegree k G i j d := by
  ext φ
  rw [mem_zigzagProjectiveTargetShiftHom_iff, mem_zigzagProjectiveHomOfDegree_iff]
  simp

/-- Positive target shifts carry no homogeneous maps between the nonnegatively graded vertex
projectives. -/
theorem zigzagProjectiveTargetShiftHom_eq_bot_of_pos (i j : V) {d : ℤ} (hd : 0 < d) :
    zigzagProjectiveTargetShiftHom k G i j d = ⊥ := by
  refine le_antisymm (fun φ hφ => ?_) bot_le
  rw [Submodule.mem_bot]
  have hgen :
      (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) = 0 := by
    have h := (mem_zigzagProjectiveTargetShiftHom_iff k G).1 hφ
    rw [zigzagIntegerGradedCorner_eq_bot_of_neg k G i j (neg_neg_of_pos hd),
      Submodule.mem_bot] at h
    exact h
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_zigzagProjectiveHom_apply, hgen, mul_zero]
  exact Submodule.coe_zero.symm

/-- The dimension of a target-shifted Hom space is the dimension of the corresponding signed
corner. -/
theorem finrank_zigzagProjectiveTargetShiftHom (i j : V) (d : ℤ) :
    Module.finrank k (zigzagProjectiveTargetShiftHom k G i j d) =
      Module.finrank k (zigzagIntegerGradedCorner k G i j (-d)) :=
  (zigzagProjectiveTargetShiftHomEquivIntegerGradedCorner k G i j d).finrank_eq

/-- The dimension of a homogeneous homomorphism space is the dimension of the corresponding graded
corner. -/
theorem finrank_zigzagProjectiveHomOfDegree (i j : V) (d : ℕ) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i j d) =
      Module.finrank k (zigzagGradedCorner k G i j d) :=
  (zigzagProjectiveHomOfDegreeEquivGradedCorner k G i j d).finrank_eq

/-- Right multiplication by a degree-`d` element of the corner raises degree by `d`. -/
theorem zigzagProjectiveHomEquivCorner_symm_apply_mem {i j : V} {d : ℕ}
    (x : zigzagCorner k G i j) (hx : (x : nonisolatedZigzagQuotient k G) ∈ zigzagGrade k G d) :
    (zigzagProjectiveHomEquivCorner k G i j).symm x ∈ zigzagProjectiveHomOfDegree k G i j d := by
  rw [mem_zigzagProjectiveHomOfDegree_iff]
  refine (mem_zigzagGradedCorner_iff k G).2 ⟨?_, ?_⟩ <;>
    rw [← coe_zigzagProjectiveHomEquivCorner_apply, LinearEquiv.apply_symm_apply]
  · exact x.2
  · exact hx

/-- **The identity of a vertex projective raises degree by zero.** -/
theorem id_mem_zigzagProjectiveHomOfDegree_zero (i : V) :
    (LinearMap.id : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
      zigzagProjective k G i) ∈ zigzagProjectiveHomOfDegree k G i i 0 := by
  rw [zigzagProjectiveHomOfDegree, LinearMap.mem_homogeneousSubmodule]
  exact LinearMap.isHomogeneous_id (zigzagProjectiveNatGrade k G i)

/-! ### The homogeneous homomorphism spaces -/

/-- **No homomorphism of vertex projectives raises degree by three or more**, since the zigzag
quotient has nothing in those degrees. -/
theorem zigzagProjectiveHomOfDegree_eq_bot_of_three_le (i j : V) {d : ℕ} (hd : 3 ≤ d) :
    zigzagProjectiveHomOfDegree k G i j d = ⊥ := by
  refine le_antisymm (fun φ hφ => ?_) bot_le
  rw [Submodule.mem_bot]
  have hgen : (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) = 0 := by
    have h := ((mem_zigzagGradedCorner_iff k G).1
      ((mem_zigzagProjectiveHomOfDegree_iff k G).1 hφ)).2
    rwa [zigzagGrade_eq_bot_of_three_le k G hd, Submodule.mem_bot] at h
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_zigzagProjectiveHom_apply, hgen, mul_zero]
  exact Submodule.coe_zero.symm

/-- **The degree-zero endomorphism space of a vertex projective is one-dimensional.**  It
contains the identity, by `TauCeti.id_mem_zigzagProjectiveHomOfDegree_zero`. -/
theorem finrank_zigzagProjectiveHomOfDegree_zero_self (i : V) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i i 0) = 1 := by
  rw [finrank_zigzagProjectiveHomOfDegree, finrank_zigzagGradedCorner_zero_self]

/-- There is no nonzero degree-zero homomorphism between the vertex projectives at two distinct
vertices. -/
theorem finrank_zigzagProjectiveHomOfDegree_zero_of_ne {i j : V} (h : i ≠ j) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i j 0) = 0 := by
  rw [finrank_zigzagProjectiveHomOfDegree, finrank_zigzagGradedCorner_zero_of_ne k G h]

/-- **An edge gives a one-dimensional space of degree-one homomorphisms.**  The corner it comes
from is spanned by the arrow crossing the edge
(`TauCeti.zigzagGradedCorner_one_eq_span_of_adj`), which
`TauCeti.coe_zigzagProjectiveHomEquivCorner_symm_apply` reads as right multiplication by that
arrow. -/
theorem finrank_zigzagProjectiveHomOfDegree_one_of_adj {i j : V} (h : G.Adj j i) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i j 1) = 1 := by
  rw [finrank_zigzagProjectiveHomOfDegree, finrank_zigzagGradedCorner_one_of_adj k G h]

/-- Nonadjacent vertices carry no degree-one homomorphism of vertex projectives. -/
theorem finrank_zigzagProjectiveHomOfDegree_one_of_not_adj {i j : V} (h : ¬G.Adj j i) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i j 1) = 0 := by
  rw [finrank_zigzagProjectiveHomOfDegree, finrank_zigzagGradedCorner_one_of_not_adj k G h]

/-- **The volume class gives a one-dimensional space of degree-two endomorphisms** of a vertex
projective at a vertex with a neighbour: the corner it comes from is spanned by that class, by
`TauCeti.zigzagGradedCorner_two_self_eq_span`. -/
theorem finrank_zigzagProjectiveHomOfDegree_two_self_of_adj {i j : V} (h : G.Adj i j) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i i 2) = 1 := by
  rw [finrank_zigzagProjectiveHomOfDegree, finrank_zigzagGradedCorner_two_self_of_adj k G h]

/-- Distinct vertices carry no degree-two homomorphism of vertex projectives. -/
theorem finrank_zigzagProjectiveHomOfDegree_two_of_ne {i j : V} (h : i ≠ j) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i j 2) = 0 := by
  rw [finrank_zigzagProjectiveHomOfDegree, finrank_zigzagGradedCorner_two_of_ne k G h]

/-! ### The graded Cartan matrix as a matrix of homomorphism dimensions -/

/-- **The graded Cartan entry is the graded dimension of the homomorphism spaces of the vertex
projectives**, `∑_d dim_k Hom(P_i{d}, P_j) qᵈ`.  Together with
`TauCeti.zigzagGradedCartanMatrix_eq` this is the roadmap's graded Cartan formula read on the
projectives themselves, and by
`TauCeti.zigzagProjectiveHomOfDegree_eq_bot_of_three_le` the truncation of the sum below degree
three discards only zeros. -/
theorem zigzagGradedCartanMatrix_eq_sum_finrank_zigzagProjectiveHomOfDegree (i j : V) :
    zigzagGradedCartanMatrix k G i j =
      ∑ n ∈ Finset.range 3,
        (Module.finrank k (zigzagProjectiveHomOfDegree k G i j n) : ℤ[X]) * X ^ n := by
  rw [zigzagGradedCartanMatrix_apply_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, finrank_zigzagProjectiveHomOfDegree,
    finrank_zigzagProjectiveHomOfDegree, finrank_zigzagProjectiveHomOfDegree, pow_zero, mul_one,
    pow_one]

end TauCeti
