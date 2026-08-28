/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix

/-!
# The graded homomorphism spaces of the zigzag vertex projectives

For a finite simple graph without isolated vertices, `TauCeti.zigzagProjective` is the
indecomposable left projective `P_i = Z e_i` of the zigzag relation quotient and
`TauCeti.zigzagCorner` is the corner `e_i Z e_j`.  This file supplies the dictionary those two
files leave open, namely

`Hom_Z(P_i, P_j) ≅ e_i Z e_j`,

together with its refinement by the path-length grading: the homomorphisms which raise degree by
`d` — that is, the degree-zero homomorphisms `P_i{d} → P_j` in the graded module category — are
the degree-`d` part of the corner.

Combining the two identifications with the entrywise computation of the graded corners in
`TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix` turns the graded Cartan matrix into what
the roadmap asks it to be, a matrix of graded dimensions of homomorphism spaces,

`C_G(q)_{i,j} = ∑_d dim_k Hom(P_i{d}, P_j) q^d = (1 + q²) δ_{i,j} + q A_{i,j}`.

## Main definitions

* `TauCeti.zigzagProjectiveHomEquivCorner`: **the dictionary `Hom_Z(P_i, P_j) ≃ₗ[k] e_i Z e_j`.**
* `TauCeti.zigzagProjectiveHomOfDegree`: the homomorphisms `P_i → P_j` raising path degree by
  `d`, that is `Hom(P_i{d}, P_j)`.

## Main results

* `TauCeti.zigzagGradedProjectiveHomEquiv`: **the graded dictionary**
  `Hom(P_i{d}, P_j) ≃ₗ[k] (e_i Z e_j)_d`.
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

`Hom(P_i{d}, P_j)` is defined by the intrinsic degree-raising condition, quantified over every
homogeneous element of `P_i`, rather than as the preimage of the graded corner; the comparison
`TauCeti.mem_zigzagProjectiveHomOfDegree_iff` with the value at the generator is a theorem.  Only
the internal shift `{d}` of the source appears, so no graded module category is set up here: a
`k`-submodule of the ungraded homomorphism space carries all the information the graded Cartan
matrix consumes.

## References

This is the homomorphism half of Layer 3 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which
asks for `P_i` together with "all homogeneous `Hom(P_i,P_j{d})` spaces"; by its pinned shift
convention, these are equivalently indexed as `Hom(P_i{d},P_j)`.  See
Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver Polynomial

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### The ungraded dictionary -/

/-- **The homomorphisms `Z e_i → Z e_j` are the corner `e_i Z e_j`**, by evaluation at the
generator `e_i`.  This is the dictionary through which the corners computed by
`TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix` are homomorphism spaces of the vertex
projectives. -/
noncomputable def zigzagProjectiveHomEquivCorner (i j : V) :
    (zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) ≃ₗ[k]
      zigzagCorner k G i j :=
  spanSingletonHomEquivCorner (zigzagMk_vertexIdempotent_mul_self k G i)
    (zigzagMk_vertexIdempotent_mul_self k G j)

@[simp]
theorem coe_zigzagProjectiveHomEquivCorner_apply {i j : V}
    (φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) :
    ((zigzagProjectiveHomEquivCorner k G i j φ : zigzagCorner k G i j) :
        nonisolatedZigzagQuotient k G) =
      (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) :=
  (rfl)

@[simp]
theorem coe_zigzagProjectiveHomEquivCorner_symm_apply {i j : V} (x : zigzagCorner k G i j)
    (y : zigzagProjective k G i) :
    (((zigzagProjectiveHomEquivCorner k G i j).symm x) y : nonisolatedZigzagQuotient k G) =
      (y : nonisolatedZigzagQuotient k G) * (x : nonisolatedZigzagQuotient k G) :=
  (rfl)

/-- A homomorphism `Z e_i → Z e_j` is right multiplication by its value at the generator. -/
theorem coe_zigzagProjectiveHom_apply {i j : V}
    (φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j)
    (x : zigzagProjective k G i) :
    (φ x : nonisolatedZigzagQuotient k G) =
      (x : nonisolatedZigzagQuotient k G) *
        (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) :=
  coe_apply_eq_mul_apply_generator (zigzagMk_vertexIdempotent_mul_self k G i) φ x

/-! ### The graded dictionary -/

/-- **The homomorphisms `P_i{d} → P_j`**: those `Z`-linear maps `Z e_i → Z e_j` which send a
homogeneous element of degree `n` to a homogeneous element of degree `n + d`. -/
def zigzagProjectiveHomOfDegree (i j : V) (d : ℕ) :
    Submodule k
      (zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) where
  carrier := {φ | ∀ (n : ℕ) (x : zigzagProjective k G i),
    (x : nonisolatedZigzagQuotient k G) ∈ zigzagGrade k G n →
      (φ x : nonisolatedZigzagQuotient k G) ∈ zigzagGrade k G (n + d)}
  add_mem' hφ hψ n x hx := Submodule.add_mem _ (hφ n x hx) (hψ n x hx)
  zero_mem' _ _ _ := Submodule.zero_mem _
  smul_mem' c _ hφ n x hx := Submodule.smul_mem _ c (hφ n x hx)

/-- **A homomorphism raises degree by `d` exactly when its value at the generator is a degree-`d`
element of the corner.** The generator `e_i` has degree zero, which gives one direction, and
multiplication adds degrees, which gives the other. -/
theorem mem_zigzagProjectiveHomOfDegree_iff {i j : V} {d : ℕ}
    {φ : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j} :
    φ ∈ zigzagProjectiveHomOfDegree k G i j d ↔
      (φ (zigzagProjectiveGenerator k G i) : nonisolatedZigzagQuotient k G) ∈
        zigzagGradedCorner k G i j d := by
  have hgen : (zigzagProjectiveGenerator k G i : nonisolatedZigzagQuotient k G) ∈
      zigzagGrade k G 0 := by
    rw [coe_zigzagProjectiveGenerator]
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)
  constructor
  · intro hφ
    refine (mem_zigzagGradedCorner_iff k G).2
      ⟨apply_generator_mem_cornerSubmodule (zigzagMk_vertexIdempotent_mul_self k G i)
        (zigzagMk_vertexIdempotent_mul_self k G j) φ, ?_⟩
    simpa only [Nat.zero_add] using hφ 0 (zigzagProjectiveGenerator k G i) hgen
  · intro hφ n x hx
    rw [coe_zigzagProjectiveHom_apply]
    exact mul_mem_zigzagGrade k G hx ((mem_zigzagGradedCorner_iff k G).1 hφ).2

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
noncomputable def zigzagGradedProjectiveHomEquiv (i j : V) (d : ℕ) :
    zigzagProjectiveHomOfDegree k G i j d ≃ₗ[k] zigzagGradedCorner k G i j d :=
  (LinearEquiv.ofEq _ _ (zigzagProjectiveHomOfDegree_eq_comap k G i j d)).trans
    (((zigzagProjectiveHomEquivCorner k G i j).ofSubmodules _ _
        (Submodule.map_comap_eq_of_surjective
          (zigzagProjectiveHomEquivCorner k G i j).surjective _)).trans
      (Submodule.comapSubtypeEquivOfLe (zigzagGradedCorner_le_zigzagCorner k G i j d)))

/-- The dimension of a homogeneous homomorphism space is the dimension of the corresponding graded
corner. -/
theorem finrank_zigzagProjectiveHomOfDegree (i j : V) (d : ℕ) :
    Module.finrank k (zigzagProjectiveHomOfDegree k G i j d) =
      Module.finrank k (zigzagGradedCorner k G i j d) :=
  (zigzagGradedProjectiveHomEquiv k G i j d).finrank_eq

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
      zigzagProjective k G i) ∈ zigzagProjectiveHomOfDegree k G i i 0 :=
  fun n x hx => by simpa only [LinearMap.id_coe, id_eq, Nat.add_zero] using hx

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
