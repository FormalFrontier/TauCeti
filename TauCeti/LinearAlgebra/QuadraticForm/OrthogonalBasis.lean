/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Radical
-- Non-public: the list reformulation only uses `List.ofFn` inside its proof, and the passage
-- between the vanishing of the associated bilinear form and orthogonality for the quadratic form
-- is likewise a proof step.
import Mathlib.Data.List.OfFn

/-!
# An anisotropic orthogonal basis of a nondegenerate quadratic form

Over a field in which `2` is invertible, every symmetric bilinear form on a finite-dimensional
space admits an orthogonal basis (`LinearMap.BilinForm.exists_orthogonal_basis`). This file records
the refinement that nondegeneracy adds: **no member of such a basis is isotropic**. Indeed a basis
vector orthogonal to all the others and to itself is orthogonal to everything, so it lies in the
radical; nondegeneracy makes it zero, which a basis vector is not.

The refinement is what turns an orthogonal basis into a *usable* one: the volume element
`v₁ ⋯ vₙ` of an orthogonal family in a Clifford algebra squares to the scalar
`(-1) ^ (n.choose 2) ∏ᵢ Q vᵢ` (`CliffordAlgebra.prod_map_ι_sq_scalar`), which is invertible exactly
when no `Q vᵢ` vanishes. The second statement below packages the basis as the spanning list of
pairwise orthogonal vectors that the Clifford-algebra API asks for.

## Main results

* `QuadraticMap.Nondegenerate.exists_orthogonal_basis`: a nondegenerate quadratic form on a
  finite-dimensional space has an orthogonal basis none of whose members is isotropic.
* `QuadraticMap.Nondegenerate.exists_list_pairwise_isOrtho`: the same basis read as a spanning list
  of pairwise orthogonal, non-isotropic vectors whose length is the dimension.
-/

public section

namespace QuadraticMap

open Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Invertible (2 : F)] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- **A nondegenerate quadratic form has an anisotropic orthogonal basis.** Mathlib's
`LinearMap.BilinForm.exists_orthogonal_basis` supplies the orthogonality, and
`LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft` rules out an isotropic member: such a
member would be orthogonal to the whole space. -/
theorem Nondegenerate.exists_orthogonal_basis (hQ : Q.Nondegenerate) :
    ∃ b : Basis (Fin (finrank F V)) F V,
      (∀ i j, i ≠ j → Q.IsOrtho (b i) (b j)) ∧ ∀ i, Q (b i) ≠ 0 := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (B := QuadraticMap.associated Q) (QuadraticForm.associated_isSymm F Q)
  refine ⟨b, fun i j hij => associated_isOrtho.mp (hb hij), fun i => ?_⟩
  -- Read the statement through the associated bilinear form, which is nondegenerate too.
  have hb' := hb.not_isOrtho_basis_self_of_separatingLeft
    (nondegenerate_associated_iff.mpr hQ).1 i
  rwa [associated_eq_self_apply F Q] at hb'

/-- **A nondegenerate quadratic form has an anisotropic orthogonal spanning list.** This is
`QuadraticMap.Nondegenerate.exists_orthogonal_basis` read as a list, the shape in which the Clifford
volume element of `CliffordAlgebra.prod_map_ι_sq_scalar` consumes an orthogonal family. -/
theorem Nondegenerate.exists_list_pairwise_isOrtho (hQ : Q.Nondegenerate) :
    ∃ l : List V, l.Pairwise Q.IsOrtho ∧ l.length = finrank F V ∧
      Submodule.span F {x : V | x ∈ l} = ⊤ ∧ ∀ v ∈ l, Q v ≠ 0 := by
  obtain ⟨b, hortho, haniso⟩ := hQ.exists_orthogonal_basis
  refine ⟨List.ofFn b, ?_, List.length_ofFn, ?_, ?_⟩
  · exact List.pairwise_ofFn.mpr fun i j hij => hortho i j (Fin.ne_of_lt hij)
  · have hset : {x : V | x ∈ List.ofFn b} = Set.range b := by
      ext x
      simp
    rw [hset, b.span_eq]
  · rintro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact haniso i

end QuadraticMap
