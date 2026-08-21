/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PositiveDefinite
public import TauCeti.RepresentationTheory.Compact.Unitarizable
public import TauCeti.RepresentationTheory.Continuous.Representative

/-!
# The unitary model of a finite-dimensional representation of a compact group

Weyl's unitarian trick, in `TauCeti/RepresentationTheory/Compact/Unitarizable.lean`, averages the
inner product of a continuous representation `π` of a compact group over Haar measure and records
the averaged form through its Gram operator `S`, a positive-definite self-adjoint operator with
`(π g)† ∘ S ∘ (π g) = S`. That is an invariant form, not yet a unitary representation: Lean fixes
one `InnerProductSpace` structure on the carrier, and `π` is in general not unitary for it.

This file closes the gap in finite dimensions. Changing coordinates by the automorphism `A` that
standardizes the invariant form
(`TauCeti.exists_continuousLinearEquiv_inner_map_map`, morally `A = S ^ (-1 / 2)`) conjugates `π`
into a representation that *is* unitary for the given inner product:

`TauCeti.ContRepresentation.exists_isUnitary_congr` produces `e : V ≃L[𝕜] V` with
`IsUnitary (congr e π)`.

What this buys is a replacement of `π` by an equivalent representation, not by `π` itself, so a
property may be proved for unitary representations alone exactly when it is invariant under
conjugation by a continuous linear automorphism. The two consequences recorded here are the form
that fact is consumed in, and both are of that kind: a matrix coefficient of an arbitrary
finite-dimensional continuous representation is a matrix coefficient of a unitary one, and hence
the representative ring `𝓡(G)` is spanned by the matrix coefficients of the **unitary**
finite-dimensional continuous representations alone.

## Main statements

* `TauCeti.ContRepresentation.exists_isUnitary_congr`: a finite-dimensional continuous
  representation of a compact group is conjugate to a unitary one.
* `TauCeti.ContRepresentation.exists_isUnitary_matrixCoeff_eq`: its matrix coefficients are matrix
  coefficients of a unitary representation.
* `TauCeti.isRepresentative_iff_exists_isUnitary`: a representative function is a matrix
  coefficient of a unitary representation on a standard model.

## Implementation notes

The conjugating automorphism is not asked to be canonical:
`TauCeti.exists_continuousLinearEquiv_inner_map_map` chooses an eigenbasis of the Gram operator,
and only its existence is exported. Nothing downstream needs more, since the unitary structure it
produces is unique up to a unitary equivalence anyway.

Finite dimensionality enters only through that standardization, which is proved by the spectral
theorem; the Gram operator itself is built for an arbitrary Hilbert-space carrier.

This finishes Layer 1 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
whose statement of the unitarian trick asks that "downstream results may assume `IsUnitary` without
loss of generality". The Layer 5 (Peter-Weyl) completeness argument is the intended consumer: the
matrix coefficients that have to be expanded in the coefficients of a family of irreducible
*unitary* representations are, a priori, coefficients of arbitrary ones. The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory RCLike
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section Unitarization

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceUnitaryModel : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

/-- **A finite-dimensional continuous representation of a compact group is conjugate to a unitary
one.** There is a continuous linear automorphism `e` of the carrier for which the transported
representation `TauCeti.ContRepresentation.congr e π` preserves the inner product.

This is the unitarian trick in its usable form. Haar averaging supplies the invariant
positive-definite form `⟪S ·, ·⟫`; the automorphism `A` carrying the standard inner product to
that form (`TauCeti.exists_continuousLinearEquiv_inner_map_map`) conjugates the invariance of the
form into unitarity of `A⁻¹ ∘ π · ∘ A`. -/
theorem exists_isUnitary_congr (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ∃ e : V ≃L[𝕜] V, IsUnitary (congr e π) := by
  obtain ⟨A, hA⟩ := exists_continuousLinearEquiv_inner_map_map (gramOperator π hπ)
    (isSymmetric_gramOperator π hπ) fun _ hv ↦ re_inner_gramOperator_self_pos π hπ hv
  -- The same standardization with the Gram operator on the second argument, which is the side
  -- `inner_gramOperator_map_map` states invariance of the averaged form on.
  have hA' : ∀ x y : V, ⟪A x, gramOperator π hπ (A y)⟫_𝕜 = ⟪x, y⟫_𝕜 := fun x y ↦ by
    rw [← inner_conj_symm, hA, inner_conj_symm]
  have hunitary : ∀ (g : G) (x y : V), ⟪congr A.symm π g x, congr A.symm π g y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
    intro g x y
    rw [congr_apply, congr_apply, ContinuousLinearEquiv.symm_symm,
      ← hA' (A.symm (π g (A x))) (A.symm (π g (A y))), ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply, inner_gramOperator_map_map, hA']
  exact ⟨A.symm, (isUnitary_iff_norm_map _).mpr fun g ↦
    (LinearMap.norm_map_iff_inner_map_map _).mpr (hunitary g)⟩

/-- **A matrix coefficient of a finite-dimensional continuous representation of a compact group is
a matrix coefficient of a unitary one**, on the same carrier and at suitably moved vectors.

Matrix coefficients depend only on the equivalence class of a representation
(`TauCeti.ContRepresentation.matrixCoeff_congr_adjoint`), so the conjugate unitary model produced
by `TauCeti.ContRepresentation.exists_isUnitary_congr` produces every matrix coefficient of the
original. -/
theorem exists_isUnitary_matrixCoeff_eq (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) :
    ∃ (ρ : ContRepresentation 𝕜 G V) (hρ : Continuous ρ), IsUnitary ρ ∧
      ∃ v' w' : V, matrixCoeff π hπ v w = matrixCoeff ρ hρ v' w' :=
  let ⟨e, he⟩ := exists_isUnitary_congr π hπ
  ⟨congr e π, continuous_congr e hπ, he, e v,
    ContinuousLinearMap.adjoint (e.symm : V →L[𝕜] V) w, (matrixCoeff_congr_adjoint e hπ v w).symm⟩

end Unitarization

end ContRepresentation

section Representative

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **The representative functions of a compact group are the matrix coefficients of its unitary
finite-dimensional continuous representations.** Restricting the representations allowed in the
definition of `TauCeti.IsRepresentative` to the unitary ones changes nothing.

The forward direction is unitarization; the reverse is the definition. Consequently the
representative ring `𝓡(G)`, whose uniform density in `C(G, 𝕜)` is the analytic core of the
Peter-Weyl theorem, is spanned by the matrix coefficients of unitary representations, which are
the ones Schur orthogonality applies to. -/
theorem isRepresentative_iff_exists_isUnitary {f : C(G, 𝕜)} :
    IsRepresentative f ↔ ∃ (n : ℕ) (π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin n)))
      (hπ : Continuous π), ContRepresentation.IsUnitary π ∧
        ∃ v w : EuclideanSpace 𝕜 (Fin n), f = ContRepresentation.matrixCoeff π hπ v w := by
  rw [isRepresentative_iff]
  constructor
  · rintro ⟨n, π, hπ, v, w, rfl⟩
    obtain ⟨ρ, hρ, hunitary, v', w', hvw⟩ :=
      ContRepresentation.exists_isUnitary_matrixCoeff_eq π hπ v w
    exact ⟨n, ρ, hρ, hunitary, v', w', hvw⟩
  · rintro ⟨n, π, hπ, -, v, w, rfl⟩
    exact ⟨n, π, hπ, v, w, rfl⟩

end Representative

end TauCeti
