/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Datum

/-!
# The diagonal root datum and the adjoint roots of the general linear group

For `GL_n` with its diagonal split torus, the coordinate root datum has roots `e_i - e_j`,
indexed by ordered pairs `i ≠ j`. Independently, the nontrivial weights of the restricted
adjoint representation have been classified as the same characters. This file identifies the
two constructions exactly.

Thus the roots packaged by `GeneralLinear.diagonalRootDatum` are neither merely an abstract
coordinate model nor just a subset of the adjoint weights: their range is the complete set
`Derivation.nontrivialAdjointWeights` for the diagonal-torus morphism. The induced equivalence
records the canonical root indexing. The existing adjoint classification then identifies each
root space with the line spanned by the corresponding matrix unit `E_ij`.

This is a worked-example bridge between two concrete constructions. It does not assert that the
diagonal torus is maximal or construct the general root datum of a reductive pair.

## Main declarations

* `TauCeti.GeneralLinear.mem_nontrivialAdjointWeights_iff_exists_diagonalRoot`: a character is a
  nontrivial adjoint weight exactly when it is a root of the diagonal root datum.
* `TauCeti.GeneralLinear.range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights`: the
  packaged root set equals the adjoint root set.
* `TauCeti.GeneralLinear.diagonalRootIndexEquivNontrivialAdjointWeights`: the canonical
  equivalence from root indices to nontrivial adjoint weights.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This supplies the root-set computation for the standard split `GL_n` worked example in Layer 7,
"Root datum of `(G, T)`", of the ReductiveGroups roadmap. Proving maximality of the diagonal torus,
constructing root data for arbitrary split reductive pairs, and identifying their Weyl groups
remain separate milestones.
-/

public section

open Function Set

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {k : Type u} [Field k] {n : ℕ}

/-- A character of the diagonal torus is a nontrivial adjoint weight exactly when it is the
multiplicative form of a root in `diagonalRootDatum`. -/
theorem mem_nontrivialAdjointWeights_iff_exists_diagonalRoot
    (alpha : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) :
    alpha ∈ Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom ↔
      ∃ p : DiagonalRootIndex n,
        alpha = Multiplicative.ofAdd
          ((diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p) := by
  rw [mem_nontrivialAdjointWeights_diagonalTorus_iff]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    let p : DiagonalRootIndex n :=
      ⟨(ULift.up i, ULift.up j), fun h ↦ hij (congrArg ULift.down h)⟩
    refine ⟨p, ?_⟩
    rw [diagonalRootDatum_root, ofAdd_diagonalRoot]
  · rintro ⟨p, rfl⟩
    refine ⟨p.1.1.down, p.1.2.down, ?_, ?_⟩
    · intro h
      exact p.2 (congrArg ULift.up h)
    · rw [diagonalRootDatum_root, ofAdd_diagonalRoot]

/-- The multiplicative roots of the diagonal coordinate root datum are exactly the nontrivial
adjoint weights of `GL_n` relative to its diagonal torus. -/
theorem range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights :
    Set.range (fun p : DiagonalRootIndex n ↦
        Multiplicative.ofAdd
          ((diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p)) =
      Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom := by
  ext alpha
  rw [Set.mem_range, mem_nontrivialAdjointWeights_iff_exists_diagonalRoot]
  exact exists_congr fun p ↦ eq_comm

/-- The root indices of the diagonal coordinate root datum are canonically equivalent to the
nontrivial adjoint weights of `GL_n` relative to its diagonal torus. -/
noncomputable def diagonalRootIndexEquivNontrivialAdjointWeights :
    DiagonalRootIndex n ≃
      {alpha // alpha ∈ Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom} :=
  Equiv.ofBijective
    (fun p ↦ ⟨Multiplicative.ofAdd
        ((diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p),
      ofAdd_root_mem_nontrivialAdjointWeights (k := k) p⟩)
    ⟨fun p q h ↦ (diagonalRootDatum n).root.injective
        (Multiplicative.ofAdd.injective (congrArg Subtype.val h)),
      fun ⟨alpha, halpha⟩ ↦ by
        obtain ⟨p, hp⟩ :=
          (mem_nontrivialAdjointWeights_iff_exists_diagonalRoot alpha).mp halpha
        exact ⟨p, Subtype.ext hp.symm⟩⟩

/-- The root-index equivalence sends an index to the multiplicative form of its packaged root. -/
@[simp]
theorem diagonalRootIndexEquivNontrivialAdjointWeights_apply (p : DiagonalRootIndex n) :
    (diagonalRootIndexEquivNontrivialAdjointWeights (k := k) p :
      Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) =
      Multiplicative.ofAdd
        ((diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p) :=
  (rfl)

end

end TauCeti.GeneralLinear
