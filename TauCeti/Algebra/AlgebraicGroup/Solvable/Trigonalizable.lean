/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Triangular
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

/-!
# Trigonalizing the representations of a commutative affine group

Let `H` be a reduced finite-type commutative Hopf algebra over an algebraically closed field `k`.
If the points of `H` act on a finite-dimensional comodule by pairwise-commuting operators, that
comodule has a nonzero weight vector: a joint eigenvector of the commuting operators spans a
point-stable line, and point separation promotes that line to a subcomodule, whose weight is
automatically a character.

Feeding this into the flag induction of
`TauCeti.Algebra.Coalgebra.Comodule.Flag.Triangular` trigonalizes every finite-dimensional
representation of a commutative affine group: over a cocommutative `H` the convolution group of
points is commutative, so the hypothesis holds for every comodule at once.

This is the base case of the Lie--Kolchin induction, which reduces a connected solvable group to
its commutative quotient by the derived subgroup. The induction step, which is where connectedness
enters, is not proved here.

## Main declarations

* `TauCeti.Comodule.hasNonzeroWeightVector_of_pairwise_commute`: commuting point actions produce a
  weight vector.
* `TauCeti.Comodule.hasNonzeroWeightVector_of_isCocomm`: every nonzero finite-dimensional
  representation of a commutative affine group has a weight vector.
* `TauCeti.Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_isCocomm`: every
  finite-dimensional representation of a commutative affine group has an upper-triangular basis
  with group-like diagonal.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1, whose commutative case is proved here.
* A. Borel, *Linear Algebraic Groups*, §10.5.

This advances the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

open WithConv

universe u v w

noncomputable section

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- If the base-valued points of a reduced finite-type commutative Hopf algebra over an
algebraically closed field act on a nonzero finite-dimensional comodule by pairwise-commuting
operators, then that comodule has a nonzero weight vector. -/
theorem hasNonzeroWeightVector_of_pairwise_commute
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    [FiniteDimensional k M] [Nontrivial M]
    (hcomm : Pairwise fun g h : WithConv (H →ₐ[k] k) ↦
      Commute (basePointsRepresentation (R := k) (H := H) M g)
        (basePointsRepresentation (R := k) (H := H) M h)) :
    HasNonzeroWeightVector k H M := by
  obtain ⟨chi, p, hrank, hact⟩ :=
    TauCeti.exists_unitHom_submodule_finrank_eq_one_of_pairwise_commute_of_isAlgClosed
      (basePointsRepresentation (R := k) (H := H) M) hcomm
  have hbot : p ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrank
    exact absurd hrank (by norm_num)
  obtain ⟨v, hvp, hv⟩ := p.ne_bot_iff.mp hbot
  have hspan : (k ∙ v) = p :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v p).mpr hvp)
      ((finrank_span_singleton hv).trans hrank.symm)
  have hstable : ∀ (g : H →ₐ[k] k) {m : M}, m ∈ p →
      Comodule.endOfPoint M g ((1 : k) ⊗ₜ[k] m) ∈ p.baseChange k := by
    intro g m hm
    have haction := endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation
      (R := k) (H := H) (M := M) (toConv g) m
    rw [ofConv_toConv] at haction
    rw [endOfPoint_tmul, one_smul, haction]
    exact Submodule.tmul_mem_baseChange_of_mem _ (hact (toConv g) m hm ▸ p.smul_mem _ hm)
  exact hasNonzeroWeightVector_of_toSubmodule_eq_span
    (Subcomodule.ofEndOfPointStable (K := k) p hstable) hv
    ((Subcomodule.ofEndOfPointStable_toSubmodule (K := k) p hstable).trans hspan.symm)

/-- Every nonzero finite-dimensional representation of a commutative affine group, reduced and of
finite type over an algebraically closed field, has a nonzero weight vector. -/
theorem hasNonzeroWeightVector_of_isCocomm
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] [Coalgebra.IsCocomm k H]
    [FiniteDimensional k M] [Nontrivial M] :
    HasNonzeroWeightVector k H M :=
  hasNonzeroWeightVector_of_pairwise_commute fun g h _ ↦
    (Commute.all g h).map (basePointsRepresentation (R := k) (H := H) M)

/-- **Every finite-dimensional representation of a commutative affine group is trigonalizable.**
For a reduced finite-type cocommutative Hopf algebra over an algebraically closed field, every
finite-dimensional comodule has a basis whose coefficient matrix is upper triangular with
group-like diagonal entries: the group acts by upper-triangular matrices whose diagonal entries
are characters. -/
theorem exists_basis_coefficientMatrix_isUpperTriangular_of_isCocomm
    [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] [Coalgebra.IsCocomm k H]
    [FiniteDimensional k M] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M),
      (coefficientMatrix (C := H) b).IsUpperTriangular ∧
        ∀ i, IsGroupLikeElem k (coefficientMatrix (C := H) b i i) :=
  exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors
    fun _ _ _ _ _ _ ↦ hasNonzeroWeightVector_of_isCocomm

end

end TauCeti.Comodule
