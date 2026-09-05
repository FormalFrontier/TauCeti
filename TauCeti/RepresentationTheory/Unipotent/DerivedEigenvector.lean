/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Kolchin
import Mathlib.RepresentationTheory.Invariants

/-!
# Eigenvectors modulo a unipotent normal subgroup

Let `N` be a normal subgroup containing the commutator subgroup of `G`, and let `G` act on a
nonzero finite-dimensional vector space over an algebraically closed field. If every element of
`N` acts unipotently, then the representation has a common eigenvector.

Kolchin first supplies a nonzero `N`-fixed vector. The whole group preserves the space of
`N`-fixed vectors, and its action there factors through the commutative quotient `G/N`.
Commuting operators over an algebraically closed field have a common eigenvector, whose
eigenvalues assemble into a unit-valued character of `G`.

## Main declaration

* `Representation.exists_unitHom_jointEigenvector_of_commutator_le_of_isUnipotent`: a unipotent
  subgroup containing every commutator forces a common eigenvector.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Theorem 6.3.1.

This supplies the abstract reduction used in Lie--Kolchin arguments.
-/

public section

namespace TauCeti

universe u v w

noncomputable section

variable {K : Type u} {G : Type v} {V : Type w}
variable [Field K] [IsAlgClosed K] [Group G]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

/-- A representation has a common eigenvector if some subgroup containing the commutator subgroup
acts unipotently. Such a subgroup is automatically normal.

Kolchin first produces a nonzero vector fixed by the normal subgroup. Its entire fixed space is
stable under the ambient group, and the induced action factors through the commutative quotient.
-/
theorem _root_.Representation.exists_unitHom_jointEigenvector_of_commutator_le_of_isUnipotent
    (rho : _root_.Representation K G V) (N : Subgroup G)
    (hcomm : _root_.commutator G ≤ N)
    (hunipotent : ∀ n : N, IsNilpotent (rho n - 1)) :
    ∃ (χ : G →* Kˣ) (v : V), v ≠ 0 ∧ ∀ g, rho g v = (χ g : K) • v := by
  let _ : N.Normal := Subgroup.Normal.of_commutator_le (G := G) hcomm
  let S := Representation.invariants (rho.comp N.subtype)
  obtain ⟨x, hx, hfixed⟩ :=
    _root_.Representation.exists_common_fixed_vector_of_isUnipotent
      (rho.comp N.subtype) hunipotent
  let xS : S := ⟨x, hfixed⟩
  let _ : Nontrivial S := ⟨xS, 0, fun h ↦ hx (congrArg Subtype.val h)⟩
  let rhoQ : _root_.Representation K (G ⧸ N) S := rho.quotientToInvariants N
  let _ : IsMulCommutative (G ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  obtain ⟨χ, y, hy, heigen⟩ :=
    TauCeti.exists_unitHom_jointEigenvector_of_pairwise_commute_of_isAlgClosed
      rhoQ fun (g h : G ⧸ N) _ ↦ by
        exact (rhoQ.map_mul g h).symm.trans <|
          (congrArg rhoQ (mul_comm' g h)).trans (rhoQ.map_mul h g)
  let χ' : G →* Kˣ := χ.comp (QuotientGroup.mk' N)
  refine ⟨χ', y, fun h ↦ hy (Subtype.ext h), fun g ↦ ?_⟩
  exact congrArg Subtype.val (heigen (QuotientGroup.mk' N g))

end

end TauCeti
