/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Solvable

/-!
# Candidates for the solvable radical

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. A candidate
for its solvable radical is a connected normal smooth solvable closed subgroup. In Hopf
coordinates this is a normal Hopf ideal `I` whose quotient `H/I` is geometrically connected,
smooth, and has a solvable group of geometric points.

This file proves the boundedness step in the maximal-dimension construction. Every
unipotent-radical candidate is a solvable-radical candidate, so in particular the identity
subgroup is a candidate. The Lie dimension of every candidate is bounded by that of the ambient
group. Hence the natural numbers occurring as candidate dimensions form a nonempty finite set,
and one of the candidates has maximal Lie dimension.

To turn a maximal-dimensional candidate into the solvable radical, one must next show that the
scheme-theoretic multiplication image of two candidates is again a candidate. The connectedness,
smoothness, and source-solvability results already exist; the remaining input is solvability of
the image, for which the current image theorem requires faithful flatness of the canonical Hopf
image inclusion.

## Main declarations

* `TauCeti.HopfIdeal.IsSolvableRadicalCandidate`: a connected normal smooth solvable closed
  subgroup in coordinate-Hopf-algebra form.
* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.isSolvableRadicalCandidate`: every
  unipotent-radical candidate is a solvable-radical candidate.
* `TauCeti.HopfIdeal.isSolvableRadicalCandidate_augmentation`: the identity subgroup is a
  candidate.
* `TauCeti.HopfIdeal.exists_isSolvableRadicalCandidate_maximal_finrank_quotientLie`: existence of
  a solvable-radical candidate of maximal Lie dimension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§6.45–6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap. The
radical `R(G)` required there is the greatest connected normal smooth solvable closed subgroup;
the maximal-dimension candidate constructed here is the first step in that construction.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]

/-- A Hopf ideal cuts out a **solvable-radical candidate** when the represented closed subgroup
is normal, geometrically connected, smooth, and has a solvable group of geometric points.

Normality is a property of the ideal in the ambient coordinate Hopf algebra. The other three
conditions are properties of its finite-type quotient coordinate Hopf algebra. -/
def IsSolvableRadicalCandidate (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) : Prop :=
  I.IsNormal ∧
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj ∧
    Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I) ∧
    geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj

namespace IsSolvableRadicalCandidate

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- A normal Hopf ideal with geometrically connected, smooth, solvable quotient is a
solvable-radical candidate. -/
theorem mk (h_normal : I.IsNormal)
    (h_connected : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj)
    (h_smooth : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I))
    (h_solvable : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj) :
    IsSolvableRadicalCandidate H I :=
  ⟨h_normal, h_connected, h_smooth, h_solvable⟩

/-- A solvable-radical candidate is normal in the ambient affine group. -/
theorem isNormal (hI : IsSolvableRadicalCandidate H I) : I.IsNormal :=
  hI.1

/-- A solvable-radical candidate is geometrically connected. -/
theorem geometricallyConnected (hI : IsSolvableRadicalCandidate H I) :
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj :=
  hI.2.1

/-- A solvable-radical candidate is smooth. -/
theorem smooth (hI : IsSolvableRadicalCandidate H I) :
    Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I) :=
  hI.2.2.1

/-- A solvable-radical candidate has a solvable group of geometric points. -/
theorem geometricallySolvable (hI : IsSolvableRadicalCandidate H I) :
    geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj :=
  hI.2.2.2

end IsSolvableRadicalCandidate

namespace IsUnipotentRadicalCandidate

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- Every unipotent-radical candidate is a solvable-radical candidate. -/
theorem isSolvableRadicalCandidate (hI : IsUnipotentRadicalCandidate H I) :
    IsSolvableRadicalCandidate H I := by
  have hU := (smoothUnipotentCommHopfAlgProperty_iff k
    (FiniteTypeCommHopfAlgCat.quotient H I)).mp hI.smoothUnipotent
  have hU' : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj :=
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hU.2
  exact IsSolvableRadicalCandidate.mk hI.isNormal hI.geometricallyConnected hU.1
    (geometricallyUnipotentPointsCommHopfAlgProperty.geometricallySolvable hU')

end IsUnipotentRadicalCandidate

/-- The augmentation ideal cuts out the identity subgroup, hence is a solvable-radical
candidate. This makes the family of candidates nonempty without any hypothesis on the ambient
finite-type affine group. -/
theorem isSolvableRadicalCandidate_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsSolvableRadicalCandidate H (augmentation k H) :=
  (isUnipotentRadicalCandidate_augmentation H).isSolvableRadicalCandidate

/-- There exists a connected normal smooth solvable closed subgroup of maximal Lie dimension.

The theorem asserts maximality only among solvable-radical candidates. Turning this candidate
into the greatest such subgroup requires closure of candidates under scheme-theoretic binary
products. -/
theorem exists_isSolvableRadicalCandidate_maximal_finrank_quotientLie
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ∃ I : HopfIdeal k H,
      IsSolvableRadicalCandidate H I ∧
        ∀ J : HopfIdeal k H, IsSolvableRadicalCandidate H J →
          Module.finrank k
              (Derivation k (H ⧸ J.toIdeal)
                (Bialgebra.CounitAlgebra k (H ⧸ J.toIdeal) k)) ≤
            Module.finrank k
              (Derivation k (H ⧸ I.toIdeal)
                (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) := by
  exact exists_maximal_finrank_quotientLie (IsSolvableRadicalCandidate H)
    ⟨augmentation k H, isSolvableRadicalCandidate_augmentation H⟩

end HopfIdeal

end

end TauCeti
