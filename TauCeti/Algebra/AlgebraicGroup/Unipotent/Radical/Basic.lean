/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Trivial
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic

/-!
# Candidates for the unipotent radical

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. A candidate
for its unipotent radical is a connected normal smooth unipotent closed subgroup. In Hopf
coordinates this is a normal Hopf ideal `I` whose quotient `H/I` is geometrically connected,
smooth, and geometrically unipotent.

This file proves the boundedness step in the standard maximal-dimension construction. The
trivial subgroup, cut out by the augmentation ideal, is a candidate. The Lie dimension of every
candidate is bounded by the Lie dimension of the ambient group, by the conormal exact sequence.
Consequently the set of Lie dimensions attained by candidates is a nonempty finite set of natural
numbers, and some candidate has maximal Lie dimension.

Binary-product closure is the next step: once the product of two candidates is again a candidate,
a maximal-dimension candidate contains every other one and is the unipotent radical.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate`: a connected normal smooth unipotent closed
  subgroup in coordinate-Hopf-algebra form.
* `TauCeti.HopfIdeal.isUnipotentRadicalCandidate_augmentation`: the identity subgroup is a
  candidate.
* `TauCeti.HopfIdeal.finrank_quotientLie_le`: the Lie dimension of a closed subgroup is bounded
  by that of the ambient affine group.
* `TauCeti.HopfIdeal.exists_isUnipotentRadicalCandidate_maximal_finrank_quotientLie`: existence of a
  candidate of maximal Lie dimension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§6.45–6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap. It supplies the
maximal-dimension choice used after closure of connected normal smooth unipotent subgroups under
binary products.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]

/-- A Hopf ideal cuts out an **unipotent-radical candidate** when the represented closed subgroup
is normal, geometrically connected, smooth, and geometrically unipotent.

Normality is a property of the ideal in the ambient coordinate Hopf algebra. The other three
conditions are properties of its finite-type quotient coordinate Hopf algebra. -/
def IsUnipotentRadicalCandidate (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (I : HopfIdeal k H) : Prop :=
  I.IsNormal ∧
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj ∧
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I)

namespace IsUnipotentRadicalCandidate

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- A normal Hopf ideal with geometrically connected, smooth unipotent quotient is a
unipotent-radical candidate. -/
theorem mk (h_normal : I.IsNormal)
    (h_connected : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj)
    (h_smoothUnipotent : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I)) :
    IsUnipotentRadicalCandidate H I :=
  ⟨h_normal, h_connected, h_smoothUnipotent⟩

/-- A unipotent-radical candidate is normal in the ambient affine group. -/
theorem isNormal (hI : IsUnipotentRadicalCandidate H I) : I.IsNormal :=
  hI.1

/-- A unipotent-radical candidate is geometrically connected. -/
theorem geometricallyConnected (hI : IsUnipotentRadicalCandidate H I) :
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I).obj :=
  hI.2.1

/-- A unipotent-radical candidate is smooth unipotent. -/
theorem smoothUnipotent (hI : IsUnipotentRadicalCandidate H I) :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I) :=
  hI.2.2

end IsUnipotentRadicalCandidate

/-- The quotient by the augmentation ideal is the trivial finite-type Hopf algebra. -/
private noncomputable def quotientAugmentationIso
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    FiniteTypeCommHopfAlgCat.quotient H (augmentation k H) ≅
      FiniteTypeCommHopfAlgCat.of k k := by
  rw [augmentation_def]
  exact ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk <|
    kerLiftBialgEquiv (Bialgebra.counitBialgHom k H) Bialgebra.counit_surjective

/-- The trivial finite-type affine group is geometrically connected. -/
private theorem geometricallyConnected_trivial :
    geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k k) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.lid k K).toRingEquiv).connectedSpace_iff.mpr inferInstance

/-- The trivial finite-type affine group is smooth unipotent. -/
private theorem smoothUnipotent_trivial :
    smoothUnipotentCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k k) := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine ⟨⟨inferInstance, inferInstance⟩, fun g ↦ ?_⟩
  rw [TrivialGroup.convPoint_eq_one g]
  exact HopfAlgebra.isUnipotentPoint_one

/-- The augmentation ideal cuts out the identity subgroup, hence is an unipotent-radical
candidate. This makes the family of candidates nonempty without any hypothesis on the ambient
finite-type affine group. -/
theorem isUnipotentRadicalCandidate_augmentation
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    IsUnipotentRadicalCandidate H (augmentation k H) := by
  refine IsUnipotentRadicalCandidate.mk
    (CommHopfAlgCat.isCentral_augmentation H.obj).isNormal ?_ ?_
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
        (_root_.CommHopfAlgCat.{u} k)).mapIso (quotientAugmentationIso H).symm)
      geometricallyConnected_trivial
  · exact (smoothUnipotentCommHopfAlgProperty k).prop_of_iso
      (quotientAugmentationIso H).symm smoothUnipotent_trivial

/-- There exists a connected normal smooth unipotent closed subgroup of maximal Lie dimension.

The theorem asserts maximality only among unipotent-radical candidates. Turning this candidate
into the greatest such subgroup requires the separate binary-product theorem: the product with
any other candidate is again a candidate and cannot have larger dimension. -/
theorem exists_isUnipotentRadicalCandidate_maximal_finrank_quotientLie
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ∃ I : HopfIdeal k H,
      IsUnipotentRadicalCandidate H I ∧
        ∀ J : HopfIdeal k H, IsUnipotentRadicalCandidate H J →
          Module.finrank k
              (Derivation k (H ⧸ J.toIdeal)
                (Bialgebra.CounitAlgebra k (H ⧸ J.toIdeal) k)) ≤
            Module.finrank k
              (Derivation k (H ⧸ I.toIdeal)
                (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) := by
  let dimensions : Set ℕ := {n | ∃ I : HopfIdeal k H,
    IsUnipotentRadicalCandidate H I ∧
      Module.finrank k
        (Derivation k (H ⧸ I.toIdeal)
          (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) = n}
  have hdimensions_finite : dimensions.Finite := by
    apply (Set.finite_Iic
      (Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)))).subset
    rintro n ⟨I, _, rfl⟩
    exact finrank_quotientLie_le I
  have hdimensions_nonempty : dimensions.Nonempty := by
    exact ⟨_, augmentation k H, isUnipotentRadicalCandidate_augmentation H, rfl⟩
  obtain ⟨n, hn, hnmax⟩ :=
    Set.exists_max_image dimensions id hdimensions_finite hdimensions_nonempty
  obtain ⟨I, hI, hIn⟩ := hn
  refine ⟨I, hI, fun J hJ ↦ ?_⟩
  have hJmem : Module.finrank k
      (Derivation k (H ⧸ J.toIdeal)
        (Bialgebra.CounitAlgebra k (H ⧸ J.toIdeal) k)) ∈ dimensions :=
    ⟨J, hJ, rfl⟩
  simpa only [id_eq, hIn] using hnmax _ hJmem

end HopfIdeal

end

end TauCeti
