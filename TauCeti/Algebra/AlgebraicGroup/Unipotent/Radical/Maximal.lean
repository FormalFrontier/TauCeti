/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Product
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Properties
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.SmoothContainment
import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension

/-!
# Maximal-dimensional unipotent-radical candidates

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. The existing
maximal-dimension construction chooses a connected normal smooth unipotent closed subgroup `U`
whose Lie dimension is at least that of every other such subgroup. The existing product theorem
shows that the scheme-theoretic product `UV` is another candidate containing both `U` and `V`.

This file combines those two inputs. Containment makes Lie dimension monotone, while maximality
gives the reverse inequality, so `U` and `UV` have equal Lie dimension for every candidate `V`.
The resulting tangent-space equality, together with smoothness and connectedness, proves `UV = U`
and hence that `U` contains every candidate.

## Main declarations

The declarations are in `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate`.

* `finrank_quotientLie_productOfNormal_eq_of_maximal`:
  multiplying a maximal-dimensional candidate by any candidate preserves its Lie dimension.
* `derivationCompLieHom_productOfNormal_bijective_of_maximal`:
  the inclusion of a maximal candidate into its product with another candidate induces a
  bijection on tangent Lie algebras.
* `conormalSubspace_productOfNormal_le_left_eq_bot_of_maximal`:
  the relative defining ideal of the maximal candidate in that product has zero conormal space.
* `productOfNormal_eq_left_of_maximal`:
  a maximal-dimensional candidate contains every candidate, because their product equals it.
* `le_of_finrank_maximal`:
  a maximal-dimensional candidate is the greatest unipotent-radical candidate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap. It is the
dimension-comparison step between binary-product closure and the zero-dimensional quotient
argument that makes a maximal candidate the greatest candidate.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- Multiplying a maximal-dimensional unipotent-radical candidate by any other candidate does
not change its Lie dimension. -/
theorem finrank_quotientLie_productOfNormal_eq_of_maximal
    (hI : IsUnipotentRadicalCandidate H I)
    (hmax : ∀ K : HopfIdeal k H, IsUnipotentRadicalCandidate H K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : IsUnipotentRadicalCandidate H J) :
    Module.finrank k
        (Derivation k
          (H ⧸ (HopfIdeal.ker
            (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom).toIdeal)
          (Bialgebra.CounitAlgebra k
            (H ⧸ (HopfIdeal.ker
              (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom).toIdeal) k)) =
      Module.finrank k
        (Derivation k (H ⧸ I.toIdeal)
          (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)) := by
  let P : HopfIdeal k H :=
    HopfIdeal.ker (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom
  have hP : IsUnipotentRadicalCandidate H P := hI.productOfNormal hJ
  apply le_antisymm
  · exact hmax P hP
  · exact HopfIdeal.finrank_quotientLie_antitone
      (CommHopfAlgCat.ker_productMapOfNormal_le_left H.obj I J hI.isNormal)

/-- The closed-subgroup inclusion from a maximal-dimensional unipotent-radical candidate into
its product with another candidate induces a bijection on tangent Lie algebras. -/
theorem derivationCompLieHom_productOfNormal_bijective_of_maximal
    (hI : IsUnipotentRadicalCandidate H I)
    (hmax : ∀ K : HopfIdeal k H, IsUnipotentRadicalCandidate H K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : IsUnipotentRadicalCandidate H J) :
    Function.Bijective
      (derivationCompLieHom (B := k)
        (FiniteTypeCommHopfAlgCat.toBialgHom
          (FiniteTypeCommHopfAlgCat.quotientMapOfLe H
            (CommHopfAlgCat.ker_productMapOfNormal_le_left H.obj I J hI.isNormal)))) := by
  let hPI := CommHopfAlgCat.ker_productMapOfNormal_le_left H.obj I J hI.isNormal
  have hfinrank := hI.finrank_quotientLie_productOfNormal_eq_of_maximal hmax hJ
  exact derivationCompLieHom_bijective_of_surjective_of_finrank_eq _
    (FiniteTypeCommHopfAlgCat.quotientMapOfLe_surjective H hPI) hfinrank.symm

/-- The relative defining ideal of a maximal-dimensional unipotent-radical candidate inside its
product with any other candidate has zero conormal space at the identity.

Thus the maximal candidate and the product candidate agree to first order. The remaining
maximality step is global: smoothness and connectedness must upgrade this infinitesimal equality
to equality of the two closed subgroups. -/
theorem conormalSubspace_productOfNormal_le_left_eq_bot_of_maximal
    (hI : IsUnipotentRadicalCandidate H I)
    (hmax : ∀ K : HopfIdeal k H, IsUnipotentRadicalCandidate H K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : IsUnipotentRadicalCandidate H J) :
    HopfIdeal.conormalSubspace
      (I.map (Bialgebra.Quotient.mkBialgHom
        (HopfIdeal.ker
          (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom).toIdeal)) =
      ⊥ := by
  let P : HopfIdeal k H :=
    HopfIdeal.ker (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom
  let hPI : P ≤ I :=
    CommHopfAlgCat.ker_productMapOfNormal_le_left H.obj I J hI.isNormal
  let q := FiniteTypeCommHopfAlgCat.toBialgHom
    (FiniteTypeCommHopfAlgCat.quotientMapOfLe H hPI)
  have hq_surjective : Function.Surjective q :=
    FiniteTypeCommHopfAlgCat.quotientMapOfLe_surjective H hPI
  have hdq_surjective :
      Function.Surjective (derivationCompLieHom (B := k) q) :=
    (hI.derivationCompLieHom_productOfNormal_bijective_of_maximal hmax hJ).2
  have hconormal : HopfIdeal.conormalSubspace (HopfIdeal.ker q) = ⊥ :=
    HopfIdeal.conormalSubspace_ker_eq_bot_of_surjective_of_derivationCompLieHom_surjective
      q hq_surjective hdq_surjective
  have hker : HopfIdeal.ker q =
      I.map (Bialgebra.Quotient.mkBialgHom P.toIdeal) :=
    CommHopfAlgCat.ker_quotientMapOfLe H.obj hPI
  simpa only [P] using hker ▸ hconormal

/-- Multiplying a maximal-dimensional unipotent-radical candidate by any other candidate does
not enlarge it.

The preceding tangent-space calculation gives zero conormal space for the inclusion of the
maximal candidate in the product. Both groups are smooth and connected, so
`HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot` upgrades this
first-order equality to equality of the closed subgroups. -/
theorem productOfNormal_eq_left_of_maximal
    (hI : IsUnipotentRadicalCandidate H I)
    (hmax : ∀ K : HopfIdeal k H, IsUnipotentRadicalCandidate H K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : IsUnipotentRadicalCandidate H J) :
    HopfIdeal.ker
        (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom = I := by
  let P : HopfIdeal k H :=
    HopfIdeal.ker (CommHopfAlgCat.productMapOfNormal H.obj I J hI.isNormal).hom
  let hPI : P ≤ I :=
    CommHopfAlgCat.ker_productMapOfNormal_le_left H.obj I J hI.isNormal
  let q := FiniteTypeCommHopfAlgCat.toBialgHom
    (FiniteTypeCommHopfAlgCat.quotientMapOfLe H hPI)
  have hP : IsUnipotentRadicalCandidate H P := hI.productOfNormal hJ
  have hP_smooth : smoothCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (H ⧸ P.toIdeal)) :=
    (smoothCommHopfAlgProperty_iff _).mpr
      ((smoothUnipotentCommHopfAlgProperty_iff k
        (FiniteTypeCommHopfAlgCat.quotient H P)).mp hP.smoothUnipotent).1
  have hI_smooth : smoothCommHopfAlgProperty k
      (_root_.CommHopfAlgCat.of k (H ⧸ I.toIdeal)) :=
    (smoothCommHopfAlgProperty_iff _).mpr
      ((smoothUnipotentCommHopfAlgProperty_iff k
        (FiniteTypeCommHopfAlgCat.quotient H I)).mp hI.smoothUnipotent).1
  have hP_connected : ConnectedSpace (PrimeSpectrum (H ⧸ P.toIdeal)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hP.geometricallyConnected
  have hI_connected : ConnectedSpace (PrimeSpectrum (H ⧸ I.toIdeal)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hI.geometricallyConnected
  have hker_q : HopfIdeal.ker q =
      I.map (Bialgebra.Quotient.mkBialgHom P.toIdeal) :=
    CommHopfAlgCat.ker_quotientMapOfLe H.obj hPI
  have hconormal_q : HopfIdeal.conormalSubspace (HopfIdeal.ker q) = ⊥ := by
    rw [hker_q]
    simpa only [P] using
      hI.conormalSubspace_productOfNormal_le_left_eq_bot_of_maximal hmax hJ
  have hqker : HopfIdeal.ker q = ⊥ :=
    HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot q
      (FiniteTypeCommHopfAlgCat.quotientMapOfLe_surjective H hPI)
      hP_smooth hP_connected hI_smooth hI_connected
      hconormal_q
  have hmap : I.map (Bialgebra.Quotient.mkBialgHom P.toIdeal) = ⊥ := by
    rw [← CommHopfAlgCat.ker_quotientMapOfLe H.obj hPI]
    exact hqker
  have hIP : I ≤ P := by
    rw [← toIdeal_le_toIdeal]
    have hle := (HopfIdeal.map_eq_bot_iff I
      (Bialgebra.Quotient.mkBialgHom P.toIdeal)).mp hmap
    intro x hx
    have hxker := hle hx
    rw [RingHom.mem_ker] at hxker
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxker
  exact le_antisymm hPI hIP

/-- A maximal-dimensional unipotent-radical candidate is the greatest candidate.

The order on Hopf ideals reverses inclusion of the represented closed subgroups: `I ≤ J` says
that the subgroup defined by `I` contains the subgroup defined by `J`. -/
theorem le_of_finrank_maximal
    (hI : IsUnipotentRadicalCandidate H I)
    (hmax : ∀ K : HopfIdeal k H, IsUnipotentRadicalCandidate H K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : IsUnipotentRadicalCandidate H J) : I ≤ J := by
  rw [← hI.productOfNormal_eq_left_of_maximal hmax hJ]
  exact CommHopfAlgCat.ker_productMapOfNormal_le_right H.obj I J hI.isNormal

end HopfIdeal.IsUnipotentRadicalCandidate

end

end TauCeti
