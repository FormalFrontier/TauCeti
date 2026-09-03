/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.BaseChange

/-!
# Base change of faithful comodules

Let `M` be a finite free comodule over a commutative Hopf algebra `H`. After extending both the
coefficient Hopf algebra and `M` along a morphism of commutative rings, the coordinate morphism of
the extended comodule is the scalar extension of the original coordinate morphism, transported
through the canonical base-change isomorphism for `O(GLₙ)`.

Consequently, scalar extension preserves faithful comodules: surjectivity of the coordinate
morphism survives base change.

## Main declarations

* `TauCeti.Comodule.coordinateBialgHom_baseChange`: compatibility of the coordinate morphism with
  scalar extension.
* `TauCeti.Comodule.IsFaithful.baseChange`: a faithful finite free comodule remains faithful after
  scalar extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Remarks 4.1 and 4.8.

This transports the faithful representation used to prove base-change invariance of geometric
unipotence, the next scalar-extension step for the unipotent radical in Layer 5 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory Module
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v

noncomputable section

variable {k H M : Type u} {K : Type max u v} [CommRing k] [CommRing K] [Algebra k K]
variable [CommRing H] [HopfAlgebra k H]
variable [AddCommMonoid M] [Module k M] [Comodule k H M]

/-- The coordinate morphism of a base-changed comodule is the scalar extension of its original
coordinate morphism, after identifying the scalar extension of `O(GLₙ)` with `O(GLₙ)` over the
new base. -/
theorem coordinateBialgHom_baseChange {d : ℕ} (b : Basis (Fin d) k M) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
    coordinateBialgHom (H := K ⊗[k] H) (b.baseChange K) =
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K d).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b))).hom := by
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  apply BialgHom.ext
  intro z
  have hAlg :
      (coordinateBialgHom (H := K ⊗[k] H) (b.baseChange K)).toAlgHom =
        (((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K d).inv ≫
          CommHopfAlgCat.baseChangeMap (K := K)
            (CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b))).hom).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext K d
    intro i j
    erw [coordinateBialgHom_X]
    rw [coefficientMatrix_baseChange, Matrix.map_apply]
    have hx := GeneralLinear.coordinateHopfAlgebraBaseChangeMap_X k K d
      (CommHopfAlgCat.of k H) (CommHopfAlgCat.baseChange (K := K) (CommHopfAlgCat.of k H))
      (CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b))
      (Iso.refl _) i j
    have hx' := hx.symm
    simp only [Iso.refl_hom, Category.comp_id, CommHopfAlgCat.hom_comp,
      CommHopfAlgCat.hom_ofHom, BialgHom.comp_apply, coordinateBialgHom_X] at hx'
    -- Remove the categorical identity and `ofHom` wrappers so the bialgebra tensor map can be
    -- compared with the algebra tensor map stored in the target `AlgHom`.
    change (1 : K) ⊗ₜ[k] coefficientMatrix (C := H) b i j =
      (Bialgebra.TensorProduct.map (BialgHom.id K K)
        (coordinateBialgHom (H := H) b)).toAlgHom
          ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K d).inv.hom.toAlgHom
            (GeneralLinear.coordinateHopfAlgebraAlgEquiv K d
              (GeneralLinear.coordinateRingMap K d (MvPolynomial.X (i, j))))) at hx'
    rw [Bialgebra.TensorProduct.map_toAlgHom] at hx'
    exact hx'
  exact DFunLike.congr_fun hAlg z

namespace IsFaithful

/-- Scalar extension of the coefficient Hopf algebra and underlying module preserves a faithful
finite free comodule. -/
theorem baseChange (hM : IsFaithful (k := k) (H := H) (V := M)) :
    letI := Comodule.baseChange (R := k) (H := H) (M := M) K
    IsFaithful (k := K) (H := K ⊗[k] H) (V := K ⊗[k] M) := by
  rcases isFaithful_def.mp hM with ⟨d, b, hb⟩
  let _ := Comodule.baseChange (R := k) (H := H) (M := M) K
  refine (isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom
    (H := K ⊗[k] H) (b := b.baseChange K)).2 ?_
  rw [isClosedImmersion_coordinateGroupSchemeHom_iff]
  rw [coordinateBialgHom_baseChange]
  have hinv : Function.Surjective
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K d).inv.hom := by
    intro y
    refine ⟨(GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K d).hom.hom y, ?_⟩
    exact Iso.hom_inv_id_apply _ y
  exact (CommHopfAlgCat.baseChangeMap_surjective
    (CommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b))
      ((isClosedImmersion_coordinateGroupSchemeHom_iff b).1 hb)).comp hinv

end IsFaithful

end

end TauCeti.Comodule
