/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# Faithful representations of closed subgroups

Let `M` be a finite free comodule over a commutative Hopf algebra `H`. Corestricting its coaction
along a surjective bialgebra morphism `H ⟶ K` restricts the corresponding representation to the
closed subgroup represented by `K`. Its coordinate morphism is the composite

```text
O(GL(M)) ⟶ H ⟶ K.
```

Consequently a faithful representation stays faithful after restriction to a closed subgroup. If
that restricted representation is trivial, faithfulness forces the subgroup itself to be the
identity subgroup. The final Hopf-ideal form says that a closed subgroup acting trivially through
a faithful ambient representation is cut out by the augmentation ideal.

This is the kernel-elimination input for the direct proof that `GLₙ` is reductive. For a connected
normal smooth unipotent closed subgroup, the normal-invariants argument makes its fixed vectors an
ambient subrepresentation; simplicity of the standard representation makes every vector fixed,
and the result here then identifies the subgroup with the identity.

## Main declarations

* `TauCeti.Comodule.coordinateBialgHom_corestrict`: the coordinate morphism of a corestricted
  comodule is the expected composite.
* `TauCeti.Comodule.isFaithful_corestrict_of_surjective`: restriction to a closed subgroup
  preserves faithfulness.
* `TauCeti.Comodule.augmentation_eq_bot_of_isFaithful_of_coact_eq_tmul_one`: a Hopf algebra with
  a faithful trivial representation is trivial.
* `TauCeti.Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one`: a closed
  subgroup acting trivially in a faithful representation is the identity subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), §4.a and §5.
* T. A. Springer, *Linear Algebraic Groups*, §2.2.

This advances the worked-example target `GLₙ` is reductive in Layer 6 of the ReductiveGroups
roadmap. It supplies the faithful-representation step used after normal-subgroup invariants and
Kolchin's fixed-vector theorem.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

noncomputable section

section CoordinateCorestrict

variable {R : Type u} {H : Type v} {K : Type w} {M : Type x} {n : ℕ}
variable [CommRing R] [CommRing H] [CommRing K]
variable [HopfAlgebra R H] [HopfAlgebra R K]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- The coordinate morphism of a comodule corestricted along a bialgebra morphism is the
composite of the original coordinate morphism with that bialgebra morphism. -/
theorem coordinateBialgHom_corestrict (f : H →ₐc[R] K) (b : Basis (Fin n) R M) :
    letI : Comodule R K M := Corestrict f.toCoalgHom
    coordinateBialgHom (H := K) b = f.comp (coordinateBialgHom (H := H) b) := by
  let _ : Comodule R K M := Corestrict f.toCoalgHom
  apply BialgHom.ext
  intro z
  have hAlg : (coordinateBialgHom (H := K) b).toAlgHom =
      (f.comp (coordinateBialgHom (H := H) b)).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
    intro i j
    rw [BialgHom.comp_toAlgHom, AlgHom.comp_apply]
    erw [coordinateBialgHom_X (H := K), coordinateBialgHom_X (H := H)]
    rw [coefficientMatrix_apply, coefficientMatrix_apply,
      matrixCoefficient_def, matrixCoefficient_def, corestrict_coact_apply]
    have h := LinearMap.congr_fun
      (CoassocSimps.lid_comp_map (b.coord i) f.toLinearMap)
      (coact (R := R) (C := H) (M := M) (b j))
    rw [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
    -- `lid_comp_map` states naturality for the underlying linear map; expose that coercion on
    -- the right-hand side after tensor-map composition has been normalized.
    change _ = f.toLinearMap _
    exact h
  exact DFunLike.congr_fun hAlg z

end CoordinateCorestrict

section FaithfulCorestrict

variable {R H K M : Type u} {n : ℕ}
variable [CommRing R] [CommRing H] [CommRing K]
variable [HopfAlgebra R H] [HopfAlgebra R K]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Corestricting a faithful finite free comodule along a surjective bialgebra morphism gives a
faithful comodule over the codomain. Geometrically, restricting a faithful representation to a
closed subgroup remains faithful. -/
theorem isFaithful_corestrict_of_surjective (f : H →ₐc[R] K) (hf : Function.Surjective f)
    (b : Basis (Fin n) R M) (hM : IsFaithful (k := R) (H := H) (V := M)) :
    letI : Comodule R K M := Corestrict f.toCoalgHom
    IsFaithful (k := R) (H := K) (V := M) := by
  let _ : Comodule R K M := Corestrict f.toCoalgHom
  have hsurj : Function.Surjective (coordinateBialgHom (H := H) b) := by
    rw [← isClosedImmersion_coordinateGroupSchemeHom_iff,
      ← isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom (b := b)]
    exact hM
  rw [isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom (b := b),
    isClosedImmersion_coordinateGroupSchemeHom_iff, coordinateBialgHom_corestrict f b]
  exact hf.comp hsurj

end FaithfulCorestrict

section TrivialCoordinate

variable {R : Type u} {H : Type v} {M : Type w} {n : ℕ}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- If every vector has trivial coaction, the coordinate morphism of the representation factors
through the counit of `O(GLₙ)` and the unit of the coefficient Hopf algebra. -/
theorem coordinateBialgHom_eq_unit_comp_counit_of_coact_eq_tmul_one
    (b : Basis (Fin n) R M)
    (htrivial : ∀ m : M, coact (R := R) (C := H) m = m ⊗ₜ[R] (1 : H)) :
    coordinateBialgHom (H := H) b =
      (Bialgebra.unitBialgHom R H).comp
        (Bialgebra.counitBialgHom R (GeneralLinear.coordinateHopfAlgebra R n)) := by
  apply BialgHom.ext
  intro z
  have hAlg : (coordinateBialgHom (H := H) b).toAlgHom =
      ((Bialgebra.unitBialgHom R H).comp
        (Bialgebra.counitBialgHom R
          (GeneralLinear.coordinateHopfAlgebra R n))).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
    intro i j
    rw [BialgHom.comp_toAlgHom, AlgHom.comp_apply]
    erw [coordinateBialgHom_X]
    rw [coefficientMatrix_apply, matrixCoefficient_def, htrivial]
    by_cases hij : i = j <;> simp [hij]
  exact DFunLike.congr_fun hAlg z

end TrivialCoordinate

section TrivialFaithful

variable {R H M : Type u} {n : ℕ}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- A commutative Hopf algebra admitting a faithful finite free comodule with trivial coaction
has zero augmentation ideal. Equivalently, the represented affine group is the identity group. -/
theorem augmentation_eq_bot_of_isFaithful_of_coact_eq_tmul_one
    (b : Basis (Fin n) R M) (hM : IsFaithful (k := R) (H := H) (V := M))
    (htrivial : ∀ m : M, coact (R := R) (C := H) m = m ⊗ₜ[R] (1 : H)) :
    HopfIdeal.augmentation R H = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hsurj : Function.Surjective (coordinateBialgHom (H := H) b) := by
    rw [← isClosedImmersion_coordinateGroupSchemeHom_iff,
      ← isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom (b := b)]
    exact hM
  obtain ⟨z, rfl⟩ := hsurj x
  have hcoordinate := DFunLike.congr_fun
    (coordinateBialgHom_eq_unit_comp_counit_of_coact_eq_tmul_one b htrivial) z
  rw [BialgHom.comp_apply] at hcoordinate
  rw [hcoordinate]
  have hcounit : Coalgebra.counit (R := R) (A := H)
      (coordinateBialgHom (H := H) b z) = 0 :=
    (HopfIdeal.mem_augmentation R H).mp hx
  have hcounit_z : Coalgebra.counit (R := R) z = 0 :=
    (CoalgHomClass.counit_comp_apply (coordinateBialgHom (H := H) b) z).symm.trans hcounit
  rw [HopfIdeal.mem_bot]
  -- The unit bialgebra morphism is the algebra structure map; expose its value after the
  -- coordinate factorization has reduced the goal to a scalar.
  change algebraMap R H (Coalgebra.counit (R := R) z) = 0
  rw [hcounit_z, map_zero]

/-- A closed subgroup acting trivially through a faithful finite free representation is the
identity subgroup: its defining Hopf ideal is the augmentation ideal of the ambient group. -/
theorem eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one
    (I : HopfIdeal R H) (b : Basis (Fin n) R M)
    (hM : IsFaithful (k := R) (H := H) (V := M))
    (htrivial : ∀ m : M,
      TensorProduct.map LinearMap.id
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H) I).hom.toLinearMap
          (coact (R := R) (C := H) m) =
        m ⊗ₜ[R]
          (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) I)) :
    I = HopfIdeal.augmentation R H := by
  let q := (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H) I).hom
  let Q := CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) I
  let _ : Comodule R Q M := Corestrict q.toCoalgHom
  have hq : Function.Surjective q :=
    CommHopfAlgCat.mkQuotient_surjective (_root_.CommHopfAlgCat.of R H) I
  have hfaithfulQ : IsFaithful (k := R) (H := Q) (V := M) :=
    isFaithful_corestrict_of_surjective q hq b hM
  have htrivialQ : ∀ m : M, coact (R := R) (C := Q) m = m ⊗ₜ[R] (1 : Q) := by
    intro m
    exact htrivial m
  have haugmentationQ : HopfIdeal.augmentation R Q = ⊥ :=
    augmentation_eq_bot_of_isFaithful_of_coact_eq_tmul_one b hfaithfulQ htrivialQ
  have hcomapBot : (⊥ : HopfIdeal R Q).comap q hq = I := by
    ext x
    rw [HopfIdeal.mem_comap, HopfIdeal.mem_bot,
      CommHopfAlgCat.mkQuotient_eq_zero_iff, HopfIdeal.mem_toIdeal]
  calc
    I = (⊥ : HopfIdeal R Q).comap q hq := hcomapBot.symm
    _ = (HopfIdeal.augmentation R Q).comap q hq := by rw [haugmentationQ]
    _ = HopfIdeal.augmentation R H := HopfIdeal.comap_augmentation q hq

end TrivialFaithful

end

end TauCeti.Comodule
