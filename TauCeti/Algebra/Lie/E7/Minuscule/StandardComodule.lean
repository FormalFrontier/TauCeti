/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Lie.E7.Minuscule.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.BaseChange
import TauCeti.Algebra.Lie.E7.Minuscule.PointsFunctor

/-!
# The standard representation of the type-E7 minuscule carrier

The full-weight type-`E₇` minuscule carrier is a closed subgroup of `GL₅₆`.  After base
change to a commutative ring `R`, its standard representation is therefore the corestriction of
the standard `O(GL₅₆)`-comodule along the quotient coordinate morphism.

This file proves that the resulting representation is faithful over every commutative ring and
simple over every field.  For simplicity, restriction to the rank-seven weight torus separates a
nonzero invariant vector into its one-dimensional weight components.  The positive and negative
simple-root elements then move a coordinate vector across the connected minuscule weight graph.

## Main declarations

* `TauCeti.E7Minuscule.coordinateHopfAlgebra`: the specialized carrier coordinate Hopf algebra.
* `TauCeti.E7Minuscule.standardComodule`: its standard comodule on `R⁵⁶`.
* `TauCeti.E7Minuscule.isFaithful_standardComodule`: faithfulness of the standard comodule.
* `TauCeti.E7Minuscule.specializedPointsMulEquiv`: specialized coordinate-algebra points are
  identified with concrete carrier points.
* `TauCeti.E7Minuscule.points_mulVec_mem`: invariant submodules are stable under concrete carrier
  points.
* `TauCeti.E7Minuscule.instIsSimpleOrderSubcomodule`: simplicity over a field.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.

The corestriction and point-action interface follows
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule` and is adapted from
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.StandardComodule`; the specialized point
identification uses `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.BaseChange`.
-/

public section

open CategoryTheory Module WithConv
open scoped Matrix TensorProduct

namespace TauCeti.E7Minuscule

universe u

variable (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized type-`E₇` minuscule carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra R) (Fin 56 → R) :=
  let _ := GeneralLinear.standardComodule R 56
  Comodule.Corestrict (coordinateMap R).hom.toCoalgHom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard carrier coaction is the standard general-linear coaction followed by the
quotient coordinate morphism. -/
@[simp]
theorem standardComodule_coact :
    let _ := GeneralLinear.standardComodule R 56
    Comodule.corestrictCoact
        (R := R) (C := GeneralLinear.coordinateHopfAlgebra R 56)
        (D := coordinateHopfAlgebra R) (M := Fin 56 → R)
        (coordinateMap R).hom.toCoalgHom =
      TensorProduct.map LinearMap.id
          (coordinateMap R).hom.toCoalgHom.toLinearMap ∘ₗ
        GeneralLinear.standardCoact R 56 := by
  apply LinearMap.ext
  intro v
  rw [Comodule.corestrictCoact_apply, LinearMap.comp_apply,
    GeneralLinear.standardComodule_coact]

/-- **The standard comodule of the specialized type-`E₇` minuscule carrier is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra R) (V := Fin 56 → R) := by
  exact Comodule.isFaithful_corestrict_of_surjective (coordinateMap R).hom
    (coordinateMap_surjective R)
    (GeneralLinear.isFaithful_standardComodule R 56)

section PointAction

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under scalar extension, a carrier-valued point acts on the standard comodule by the matrix
obtained from its ambient `GL₅₆` point. -/
theorem piScalarRight_comp_endOfPoint
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] A)) :
    (TensorProduct.piScalarRight R A A (Fin 56)).toLinearMap.comp
        (Comodule.endOfPoint (Fin 56 → R) g.ofConv) =
      (Matrix.GeneralLinearGroup.toLin
          (GeneralLinear.pointToGeneralLinear 56
            (CommHopfAlgCat.quotientPointsHom
              (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
              (CommAlgCat.of R A) g)) :
          (Fin 56 → A) →ₗ[A] Fin 56 → A).comp
        (TensorProduct.piScalarRight R A A (Fin 56)).toLinearMap := by
  rw [Comodule.endOfPoint_corestrict]
  have hpoint :
      g.ofConv.comp ((coordinateMap R).hom :
        GeneralLinear.coordinateHopfAlgebra R 56 →ₐ[R] coordinateHopfAlgebra R) =
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R A) g).ofConv := by
    exact congrArg WithConv.ofConv (mapPointsFunctor_coordinateMap_app R g)
  rw [hpoint]
  exact GeneralLinear.piScalarRight_comp_endOfPoint R 56 _

end PointAction

/-- **A subcomodule of the standard carrier comodule is stable under every carrier-valued
point.** -/
theorem mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 56 → R))
    (g : WithConv (coordinateHopfAlgebra R →ₐ[R] R)) {w : Fin 56 → R} (hw : w ∈ N) :
    (GeneralLinear.pointToGeneralLinear 56
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R R) g) : Matrix (Fin 56) (Fin 56) R) *ᵥ w ∈ N := by
  have h := Comodule.basePointsRepresentation_mem N g hw
  rw [Comodule.basePointsRepresentation_corestrict (coordinateMap R).hom g,
    GeneralLinear.basePointsRepresentation_eq_mulVec] at h
  have hpoint :
      AlgHom.mapDomain (coordinateMap R).hom g =
        CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
          (CommAlgCat.of R R) g := by
    exact mapPointsFunctor_coordinateMap_app R g
  rw [hpoint] at h
  exact h

/-- Base-valued points of the specialized coordinate algebra, identified with points of the
integral minuscule carrier after base change. -/
noncomputable def specializedPointsMulEquiv :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) (CommAlgCat.of R R) ≃*
      points R :=
  (CommHopfAlgCat.baseChangeIsoPointsMulEquiv (baseChangeCoordinateIso R)
      (CommAlgCat.of R R)).trans
    (pointsMulEquiv
      (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ R) (CommAlgCat.of R R)))

/-- Under the specialized point equivalence, the quotient point is represented by the carrier
point's ambient general-linear matrix. -/
theorem quotientPointsHom_specializedPointsMulEquiv_symm (g : points R) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
        (CommAlgCat.of R R) ((specializedPointsMulEquiv R).symm g) =
      (GeneralLinear.pointsMulEquiv (R := R) 56).symm
        (g : Matrix.GeneralLinearGroup (Fin 56) R) := by
  have h :
      ((specializedPointsMulEquiv R)
          ((specializedPointsMulEquiv R).symm g) : Matrix.GeneralLinearGroup (Fin 56) R) =
        GeneralLinear.pointsMulEquiv 56
          (CommHopfAlgCat.quotientPointsHom
            (GeneralLinear.coordinateHopfAlgebra R 56) (baseChangeDefiningIdeal R)
            (CommAlgCat.of R R) ((specializedPointsMulEquiv R).symm g)) := by
    rw [specializedPointsMulEquiv, MulEquiv.trans_apply, coe_pointsMulEquiv_apply]
    exact GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
      56 definingIdeal (baseChangeDefiningIdeal R) (baseChangeCoordinateIso R)
      (mkQuotient_comp_baseChangeCoordinateIso_hom R) (CommAlgCat.of R R) _
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

/-- A subcomodule of the standard carrier comodule is stable under every concrete carrier
point. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra R) (Fin 56 → R))
    (g : points R) {w : Fin 56 → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin 56) R) : Matrix (Fin 56) (Fin 56) R) *ᵥ w ∈ N := by
  have h := mulVec_mem R N ((specializedPointsMulEquiv R).symm g) hw
  rw [quotientPointsHom_specializedPointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

/-! ## Simplicity over a field -/

section Simple

variable (k : Type u) [Field k]

private theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k))
    (i : Fin 7 ⊕ Fin 7) {w : Fin 56 → k} (hw : w ∈ N) :
    ((rootSubgroupPoints i k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 56) k) : Matrix (Fin 56) (Fin 56) k) *ᵥ w ∈ N := by
  exact points_mulVec_mem k N (rootSubgroupPoints i k (Multiplicative.ofAdd 1)) hw

/-- The character of the weight torus corresponding to a minuscule-basis index. -/
private noncomputable abbrev minusculeCharacter (a : Fin 56) :
    Multiplicative (Fin 7 →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (DynkinType.e7MinusculeWeight a))

private theorem weightTorusToBaseChangeCoordinateMap_coordinate (i a : Fin 56) :
    (weightTorusToBaseChangeCoordinateMap k).hom
        ((coordinateMap k).hom
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv k 56
            (GeneralLinear.coordinateRingMap k 56 (MvPolynomial.X (i, a))))) =
      if i = a then MonoidAlgebra.single (minusculeCharacter a) (1 : k) else 0 := by
  rw [← _root_.BialgHom.comp_apply, ← _root_.CommHopfAlgCat.hom_comp]
  rw [coordinateMap_comp_weightTorusToBaseChangeCoordinateMap]
  rw [GeneralLinear.hom_weightTorusBaseChangeCoordinateMap,
    GeneralLinear.weightTorusCoordinateBialgHom_X]
  split_ifs with h
  · subst i
    rfl
  · rfl

private theorem torusCorestrict_eq_ofWeights :
    let _ := standardComodule k
    Comodule.Corestrict (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun k (Fin 56)) minusculeCharacter := by
  let _ := standardComodule k
  apply Comodule.ext
    (rho := Comodule.Corestrict
      (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom)
    (sigma := Comodule.ofWeights (Pi.basisFun k (Fin 56)) minusculeCharacter)
  apply (Pi.basisFun k (Fin 56)).ext
  intro a
  rw [Comodule.ofWeights_coact_basis]
  rw [Pi.basisFun_apply]
  rw [Comodule.corestrict_coact_apply
    (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom]
  rw [Comodule.corestrict_coact]
  rw [standardComodule_coact, LinearMap.comp_apply,
    GeneralLinear.standardCoact_apply_basisFun, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  have hweightLinear :
      (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom.toLinearMap =
        (weightTorusToBaseChangeCoordinateMap k).hom.toAlgHom.toLinearMap :=
    (_root_.BialgHom.toAlgHom_toLinearMap
      (weightTorusToBaseChangeCoordinateMap k).hom).symm
  have hcoordinateLinear :
      (coordinateMap k).hom.toCoalgHom.toLinearMap =
        (coordinateMap k).hom.toAlgHom.toLinearMap :=
    (_root_.BialgHom.toAlgHom_toLinearMap
      (coordinateMap k).hom).symm
  rw [hweightLinear, hcoordinateLinear]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    AlgHom.toLinearMap_apply]
  calc
    _ = ∑ i, (Pi.single i (1 : k) : Fin 56 → k) ⊗ₜ[k]
        (if i = a then MonoidAlgebra.single (minusculeCharacter a) (1 : k) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z ↦ (Pi.single i (1 : k) : Fin 56 → k) ⊗ₜ[k] z)
        (weightTorusToBaseChangeCoordinateMap_coordinate k i a)
    _ = _ := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hia
        simp [hia]
      · simp

private theorem minusculeCharacter_injective : Function.Injective minusculeCharacter := by
  intro a b h
  apply DynkinType.e7MinusculeWeight_injective
  apply Finsupp.equivFunOnFinite.symm.injective
  exact Multiplicative.ofAdd.injective h

private theorem weightProj_ofWeights_eq_single (a : Fin 56) (v : Fin 56 → k) :
    let _ : Comodule k (MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ))) (Fin 56 → k) :=
      Comodule.ofWeights (Pi.basisFun k (Fin 56)) minusculeCharacter
    Comodule.weightProj k (Multiplicative (Fin 7 →₀ ℤ)) (Fin 56 → k)
        (minusculeCharacter a) v = Pi.single a (v a) := by
  let _ : Comodule k (MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ))) (Fin 56 → k) :=
    Comodule.ofWeights (Pi.basisFun k (Fin 56)) minusculeCharacter
  dsimp only
  have hv : v = ∑ b, v b • (Pi.single b (1 : k) : Fin 56 → k) := by
    ext b
    simp [Pi.single_apply]
  rw [hv]
  simp only [map_sum]
  rw [Finset.sum_eq_single a]
  · rw [map_smul, Comodule.weightProj_of_mem]
    · ext b
      simp [Pi.single_apply]
    · simpa only [Pi.basisFun_apply] using
        (Comodule.basis_mem_weightSpace_ofWeights
          (Pi.basisFun k (Fin 56)) minusculeCharacter a)
  · intro b _ hba
    rw [map_smul, Comodule.weightProj_of_mem_of_ne]
    · simp
    · exact fun hab ↦ hba (minusculeCharacter_injective hab).symm
    · simpa only [Pi.basisFun_apply] using
        (Comodule.basis_mem_weightSpace_ofWeights
          (Pi.basisFun k (Fin 56)) minusculeCharacter b)
  · simp

/-- Restriction to the weight torus shows that every coordinate component of an invariant
vector remains in the invariant submodule. -/
private theorem single_self_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k))
    {v : Fin 56 → k} (hv : v ∈ N) (a : Fin 56) : Pi.single a (v a) ∈ N := by
  let _ := standardComodule k
  let f := (weightTorusToBaseChangeCoordinateMap k).hom.toCoalgHom
  let _ : Comodule k (MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ))) (Fin 56 → k) :=
    Comodule.Corestrict f
  have hvtorus : v ∈ N.corestrict f :=
    (Subcomodule.mem_corestrict f N v).2 hv
  have hp := Comodule.weightProj_mem_subcomodule (N.corestrict f)
    (minusculeCharacter a) hvtorus
  have hcomodule := torusCorestrict_eq_ofWeights k
  have hpN :
      Comodule.weightProj k (Multiplicative (Fin 7 →₀ ℤ)) (Fin 56 → k)
          (minusculeCharacter a) v ∈ N :=
    (Subcomodule.mem_corestrict f N _).1 hp
  have hproj :
      (let _ : Comodule k (MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)))
          (Fin 56 → k) := Comodule.Corestrict f;
        Comodule.weightProj k (Multiplicative (Fin 7 →₀ ℤ)) (Fin 56 → k)
          (minusculeCharacter a) v) =
      (let _ : Comodule k (MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)))
          (Fin 56 → k) :=
          Comodule.ofWeights (Pi.basisFun k (Fin 56)) minusculeCharacter;
        Comodule.weightProj k (Multiplicative (Fin 7 →₀ ℤ)) (Fin 56 → k)
          (minusculeCharacter a) v) :=
    congrArg (fun c : Comodule k (MonoidAlgebra k (Multiplicative (Fin 7 →₀ ℤ)))
      (Fin 56 → k) ↦
        let _ := c;
        Comodule.weightProj k (Multiplicative (Fin 7 →₀ ℤ)) (Fin 56 → k)
          (minusculeCharacter a) v) hcomodule
  rw [hproj, weightProj_ofWeights_eq_single] at hpN
  exact hpN

private theorem positiveRoot_mulVec_single_sub (i : Fin 7) (a : Fin 56)
    (ha : DynkinType.e7MinusculeWeight a i = -1) :
    (((rootSubgroupPoints (.inl i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 56) k) : Matrix (Fin 56) (Fin 56) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      Pi.single (DynkinType.e7MinusculeReflection i a) 1 := by
  rw [coe_rootSubgroupPoints_inl]
  ext b
  simp [Matrix.one_apply, Pi.single_apply, raisingMatrix_apply, ha]

private theorem negativeRoot_mulVec_single_sub (i : Fin 7) (a : Fin 56)
    (ha : DynkinType.e7MinusculeWeight a i = 1) :
    (((rootSubgroupPoints (.inr i) k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin 56) k) : Matrix (Fin 56) (Fin 56) k) *ᵥ
          Pi.single a 1) - Pi.single a 1 =
      Pi.single (DynkinType.e7MinusculeReflection i a) 1 := by
  rw [coe_rootSubgroupPoints_inr]
  ext b
  simp [Matrix.one_apply, Pi.single_apply, loweringMatrix_apply, ha]

/-- Invariance under the two simple-root points makes membership of coordinate basis vectors
stable under every simple reflection. -/
private theorem single_reflection_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k))
    (a : Fin 56) (i : Fin 7) (ha : Pi.single a 1 ∈ N) :
    Pi.single (DynkinType.e7MinusculeReflection i a) 1 ∈ N := by
  rcases DynkinType.e7MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a i with
    hneg | hzero | hpos
  · have hact := rootSubgroupPoints_mulVec_mem k N (.inl i) ha
    have hsub := N.toSubmodule.sub_mem hact ha
    rwa [positiveRoot_mulVec_single_sub k i a hneg] at hsub
  · rw [(DynkinType.e7MinusculeReflection_eq_self_iff i a).2 hzero]
    exact ha
  · have hact := rootSubgroupPoints_mulVec_mem k N (.inr i) ha
    have hsub := N.toSubmodule.sub_mem hact ha
    rwa [negativeRoot_mulVec_single_sub k i a hpos] at hsub

private theorem single_foldl_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k))
    (l : List (Fin 7)) (a : Fin 56) (ha : Pi.single a 1 ∈ N) :
    Pi.single (l.foldl (fun b i ↦ DynkinType.e7MinusculeReflection i b) a) 1 ∈ N := by
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih =>
      exact ih _ (single_reflection_mem k N a i ha)

private theorem single_mem_of_foldl_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k))
    (l : List (Fin 7)) (a : Fin 56)
    (ha : Pi.single (l.foldl
      (fun b i ↦ DynkinType.e7MinusculeReflection i b) a) 1 ∈ N) :
    Pi.single a 1 ∈ N := by
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih =>
      have hreflected := ih (DynkinType.e7MinusculeReflection i a) ha
      have hback := single_reflection_mem k N
        (DynkinType.e7MinusculeReflection i a) i hreflected
      simpa using hback

private theorem single_one_mem_of_ne_bot
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k)) (hN : N ≠ ⊥)
    (a : Fin 56) : Pi.single a 1 ∈ N := by
  obtain ⟨v, hv, hv0⟩ := N.ne_bot_iff.mp hN
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hv0
  have hb0 : v b ≠ 0 := by simpa using hb
  have hbmem := single_self_mem k N hv b
  have hseed : Pi.single b 1 ∈ N := by
    have hscaled := N.toSubmodule.smul_mem (v b)⁻¹ hbmem
    have heq : (v b)⁻¹ • Pi.single b (v b) = (Pi.single b 1 : Fin 56 → k) := by
      ext c
      by_cases hcb : c = b
      · subst c
        simp [hb0]
      · simp [hcb]
    rwa [heq] at hscaled
  obtain ⟨l, hl⟩ := DynkinType.exists_e7MinusculeReflections_eq b
  have hzero : Pi.single (0 : Fin 56) 1 ∈ N := by
    apply single_mem_of_foldl_mem k N l 0
    rwa [hl]
  obtain ⟨m, hm⟩ := DynkinType.exists_e7MinusculeReflections_eq a
  have := single_foldl_mem k N m 0 hzero
  rwa [hm] at this

/-- **The standard comodule of the specialized type-`E₇` minuscule carrier is simple over
every field.** -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k)) := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have hone : (Pi.single (0 : Fin 56) (1 : k) : Fin 56 → k) ∈
        (⊥ : Subcomodule k (coordinateHopfAlgebra k) (Fin 56 → k)) :=
      h ▸ Subcomodule.mem_top _
    rw [Subcomodule.mem_bot] at hone
    simpa using congrFun hone (0 : Fin 56)
  · intro N
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · right
      apply top_unique
      intro v _
      have hv : v = ∑ a, v a • Pi.single a 1 := by
        ext a
        simp [Pi.single_apply]
      rw [hv]
      exact N.toSubmodule.sum_mem fun a _ ↦
        N.toSubmodule.smul_mem (v a) (single_one_mem_of_ne_bot k N hN a)

end Simple

end TauCeti.E7Minuscule
