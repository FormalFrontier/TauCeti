/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic

/-!
# Functorial points of the full-weight type-D spin carrier

`TauCeti.TypeDSpinCarrier.points n hn A` realizes the `A`-valued points of the full-weight
type-`Dₙ` spin carrier as a subgroup of `GL_(2^n)(A)`. This file supplies the group homomorphism
induced by a homomorphism of value rings, together with its identity, composition, and
injectivity laws.

## Main declarations

* `TauCeti.TypeDSpinCarrier.pointsMap`: the map on carrier points induced by a ring homomorphism.
* `TauCeti.TypeDSpinCarrier.pointsMap_id` and
  `TauCeti.TypeDSpinCarrier.pointsMap_comp`: functoriality of the induced maps.
* `TauCeti.TypeDSpinCarrier.pointsMap_injective`: injectivity when the ring homomorphism is
  injective.
* `TauCeti.TypeDSpinCarrier.pointsMap_rootSubgroupPoints` and
  `TauCeti.TypeDSpinCarrier.pointsMap_weightTorusPoints`: naturality of the distinguished
  root-subgroup and weight-torus families.

The interface follows the analogous full-weight type-`A`, type-`C`, and type-`E₆` carrier
interfaces. It advances the functorial-points target in Layer 9 of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti.TypeDSpinCarrier

universe v w

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

section Map

variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]

/-- The map on type-`Dₙ` spin-carrier points induced by a homomorphism of value rings. It is the
entrywise map on the ambient general linear group, restricted to the carrier subgroup. -/
def pointsMap (f : A →+* B) : points n hn A →* points n hn B :=
  ((MulEquiv.subgroupCongr (points_def n hn B)).symm.toMonoidHom).comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup (dimension n) (definingIdeal n hn)
          f.toIntAlgHom).comp
      (MulEquiv.subgroupCongr (points_def n hn A)).toMonoidHom)

/-- The induced map on type-`Dₙ` spin-carrier points is the entrywise matrix map. -/
@[simp]
theorem coe_pointsMap (f : A →+* B) (g : points n hn A) :
    (pointsMap n hn f g : Matrix.GeneralLinearGroup (Fin (dimension n)) B) =
      Matrix.GeneralLinearGroup.map f g := by
  have hring : f.toIntAlgHom.toRingHom = f := RingHom.ext (RingHom.toIntAlgHom_apply f)
  rw [pointsMap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply, GeneralLinear.coe_mapHopfIdealPointsSubgroup,
    MulEquiv.subgroupCongr_apply, hring]

/-- Entrywise, the induced map applies the homomorphism of value rings to each matrix entry. -/
theorem coe_pointsMap_apply (f : A →+* B) (g : points n hn A)
    (i j : Fin (dimension n)) :
    ((pointsMap n hn f g : Matrix.GeneralLinearGroup (Fin (dimension n)) B) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) i j) := by
  rw [coe_pointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism induces the identity on type-`Dₙ` spin-carrier points. -/
@[simp]
theorem pointsMap_id : pointsMap n hn (RingHom.id A) = MonoidHom.id _ := by
  have hid : (RingHom.id A).toIntAlgHom = AlgHom.id ℤ A := AlgHom.ext fun _ ↦ rfl
  rw [pointsMap, hid, GeneralLinear.mapHopfIdealPointsSubgroup_id]
  apply MonoidHom.ext
  intro g
  exact (MulEquiv.subgroupCongr (points_def n hn A)).symm_apply_apply g

/-- The induced maps on type-`Dₙ` spin-carrier points compose. -/
@[simp]
theorem pointsMap_comp {C : Type*} [CommRing C] (f : A →+* B) (g : B →+* C) :
    pointsMap n hn (g.comp f) = (pointsMap n hn g).comp (pointsMap n hn f) := by
  have hcomp : (g.comp f).toIntAlgHom = g.toIntAlgHom.comp f.toIntAlgHom :=
    AlgHom.ext fun _ ↦ rfl
  apply MonoidHom.ext
  intro x
  simp only [pointsMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcomp,
    GeneralLinear.mapHopfIdealPointsSubgroup_comp, MulEquiv.apply_symm_apply]

/-- An injective homomorphism of value rings induces an injective map on type-`Dₙ` spin-carrier
points. -/
theorem pointsMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (pointsMap n hn f) := by
  rw [pointsMap]
  exact (MulEquiv.subgroupCongr (points_def n hn B)).symm.injective.comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup_injective
      (dimension n) (definingIdeal n hn) hf).comp
        (MulEquiv.subgroupCongr (points_def n hn A)).injective)

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem pointsMap_rootSubgroupPoints (f : A →+* B) (k : Fin n ⊕ Fin n)
    (u : Multiplicative A) :
    pointsMap n hn f (rootSubgroupPoints n hn k A u) =
      rootSubgroupPoints n hn k B
        (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the split spin weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem pointsMap_weightTorusPoints (f : A →+* B) (s : Fin n → Aˣ) :
    pointsMap n hn f (weightTorusPoints n hn A s) =
      weightTorusPoints n hn B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := (lattice n).toAddSubgroup) (b := latticeBasis n) (wt := basisWeight n) f s

end Map

end

end TauCeti.TypeDSpinCarrier
