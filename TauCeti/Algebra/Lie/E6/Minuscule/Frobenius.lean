/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
public import
  TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Frobenius

/-!
# The Frobenius of the full-weight type-E6 minuscule carrier

The type-`E₆` minuscule carrier is the explicit Kostant toral closure over `ℤ` built from the
27-dimensional minuscule representation and its admissible full-weight lattice. Over a commutative
ring `A` of exponential characteristic `p`, entrywise `p ^ k`-th powers preserve its defining Hopf
ideal and therefore give a group endomorphism of its `A`-valued points.

This file names that endomorphism `TauCeti.E6Minuscule.frobenius` and records its characteristic
equations:

```text
F (g)ᵢⱼ = gᵢⱼ ^ (p ^ k),
F (xᵢ(u)) = xᵢ(u ^ (p ^ k)),
F (t(s)) = t(s ^ (p ^ k)).
```

The zeroth iterate is the identity and exponents add under composition. The fixed points are the
points of the same carrier over the Frobenius-fixed subring. No reductivity, finiteness, or
simplicity statement is involved.

## Main declarations

* `TauCeti.E6Minuscule.frobenius`: the `p ^ k`-power Frobenius on the carrier's points.
* `TauCeti.E6Minuscule.coe_frobenius` and `coe_frobenius_apply`: its matrix and entrywise actions.
* `TauCeti.E6Minuscule.frobenius_rootSubgroupPoints`: its action on every numbered simple-root
  subgroup.
* `TauCeti.E6Minuscule.frobenius_weightTorusPoints`: its action on the split weight torus.
* `TauCeti.E6Minuscule.frobenius_zero` and `frobenius_add`: its iteration laws.
* `TauCeti.E6Minuscule.map_subtype_fixedSubgroup_frobenius_eq`: the identification of its fixed
  points with points over the fixed subring.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* The formal organization follows the carrier specializations
  `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Frobenius` and
  `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Frobenius`; all mathematical content is
  transported from the generic
  `TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius` API.

This advances the Layer 9 target "points over an algebraically closed field as a group,
functorially in the field" of `TauCetiRoadmap/ReductiveGroups/README.md`, which names the
`q`-power Frobenius as its first consumer-facing case. Milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md` consumes this endomorphism and its root-subgroup equation
as the ordinary `E₆(q)` Steinberg map.
-/

public section

open WithConv
open scoped Matrix

namespace TauCeti.E6Minuscule

universe v

noncomputable section

open TauCeti.DynkinType

variable (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

private theorem points_eq_kostantToralPointsSubgroup :
    points A =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight A := by
  ext g
  rw [mem_points_iff, definingIdeal_def,
    TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff]

/-- The presentation of the named minuscule-carrier points as the generic Kostant toral-closure
points. -/
private def pointsEquivKostantToralPoints :
    points A ≃*
      TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight A :=
  MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup A)

@[simp]
private theorem coe_pointsEquivKostantToralPoints (g : points A) :
    (pointsEquivKostantToralPoints A g :
      _root_.Matrix.GeneralLinearGroup (Fin 27) A) = g :=
  rfl

/-- **The `p ^ k`-power Frobenius endomorphism of the full-weight type-`E₆` minuscule carrier.**

For `p` prime, `0 < k`, and `A` an algebraic closure of `ZMod p`, this is the Frobenius component
of the ordinary `E₆(p ^ k)` Steinberg map. -/
def frobenius : points A →* points A :=
  (pointsEquivKostantToralPoints A).symm.toMonoidHom.comp
    ((TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A).comp
        (pointsEquivKostantToralPoints A).toMonoidHom)

private theorem pointsEquivKostantToralPoints_frobenius (g : points A) :
    pointsEquivKostantToralPoints A (frobenius p k A g) =
      TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
          rw [TauCeti.serreKostantForm_def]
          exact hu) hv)
        isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A
        (pointsEquivKostantToralPoints A g) := by
  simp only [frobenius, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]

/-- The Frobenius endomorphism of the minuscule carrier acts by entrywise Frobenius.

This is not a `simp` lemma because `coe_frobenius_apply` is the canonical coefficient-level
normal form. -/
theorem coe_frobenius (g : points A) :
    (frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) =
      _root_.Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  have h := congrArg Subtype.val (pointsEquivKostantToralPoints_frobenius p k A g)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  simpa only [coe_pointsEquivKostantToralPoints] using h

/-- Entrywise, the Frobenius endomorphism raises each matrix coefficient to its `p ^ k`-th
power. -/
@[simp]
theorem coe_frobenius_apply (g : points A) (i j : Fin 27) :
    ((frobenius p k A g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) :
        _root_.Matrix (Fin 27) (Fin 27) A) i j =
      ((g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) :
        _root_.Matrix (Fin 27) (Fin 27) A) i j ^ p ^ k := by
  have h := TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius_apply
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A
      (pointsEquivKostantToralPoints A g) i j
  rw [← pointsEquivKostantToralPoints_frobenius] at h
  simpa only [coe_pointsEquivKostantToralPoints] using h

/-- **Frobenius raises the parameter of every numbered type-`E₆` simple-root subgroup to its
`p ^ k`-th power.** -/
@[simp]
theorem frobenius_rootSubgroupPoints (i : Fin 6 ⊕ Fin 6) (u : Multiplicative A) :
    frobenius p k A (rootSubgroupPoints i A u) =
      rootSubgroupPoints i A
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  apply (pointsEquivKostantToralPoints A).injective
  rw [pointsEquivKostantToralPoints_frobenius]
  apply Subtype.ext
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius,
    coe_pointsEquivKostantToralPoints, coe_rootSubgroupPoints,
    coe_pointsEquivKostantToralPoints, coe_rootSubgroupPoints]
  have h := congrArg Subtype.val
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_kostantRootSubgroupMatrix
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A i u)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  exact h

/-- **Frobenius raises every coordinate of the pinned split torus to its `p ^ k`-th power.** -/
@[simp]
theorem frobenius_weightTorusPoints (s : Fin 6 → Aˣ) :
    frobenius p k A (weightTorusPoints A s) = weightTorusPoints A (s ^ p ^ k) := by
  apply (pointsEquivKostantToralPoints A).injective
  rw [pointsEquivKostantToralPoints_frobenius]
  apply Subtype.ext
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius,
    coe_pointsEquivKostantToralPoints, coe_weightTorusPoints,
    coe_pointsEquivKostantToralPoints, coe_weightTorusPoints]
  have h := congrArg Subtype.val
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_kostantTorusMatrix
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A s)
  rw [TauCeti.UniversalEnvelopingAlgebra.coe_kostantToralFrobenius] at h
  simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using h

/-- The zeroth Frobenius iterate is the identity on the minuscule carrier's point group. -/
@[simp]
theorem frobenius_zero : frobenius p 0 A = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply (pointsEquivKostantToralPoints A).injective
  rw [pointsEquivKostantToralPoints_frobenius, MonoidHom.id_apply]
  have h := DFunLike.congr_fun
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_zero
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p A)
    (pointsEquivKostantToralPoints A g)
  simpa only [MonoidHom.id_apply] using h

/-- Frobenius iterates add under composition on the minuscule carrier's point group. -/
theorem frobenius_add (m : ℕ) :
    frobenius p (k + m) A = (frobenius p k A).comp (frobenius p m A) := by
  apply MonoidHom.ext
  intro g
  apply (pointsEquivKostantToralPoints A).injective
  rw [pointsEquivKostantToralPoints_frobenius, MonoidHom.comp_apply,
    pointsEquivKostantToralPoints_frobenius, pointsEquivKostantToralPoints_frobenius]
  exact DFunLike.congr_fun
    (TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_add
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A m)
    (pointsEquivKostantToralPoints A g)

/-- A minuscule-carrier point is fixed by Frobenius exactly when all of its matrix entries lie in
the Frobenius-fixed subring. -/
@[simp]
theorem frobenius_eq_self_iff (g : points A) :
    frobenius p k A g = g ↔
      ∀ i j, ((g : _root_.Matrix.GeneralLinearGroup (Fin 27) A) :
        _root_.Matrix (Fin 27) (Fin 27) A) i j ∈ frobeniusFixedSubring A p k := by
  have h := TauCeti.UniversalEnvelopingAlgebra.kostantToralFrobenius_eq_self_iff
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A
      (pointsEquivKostantToralPoints A g)
  rw [← pointsEquivKostantToralPoints_frobenius] at h
  simp only [coe_pointsEquivKostantToralPoints] at h
  constructor
  · intro hg
    exact h.mp (congrArg (pointsEquivKostantToralPoints A) hg)
  · intro hg
    exact (pointsEquivKostantToralPoints A).injective (h.mpr hg)

/-- **The Frobenius-fixed points of the full-weight minuscule carrier are its points over the
Frobenius-fixed subring.** -/
theorem map_subtype_fixedSubgroup_frobenius_eq :
    (fixedSubgroup (frobenius p k A)).map (points A).subtype =
      (points ↥(frobeniusFixedSubring A p k)).map
        (_root_.Matrix.GeneralLinearGroup.map (frobeniusFixedSubring A p k).subtype) := by
  rw [TauCeti.map_subtype_fixedSubgroup_of_coe_eq (frobenius p k A) _
    (coe_frobenius p k A)]
  rw [points_eq_kostantToralPointsSubgroup, points_eq_kostantToralPointsSubgroup]
  rw [← TauCeti.UniversalEnvelopingAlgebra.map_subtype_fixedSubgroup_kostantToralFrobenius]
  exact
    TauCeti.UniversalEnvelopingAlgebra.map_subtype_fixedSubgroup_kostantToralFrobenius_eq
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      (fun _ hu _ hv ↦ rep_serreKostantForm_mem_lattice (by
        rw [TauCeti.serreKostantForm_def]
        exact hu) hv)
      isNilpotent_rep_serreRootGenerator latticeBasis e6MinusculeWeight p k A

end


end TauCeti.E6Minuscule
