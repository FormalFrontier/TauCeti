/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem

/-!
# Base change of a toral Kostant subsystem

For a set `S` of root indices, its toral Kostant subsystem over `ℤ` is the closed subgroup scheme
of `GLₙ` generated jointly by the represented root subgroups indexed by `S` and a represented split
torus. Its coordinate ring is the general-linear coordinate Hopf algebra modulo the corresponding
toral-subsystem defining ideal.

This file transports that presentation along `ℤ → A`. The base-changed defining ideal cuts out
the specialized carrier, its quotient is canonically the base change of the original coordinate
ring, and the factored root-subgroup and torus maps base-change without being chosen again.

The construction deliberately stays in the base-changed coordinate algebras. Identifying the
base change of `O(GLₙ/ℤ)`, `O(𝔾ₐ/ℤ)`, and `O(T/ℤ)` with the corresponding coordinate Hopf
algebras constructed directly over `A` is the next, independent comparison step.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantToralSubsystemBaseChangeIdeal`: the base change of the
  ideal defining the toral subsystem.
* `TauCeti.UniversalEnvelopingAlgebra.kostantToralSubsystemBaseChangeIso`: the quotient by that
  ideal is the base change of the toral subsystem's coordinate ring.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralSubsystemBaseChangeCoordinateMap`:
  the base-changed factored root-subgroup map.
* `TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToralSubsystemBaseChangeCoordinateMap`:
  the base-changed factored torus map.

## References

This is the base-change compatibility in the pinned Chevalley--Demazure construction; see
R. W. Carter, *Simple Groups of Lie Type*, §4.4, and B. Conrad, *Reductive Group Schemes*, §1.
It advances Layer 9 of the ReductiveGroups roadmap, whose base-changed pinned carrier is consumed
by milestone L0 of the CFSGStatement roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (S : Set I)
variable (hnil : ∀ i ∈ S, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (A : Type*) [CommRing A]

/-- The base change along `ℤ → A` of the Hopf ideal defining the toral Kostant subsystem. -/
noncomputable def kostantToralSubsystemBaseChangeIdeal :
    HopfIdeal A
      (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n)) :=
  CommHopfAlgCat.baseChangeHopfIdeal
    (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)

/-- The specialized defining ideal is the generic base change of the ideal of the toral subsystem
over `ℤ`. -/
@[simp]
theorem kostantToralSubsystemBaseChangeIdeal_def :
    kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A =
      CommHopfAlgCat.baseChangeHopfIdeal
        (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil) := by
  unfold kostantToralSubsystemBaseChangeIdeal
  rfl

/-- Quotienting by the specialized toral ideal agrees with base-changing the coordinate ring of
the toral subsystem. -/
noncomputable def kostantToralSubsystemBaseChangeIso :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)) :=
  CommHopfAlgCat.quotientBaseChangeIso
    (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)

/-- The base-change identification is compatible with the quotient morphism presenting the toral
subsystem over `ℤ`. -/
@[simp]
theorem mkQuotient_comp_kostantToralSubsystemBaseChangeIso_hom :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
          (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) ≫
        (kostantToralSubsystemBaseChangeIso e h ρ M hM b wt S hnil A).hom =
      CommHopfAlgCat.baseChangeMap
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)) := by
  unfold kostantToralSubsystemBaseChangeIdeal kostantToralSubsystemBaseChangeIso
  exact CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom (K := A)
    (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)

/-- The `i`th factored root-subgroup coordinate map after base change: the base change of the map
into the toral subsystem, read through its specialized quotient presentation. -/
noncomputable def kostantRootSubgroupToralSubsystemBaseChangeCoordinateMap (i : S) :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) ⟶
      CommHopfAlgCat.baseChange (K := A) (AdditiveGroup.coordinateHopfAlgebra ℤ) :=
  (kostantToralSubsystemBaseChangeIso e h ρ M hM b wt S hnil A).hom ≫
    CommHopfAlgCat.baseChangeMap
      (kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i)

/-- The specialized quotient map followed by the factored root-subgroup map is the base change of
the original represented root-subgroup coordinate map. -/
@[simp]
theorem mkQuotient_comp_kostantRootSubgroupToralSubsystemBaseChangeCoordinateMap (i : S) :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
          (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) ≫
        kostantRootSubgroupToralSubsystemBaseChangeCoordinateMap e h ρ M hM b wt S hnil A i =
      CommHopfAlgCat.baseChangeMap
        (kostantRootSubgroupCoordinateMap e h ρ M hM i.1 (hnil i.1 i.2) b) := by
  rw [kostantRootSubgroupToralSubsystemBaseChangeCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralSubsystemBaseChangeIso_hom,
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    mkQuotient_comp_kostantRootSubgroupToralSubsystemCoordinateMap]

/-- The factored weight-torus coordinate map after base change: the base change of the map into
the toral subsystem, read through its specialized quotient presentation. -/
noncomputable def kostantWeightTorusToralSubsystemBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) ⟶
      CommHopfAlgCat.baseChange (K := A)
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj :=
  (kostantToralSubsystemBaseChangeIso e h ρ M hM b wt S hnil A).hom ≫
    CommHopfAlgCat.baseChangeMap
      (kostantWeightTorusToralSubsystemCoordinateMap e h ρ M hM b wt S hnil)

/-- The specialized quotient map followed by the factored weight-torus map is the base change of
the original represented weight-torus coordinate map. -/
@[simp]
theorem mkQuotient_comp_kostantWeightTorusToralSubsystemBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
          (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A) ≫
        kostantWeightTorusToralSubsystemBaseChangeCoordinateMap e h ρ M hM b wt S hnil A =
      CommHopfAlgCat.baseChangeMap (GeneralLinear.weightTorusCoordinateMap wt) := by
  rw [kostantWeightTorusToralSubsystemBaseChangeCoordinateMap, ← Category.assoc,
    mkQuotient_comp_kostantToralSubsystemBaseChangeIso_hom,
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    mkQuotient_comp_kostantWeightTorusToralSubsystemCoordinateMap]

/-- Every base-changed represented root-subgroup map kills the specialized toral defining ideal. -/
theorem kostantToralSubsystemBaseChangeIdeal_toIdeal_le_root_ker (i : S) :
    (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A).toIdeal ≤
      RingHom.ker
        (CommHopfAlgCat.baseChangeMap (K := A)
          (kostantRootSubgroupCoordinateMap e h ρ M hM i.1
            (hnil i.1 i.2) b)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.baseChangeHopfIdeal_toIdeal_le_ker_baseChangeMap
    (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)
    (kostantRootSubgroupCoordinateMap e h ρ M hM i.1 (hnil i.1 i.2) b)
    (kostantToralSubsystemDefiningIdeal_toIdeal_le_root_ker e h ρ M hM b wt S hnil i)

/-- The base-changed represented weight-torus map kills the specialized toral defining ideal. -/
theorem kostantToralSubsystemBaseChangeIdeal_toIdeal_le_torus_ker :
    (kostantToralSubsystemBaseChangeIdeal e h ρ M hM b wt S hnil A).toIdeal ≤
      RingHom.ker
        (CommHopfAlgCat.baseChangeMap (K := A)
          (GeneralLinear.weightTorusCoordinateMap wt)).hom.toAlgHom.toRingHom :=
  CommHopfAlgCat.baseChangeHopfIdeal_toIdeal_le_ker_baseChangeMap
    (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)
    (GeneralLinear.weightTorusCoordinateMap wt)
    (kostantToralSubsystemDefiningIdeal_toIdeal_le_torus_ker e h ρ M hM b wt S hnil)

end TauCeti.UniversalEnvelopingAlgebra
