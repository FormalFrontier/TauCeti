/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Subsystem

/-!
# Root subgroups inside toral-subsystem carriers

This file proves that a selected represented root subgroup is a closed immersion into its
toral-subsystem carrier under the standard unit root-step hypotheses. It is the toral-subsystem
counterpart of `Kostant.RootSubgroup.Scheme.RootInGenerated`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.
  kostantRootSubgroupToralSubsystemCoordinateMap_surjective`: surjectivity of the factored
  coordinate map under the root-step hypotheses.
* `TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToralSubsystem`:
  the selected root subgroup is a closed immersion into the subsystem carrier.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)
variable (S : Set I) {r s : Fin n} {c : ℤ}
variable (hnil : ∀ j ∈ S, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (i : S)

/-- A surjective selected root coordinate map remains surjective after factorization through the
toral-subsystem carrier. -/
theorem kostantRootSubgroupToralSubsystemCoordinateMap_surjective_of_surjective
    (hi : Function.Surjective
      (kostantRootSubgroupCoordinateMap e h ρ M hM i.1 (hnil i.1 i.2) b).hom) :
    Function.Surjective
      (kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i).hom := by
  intro y
  obtain ⟨x, hx⟩ := hi y
  refine ⟨(CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
    (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil)).hom x, ?_⟩
  change ((CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
      (kostantToralSubsystemDefiningIdeal e h ρ M hM b wt S hnil) ≫
    kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i).hom x) = y
  rw [mkQuotient_comp_kostantRootSubgroupToralSubsystemCoordinateMap]
  exact hx

/-- If a selected root coordinate map is surjective, its factorization through the
toral-subsystem carrier is a closed immersion. -/
theorem isClosedImmersion_kostantRootSubgroupToToralSubsystem_of_surjective
    (hi : Function.Surjective
      (kostantRootSubgroupCoordinateMap e h ρ M hM i.1 (hnil i.1 i.2) b).hom) :
    IsClosedImmersion
      (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom.left := by
  rw [kostantRootSubgroupToToralSubsystem_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (AdditiveGroup.groupScheme_def ℤ)
    (kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i)).2
    (kostantRootSubgroupToralSubsystemCoordinateMap_surjective_of_surjective
      e h ρ M hM b wt S hnil i hi)

variable (hc : IsUnit c)
variable (hstep :
  ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i.1)) (b s : V) = c • (b r : V))
variable (hsq : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i.1))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i.1)) (b s : V)) = 0)

include hc hstep hsq in
/-- The coordinate map of a selected root subgroup remains surjective after factorization through
the toral-subsystem carrier. -/
theorem kostantRootSubgroupToralSubsystemCoordinateMap_surjective :
    Function.Surjective
      (kostantRootSubgroupToralSubsystemCoordinateMap e h ρ M hM b wt S hnil i).hom :=
  kostantRootSubgroupToralSubsystemCoordinateMap_surjective_of_surjective
    e h ρ M hM b wt S hnil i
    (kostantRootSubgroupCoordinateMap_surjective
      e h ρ M hM i.1 (hnil i.1 i.2) b hc hstep hsq)

include hc hstep hsq in
/-- A selected root subgroup is a closed immersion into its toral-subsystem carrier. -/
theorem isClosedImmersion_kostantRootSubgroupToToralSubsystem :
    IsClosedImmersion
      (kostantRootSubgroupToToralSubsystem e h ρ M hM b wt S hnil i).hom.hom.left :=
  isClosedImmersion_kostantRootSubgroupToToralSubsystem_of_surjective
    e h ρ M hM b wt S hnil i
    (kostantRootSubgroupCoordinateMap_surjective
      e h ρ M hM i.1 (hnil i.1 i.2) b hc hstep hsq)

end TauCeti.UniversalEnvelopingAlgebra
