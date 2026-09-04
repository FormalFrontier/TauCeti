/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Cohomology
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic

/-!
# Functoriality of the cohomology algebra

A morphism of differential graded algebras induces a graded algebra homomorphism on cohomology,
compatibly with identities and composition.

The induced map is obtained in two stages.  Commutation with the differentials first restricts the
underlying algebra homomorphism to cycles and sends boundaries to boundaries.  The quotient
universal property then descends this map to cohomology.  Its preservation of the cohomological
grading follows from the description of a homogeneous cohomology class by a homogeneous cycle
representative.

Functoriality is what makes cohomology a usable invariant: it is the source of the notion of a
quasi-isomorphism, a morphism inducing an isomorphism on cohomology, and it is the shadow on
cohomology of the comparison between differential graded algebras and `A∞` algebras.

## Main definitions

* `TauCeti.DGAlgHom.cycles`: the induced graded algebra homomorphism on cycles.
* `TauCeti.DGAlgHom.cohomology`: the induced graded algebra homomorphism on cohomology.

## Main results

* `TauCeti.DGAlgHom.cohomology_mk`: the cohomology map sends the class of a cycle to the class of
  its image.
* `TauCeti.DGAlgHom.cohomology_id` and `TauCeti.DGAlgHom.cohomology_comp`: passage to cohomology
  preserves identities and composition.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace DGAlgHom

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {hC : IsDGAlgebra 𝒞 dC}

/-- A DG algebra morphism restricts to a graded algebra homomorphism on cycles. -/
def cycles (f : DGAlgHom hA hB) : hA.cyclesDeg →ₐᵍ[R] hB.cyclesDeg where
  toFun z := ⟨f (z : A), by
    rw [hB.mem_cycles, f.map_d, hA.mem_cycles.mp z.2, map_zero]⟩
  map_one' := Subtype.ext (map_one f.toGradedAlgHom)
  map_mul' x y := Subtype.ext (map_mul f.toGradedAlgHom (x : A) (y : A))
  map_zero' := Subtype.ext (map_zero f.toGradedAlgHom)
  map_add' x y := Subtype.ext (map_add f.toGradedAlgHom (x : A) (y : A))
  commutes' r := Subtype.ext (f.toGradedAlgHom.commutes r)
  map_mem hz :=
    hB.mem_cyclesDeg.mpr (f.toGradedAlgHom.map_mem (hA.mem_cyclesDeg.mp hz))

@[simp]
theorem cycles_apply_coe (f : DGAlgHom hA hB) (z : hA.cycles) :
    ((f.cycles z : hB.cycles) : B) = f (z : A) := (rfl)

/-- Restriction to cycles preserves identity morphisms. -/
@[simp]
theorem cycles_id (hA : IsDGAlgebra 𝒜 dA) :
    (DGAlgHom.id hA).cycles = GradedAlgHom.id R hA.cyclesDeg := by
  apply GradedAlgHom.ext
  intro z
  apply Subtype.ext
  simp only [cycles_apply_coe, id_apply, GradedAlgHom.id_apply]

/-- Restriction to cycles preserves composition. -/
@[simp]
theorem cycles_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).cycles = g.cycles.comp f.cycles := by
  apply GradedAlgHom.ext
  intro z
  apply Subtype.ext
  simp only [cycles_apply_coe, comp_apply, GradedAlgHom.comp_apply]

/-- The restriction of a DG algebra morphism to cycles sends boundaries to boundaries. -/
theorem cycles_map_mem_boundaries (f : DGAlgHom hA hB) {z : hA.cycles}
    (hz : z ∈ hA.boundaries) : f.cycles z ∈ hB.boundaries := by
  rw [hA.mem_boundaries] at hz
  obtain ⟨a, ha⟩ := hz
  refine hB.mem_boundaries.mpr ⟨f a, ?_⟩
  rw [cycles_apply_coe, ← ha, f.map_d]

/-- The composite of the map on cycles with the projection onto cohomology kills the boundaries.
This is the hypothesis feeding the universal property of the quotient below. -/
private theorem quotientMk_comp_cycles_eq_zero (f : DGAlgHom hA hB) (z : hA.cycles)
    (hz : z ∈ hA.boundaries.asIdeal) :
    ((Ideal.Quotient.mkₐ R hB.boundaries.asIdeal).comp f.cycles.toAlgHom) z = 0 := by
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hB.quotientMk_eq_zero_iff]
  exact f.cycles_map_mem_boundaries (TwoSidedIdeal.mem_asIdeal.mp hz)

/-- The algebra homomorphism induced on cohomology, before its compatibility with the gradings is
recorded in `TauCeti.DGAlgHom.cohomology`. -/
private noncomputable def cohomologyAlgHom (f : DGAlgHom hA hB) :
    hA.Cohomology →ₐ[R] hB.Cohomology :=
  Ideal.Quotient.liftₐ hA.boundaries.asIdeal
    ((Ideal.Quotient.mkₐ R hB.boundaries.asIdeal).comp f.cycles.toAlgHom)
    f.quotientMk_comp_cycles_eq_zero

/-- Evaluation of the lifted algebra homomorphism on the class of a cycle. -/
private theorem cohomologyAlgHom_mk (f : DGAlgHom hA hB) (z : hA.cycles) :
    f.cohomologyAlgHom (Ideal.Quotient.mk hA.boundaries.asIdeal z) =
      Ideal.Quotient.mk hB.boundaries.asIdeal (f.cycles z) := by
  simp only [cohomologyAlgHom, Ideal.Quotient.liftₐ_apply]
  -- `Ideal.Quotient.lift_mk` evaluates the lift; what remains is the unfolding of the coercions
  -- of `Ideal.Quotient.mkₐ` and of the composite to a ring homomorphism.
  exact Ideal.Quotient.lift_mk _ _ _

/-- A DG algebra morphism induces a graded algebra homomorphism on cohomology. -/
noncomputable def cohomology (f : DGAlgHom hA hB) :
    hA.cohomologyGrading →ₐᵍ[R] hB.cohomologyGrading where
  toFun := f.cohomologyAlgHom
  map_one' := map_one f.cohomologyAlgHom
  map_mul' := map_mul f.cohomologyAlgHom
  map_zero' := map_zero f.cohomologyAlgHom
  map_add' := map_add f.cohomologyAlgHom
  commutes' := f.cohomologyAlgHom.commutes
  map_mem := fun {p} {x} hx => by
    obtain ⟨z, hz, rfl⟩ := hA.mem_cohomologyGrading.mp hx
    exact hB.mem_cohomologyGrading.mpr
      ⟨f.cycles z, f.toGradedAlgHom.map_mem hz, (f.cohomologyAlgHom_mk z).symm⟩

/-- The cohomology map sends the class of a cycle to the class of its image. -/
@[simp]
theorem cohomology_mk (f : DGAlgHom hA hB) (z : hA.cycles) :
    f.cohomology (Ideal.Quotient.mk hA.boundaries.asIdeal z) =
      Ideal.Quotient.mk hB.boundaries.asIdeal (f.cycles z) :=
  f.cohomologyAlgHom_mk z

/-- Passage to cohomology sends the identity DG algebra morphism to the identity graded algebra
homomorphism. -/
@[simp]
theorem cohomology_id (hA : IsDGAlgebra 𝒜 dA) :
    (DGAlgHom.id hA).cohomology = GradedAlgHom.id R hA.cohomologyGrading := by
  apply GradedAlgHom.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [cohomology_mk, cycles_id, GradedAlgHom.id_apply]

/-- Passage to cohomology preserves composition of DG algebra morphisms. -/
@[simp]
theorem cohomology_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).cohomology = g.cohomology.comp f.cohomology := by
  apply GradedAlgHom.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [cohomology_mk, GradedAlgHom.comp_apply, cycles_comp]

end DGAlgHom

end TauCeti
