/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.Algebra.Homology.DG.Algebra.Cohomology

/-!
# Morphisms of differential graded algebras

A morphism of differential graded algebras is a graded algebra homomorphism that commutes with the
differentials.  This file bundles those maps, supplies their identity and composition operations,
and constructs the induced graded algebra homomorphism on cohomology.

The cohomology map is obtained in two stages.  Commutation with the differentials first restricts
the underlying algebra homomorphism to cycles and sends boundaries to boundaries.  The quotient
universal property then descends this map to cohomology.  Its preservation of the cohomological
grading follows from the existing description of a homogeneous cohomology class by a homogeneous
cycle representative.

## Main definitions

* `TauCeti.DGAlgHom`: a graded algebra homomorphism commuting with the differentials.
* `TauCeti.DGAlgHom.cycles`: the induced graded algebra homomorphism on cycles.
* `TauCeti.DGAlgHom.cohomology`: the induced graded algebra homomorphism on cohomology.

## Main results

* `TauCeti.DGAlgHom.cohomology_mk`: the cohomology map sends the class of a cycle to the class of
  its image.
* `TauCeti.DGAlgHom.cohomology_id` and `TauCeti.DGAlgHom.cohomology_comp`: passage to cohomology
  preserves identities and composition.

This advances `TauCetiRoadmap/DGAInfinity/README.md`, Layer 1, item "DG algebras, categories,
modules, and bimodules", specifically the requested DG algebra morphisms.  It also makes the
graded cohomology algebra constructed in `TauCeti.Algebra.Homology.DG.Algebra.Cohomology`
functorial, which is needed for quasi-isomorphisms and for the later comparison with `A∞`
morphisms.

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

/-- A morphism of differential graded algebras: a degree-zero graded algebra homomorphism that
commutes with the differentials. -/
structure DGAlgHom (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB)
    extends 𝒜 →ₐᵍ[R] ℬ where
  /-- A DG algebra morphism commutes with the differentials. -/
  map_d' (a : A) : dB (toGradedAlgHom a) = toGradedAlgHom (dA a)

namespace DGAlgHom

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {hC : IsDGAlgebra 𝒞 dC}

/-- Two DG algebra morphisms are equal if their underlying graded algebra homomorphisms are equal.
-/
theorem toGradedAlgHom_injective :
    Function.Injective (toGradedAlgHom : DGAlgHom hA hB → 𝒜 →ₐᵍ[R] ℬ) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  cases h
  rfl

instance : FunLike (DGAlgHom hA hB) A B where
  coe f := f.toGradedAlgHom
  coe_injective _f _g h := toGradedAlgHom_injective <| GradedAlgHom.ext fun a => congrFun h a

instance : GradedFunLike (DGAlgHom hA hB) 𝒜 ℬ where
  map_mem f := f.toGradedAlgHom.map_mem

instance : AlgHomClass (DGAlgHom hA hB) R A B where
  map_add f := f.toGradedAlgHom.map_add
  map_zero f := f.toGradedAlgHom.map_zero
  map_mul f := f.toGradedAlgHom.map_mul
  map_one f := f.toGradedAlgHom.map_one
  commutes f := f.toGradedAlgHom.commutes

instance : CoeOut (DGAlgHom hA hB) (𝒜 →ₐᵍ[R] ℬ) := ⟨toGradedAlgHom⟩

@[simp]
theorem coe_toGradedAlgHom (f : DGAlgHom hA hB) : ⇑f.toGradedAlgHom = f := rfl

@[simp]
theorem coe_mk (f : 𝒜 →ₐᵍ[R] ℬ) (hf) : ⇑(DGAlgHom.mk f hf : DGAlgHom hA hB) = f := rfl

/-- Two DG algebra morphisms are equal if they agree on every element. -/
@[ext]
theorem ext {f g : DGAlgHom hA hB} (h : ∀ a, f a = g a) : f = g :=
  toGradedAlgHom_injective <| GradedAlgHom.ext h

/-- A DG algebra morphism commutes with the differentials. -/
@[simp]
theorem map_d (f : DGAlgHom hA hB) (a : A) : dB (f a) = f (dA a) :=
  f.map_d' a

/-- The identity morphism of a differential graded algebra. -/
protected def id (hA : IsDGAlgebra 𝒜 dA) : DGAlgHom hA hA where
  toGradedAlgHom := GradedAlgHom.id R 𝒜
  map_d' _ := rfl

@[simp]
theorem coe_id (hA : IsDGAlgebra 𝒜 dA) : ⇑(DGAlgHom.id hA) = _root_.id := (rfl)

@[simp]
theorem id_apply (hA : IsDGAlgebra 𝒜 dA) (a : A) : DGAlgHom.id hA a = a :=
  congrFun (coe_id hA) a

/-- Composition of morphisms of differential graded algebras. -/
def comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) : DGAlgHom hA hC where
  toGradedAlgHom := g.toGradedAlgHom.comp f.toGradedAlgHom
  map_d' a := by
    change dC (g.toGradedAlgHom (f.toGradedAlgHom a)) =
      g.toGradedAlgHom (f.toGradedAlgHom (dA a))
    rw [g.map_d', f.map_d']

@[simp]
theorem coe_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) : ⇑(g.comp f) = g ∘ f := (rfl)

@[simp]
theorem comp_apply (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) (a : A) :
    g.comp f a = g (f a) :=
  congrFun (coe_comp g f) a

@[simp]
theorem comp_id (f : DGAlgHom hA hB) : f.comp (DGAlgHom.id hA) = f := by
  ext a
  rw [comp_apply, id_apply]

@[simp]
theorem id_comp (f : DGAlgHom hA hB) : (DGAlgHom.id hB).comp f = f := by
  ext a
  rw [comp_apply, id_apply]

theorem comp_assoc {D : Type*} [Ring D] [Algebra R D]
    {𝒟 : ℤ → Submodule R D} [GradedAlgebra 𝒟] {dD : D →ₗ[R] D}
    {hD : IsDGAlgebra 𝒟 dD} (k : DGAlgHom hC hD) (g : DGAlgHom hB hC)
    (f : DGAlgHom hA hB) : (k.comp g).comp f = k.comp (g.comp f) := by
  ext a
  simp only [comp_apply]

/-! ### Maps on cycles and cohomology -/

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

/-- A DG algebra morphism sends boundaries to boundaries. -/
theorem cycles_mem_boundaries (f : DGAlgHom hA hB) {z : hA.cycles}
    (hz : z ∈ hA.boundaries) : f.cycles z ∈ hB.boundaries := by
  rw [hA.mem_boundaries] at hz
  obtain ⟨a, ha⟩ := hz
  rw [hB.mem_boundaries]
  refine ⟨f a, ?_⟩
  change dB (f a) = f (z : A)
  rw [f.map_d, ha]

private noncomputable def cohomologyAlgHom (f : DGAlgHom hA hB) :
    hA.Cohomology →ₐ[R] hB.Cohomology :=
  Ideal.Quotient.liftₐ hA.boundaries.asIdeal
    ((Ideal.Quotient.mkₐ R hB.boundaries.asIdeal).comp f.cycles.toAlgHom)
    fun z hz => by
      change Ideal.Quotient.mk hB.boundaries.asIdeal (f.cycles z) = 0
      rw [hB.quotientMk_eq_zero_iff]
      exact f.cycles_mem_boundaries (TwoSidedIdeal.mem_asIdeal.mp hz)

private theorem cohomologyAlgHom_mk (f : DGAlgHom hA hB) (z : hA.cycles) :
    f.cohomologyAlgHom (Ideal.Quotient.mk hA.boundaries.asIdeal z) =
      Ideal.Quotient.mk hB.boundaries.asIdeal (f.cycles z) := by
  have h := Ideal.Quotient.liftₐ_comp hA.boundaries.asIdeal
    ((Ideal.Quotient.mkₐ R hB.boundaries.asIdeal).comp f.cycles.toAlgHom)
    (fun z hz => by
      change Ideal.Quotient.mk hB.boundaries.asIdeal (f.cycles z) = 0
      rw [hB.quotientMk_eq_zero_iff]
      exact f.cycles_mem_boundaries (TwoSidedIdeal.mem_asIdeal.mp hz))
  have hz := AlgHom.congr_fun h z
  change f.cohomologyAlgHom (Ideal.Quotient.mk hA.boundaries.asIdeal z) =
    Ideal.Quotient.mk hB.boundaries.asIdeal (f.cycles z) at hz
  exact hz

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
    change f.cohomologyAlgHom (Ideal.Quotient.mk hA.boundaries.asIdeal z) ∈
      hB.cohomologyGrading p
    rw [cohomologyAlgHom_mk]
    exact hB.mem_cohomologyGrading.mpr
      ⟨f.cycles z, f.toGradedAlgHom.map_mem hz, rfl⟩

/-- The cohomology map sends the class of a cycle to the class of its image. -/
@[simp]
theorem cohomology_mk (f : DGAlgHom hA hB) (z : hA.cycles) :
    f.cohomology (Ideal.Quotient.mk hA.boundaries.asIdeal z) =
      Ideal.Quotient.mk hB.boundaries.asIdeal (f.cycles z) := by
  change f.cohomologyAlgHom (Ideal.Quotient.mk hA.boundaries.asIdeal z) = _
  exact f.cohomologyAlgHom_mk z

/-- Passage to cohomology sends the identity DG algebra morphism to the identity graded algebra
homomorphism. -/
@[simp]
theorem cohomology_id (hA : IsDGAlgebra 𝒜 dA) :
    (DGAlgHom.id hA).cohomology = GradedAlgHom.id R hA.cohomologyGrading := by
  apply GradedAlgHom.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [cohomology_mk]
  change Ideal.Quotient.mk hA.boundaries.asIdeal ((DGAlgHom.id hA).cycles z) =
    Ideal.Quotient.mk hA.boundaries.asIdeal z
  have hz := DFunLike.congr_fun (cycles_id hA) z
  exact congrArg (Ideal.Quotient.mk hA.boundaries.asIdeal)
    (hz.trans (GradedAlgHom.id_apply R hA.cyclesDeg z))

/-- Passage to cohomology preserves composition of DG algebra morphisms. -/
@[simp]
theorem cohomology_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).cohomology = g.cohomology.comp f.cohomology := by
  apply GradedAlgHom.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [cohomology_mk, GradedAlgHom.comp_apply, cohomology_mk, cohomology_mk]
  exact congrArg (Ideal.Quotient.mk hC.boundaries.asIdeal)
    (DFunLike.congr_fun (cycles_comp g f) z)

end DGAlgHom

end TauCeti
