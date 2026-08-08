/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.LinearAlgebra.CliffordAlgebra.QuadraticLieSubalgebra

/-!
# The orthogonal action of quadratic Clifford elements

Quadratic elements of a Clifford algebra act on its generators by the commutator. This module
transports that action from the image of `CliffordAlgebra.ι` back to the original module and proves
that every resulting endomorphism is skew-adjoint for `QuadraticMap.polarBilin Q`.

The construction is generic over a commutative ring in which `2` is invertible. It needs no basis,
finiteness, field, or nondegeneracy assumption. It supplies the forward action map used in the
roadmap's Layer 9 `soEquivQuadratic` target, but does not prove that map bijective.

## Main definition

* `TauCeti.CliffordAlgebra.quadraticLieAction`: the Lie action of quadratic Clifford elements as
  skew-adjoint endomorphisms of the original module.

## Main results

* `TauCeti.CliffordAlgebra.ι_quadraticLieAction_apply`: applying a quadratic element to a vector
  agrees, after `CliffordAlgebra.ι`, with the ambient Clifford commutator.
* `TauCeti.CliffordAlgebra.quadraticLieAction_cliffordBivector_apply`: a Clifford bivector acts by
  the infinitesimal rotation determined by `QuadraticMap.polar`.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 9, "the abstract quadratic realization".
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

private noncomputable def vectorLieSubmodule :
    LieSubmodule R (quadraticLieSubalgebra Q) (CliffordAlgebra Q) :=
  { LinearMap.range (ι Q) with
    lie_mem := by
      rintro x _ ⟨m, rfl⟩
      exact lie_ι_mem_range_ι_of_mem_quadraticLieSubalgebra Q x.property m }

private noncomputable def vectorLieEquiv : M ≃ₗ[R] vectorLieSubmodule Q :=
  ιRangeEquiv Q

private theorem coe_vectorLieEquiv_apply (m : M) :
    (vectorLieEquiv Q m : CliffordAlgebra Q) = ι Q m :=
  coe_ιRangeEquiv_apply Q m

private noncomputable def quadraticActionEnd :
    quadraticLieSubalgebra Q →ₗ⁅R⁆ Module.End R M :=
  (vectorLieEquiv Q).symm.lieConj.toLieHom.comp
    (LieModule.toEnd R (quadraticLieSubalgebra Q) (vectorLieSubmodule Q))

private theorem vectorLieEquiv_quadraticActionEnd_apply
    (x : quadraticLieSubalgebra Q) (m : M) :
    vectorLieEquiv Q (quadraticActionEnd Q x m) = ⁅x, vectorLieEquiv Q m⁆ := by
  simp only [quadraticActionEnd, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
    LieModule.toEnd_apply_apply, LinearEquiv.apply_symm_apply]

private theorem ι_quadraticActionEnd_apply (x : quadraticLieSubalgebra Q) (m : M) :
    ι Q (quadraticActionEnd Q x m) = ⁅(x : CliffordAlgebra Q), ι Q m⁆ := by
  rw [← coe_vectorLieEquiv_apply Q, vectorLieEquiv_quadraticActionEnd_apply,
    LieSubmodule.coe_bracket, coe_vectorLieEquiv_apply,
    LieSubalgebra.coe_bracket_of_module]

private theorem quadraticActionEnd_cliffordBivector_apply (a b m : M) :
    quadraticActionEnd Q
        ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩ m =
      QuadraticMap.polar Q b m • a - QuadraticMap.polar Q a m • b := by
  apply ι_injective Q
  rw [ι_quadraticActionEnd_apply, cliffordBivector_lie_ι]

private theorem quadraticActionEnd_cliffordBivector_mem_skewAdjoint (a b : M) :
    quadraticActionEnd Q
        ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩ ∈
      (QuadraticMap.polarBilin Q).skewAdjointSubmodule := by
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro m n
  simp only [Pi.neg_apply, quadraticActionEnd_cliffordBivector_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_left,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_neg_right,
    QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right]
  rw [QuadraticMap.polar_comm Q m a, QuadraticMap.polar_comm Q m b]
  ring

private theorem quadraticActionEnd_mem_skewAdjoint (x : quadraticLieSubalgebra Q) :
    quadraticActionEnd Q x ∈ (QuadraticMap.polarBilin Q).skewAdjointSubmodule := by
  let K := (QuadraticMap.polarBilin Q).skewAdjointSubmodule.comap
    (quadraticActionEnd Q).toLinearMap
  have hK : (quadraticLieSubalgebra Q).toSubmodule ≤
      K.map (quadraticLieSubalgebra Q).toSubmodule.subtype :=
    quadraticLieSubalgebra_toSubmodule_le_of_cliffordBivector_mem Q fun a b =>
      ⟨⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩,
        quadraticActionEnd_cliffordBivector_mem_skewAdjoint Q a b, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hK x.property
  have : y = x := Subtype.ext hxy
  subst x
  exact hy

/-- The commutator action of quadratic Clifford elements on the generators, regarded as
skew-adjoint endomorphisms for the polar form. -/
noncomputable def quadraticLieAction :
    quadraticLieSubalgebra Q →ₗ⁅R⁆
      skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) :=
  { (quadraticActionEnd Q).toLinearMap.codRestrict _
      (quadraticActionEnd_mem_skewAdjoint Q) with
    map_lie' := by
      intro x y
      apply Subtype.ext
      exact (quadraticActionEnd Q).map_lie x y }

private theorem quadraticLieAction_apply (x : quadraticLieSubalgebra Q) (m : M) :
    (((quadraticLieAction Q x :
      skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End R M) m) =
      quadraticActionEnd Q x m :=
  rfl

/-- The quadratic action agrees with the ambient Clifford commutator after applying `ι`. -/
@[simp]
theorem ι_quadraticLieAction_apply (x : quadraticLieSubalgebra Q) (m : M) :
    ι Q (((quadraticLieAction Q x :
      skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End R M) m) =
      ⁅(x : CliffordAlgebra Q), ι Q m⁆ := by
  rw [quadraticLieAction_apply, ι_quadraticActionEnd_apply]

/-- A Clifford bivector acts by the infinitesimal rotation determined by the polar form. -/
@[simp]
theorem quadraticLieAction_cliffordBivector_apply (a b m : M) :
    (((quadraticLieAction Q
        ⟨cliffordBivector Q a b, cliffordBivector_mem_quadraticLieSubalgebra Q a b⟩ :
      skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End R M) m) =
      QuadraticMap.polar Q b m • a - QuadraticMap.polar Q a m • b := by
  rw [quadraticLieAction_apply, quadraticActionEnd_cliffordBivector_apply]

end CommRing

end CliffordAlgebra

end TauCeti
