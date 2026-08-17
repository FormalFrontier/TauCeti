/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.ExteriorSquare
public import TauCeti.LinearAlgebra.CliffordAlgebra.CliffordExteriorSquare
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors

/-!
# The quadratic realization of a skew-adjoint Lie algebra

For a nondegenerate quadratic form on a finite-dimensional vector space, the skew-adjoint
endomorphisms of its polar form are exactly the quadratic elements of its Clifford algebra. The
equivalence factors through the second exterior power, so its normalization is inherited from the
canonical bivector action rather than from a basis-dependent inverse.

## Main results

* `CliffordAlgebra.soEquivQuadratic`: the quadratic realization Lie equivalence.
* `CliffordAlgebra.soEquivQuadratic_lie_ι`: its defining generator-action equation.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory / Spin
  Representations, Layer 9, "The abstract quadratic realization".
-/

public section

open CliffordAlgebra

universe u v

namespace CliffordAlgebra

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

omit [FiniteDimensional K V] [Invertible (2 : K)] in
private theorem polarBilin_isSymm (Q : QuadraticForm K V) :
    LinearMap.BilinForm.IsSymm (QuadraticMap.polarBilin Q) :=
  ⟨fun x y => QuadraticMap.polar_comm Q x y⟩

private noncomputable def exteriorSquareEquivSkewAdjointPolar
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    ⋀[K]^2 V ≃ₗ[K] skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) :=
  exteriorSquareEquivSkewAdjoint (QuadraticMap.polarBilin Q)
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (polarBilin_isSymm Q)

private theorem ι_exteriorSquareEquivSkewAdjoint_apply
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (z : ⋀[K]^2 V) (x : V) :
    ι Q (((exteriorSquareEquivSkewAdjointPolar Q hQ z :
        skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End K V) x) =
      ⁅((bivectorExteriorEquivQuadraticLieSubalgebra Q z : quadraticLieSubalgebra Q) :
        CliffordAlgebra Q), ι Q x⁆ := by
  let lhs : ⋀[K]^2 V →ₗ[K] CliffordAlgebra Q :=
    { toFun := fun y =>
        ι Q (((exteriorSquareEquivSkewAdjointPolar Q hQ y :
            skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End K V) x)
      map_add' := by simp
      map_smul' := by simp }
  let rhs : ⋀[K]^2 V →ₗ[K] CliffordAlgebra Q :=
    { toFun := fun y =>
        ⁅((bivectorExteriorEquivQuadraticLieSubalgebra Q y : quadraticLieSubalgebra Q) :
          CliffordAlgebra Q), ι Q x⁆
      map_add' := by
        intro a b
        rw [(bivectorExteriorEquivQuadraticLieSubalgebra Q).map_add]
        -- Expose addition in the ambient Clifford algebra before applying bracket bilinearity.
        change ⁅(↑(bivectorExteriorEquivQuadraticLieSubalgebra Q a) : CliffordAlgebra Q) +
            ↑(bivectorExteriorEquivQuadraticLieSubalgebra Q b), ι Q x⁆ = _
        exact add_lie _ _ _
      map_smul' := by
        intro c a
        rw [(bivectorExteriorEquivQuadraticLieSubalgebra Q).map_smul]
        -- Expose scalar multiplication in the ambient Clifford algebra.
        change ⁅c • (↑(bivectorExteriorEquivQuadraticLieSubalgebra Q a) : CliffordAlgebra Q),
            ι Q x⁆ = _
        exact smul_lie _ _ _ }
  -- Return to the two local linear maps so extensionality can reduce to exterior generators.
  change lhs z = rhs z
  apply LinearMap.congr_fun
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  have hw : w = ![w 0, w 1] := (FinVec.etaExpand_eq w).symm
  rw [hw]
  -- Expose the skew-adjoint equivalence on a decomposable exterior element.
  change ι Q
      (((exteriorSquareEquivSkewAdjointPolar Q hQ
        (exteriorPower.ιMulti K 2 ![w 0, w 1]) :
          skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) : Module.End K V) x) = _
  unfold exteriorSquareEquivSkewAdjointPolar
  rw [exteriorSquareEquivSkewAdjoint_apply_ιMulti_apply]
  -- Expose the quadratic-subalgebra carrier before using its Clifford computation theorem.
  change _ = ⁅((bivectorExteriorEquivQuadraticLieSubalgebra Q
      (exteriorPower.ιMulti K 2 ![w 0, w 1]) : quadraticLieSubalgebra Q) :
        CliffordAlgebra Q), ι Q x⁆
  rw [coe_bivectorExteriorEquivQuadraticLieSubalgebra_apply,
    bivectorExterior_apply_ιMulti, bivector_lie_ι]
  simp only [QuadraticMap.polarBilin_apply_apply, map_sub, map_smul]

private noncomputable def soToQuadraticLinearEquiv
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) ≃ₗ[K] quadraticLieSubalgebra Q :=
  (exteriorSquareEquivSkewAdjointPolar Q hQ).symm.trans
    (bivectorExteriorEquivQuadraticLieSubalgebra Q)

private theorem soToQuadraticLinearEquiv_lie_ι
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (x : V) :
    ⁅((soToQuadraticLinearEquiv Q hQ f : quadraticLieSubalgebra Q) : CliffordAlgebra Q),
        ι Q x⁆ = ι Q ((f : Module.End K V) x) := by
  let e := exteriorSquareEquivSkewAdjointPolar Q hQ
  calc
    _ = ι Q (((e (e.symm f) : skewAdjointLieSubalgebra
        (QuadraticMap.polarBilin Q)) : Module.End K V) x) :=
      (ι_exteriorSquareEquivSkewAdjoint_apply Q hQ (e.symm f) x).symm
    _ = _ := by rw [e.apply_symm_apply]

private theorem soToQuadraticLinearEquiv_map_lie
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (f g : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    soToQuadraticLinearEquiv Q hQ ⁅f, g⁆ =
      ⁅soToQuadraticLinearEquiv Q hQ f, soToQuadraticLinearEquiv Q hQ g⁆ := by
  let e := soToQuadraticLinearEquiv Q hQ
  have hfg : (e.symm ⁅e f, e g⁆ : skewAdjointLieSubalgebra
      (QuadraticMap.polarBilin Q)) = ⁅f, g⁆ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply ι_injective Q
    rw [← soToQuadraticLinearEquiv_lie_ι Q hQ (e.symm ⁅e f, e g⁆) x]
    rw [e.apply_symm_apply]
    rw [LieSubalgebra.coe_bracket, lie_lie]
    rw [soToQuadraticLinearEquiv_lie_ι Q hQ g x,
      soToQuadraticLinearEquiv_lie_ι Q hQ f x]
    rw [soToQuadraticLinearEquiv_lie_ι Q hQ f ((g : Module.End K V) x),
      soToQuadraticLinearEquiv_lie_ι Q hQ g ((f : Module.End K V) x)]
    rw [← map_sub]
    congr 1
  apply e.symm.injective
  rw [e.symm_apply_apply]
  exact hfg.symm

/-- The skew-adjoint endomorphisms of a nondegenerate finite-dimensional quadratic module are
the quadratic elements of its Clifford algebra. -/
noncomputable def soEquivQuadratic (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) ≃ₗ⁅K⁆ quadraticLieSubalgebra Q :=
  LieEquiv.mk
    { toLinearMap := (soToQuadraticLinearEquiv Q hQ).toLinearMap
      map_lie' := fun {f g} => soToQuadraticLinearEquiv_map_lie Q hQ f g }
    (soToQuadraticLinearEquiv Q hQ).symm
    (soToQuadraticLinearEquiv Q hQ).symm_apply_apply
    (soToQuadraticLinearEquiv Q hQ).apply_symm_apply

/-- The quadratic element realizing a skew-adjoint endomorphism acts by that endomorphism on the
Clifford generators. -/
@[simp]
theorem soEquivQuadratic_lie_ι (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (x : V) :
    ⁅(soEquivQuadratic Q hQ f : CliffordAlgebra Q), ι Q x⁆ =
      ι Q ((f : Module.End K V) x) := by
  -- Unfold only the outer Lie equivalence to its underlying quadratic element.
  change ⁅((soToQuadraticLinearEquiv Q hQ f : quadraticLieSubalgebra Q) :
      CliffordAlgebra Q), ι Q x⁆ = _
  exact soToQuadraticLinearEquiv_lie_ι Q hQ f x

end CliffordAlgebra
