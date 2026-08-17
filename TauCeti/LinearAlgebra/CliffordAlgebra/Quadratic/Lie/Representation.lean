/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Realization
public import TauCeti.Algebra.Lie.SkewAdjoint

/-!
# Lie representations induced from Clifford modules

A Lie homomorphism into the skew-adjoint endomorphisms of a nondegenerate quadratic module
lifts through the quadratic realization in its Clifford algebra. Composing this lift with any
Clifford action makes the target Clifford module a module for the original Lie algebra.

## Main results

* `CliffordAlgebra.cliffordInducedRep`: the induced Lie representation on a Clifford
  module.
* `CliffordAlgebra.cliffordInducedRep_apply`: its defining equation.
* `CliffordAlgebra.cliffordDerivationRep`: the induced representation on the Clifford
  algebra by inner derivations.
* `CliffordAlgebra.cliffordDerivationRep_apply`: its defining commutator equation.
* `CliffordAlgebra.adjointCliffordHom`: the quadratic lift of the adjoint representation
  for a Killing-semisimple Lie algebra.
* `CliffordAlgebra.adjointCliffordHom_lie_ι`: the lift acts on Clifford generators by the
  original adjoint action.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory / Spin
  Representations, Layer 9, "Every Clifford module is a `𝔤`-module".
-/

public section

open CliffordAlgebra

universe u v w x

namespace CliffordAlgebra

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def quadraticLift {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    L →ₗ⁅K⁆ CliffordAlgebra Q :=
  (quadraticLieSubalgebra Q).incl.comp <|
    (soEquivQuadratic Q hQ).toLieHom.comp θ

/-- The Lie representation on a Clifford module induced through the quadratic realization. -/
noncomputable def cliffordInducedRep {K : Type u} [Field K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    {S : Type x} [AddCommGroup S] [Module K S]
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K S) : L →ₗ⁅K⁆ Module.End K S :=
  ρ.toLieHom.comp (quadraticLift Q hQ θ)

/-- The induced representation acts through the quadratic realization and the Clifford action. -/
@[simp, grind =]
theorem cliffordInducedRep_apply {K : Type u} [Field K] {V : Type v} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    {S : Type x} [AddCommGroup S] [Module K S]
    (ρ : CliffordAlgebra Q →ₐ[K] Module.End K S) (y : L) :
    cliffordInducedRep Q hQ θ ρ y = ρ ↑(soEquivQuadratic Q hQ (θ y)) := by
  rfl

/-- The representation on the Clifford algebra induced by the inner derivations of the
quadratic realization. -/
noncomputable def cliffordDerivationRep {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    L →ₗ⁅K⁆ Module.End K (CliffordAlgebra Q) :=
  (LieAlgebra.ad K (CliffordAlgebra Q)).comp (quadraticLift Q hQ θ)

/-- The induced derivation representation acts by commutator with the quadratic
realization. -/
@[simp, grind =]
theorem cliffordDerivationRep_apply {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    {L : Type w} [LieRing L] [LieAlgebra K L]
    (θ : L →ₗ⁅K⁆ skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    (y : L) (c : CliffordAlgebra Q) :
    cliffordDerivationRep Q hQ θ y c =
      ⁅(soEquivQuadratic Q hQ (θ y) : CliffordAlgebra Q), c⁆ := by
  rfl

/-- The quadratic lift of the adjoint representation of a Killing-semisimple Lie algebra into the
Clifford algebra of its Killing quadratic form. -/
noncomputable def adjointCliffordHom (K : Type u) (L : Type v) [Field K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [Invertible (2 : K)]
    [_root_.LieAlgebra.IsKilling K L] :
    L →ₗ⁅K⁆ CliffordAlgebra (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L) :=
  quadraticLift (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L)
    (_root_.TauCeti.LieAlgebra.killingQuadraticForm_nondegenerate K L)
    (_root_.TauCeti.LieAlgebra.killingAdjointSO K L)

/-- The adjoint quadratic lift acts on Clifford generators by the original adjoint action. -/
@[simp, grind =]
theorem adjointCliffordHom_lie_ι (K : Type u) (L : Type v) [Field K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [Invertible (2 : K)]
    [_root_.LieAlgebra.IsKilling K L] (x y : L) :
    ⁅adjointCliffordHom K L x,
        CliffordAlgebra.ι (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L) y⁆ =
      CliffordAlgebra.ι (_root_.TauCeti.LieAlgebra.killingQuadraticForm K L) ⁅x, y⁆ := by
  simp only [adjointCliffordHom, quadraticLift, LieHom.comp_apply,
    LieSubalgebra.coe_incl, LieEquiv.coe_toLieHom, soEquivQuadratic_lie_ι,
    _root_.TauCeti.LieAlgebra.coe_killingAdjointSO, _root_.LieAlgebra.ad_apply]

end CliffordAlgebra
