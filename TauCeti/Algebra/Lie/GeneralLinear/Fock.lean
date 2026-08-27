/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Clifford
public import TauCeti.Algebra.Lie.OfAssociative
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# The CAR module: the Clifford algebra of the trace form of `gl n`, left-regularly

The adjoint action of `gl n K` preserves its trace form, so it lifts to the Clifford algebra of
that form; adding the normal-ordering constant makes the lift the homomorphism
`TauCeti.glCliffordHom`, whose value on a matrix unit is `Eᵢⱼ ↦ ½ ∑ₖ dᵢₖ dₖⱼ`. This file installs
the `gl n K`-module structure that the `gl n` instance of Kostant's isotypy theorem is about: the
Clifford algebra acted on by **left multiplication** by that lift,

`⁅X, c⁆ = glCliffordHom X * c`.

The carrier is the **fermionic Fock space**: `CliffordAlgebra.equivExterior` identifies it with
`⋀(gl n K)`, of dimension `2 ^ N²` for `N` the cardinality of `n`
(`TauCeti.finrank_cliffordAlgebra_traceQuadraticForm`).

This is the trace-form sibling of `CliffordAlgebra.kostantLieRingModule`, the left-regular module
of the Killing form of a Killing-semisimple Lie algebra, and everything structural is shared with
it: the same `LieHom.leftRegularRep` builds the action, so the same right multiplications are
intertwiners (`TauCeti.carRightMul`) and the same left ideals are submodules
(`TauCeti.carLieSubmoduleOfLeftIdeal`). What is *not* shared is faithfulness. The Killing case is
faithful outright, because the centre of a Killing-semisimple Lie algebra vanishes; `gl n K` is
reductive and not semisimple, its centre is the scalar matrices, and the quadratic part of the
lift therefore has a kernel (`TauCeti.ker_traceAdjointSO`). The normal-ordering constant repairs
that, but only when `N` is invertible in `K` (`TauCeti.glCliffordHom_injective`), so
`TauCeti.carLieModule_isFaithful` carries the hypothesis `(Fintype.card n : K) ≠ 0` too.

As in the Killing case the two instances are `scoped`, because the same lift produces a second,
competing `gl n K`-module structure on the same carrier: the inner derivation action
`⁅X, c⁆ = ⁅glCliffordHom X, c⁆` of `CliffordAlgebra.cliffordDerivationRep`, which differs from this
one by a right multiplication (`TauCeti.car_lie_sub_mul`) and is not the isotypic action. Write
`open scoped TauCeti` to use them.

## Main definitions

* `TauCeti.carLieRingModule` and `TauCeti.carLieModule`: the scoped left-regular
  `gl n K`-module structure on `CliffordAlgebra (TauCeti.traceQuadraticForm K n)`.
* `TauCeti.carRightMul`: right multiplication, as an endomorphism of that module.
* `TauCeti.carLieSubmoduleOfLeftIdeal`: a left ideal, as a Lie submodule.

## Main results

* `TauCeti.car_lie_def`: the defining equation of the action.
* `TauCeti.car_lie_ι`: its value on a Clifford generator, where the matrix commutator reappears
  together with a right-multiplication term.
* `TauCeti.car_lie_sub_mul`: the comparison with the inner derivation action.
* `TauCeti.carLieModule_isFaithful`: the module is faithful once `Fintype.card n` is invertible,
  which is exactly `TauCeti.glCliffordHom_injective`.
* `TauCeti.finrank_cliffordAlgebra_traceQuadraticForm`: the Fock space has dimension `2 ^ N²`.

## References

This implements the "CAR module" target (`carLieRingModule`, `carLieModule`, `car_lie_def`) of the
`gl_N` worked instance of Layer 9 in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`.

* D. Panyushev, *On the irreducibility of the Clifford module of a semisimple Lie algebra*,
  Prop. 2.4 and Ex. 2.5(1).
* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350.
-/

public section

namespace TauCeti

open CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.decEq

variable {K n : Type*} [Field K] [Fintype n] [Invertible (2 : K)]

/-- **The CAR module.** The Clifford algebra of the trace form of `gl n K`, acted on by `gl n K`
through left multiplication by the normal-ordered quadratic lift. Scoped: the inner derivation
action of `CliffordAlgebra.cliffordDerivationRep` is a competing `gl n K`-module structure on the
same carrier, so neither may be global. -/
noncomputable scoped instance carLieRingModule :
    LieRingModule (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) :=
  LieRingModule.compLieHom _ (LieHom.leftRegularRep (glCliffordHom (K := K) (n := n)))

/-- The CAR module is a Lie module over the base field. -/
noncomputable scoped instance carLieModule :
    LieModule K (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) :=
  LieModule.compLieHom _ (LieHom.leftRegularRep (glCliffordHom (K := K) (n := n)))

/-- **The defining equation of the CAR module**: `gl n K` acts by left multiplication by the
normal-ordered quadratic lift. -/
@[simp, grind =]
theorem car_lie_def (X : Matrix n n K) (c : CliffordAlgebra (traceQuadraticForm K n)) :
    ⁅X, c⁆ = glCliffordHom X * c :=
  LieHom.leftRegularRep_apply _ X c

/-- **The action on a Clifford generator.** The matrix commutator is visible in the CAR module, but
only up to a right-multiplication term: left multiplication is not the derivation action. Not a
`simp` lemma: `TauCeti.car_lie_def` already rewrites its left-hand side, so `simp` would never see
this one in simp-normal form. -/
@[grind =]
theorem car_lie_ι (X Y : Matrix n n K) :
    ⁅X, ι (traceQuadraticForm K n) Y⁆ =
      ι (traceQuadraticForm K n) ⁅X, Y⁆ +
        ι (traceQuadraticForm K n) Y * glCliffordHom X := by
  have h := glCliffordHom_lie_ι (K := K) (n := n) X Y
  rw [LieRing.of_associative_ring_bracket] at h
  rw [car_lie_def, ← h, sub_add_cancel]

/-- **The CAR action minus right multiplication is the inner derivation action.** This is the
precise sense in which the left-regular module and the exterior extension of the adjoint
representation are different modules on the same carrier; it is the pointwise form of
`LieHom.ad_apply_eq_leftRegularRep_sub_mulRight` for the normal-ordered quadratic lift. -/
theorem car_lie_sub_mul (X : Matrix n n K) (c : CliffordAlgebra (traceQuadraticForm K n)) :
    ⁅X, c⁆ - c * glCliffordHom X = ⁅glCliffordHom X, c⁆ :=
  (congrArg (fun f : Module.End K (CliffordAlgebra (traceQuadraticForm K n)) ↦ f c)
    (LieHom.ad_apply_eq_leftRegularRep_sub_mulRight (glCliffordHom (K := K) (n := n)) X)).symm

/-- **Right multiplication is an endomorphism of the CAR module.** Associativity of the Clifford
algebra says that left and right multiplications commute, so every right multiplication lies in
the commutant of the action; this is the supply of intertwiners behind the isotypy statement. -/
noncomputable def carRightMul (d : CliffordAlgebra (traceQuadraticForm K n)) :
    CliffordAlgebra (traceQuadraticForm K n) →ₗ⁅K, Matrix n n K⁆
      CliffordAlgebra (traceQuadraticForm K n) where
  __ := LinearMap.mulRight K d
  map_lie' {X c} :=
    (congrArg (fun f : Module.End K (CliffordAlgebra (traceQuadraticForm K n)) ↦ f c)
      (LieHom.leftRegularRep_comp_mulRight (glCliffordHom (K := K) (n := n)) X d)).symm

@[simp, grind =]
theorem carRightMul_apply (d c : CliffordAlgebra (traceQuadraticForm K n)) :
    carRightMul d c = c * d :=
  (rfl)

/-- **A left ideal of the Clifford algebra is a Lie submodule of the CAR module.** The action is by
left multiplication, which a left ideal absorbs, so every left ideal is an invariant subspace. -/
noncomputable def carLieSubmoduleOfLeftIdeal
    (I : Submodule (CliffordAlgebra (traceQuadraticForm K n))
      (CliffordAlgebra (traceQuadraticForm K n))) :
    LieSubmodule K (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) where
  __ := I.restrictScalars K
  lie_mem {X _} h := LieHom.leftRegularRep_mem_of_mem (glCliffordHom (K := K) (n := n)) I X h

@[simp, grind =]
theorem mem_carLieSubmoduleOfLeftIdeal
    {I : Submodule (CliffordAlgebra (traceQuadraticForm K n))
      (CliffordAlgebra (traceQuadraticForm K n))}
    {c : CliffordAlgebra (traceQuadraticForm K n)} :
    c ∈ carLieSubmoduleOfLeftIdeal I ↔ c ∈ I :=
  Iff.rfl

/-! ### Faithfulness through the normal-ordering constant -/

/-- **The CAR module is faithful when `N` is invertible in `K`.** Acting on `1` recovers the
normal-ordered quadratic lift, so faithfulness is exactly its injectivity. -/
theorem carLieModule_isFaithful (h : (Fintype.card n : K) ≠ 0) :
    LieModule.IsFaithful K (Matrix n n K) (CliffordAlgebra (traceQuadraticForm K n)) where
  injective_toEnd _ _ hXY :=
    (LieHom.leftRegularRep_injective_iff (glCliffordHom (K := K) (n := n))).2
      (glCliffordHom_injective h) <|
      LinearMap.ext fun c =>
        congrArg (fun f : Module.End K (CliffordAlgebra (traceQuadraticForm K n)) ↦ f c) hXY

/-! ### The Fock space -/

variable (K n) in
/-- **The carrier of the CAR module is the fermionic Fock space `⋀(gl n K)`**, of dimension
`2 ^ N²`: the Clifford algebra of any quadratic form on a finite free module has rank two to the
rank of the module, and `gl n K` has rank `N²`. -/
theorem finrank_cliffordAlgebra_traceQuadraticForm :
    Module.finrank K (CliffordAlgebra (traceQuadraticForm K n))
      = 2 ^ (Fintype.card n * Fintype.card n) := by
  rw [CliffordAlgebra.finrank_eq_two_pow, Module.finrank_matrix, Module.finrank_self, mul_one]

end TauCeti
