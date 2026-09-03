/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.OfAssociative
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Representation

/-!
# Kostant's module: the Clifford algebra of the Killing form, left-regularly

For a Killing-semisimple Lie algebra `L` the adjoint action is skew-adjoint for the Killing form,
so it lifts to the quadratic elements of the Clifford algebra of that form
(`CliffordAlgebra.adjointCliffordHom`). This file installs the `L`-module structure that Kostant's
isotypy theorem is about: the Clifford algebra acted on by **left multiplication** by that lift,

`⁅x, c⁆ = adjointCliffordHom K L x * c`.

The choice of action is not cosmetic. The other `L`-module structure the same lift produces is the
inner derivation action `⁅x, c⁆ = ⁅adjointCliffordHom K L x, c⁆` of
`CliffordAlgebra.cliffordDerivationRep`, which under `CliffordAlgebra.equivExterior` is the
exterior extension of the adjoint representation and is in general *not* the isotypic action that
Kostant's theorem is about; the two differ by right multiplication
(`CliffordAlgebra.kostant_lie_sub_mul`). What distinguishes the left-regular action is that its
submodules include every left ideal (`CliffordAlgebra.kostantLieSubmoduleOfLeftIdeal`) and its
endomorphisms include every right multiplication (`CliffordAlgebra.kostantRightMul`), which is the
commutant the isotypy argument runs on.

The two instances are `scoped`, as the roadmap asks: the Clifford algebra of the Killing form is
not otherwise an `L`-module, and a global instance would fix one of the two competing actions for
every consumer. Write `open scoped CliffordAlgebra` to use them.

## Main definitions

* `CliffordAlgebra.kostantLieRingModule` and `CliffordAlgebra.kostantLieModule`: the scoped
  left-regular `L`-module structure on `CliffordAlgebra (killingQuadraticForm K L)`.
* `CliffordAlgebra.kostantRightMul`: right multiplication, as an endomorphism of that module.
* `CliffordAlgebra.kostantLieSubmoduleOfLeftIdeal`: a left ideal, as a Lie submodule.

## Main results

* `CliffordAlgebra.kostant_lie_def`: the defining equation of the action.
* `CliffordAlgebra.kostant_lie_ι`: its value on a Clifford generator, where the adjoint action of
  `L` reappears together with a right-multiplication term.
* `CliffordAlgebra.kostant_lie_sub_mul`: the comparison with the inner derivation action.
* `CliffordAlgebra.kostantLieModuleIsFaithful`: the action is faithful, because the adjoint
  representation of a Killing-semisimple Lie algebra is
  (`CliffordAlgebra.adjointCliffordHom_injective`, proved alongside the lift itself).

The carrier is a finite module over `K`, which is what makes the statement that its simple
submodules are all isomorphic a statement about something; nothing here needs that, so the
instance saying so is left to `TauCeti.LinearAlgebra.CliffordAlgebra.Dimension`, to be imported
by whichever later file uses it.

## References

This implements the "Kostant's setting, packaged" target (`kostantLieRingModule`,
`kostantLieModule`, `kostant_lie_def`) of Layer 9 in
`TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md`.

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem*, Adv. Math. 125
  (1997), 275--350.
-/

public section

universe u v

namespace CliffordAlgebra

open TauCeti.LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L]

/-- **Kostant's module.** The Clifford algebra of the Killing quadratic form, acted on by `L`
through left multiplication by the adjoint quadratic lift. Scoped: the inner derivation action of
`CliffordAlgebra.cliffordDerivationRep` is a competing `L`-module structure on the same carrier,
so neither may be global. -/
noncomputable scoped instance kostantLieRingModule :
    LieRingModule L (CliffordAlgebra (killingQuadraticForm K L)) :=
  LieRingModule.compLieHom _ (LieHom.leftRegularRep (adjointCliffordHom K L))

/-- Kostant's module is a Lie module over the base field. -/
noncomputable scoped instance kostantLieModule :
    LieModule K L (CliffordAlgebra (killingQuadraticForm K L)) :=
  LieModule.compLieHom _ (LieHom.leftRegularRep (adjointCliffordHom K L))

variable {K L}

/-- **The defining equation of Kostant's module**: `L` acts by left multiplication by the adjoint
quadratic lift. -/
@[simp, grind =]
theorem kostant_lie_def (x : L) (c : CliffordAlgebra (killingQuadraticForm K L)) :
    ⁅x, c⁆ = adjointCliffordHom K L x * c :=
  LieHom.leftRegularRep_apply _ x c

/-- **The action on a Clifford generator.** The adjoint action of `L` on itself is visible in
Kostant's module, but only up to a right-multiplication term: left multiplication is not the
derivation action. Not a `simp` lemma: `CliffordAlgebra.kostant_lie_def` already rewrites its
left-hand side, so `simp` would never see this one in simp-normal form. -/
@[grind =]
theorem kostant_lie_ι (x y : L) :
    ⁅x, ι (killingQuadraticForm K L) y⁆ =
      ι (killingQuadraticForm K L) ⁅x, y⁆ +
        ι (killingQuadraticForm K L) y * adjointCliffordHom K L x := by
  have h := adjointCliffordHom_lie_ι K L x y
  rw [LieRing.of_associative_ring_bracket] at h
  rw [kostant_lie_def, ← h, sub_add_cancel]

/-- **Kostant's action minus right multiplication is the inner derivation action.** This is the
precise sense in which the left-regular module and the exterior extension of the adjoint
representation are different modules on the same carrier; it is the pointwise form of
`LieHom.ad_apply_eq_leftRegularRep_sub_mulRight` for the adjoint quadratic lift. -/
theorem kostant_lie_sub_mul (x : L) (c : CliffordAlgebra (killingQuadraticForm K L)) :
    ⁅x, c⁆ - c * adjointCliffordHom K L x = ⁅adjointCliffordHom K L x, c⁆ :=
  (congrArg (fun f : Module.End K (CliffordAlgebra (killingQuadraticForm K L)) ↦ f c)
    (LieHom.ad_apply_eq_leftRegularRep_sub_mulRight (adjointCliffordHom K L) x)).symm

/-- **Right multiplication is an endomorphism of Kostant's module.** Associativity of the Clifford
algebra says that left and right multiplications commute, so every right multiplication lies in
the commutant of the action; this is the supply of intertwiners behind the isotypy statement. -/
noncomputable def kostantRightMul (d : CliffordAlgebra (killingQuadraticForm K L)) :
    CliffordAlgebra (killingQuadraticForm K L) →ₗ⁅K, L⁆
      CliffordAlgebra (killingQuadraticForm K L) where
  __ := LinearMap.mulRight K d
  map_lie' {x c} :=
    (congrArg (fun f : Module.End K (CliffordAlgebra (killingQuadraticForm K L)) ↦ f c)
      (LieHom.leftRegularRep_comp_mulRight (adjointCliffordHom K L) x d)).symm

@[simp, grind =]
theorem kostantRightMul_apply (d c : CliffordAlgebra (killingQuadraticForm K L)) :
    kostantRightMul d c = c * d :=
  (rfl)

/-- **A left ideal of the Clifford algebra is a Lie submodule of Kostant's module.** The action is
by left multiplication, which a left ideal absorbs, so every left ideal is an invariant subspace;
what such a submodule decomposes into is the business of the later Kostant theorems, not of this
construction. -/
noncomputable def kostantLieSubmoduleOfLeftIdeal
    (I : Submodule (CliffordAlgebra (killingQuadraticForm K L))
      (CliffordAlgebra (killingQuadraticForm K L))) :
    LieSubmodule K L (CliffordAlgebra (killingQuadraticForm K L)) where
  __ := I.restrictScalars K
  lie_mem {x _} h := LieHom.leftRegularRep_mem_of_mem (adjointCliffordHom K L) I x h

@[simp, grind =]
theorem mem_kostantLieSubmoduleOfLeftIdeal
    {I : Submodule (CliffordAlgebra (killingQuadraticForm K L))
      (CliffordAlgebra (killingQuadraticForm K L))}
    {c : CliffordAlgebra (killingQuadraticForm K L)} :
    c ∈ kostantLieSubmoduleOfLeftIdeal I ↔ c ∈ I :=
  Iff.rfl

variable (K L)

/-- **Kostant's module is faithful.** Acting on `1` recovers the adjoint quadratic lift, which is
injective because the centre of a Killing-semisimple Lie algebra vanishes. -/
scoped instance kostantLieModuleIsFaithful :
    LieModule.IsFaithful K L (CliffordAlgebra (killingQuadraticForm K L)) where
  injective_toEnd _ _ hxy :=
    (LieHom.leftRegularRep_injective_iff (adjointCliffordHom K L)).2
      (adjointCliffordHom_injective K L) <|
      LinearMap.ext fun c ↦
        congrArg (fun f : Module.End K (CliffordAlgebra (killingQuadraticForm K L)) ↦ f c) hxy

end CliffordAlgebra
