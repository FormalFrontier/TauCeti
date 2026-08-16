/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme

/-!
# Chevalley relations for Kostant root-subgroup scheme morphisms

The divided-power construction represents a root action by an affine group-scheme morphism
`𝔾ₐ → GLₙ`. This file proves the commuting and class-two Chevalley relations on the
scheme-valued points of those actual morphisms. It transports the universe-polymorphic matrix
relations from `ChevalleyRelations.lean` through the point comparison proved in `Scheme.lean`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.commute_schemePointsMulEquiv_kostantRootSubgroup`:
  commuting root vectors give commuting scheme-valued root-subgroup points.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_eq`: the class-two
  Chevalley commutator relation for scheme-valued points.

The representation carrier is universe-zero because the current group-scheme reconstruction API
requires the base, coordinate Hopf algebra, and comodule to inhabit the same universe.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Sections 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (A : Type) [CommRing A]

/-- Scheme-valued points of represented Kostant root subgroups attached to commuting root vectors
commute. -/
theorem commute_schemePointsMulEquiv_kostantRootSubgroup {i j : I} (hij : ⁅e i, e j⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    Commute
      (GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom))
      (GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)) := by
  rw [schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup]
  exact commute_kostantRootSubgroupMatrix e h ρ M hM b hij hi hj _ _

/-- **The class-two Chevalley commutator relation on scheme-valued points of represented Kostant
root subgroups.** If `r` has additive parameter `c` times the product of the parameters of `p`
and `q`, the matrix commutator of the represented `i`- and `j`-root values is the represented
`k`-root value at `r`. -/
theorem commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_eq
    {i j k : I} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (p q r : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q))) :
    ⁅GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom),
      GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)⁆ =
      GeneralLinear.schemePointsMulEquiv n A
        (r ≫ (kostantRootSubgroup e h ρ M hM k hk b).hom.hom) := by
  rw [schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup]
  apply commutatorElement_kostantRootSubgroupMatrix_of_lie_eq
    e h ρ M hM b hij hik hjk hi hj hk
  simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hr

end TauCeti.UniversalEnvelopingAlgebra
