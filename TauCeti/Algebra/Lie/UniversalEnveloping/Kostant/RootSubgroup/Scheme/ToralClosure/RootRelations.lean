/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Generated.Relations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Basic

/-!
# Chevalley relations in the toral Kostant group scheme

The represented root subgroups first generate a closed group scheme inside `GLₙ`, and that
root-generated carrier includes as a closed subgroup of the larger carrier generated jointly by
the root subgroups and the represented weight torus. This file transports the intrinsic Chevalley
relations from the root-generated carrier through that inclusion. Consequently the root subgroups
of the toral carrier satisfy the same commuting, class-two, multiply-laced, and type-`G₂`
relations on points over every commutative ring.

The transport uses
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToGenerated_comp_kostantGeneratedToToral`;
no relation is reproved at matrix level. The resulting statements are on
`kostantRootSubgroupToToral`, the root-subgroup interface of the carrier used by the
Chevalley--Demazure construction.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupToToral`: commuting root
  vectors give commuting points of the toral group scheme.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupToToral_of_lie_eq`: the class-two Chevalley relation.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupToToral_of_lie_lie_eq`: the multiply-laced relation.
* `TauCeti.UniversalEnvelopingAlgebra.
  kostantRootSubgroupToToral_mul_of_lie_eq_three_nsmul`: the type-`G₂` relation.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Sections 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This supplies the Chevalley commutator interface for the toral carrier in Layer 9 of the
`ReductiveGroups` roadmap. That carrier and its root subgroups are consumed by milestone L0 of the
`CFSGStatement` roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (wt : Fin n → κ → ℤ)
variable (A : Type) [CommRing A]

/-- Represented Kostant root subgroups attached to commuting root vectors commute as points of
the toral group scheme over every commutative value ring. -/
theorem commute_kostantRootSubgroupToToral {i j : I} (hij : ⁅e i, e j⁆ = 0)
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    Commute
      (p ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt i).hom.hom)
      (q ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt j).hom.hom) := by
  have hcomm := (commute_kostantRootSubgroupToGenerated
    e h ρ M hM b hnil A hij p q).map
      (IsMonHom.monoidHom
        (kostantGeneratedToToral e h ρ M hM hnil b wt).hom.hom
        ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ))))
  simpa only [IsMonHom.monoidHom_apply, Category.assoc, ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_kostantGeneratedToToral] using hcomm

/-- **The class-two Chevalley commutator relation inside the toral Kostant group scheme.**
Suppose `⁅eᵢ, eⱼ⁆ = c • eₖ`, with `eₖ` commuting with both input vectors. If the additive
parameter of `r` is `c` times the product of those of `p` and `q`, then the commutator of the
factored `i`- and `j`-root points is the factored `k`-root point at `r`. -/
theorem commutatorElement_kostantRootSubgroupToToral_of_lie_eq
    {i j k : I} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (p q r : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q))) :
    ⁅p ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt i).hom.hom,
      q ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt j).hom.hom⁆ =
      r ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt k).hom.hom := by
  have hrel := congrArg
    (IsMonHom.monoidHom
      (kostantGeneratedToToral e h ρ M hM hnil b wt).hom.hom
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ))))
    (commutatorElement_kostantRootSubgroupToGenerated_of_lie_eq
      e h ρ M hM b hnil A hij hik hjk p q r hr)
  simpa only [map_commutatorElement, IsMonHom.monoidHom_apply, Category.assoc,
    ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_kostantGeneratedToToral] using hrel

/-- **The multiply-laced Chevalley commutator relation inside the toral Kostant group scheme.**
The indices `i, j, k, l` correspond to `α, β, α + β, 2α + β`. If `r` and `s` have parameters
`c t u` and `d t² u`, then the commutator of the factored input points is the product of the two
factored output points. -/
theorem commutatorElement_kostantRootSubgroupToToral_of_lie_lie_eq
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (p q r s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))
    (hs : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A s) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q))) :
    ⁅p ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt i).hom.hom,
      q ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt j).hom.hom⁆ =
      (r ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt k).hom.hom) *
        (s ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt l).hom.hom) := by
  have hrel := congrArg
    (IsMonHom.monoidHom
      (kostantGeneratedToToral e h ρ M hM hnil b wt).hom.hom
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ))))
    (commutatorElement_kostantRootSubgroupToGenerated_of_lie_lie_eq
      e h ρ M hM b hnil A hij hiij hil hjk hjl hkl p q r s hr hs)
  simpa only [map_commutatorElement, map_mul, IsMonHom.monoidHom_apply, Category.assoc,
    ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_kostantGeneratedToToral] using hrel

/-- **The type-`G₂` Chevalley product relation inside the toral Kostant group scheme.**
The indices `i, j, k, l, m, o` correspond to
`α, β, α + β, 2α + β, 3α + β, 3α + 2β`. The four supplied output points have parameters
`c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem kostantRootSubgroupToToral_mul_of_lie_eq_three_nsmul
    {i j k l m o : I} {c d a b' : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b') • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (f g p q r s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hp : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (a : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))
    (hs : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A s) =
      (b' : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g) ^ 2)) :
    (f ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt i).hom.hom) *
        (g ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt j).hom.hom) =
      (g ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt j).hom.hom) *
        (p ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt k).hom.hom) *
        (q ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt l).hom.hom) *
        (r ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt m).hom.hom) *
        (s ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt o).hom.hom) *
        (f ≫ (kostantRootSubgroupToToral e h ρ M hM hnil b wt i).hom.hom) := by
  have hrel := congrArg
    (IsMonHom.monoidHom
      (kostantGeneratedToToral e h ρ M hM hnil b wt).hom.hom
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ))))
    (kostantRootSubgroupToGenerated_mul_of_lie_eq_three_nsmul
      e h ρ M hM b hnil A hij hik hil hlk him hio hjk hlm hko hlo hmo
        f g p q r s hp hq hr hs)
  simpa only [map_mul, IsMonHom.monoidHom_apply, Category.assoc, ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_kostantGeneratedToToral] using hrel

end TauCeti.UniversalEnvelopingAlgebra
