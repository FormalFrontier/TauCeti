/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.MultiplyLacedRelations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic

/-!
# Multiply-laced Chevalley relations for Kostant root-subgroup scheme morphisms

This file proves the `B`, `C`, and `F₄` Chevalley commutator relation on scheme-valued points of
the represented root-subgroup morphisms `xᵢ : 𝔾ₐ → GLₙ`. For the root string
`β`, `α + β`, `2α + β`, the relation is

```text
⁅x_α(t), x_β(u)⁆ = x_{α+β}(c t u) x_{2α+β}(d t² u).
```

It transports the matrix relation from `RootSubgroup/MultiplyLacedRelations.lean` through the
point-comparison theorem for the actual affine group-scheme morphisms. Thus the equation is stated
at the same interface used by the generated Chevalley--Demazure carrier.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq`: the multiply-laced
  relation for scheme-valued points.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq'`: the same relation
  with both output points written out.

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

/-- **The multiply-laced Chevalley commutator relation on scheme-valued points.** Suppose the
distinguished root vectors form the chain `β`, `α + β`, `2α + β`, and let `r` and `s` carry
parameters `c t u` and `d t² u`. Then the commutator of the represented `i`- and `j`-root values
is the product of the represented `k`- and `l`-root values. -/
theorem commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (p q r s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))
    (hs : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A s) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q))) :
    ⁅GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom),
      GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)⁆ =
      GeneralLinear.schemePointsMulEquiv n A
          (r ≫ (kostantRootSubgroup e h ρ M hM k hk b).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (s ≫ (kostantRootSubgroup e h ρ M hM l hl b).hom.hom) := by
  rw [schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup]
  apply commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_eq
    e h ρ M hM b hij hiij hil hjk hjl hkl hi hj hk hl
  · simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hr
  · simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hs

/-- The multiply-laced Chevalley commutator relation on scheme-valued points with both output
points written out at parameters `c t u` and `d t² u`. -/
theorem commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq'
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    ⁅GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom),
      GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)⁆ =
      GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((c : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
            (kostantRootSubgroup e h ρ M hM k hk b).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((d : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) ^ 2 *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
            (kostantRootSubgroup e h ρ M hM l hl b).hom.hom) :=
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq
    e h ρ M hM b A hij hiij hil hjk hjl hkl hi hj hk hl p q _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))

end TauCeti.UniversalEnvelopingAlgebra
