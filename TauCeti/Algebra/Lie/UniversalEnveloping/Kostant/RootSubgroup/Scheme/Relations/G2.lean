/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.G2
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic

/-!
# The type-G₂ relation for Kostant root-subgroup scheme morphisms

This file transports the integral type-`G₂` root-string identity to the scheme-valued points of
the represented Kostant root-subgroup morphisms `xᵢ : 𝔾ₐ ⟶ GLₙ`. Suppose six distinguished
root vectors follow the positive root string

```text
α, β, α + β, 2α + β, 3α + β, 3α + 2β.
```

If their scaled brackets have the integral coefficients `c`, `d`, `a`, and `b` specified in the
statements below, then on points over every commutative ring `A` one has

```text
xα(t) xβ(u) = xβ(u) x_{α+β}(c t u) x_{2α+β}(d t² u)
  x_{3α+β}(a t³ u) x_{3α+2β}(b t³ u²) xα(t).
```

The represented scheme morphisms are compared with their divided-power actions through
`schemePointsMulEquiv_kostantRootSubgroup`. Applying the matrix-coordinate homomorphism to
`kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul` then proves the relation in `GLₙ(A)`.
No factorial is inverted, so the result remains valid in characteristics two and three.

## Main results

* `schemePointsMulEquiv_kostantRootSubgroup_mul_of_lie_eq_three_nsmul` gives the product
  relation for four supplied output points.
* `schemePointsMulEquiv_kostantRootSubgroup_mul_of_lie_eq_three_nsmul'` writes those output
  points explicitly.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ x ∈ kostantForm e h, ∀ v ∈ M, ρ x v ∈ M)

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {n : ℕ} (basis : Module.Basis (Fin n) ℤ M)
variable (A : Type) [CommRing A]

/-- **The type-`G₂` product relation on scheme-valued points of represented Kostant root
subgroups.** The indices `i, j, k, l, m, o` correspond to
`α, β, α + β, 2α + β, 3α + β, 3α + 2β`. The four supplied output points have
parameters `c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem schemePointsMulEquiv_kostantRootSubgroup_mul_of_lie_eq_three_nsmul
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
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
      (b : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g) ^ 2)) :
    GeneralLinear.schemePointsMulEquiv n A
          (f ≫ (kostantRootSubgroup e h ρ M hM i hi basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (g ≫ (kostantRootSubgroup e h ρ M hM j hj basis).hom.hom) =
      GeneralLinear.schemePointsMulEquiv n A
          (g ≫ (kostantRootSubgroup e h ρ M hM j hj basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (p ≫ (kostantRootSubgroup e h ρ M hM k hk basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (q ≫ (kostantRootSubgroup e h ρ M hM l hl basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (r ≫ (kostantRootSubgroup e h ρ M hM m hm basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (s ≫ (kostantRootSubgroup e h ρ M hM o ho basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (f ≫ (kostantRootSubgroup e h ρ M hM i hi basis).hom.hom) := by
  simp only [schemePointsMulEquiv_kostantRootSubgroup]
  have hpoints := kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul e h ρ M hM
    hij hik hil hlk him hio hjk hlm hko hlo hmo hi hj hk hl hm ho
    ((AdditiveGroup.groupSchemePointMulEquiv A).symm f)
    ((AdditiveGroup.groupSchemePointMulEquiv A).symm g)
    ((AdditiveGroup.groupSchemePointMulEquiv A).symm p)
    ((AdditiveGroup.groupSchemePointMulEquiv A).symm q)
    ((AdditiveGroup.groupSchemePointMulEquiv A).symm r)
    ((AdditiveGroup.groupSchemePointMulEquiv A).symm s)
    (by simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hp)
    (by simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hq)
    (by simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hr)
    (by simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hs)
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (basis.baseChange A)).toMonoidHom) hpoints
  simpa only [kostantRootSubgroupMatrix_def, MonoidHom.comp_apply, map_mul] using hmatrix

/-- The type-`G₂` product relation on scheme-valued points with the four output points written
explicitly at parameters `c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem schemePointsMulEquiv_kostantRootSubgroup_mul_of_lie_eq_three_nsmul'
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    GeneralLinear.schemePointsMulEquiv n A
          (f ≫ (kostantRootSubgroup e h ρ M hM i hi basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (g ≫ (kostantRootSubgroup e h ρ M hM j hj basis).hom.hom) =
      GeneralLinear.schemePointsMulEquiv n A
          (g ≫ (kostantRootSubgroup e h ρ M hM j hj basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((c : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))) ≫
            (kostantRootSubgroup e h ρ M hM k hk basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((d : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 2 *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))) ≫
            (kostantRootSubgroup e h ρ M hM l hl basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((a : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 3 *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))) ≫
            (kostantRootSubgroup e h ρ M hM m hm basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((b : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 3 *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g) ^ 2))) ≫
            (kostantRootSubgroup e h ρ M hM o ho basis).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (f ≫ (kostantRootSubgroup e h ρ M hM i hi basis).hom.hom) :=
  schemePointsMulEquiv_kostantRootSubgroup_mul_of_lie_eq_three_nsmul
    e h ρ M hM basis A hij hik hil hlk him hio hjk hlm hko hlo hmo hi hj hk hl hm ho f g
      _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))

end TauCeti.UniversalEnvelopingAlgebra
