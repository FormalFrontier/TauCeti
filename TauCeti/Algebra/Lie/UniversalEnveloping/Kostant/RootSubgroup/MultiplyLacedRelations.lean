/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Multiply-laced Chevalley relations for represented Kostant root subgroups

For roots `α` and `β` whose positive rank-two root string contains both `α + β` and `2α + β`,
this file proves, under the displayed bracket and nilpotence hypotheses, the conditional relation

```text
⁅x_α(t), x_β(u)⁆ = x_{α+β}(c t u) x_{2α+β}(d t² u).
```

`Commutator.lean` proves the underlying multiplication and conjugation identities for the
divided-power actions. This file derives the canonical element-commutator form and transports it
through an arbitrary finite integral basis to the represented general linear group. The
scheme-valued form is in `RootSubgroup/Scheme/MultiplyLacedRelations.lean`.

The extra hypothesis that the `β` root vector commutes with the `2α + β` root vector is exactly
what removes the conjugated `β` factor from the element commutator. It holds for the indicated root
string because `2α + 2β` is not a root.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupPoints_of_lie_lie_eq`: the multiply-laced relation for
  divided-power root-subgroup actions.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_eq`: the same relation in an arbitrary
  finite integral basis.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Sections 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {A : Type*} [CommRing A]

/-- **The multiply-laced Chevalley commutator relation for Kostant root-subgroup actions.**
Suppose the distinguished root vectors form the chain `β`, `α + β`, `2α + β`, with the
first and second iterated brackets scaled by `c` and `2 * d`. If `p` and `q` have parameters
`c t u` and `d t² u`, then `⁅xᵢ(t), xⱼ(u)⁆ = xₖ(p) xₗ(q)`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_lie_eq
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g p q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q := by
  have hconj :=
    kostantRootSubgroupPoints_conj_of_lie_lie_eq e h ρ M hM hij hiij hil hjk hkl
      hi hj hk hl f g p q hp hq
  change MulAut.conj (kostantRootSubgroupPoints e h ρ M hM i hi f)
      (kostantRootSubgroupPoints e h ρ M hM j hj g) = _ at hconj
  rw [conj_eq_commutatorElement_mul] at hconj
  have hcomm :=
    (commute_kostantRootSubgroupPoints e h ρ M hM hjk hj hk g p).mul_right
      (commute_kostantRootSubgroupPoints e h ρ M hM hjl hj hl g q)
  rw [mul_assoc, hcomm.eq] at hconj
  exact mul_right_cancel hconj

/-- The multiply-laced Chevalley commutator relation with the two output points written out at
parameters `c t u` and `d t² u`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_lie_eq'
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM l hl
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) :=
  commutatorElement_kostantRootSubgroupPoints_of_lie_lie_eq e h ρ M hM
    hij hiij hil hjk hjl hkl hi hj hk hl f g _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

section Matrices

variable {η : Type*} [Fintype η] [DecidableEq η] (b : Module.Basis η ℤ M)

/-- **The multiply-laced Chevalley commutator relation in an integral basis.** The matrix
commutator of the first two represented root subgroups is the product of the next two root
subgroups, at parameters `c t u` and `d t² u`. -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_eq
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g p q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi b f,
        kostantRootSubgroupMatrix e h ρ M hM j hj b g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk b p *
        kostantRootSubgroupMatrix e h ρ M hM l hl b q := by
  rw [kostantRootSubgroupMatrix_def, kostantRootSubgroupMatrix_def,
    kostantRootSubgroupMatrix_def, kostantRootSubgroupMatrix_def]
  simpa only [MonoidHom.comp_apply, map_commutatorElement, map_mul] using
    congrArg (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom)
      (commutatorElement_kostantRootSubgroupPoints_of_lie_lie_eq e h ρ M hM
        hij hiij hil hjk hjl hkl hi hj hk hl f g p q hp hq)

/-- The multiply-laced matrix commutator relation with both output points written out. -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_eq'
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi b f,
        kostantRootSubgroupMatrix e h ρ M hM j hj b g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk b
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupMatrix e h ρ M hM l hl b
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) :=
  commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_eq e h ρ M hM b
    hij hiij hil hjk hjl hkl hi hj hk hl f g _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

end Matrices

end TauCeti.UniversalEnvelopingAlgebra
