/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Generated.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.MultiplyLacedRelations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Relations.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Relations.G2

/-!
# Chevalley relations in the generated Kostant group scheme

The represented Kostant root subgroups factor through the closed group scheme they generate.
This file proves that the factored root subgroups satisfy their Chevalley relations intrinsically
in that generated carrier. The earlier matrix and scheme-point relations only identify the
images of these points in `GLₙ`; the closed immersion of the generated group scheme makes the
map on points injective, so those identities descend uniquely.

The results are stated on points over every commutative ring `A : Type`. Commuting root vectors
give commuting generated-group points, while a class-two root string
`⁅eᵢ, eⱼ⁆ = c • eₖ` gives

```text
[xᵢ(s), xⱼ(t)] = xₖ(cst).
```

The file also transports the multiply-laced relation from
`Scheme/MultiplyLacedRelations.lean` and the type-`G₂` relation from
`Scheme/Relations/G2.lean`. Together these complete the four currently available relation
families on the single `kostantRootSubgroupToGenerated` interface requested by Layer 9 of the
ReductiveGroups roadmap. That carrier and its root subgroups are consumed by milestone L0 of the
CFSGStatement roadmap.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupToGenerated`: commuting root
  vectors give commuting points of the generated group scheme.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupToGenerated_of_lie_eq`: the class-two Chevalley relation
  inside the generated group scheme.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupToGenerated_of_lie_lie_eq`: the multiply-laced
  Chevalley relation inside the generated group scheme.
* `TauCeti.UniversalEnvelopingAlgebra.
  kostantRootSubgroupToGenerated_mul_of_lie_eq_three_nsmul`: the type-`G₂` Chevalley relation
  inside the generated group scheme.

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
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (A : Type) [CommRing A]

private theorem kostantGeneratedGroupSchemeι_monoidHom_injective :
    Function.Injective (IsMonHom.monoidHom
      (kostantGeneratedGroupSchemeι e h ρ M hM hnil b).hom.hom
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)))) := by
  let _ : Mono (kostantGeneratedGroupSchemeι e h ρ M hM hnil b).hom.hom :=
    Over.mono_of_mono_left _
  intro p q hpq
  exact (cancel_mono (kostantGeneratedGroupSchemeι e h ρ M hM hnil b).hom.hom).1 hpq

/-- Represented Kostant root subgroups attached to commuting root vectors commute as points of
the generated group scheme over every commutative value ring. -/
theorem commute_kostantRootSubgroupToGenerated {i j : I} (hij : ⁅e i, e j⁆ = 0)
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    Commute
      (p ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom)
      (q ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom) := by
  apply Commute.of_map
    (f := IsMonHom.monoidHom
      (kostantGeneratedGroupSchemeι e h ρ M hM hnil b).hom.hom _)
    (kostantGeneratedGroupSchemeι_monoidHom_injective e h ρ M hM b hnil A)
  simp only [IsMonHom.monoidHom_apply, Category.assoc, ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_ι]
  exact Commute.of_map (GeneralLinear.schemePointsMulEquiv n A).injective
    (commute_schemePointsMulEquiv_kostantRootSubgroup
      e h ρ M hM b A hij (hnil i) (hnil j) p q)

/-- **The class-two Chevalley commutator relation inside the generated Kostant group scheme.**
Suppose `⁅eᵢ, eⱼ⁆ = c • eₖ`, with `eₖ` commuting with both `eᵢ` and `eⱼ`. If the additive
parameter of `r` is `c` times the product of those of `p` and `q`, then the commutator of the
factored `i`- and `j`-root points is the factored `k`-root point at `r`. -/
theorem commutatorElement_kostantRootSubgroupToGenerated_of_lie_eq
    {i j k : I} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (p q r : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q))) :
    ⁅p ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom,
      q ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom⁆ =
      r ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b k).hom.hom := by
  apply kostantGeneratedGroupSchemeι_monoidHom_injective e h ρ M hM b hnil A
  rw [map_commutatorElement]
  simp only [IsMonHom.monoidHom_apply, Category.assoc, ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_ι]
  apply (GeneralLinear.schemePointsMulEquiv n A).injective
  simpa only [map_commutatorElement] using
    commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_eq
      e h ρ M hM b A hij hik hjk (hnil i) (hnil j) (hnil k) p q r hr

/-- The class-two Chevalley commutator relation inside the generated group scheme, with the
third point written explicitly at parameter `c` times the product of the first two parameters. -/
@[simp]
theorem commutatorElement_kostantRootSubgroupToGenerated_of_lie_eq'
    {i j k : I} {c : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hik : ⁅e i, e k⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    ⁅p ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom,
      q ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom⁆ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd ((c : A) *
            (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
              Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
        (kostantRootSubgroupToGenerated e h ρ M hM hnil b k).hom.hom :=
  commutatorElement_kostantRootSubgroupToGenerated_of_lie_eq
    e h ρ M hM b hnil A hij hik hjk p q _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))

/-- **The multiply-laced Chevalley commutator relation inside the generated Kostant group
scheme.** The indices `i, j, k, l` correspond to `α, β, α + β, 2α + β`. If `r` and `s`
have parameters `c t u` and `d t² u`, then the commutator of the factored `i`- and `j`-root
points is the product of the factored `k`- and `l`-root points. -/
theorem commutatorElement_kostantRootSubgroupToGenerated_of_lie_lie_eq
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
    ⁅p ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom,
      q ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom⁆ =
      (r ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b k).hom.hom) *
        (s ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b l).hom.hom) := by
  apply kostantGeneratedGroupSchemeι_monoidHom_injective e h ρ M hM b hnil A
  rw [map_commutatorElement, map_mul]
  simp only [IsMonHom.monoidHom_apply, Category.assoc, ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_ι]
  apply (GeneralLinear.schemePointsMulEquiv n A).injective
  simpa only [map_commutatorElement, map_mul] using
    commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq
      e h ρ M hM b A hij hiij hil hjk hjl hkl
        (hnil i) (hnil j) (hnil k) (hnil l) p q r s hr hs

/-- The multiply-laced Chevalley commutator relation inside the generated group scheme, with
both output points written explicitly at parameters `c t u` and `d t² u`. -/
theorem commutatorElement_kostantRootSubgroupToGenerated_of_lie_lie_eq'
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0) (hjl : ⁅e j, e l⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0)
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    ⁅p ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom,
      q ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom⁆ =
      ((AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd ((c : A) *
            (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
              Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
        (kostantRootSubgroupToGenerated e h ρ M hM hnil b k).hom.hom) *
      ((AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd ((d : A) *
            (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) ^ 2 *
              Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
        (kostantRootSubgroupToGenerated e h ρ M hM hnil b l).hom.hom) :=
  commutatorElement_kostantRootSubgroupToGenerated_of_lie_lie_eq
    e h ρ M hM b hnil A hij hiij hil hjk hjl hkl p q _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))

/-- **The type-`G₂` Chevalley product relation inside the generated Kostant group scheme.**
The indices `i, j, k, l, m, o` correspond to
`α, β, α + β, 2α + β, 3α + β, 3α + 2β`. The four supplied output points have parameters
`c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem kostantRootSubgroupToGenerated_mul_of_lie_eq_three_nsmul
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
    (f ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom) *
        (g ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom) =
      (g ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom) *
        (p ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b k).hom.hom) *
        (q ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b l).hom.hom) *
        (r ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b m).hom.hom) *
        (s ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b o).hom.hom) *
        (f ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom) := by
  apply kostantGeneratedGroupSchemeι_monoidHom_injective e h ρ M hM b hnil A
  simp only [map_mul, IsMonHom.monoidHom_apply, Category.assoc, ← Grp.comp_hom_hom,
    kostantRootSubgroupToGenerated_comp_ι]
  apply (GeneralLinear.schemePointsMulEquiv n A).injective
  simpa only [map_mul] using
    schemePointsMulEquiv_kostantRootSubgroup_mul_of_lie_eq_three_nsmul
      e h ρ M hM b A hij hik hil hlk him hio hjk hlm hko hlo hmo
        (hnil i) (hnil j) (hnil k) (hnil l) (hnil m) (hnil o)
        f g p q r s hp hq hr hs

/-- The type-`G₂` Chevalley product relation inside the generated group scheme with the four
output points written explicitly at parameters `c t u`, `d t² u`, `a t³ u`, and `b t³ u²`. -/
theorem kostantRootSubgroupToGenerated_mul_of_lie_eq_three_nsmul'
    {i j k l m o : I} {c d a b' : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b') • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (f g : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    (f ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom) *
        (g ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom) =
      (g ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b j).hom.hom) *
        ((AdditiveGroup.schemePointsMulEquiv A).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) *
                Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))) ≫
          (kostantRootSubgroupToGenerated e h ρ M hM hnil b k).hom.hom) *
        ((AdditiveGroup.schemePointsMulEquiv A).symm
            (Multiplicative.ofAdd ((d : A) *
              (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))) ≫
          (kostantRootSubgroupToGenerated e h ρ M hM hnil b l).hom.hom) *
        ((AdditiveGroup.schemePointsMulEquiv A).symm
            (Multiplicative.ofAdd ((a : A) *
              (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g)))) ≫
          (kostantRootSubgroupToGenerated e h ρ M hM hnil b m).hom.hom) *
        ((AdditiveGroup.schemePointsMulEquiv A).symm
            (Multiplicative.ofAdd ((b' : A) *
              (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A g) ^ 2))) ≫
          (kostantRootSubgroupToGenerated e h ρ M hM hnil b o).hom.hom) *
        (f ≫ (kostantRootSubgroupToGenerated e h ρ M hM hnil b i).hom.hom) :=
  kostantRootSubgroupToGenerated_mul_of_lie_eq_three_nsmul
    e h ρ M hM b hnil A hij hik hil hlk him hio hjk hlm hko hlo hmo
      f g _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))

end TauCeti.UniversalEnvelopingAlgebra
