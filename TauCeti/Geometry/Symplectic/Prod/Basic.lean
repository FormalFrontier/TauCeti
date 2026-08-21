/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Direct sums of almost complex structures and symplectic forms

Given almost complex structures `J₁` on `V` and `J₂` on `W`, the product `V × W` carries the
direct-sum almost complex structure acting componentwise, `(v, w) ↦ (J₁ v, J₂ w)`. Likewise two
symplectic forms `ω₁`, `ω₂` assemble into the direct-sum symplectic form
`(ω₁ ⊕ ω₂)((v₁, w₁), (v₂, w₂)) = ω₁(v₁, v₂) + ω₂(w₁, w₂)`. This file builds both, records their
basic API, and proves the payoff: a direct sum of tame (respectively compatible) pairs is again
tame (respectively compatible).

This is the pointwise linear algebra of product symplectic manifolds, which the analytic
Heegaard Floer roadmap needs before the symmetric-product geometry of `Sym^g(Σ)`: the standard
model and every fiberwise compatibility argument decomposes over a direct sum. It complements
the *doubling* structure `TauCeti.AlmostComplexStructure.product` on `V × V` (which mixes the two
coordinates, `(x, y) ↦ (-y, x)`); the construction here is the componentwise direct sum instead,
following Mathlib's `LinearMap.prodMap` naming convention.

## Main declarations

* `TauCeti.AlmostComplexStructure.prod`: the direct-sum almost complex structure
  `(v, w) ↦ (J₁ v, J₂ w)` on `V × W`.
* `TauCeti.AlmostComplexStructure.isComplexLinearMap_inl` / `isComplexLinearMap_inr` /
  `isComplexLinearMap_fst` / `isComplexLinearMap_snd`: the structural maps of the product are
  complex-linear for the direct-sum structure.
* `TauCeti.AlmostComplexStructure.transport_prod`: transport distributes over the direct sum.
* `TauCeti.IsComplexLinearMap.prod` and `TauCeti.IsComplexLinearMap.prodMap`: complex-linearity is
  preserved by pairing maps with a common source and by product maps into the direct sum.
* `TauCeti.SymplecticForm.prod`: the direct-sum symplectic form on `V × W`.
* `TauCeti.SymplecticForm.twistedProd`: the twisted product form `ω₁ ⊖ ω₂` on `V × W`, the
  direct sum with the second factor negated.
* `TauCeti.SymplecticForm.prod_invariant`, `prod_tames`, `prod_compatible`: a direct sum of
  invariant / tame / compatible pairs is invariant / tame / compatible.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1, where products of compatible triples model split symplectic vector spaces.
-/

@[expose] public section

namespace TauCeti

variable {V W V' W' : Type*}

namespace AlmostComplexStructure

section Prod

variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

/-- The direct-sum almost complex structure on `V × W`, acting componentwise by
`(v, w) ↦ (J₁ v, J₂ w)`.

This is the componentwise direct sum, distinct from the doubling structure
`AlmostComplexStructure.product` on `V × V`. -/
def prod (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    AlmostComplexStructure (V × W) where
  toLinearMap := J₁.toLinearMap.prodMap J₂.toLinearMap
  square_neg := by
    apply LinearMap.ext
    rintro ⟨v, w⟩
    simp

@[simp]
lemma prod_toLinearMap (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    (J₁.prod J₂).toLinearMap = J₁.toLinearMap.prodMap J₂.toLinearMap := rfl

@[simp]
lemma prod_apply (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) (p : V × W) :
    J₁.prod J₂ p = (J₁ p.1, J₂ p.2) := rfl

/-- The direct sum of negations is the negation of the direct sum. -/
@[simp]
lemma neg_prod_neg (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    (-J₁).prod (-J₂) = -(J₁.prod J₂) :=
  toLinearMap_injective (by apply LinearMap.ext; rintro ⟨v, w⟩; simp)

/-- The inclusion of the first factor is complex-linear into the direct sum. -/
@[simp]
lemma isComplexLinearMap_inl (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    IsComplexLinearMap J₁ (J₁.prod J₂) (LinearMap.inl ℝ V W) := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp

/-- The inclusion of the second factor is complex-linear into the direct sum. -/
@[simp]
lemma isComplexLinearMap_inr (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    IsComplexLinearMap J₂ (J₁.prod J₂) (LinearMap.inr ℝ V W) := by
  rw [isComplexLinearMap_iff_apply]
  intro w
  simp

/-- The first projection is complex-linear out of the direct sum. -/
@[simp]
lemma isComplexLinearMap_fst (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    IsComplexLinearMap (J₁.prod J₂) J₁ (LinearMap.fst ℝ V W) := by
  rw [isComplexLinearMap_iff_apply]
  intro p
  simp

/-- The second projection is complex-linear out of the direct sum. -/
@[simp]
lemma isComplexLinearMap_snd (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    IsComplexLinearMap (J₁.prod J₂) J₂ (LinearMap.snd ℝ V W) := by
  rw [isComplexLinearMap_iff_apply]
  intro p
  simp

/-- Transport distributes over the direct sum: conjugating a direct sum by a product of
equivalences is the direct sum of the conjugates. -/
@[simp]
lemma transport_prod (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W)
    (e₁ : V ≃ₗ[ℝ] V') (e₂ : W ≃ₗ[ℝ] W') :
    (J₁.prod J₂).transport (e₁.prodCongr e₂) = (J₁.transport e₁).prod (J₂.transport e₂) := by
  apply toLinearMap_injective
  apply LinearMap.ext
  rintro ⟨v, w⟩
  simp [LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_symm]

end Prod

end AlmostComplexStructure

section ComplexLinearMap

variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']

/-- A pair of complex-linear maps with the same source is complex-linear into the direct-sum
almost complex structure. -/
lemma IsComplexLinearMap.prod {J : AlmostComplexStructure V} {J₁ : AlmostComplexStructure W}
    {J₂ : AlmostComplexStructure V'} {F : V →ₗ[ℝ] W} {G : V →ₗ[ℝ] V'}
    (hF : IsComplexLinearMap J J₁ F) (hG : IsComplexLinearMap J J₂ G) :
    IsComplexLinearMap J (J₁.prod J₂) (F.prod G) := by
  rw [isComplexLinearMap_iff_apply] at hF hG ⊢
  intro v
  simp [hF v, hG v]

/-- A product map of complex-linear maps is complex-linear for the direct-sum almost complex
structures. -/
lemma IsComplexLinearMap.prodMap {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}
    {K₁ : AlmostComplexStructure V'} {K₂ : AlmostComplexStructure W'} {F : V →ₗ[ℝ] V'}
    {G : W →ₗ[ℝ] W'} (hF : IsComplexLinearMap J₁ K₁ F)
    (hG : IsComplexLinearMap J₂ K₂ G) :
    IsComplexLinearMap (J₁.prod J₂) (K₁.prod K₂) (F.prodMap G) := by
  rw [isComplexLinearMap_iff_apply] at hF hG ⊢
  rintro ⟨v, w⟩
  simp [hF, hG]

end ComplexLinearMap

namespace SymplecticForm

section Prod

variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The underlying bilinear form of the direct-sum symplectic form. -/
def prodBilin (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) :
    LinearMap.BilinForm ℝ (V × W) :=
  ω₁.toBilinForm.comp (LinearMap.fst ℝ V W) (LinearMap.fst ℝ V W) +
    ω₂.toBilinForm.comp (LinearMap.snd ℝ V W) (LinearMap.snd ℝ V W)

@[simp]
private lemma prodBilin_apply (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (p q : V × W) :
    prodBilin ω₁ ω₂ p q = ω₁ p.1 q.1 + ω₂ p.2 q.2 := rfl

lemma prodBilin_isAlt (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) :
    (prodBilin ω₁ ω₂).IsAlt := by
  intro p
  simp

lemma prodBilin_nondegenerate (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) :
    (prodBilin ω₁ ω₂).Nondegenerate := by
  refine ⟨fun p hp => ?_, fun q hq => ?_⟩
  · have h1 : p.1 = 0 := ω₁.separatingLeft p.1 fun x => by
      have := hp (x, 0)
      simpa using this
    have h2 : p.2 = 0 := ω₂.separatingLeft p.2 fun y => by
      have := hp (0, y)
      simpa using this
    exact Prod.ext h1 h2
  · have h1 : q.1 = 0 := ω₁.separatingRight q.1 fun x => by
      have := hq (x, 0)
      simpa using this
    have h2 : q.2 = 0 := ω₂.separatingRight q.2 fun y => by
      have := hq (0, y)
      simpa using this
    exact Prod.ext h1 h2

/-- The direct-sum symplectic form on `V × W`, given by
`(ω₁ ⊕ ω₂)((v₁, w₁), (v₂, w₂)) = ω₁(v₁, v₂) + ω₂(w₁, w₂)`. -/
def prod (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) : SymplecticForm (V × W) where
  toBilinForm := prodBilin ω₁ ω₂
  isAlt := prodBilin_isAlt ω₁ ω₂
  nondegenerate := prodBilin_nondegenerate ω₁ ω₂

@[simp]
lemma prod_apply (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (p q : V × W) :
    ω₁.prod ω₂ p q = ω₁ p.1 q.1 + ω₂ p.2 q.2 := rfl

/-- The twisted product symplectic form `ω₁ ⊖ ω₂` on `V × W`, given by
`(ω₁ ⊖ ω₂)((v₁, w₁), (v₂, w₂)) = ω₁(v₁, v₂) - ω₂(w₁, w₂)`.

It is the direct sum `prod` of `ω₁` with the negation `ω₂.rescale (-1)` of `ω₂`; the body is
`@[no_expose]`, so downstream code uses it through `twistedProd_apply` rather than by unfolding. -/
@[no_expose]
noncomputable def twistedProd (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) :
    SymplecticForm (V × W) :=
  ω₁.prod (ω₂.rescale (-1) (by norm_num))

@[simp]
lemma twistedProd_apply (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (p q : V × W) :
    twistedProd ω₁ ω₂ p q = ω₁ p.1 q.1 - ω₂ p.2 q.2 := by
  simp only [twistedProd, prod_apply, rescale_apply]
  ring

variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}

/-- The bilinear form `(ω₁ ⊕ ω₂)(·, (J₁ ⊕ J₂) ·)` is the direct sum of the factorwise associated
forms. -/
@[simp]
lemma prod_associatedBilinForm_apply (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W)
    (p q : V × W) :
    (ω₁.prod ω₂).associatedBilinForm (J₁.prod J₂) p q =
      ω₁.associatedBilinForm J₁ p.1 q.1 + ω₂.associatedBilinForm J₂ p.2 q.2 := rfl

/-- `(ω₁ ⊕ ω₂)(p, (J₁ ⊕ J₂) p) = ω₁(p.1, J₁ p.1) + ω₂(p.2, J₂ p.2)`. -/
lemma prod_apply_prod_self (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (p : V × W) :
    ω₁.prod ω₂ p (J₁.prod J₂ p) = ω₁ p.1 (J₁ p.1) + ω₂ p.2 (J₂ p.2) := rfl

variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}

/-- A direct sum of invariant pairs is invariant. -/
lemma prod_invariant (h₁ : ω₁.Invariant J₁) (h₂ : ω₂.Invariant J₂) :
    (ω₁.prod ω₂).Invariant (J₁.prod J₂) := by
  rw [invariant_iff]
  intro p q
  rw [prod_apply, prod_apply, AlmostComplexStructure.prod_apply, AlmostComplexStructure.prod_apply,
    (ω₁.invariant_iff J₁).mp h₁, (ω₂.invariant_iff J₂).mp h₂]

/-- A direct sum of tame pairs is tame. -/
lemma prod_tames (h₁ : ω₁.Tames J₁) (h₂ : ω₂.Tames J₂) :
    (ω₁.prod ω₂).Tames (J₁.prod J₂) := by
  intro p hp
  rw [prod_apply_prod_self]
  have n1 : 0 ≤ ω₁ p.1 (J₁ p.1) := by
    rcases eq_or_ne p.1 0 with hv | hv
    · rw [hv]; simp
    · exact (h₁ p.1 hv).le
  have n2 : 0 ≤ ω₂ p.2 (J₂ p.2) := by
    rcases eq_or_ne p.2 0 with hv | hv
    · rw [hv]; simp
    · exact (h₂ p.2 hv).le
  rcases not_and_or.mp (fun h => hp (Prod.ext h.1 h.2)) with hp1 | hp2
  · exact add_pos_of_pos_of_nonneg (h₁ p.1 hp1) n2
  · exact add_pos_of_nonneg_of_pos n1 (h₂ p.2 hp2)

/-- A direct sum of compatible pairs is compatible. -/
lemma prod_compatible (h₁ : ω₁.Compatible J₁) (h₂ : ω₂.Compatible J₂) :
    (ω₁.prod ω₂).Compatible (J₁.prod J₂) :=
  Compatible.of_tames (prod_invariant h₁.invariant h₂.invariant)
    (prod_tames h₁.tames h₂.tames)

end Prod

end SymplecticForm

end TauCeti
