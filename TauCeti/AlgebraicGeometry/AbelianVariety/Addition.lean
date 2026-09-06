/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.End.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.Product

/-!
# The addition homomorphism of an abelian variety

For an abelian variety `A` over a field `K`, this file constructs the addition homomorphism
`add A : prod A A ⟶ A` and its diagonal companion `diag A : A ⟶ prod A A`.

The group law `μ[A.toOver]` of the underlying group scheme is a homomorphism of monoid objects
because the group is commutative — Mathlib's `IsMonHom μ` instance for commutative monoid objects
in a braided cartesian category, available here from `AbelianVariety.isCommMonObj`. It therefore
upgrades to a homomorphism of abelian varieties `prod A A ⟶ A` after identifying `(prod A A).toOver`
with `A.toOver ⊗ A.toOver`.

The characteristic identity is `lift_comp_add`: precomposing `add A` with the lift of two
homomorphisms `f, g : C ⟶ A` recovers their pointwise product `f * g`. It reads the abelian
variety's pointwise group law on hom-sets — used throughout `AbelianVariety.MorphismGroup` and
`AbelianVariety.End` — off the categorical structure of `prod` and `add`, so any statement
about `f * g` can be transported to a statement about `prod.lift f g ≫ add A`. The doubling
formula `diag_comp_add : diag A ≫ add A = mulBy A 2` is the immediate specialization to
`f = g = 𝟙 A`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API". The group law of an abelian
variety as a homomorphism into the category is required by later Layer E items — the theorem of
the cube and the dual abelian variety — and by Layer F's Abel–Jacobi construction, all of which
quantify over homomorphisms whose target is the group law of a product.

No external mathematics is vendored. The construction reuses Mathlib's `IsMonHom μ[M]` instance
from `Mathlib.CategoryTheory.Monoidal.Cartesian.Mon` together with the Tau Ceti
product-of-abelian-varieties API from `AbelianVariety.Product`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

open scoped Hom
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K]

noncomputable section

/-- The addition homomorphism `prod A A ⟶ A` of an abelian variety, from the multiplication of
its underlying group scheme.

An abelian variety is a commutative group scheme, so its multiplication `μ` is itself a
homomorphism of group objects (Mathlib's `IsMonHom μ` instance for a commutative monoid object)
and lifts to a homomorphism of abelian varieties. -/
def add (A : AbelianVariety K) : prod A A ⟶ A := by
  refine Hom.mk'
    (eqToHom (prod_toOver A A) ≫ μ[A.toOver]) ?_ ?_
  · rw [← Category.assoc, prod_one]
    simp only [IsMonHom.one_hom]
  · rw [← Category.assoc, prod_mul]
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

/-- The morphism over `Spec K` underlying `add A` is `μ[A.toOver]`, transported through the
identification of `(prod A A).toOver` with `A.toOver ⊗ A.toOver`. -/
@[simp]
lemma toOverHom_add (A : AbelianVariety K) :
    Hom.toOverHom (add A) = eqToHom (prod_toOver A A) ≫ μ[A.toOver] := by
  simp [add]

/-- Precomposing addition with the lift of two homomorphisms with common source recovers their
pointwise product in the group of homomorphisms. -/
@[simp]
lemma lift_comp_add {A B : AbelianVariety K} (f g : A ⟶ B) :
    prod.lift f g ≫ add B = f * g := by
  apply Hom.toOverHom_injective
  rw [Hom.toOverHom_comp, prod.toOverHom_lift, toOverHom_add, Hom.toOverHom_mul, Hom.mul_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The diagonal homomorphism `A ⟶ prod A A`, pairing `A` with itself. -/
def diag (A : AbelianVariety K) : A ⟶ prod A A :=
  prod.lift (𝟙 A) (𝟙 A)

/-- The morphism over `Spec K` underlying the diagonal is the categorical diagonal on
`A.toOver`. -/
@[simp]
lemma toOverHom_diag (A : AbelianVariety K) :
    Hom.toOverHom (diag A) =
      CartesianMonoidalCategory.lift (𝟙 A.toOver) (𝟙 A.toOver) ≫
        eqToHom (prod_toOver A A).symm := by
  rw [diag, prod.toOverHom_lift, Hom.toOverHom_id]

/-- The diagonal composed with addition is multiplication by two: the doubling formula
`x + x = 2 · x` for the group law of an abelian variety, as a categorical identity. -/
@[simp]
lemma diag_comp_add (A : AbelianVariety K) :
    diag A ≫ add A = mulBy A 2 := by
  rw [diag, lift_comp_add, mulBy_eq_zpow]
  rw [show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, sq]

/-- The pairing `⟨𝟙, [-1]⟩` composed with addition is the identity element of the group of
homomorphisms `A ⟶ A`: `x + (-x) = 0` for the group law. -/
lemma lift_id_neg_one_comp_add (A : AbelianVariety K) :
    prod.lift (𝟙 A) (mulBy A (-1)) ≫ add A = 1 := by
  rw [lift_comp_add, mulBy_eq_zpow]
  -- The right-hand side is `𝟙 A * (𝟙 A)⁻¹ = 1` in the pointwise group of endomorphisms.
  simp

/-- The pairing of two multiplication endomorphisms `⟨[m], [n]⟩` composed with addition is
multiplication by their sum: `m·x + n·x = (m + n)·x` for the group law of an abelian variety. -/
lemma lift_mulBy_mulBy_comp_add (A : AbelianVariety K) (m n : ℤ) :
    prod.lift (mulBy A m) (mulBy A n) ≫ add A = mulBy A (m + n) := by
  rw [lift_comp_add, mulBy_add]

/-- The pairing `⟨1, 𝟙⟩` composed with addition is the identity: the identity element of the
pointwise group law on `A ⟶ A` is a left neutral for addition. -/
lemma lift_one_id_comp_add (A : AbelianVariety K) :
    prod.lift (1 : A ⟶ A) (𝟙 A) ≫ add A = 𝟙 A := by
  rw [lift_comp_add, _root_.one_mul]

/-- The pairing `⟨𝟙, 1⟩` composed with addition is the identity: the identity element of the
pointwise group law on `A ⟶ A` is a right neutral for addition. -/
lemma lift_id_one_comp_add (A : AbelianVariety K) :
    prod.lift (𝟙 A) (1 : A ⟶ A) ≫ add A = 𝟙 A := by
  rw [lift_comp_add, _root_.mul_one]

/-! ### Symmetry -/

/-- Addition is symmetric in its two arguments: swapping the components of a lift and then adding
gives the same result. This is the commutativity of the pointwise group law on homomorphisms, read
back through `lift_comp_add`; the abstract source is the commutativity of the group law of the
abelian variety, `AbelianVariety.isCommMonObj`. -/
lemma lift_symm_comp_add {A B : AbelianVariety K} (f g : A ⟶ B) :
    prod.lift g f ≫ add B = prod.lift f g ≫ add B := by
  rw [lift_comp_add, lift_comp_add, mul_comm]

/-! ### Postcomposition and precomposition -/

/-- Precomposing a lift of two `A ⟶ B` homomorphisms with addition and then postcomposing with
`h : B ⟶ C` is the same as first postcomposing each component and then adding. This is the
morphism-level restatement of the fact that group-scheme homomorphisms preserve the group law
(`AbelianVariety.Hom.mul_comp`). -/
@[reassoc]
lemma lift_comp_add_comp {A B C : AbelianVariety K} (f g : A ⟶ B) (h : B ⟶ C) :
    prod.lift f g ≫ add B ≫ h = prod.lift (f ≫ h) (g ≫ h) ≫ add C := by
  rw [← Category.assoc, lift_comp_add, Hom.mul_comp, ← lift_comp_add]

/-- Precomposing a lift of two `B ⟶ C` homomorphisms with addition, after precomposing each
component with `k : A ⟶ B`, is the same as first precomposing each component of the lift with
`k` and then adding. This is the morphism-level restatement of the distributivity
`k ≫ (f + g) = k ≫ f + k ≫ g` from `AbelianVariety.Hom.comp_mul`. -/
@[reassoc]
lemma comp_lift_comp_add {A B C : AbelianVariety K} (k : A ⟶ B) (f g : B ⟶ C) :
    k ≫ prod.lift f g ≫ add C = prod.lift (k ≫ f) (k ≫ g) ≫ add C := by
  rw [← Category.assoc, prod.comp_lift]

/-! ### The endomorphism-ring restatements

Two convenience restatements of `lift_comp_add`: the addition of an endomorphism `A ⟶ A` and its
inverse is the zero endomorphism, and postcomposing addition with an endomorphism translates
across the pairing. Both are direct consequences of `lift_comp_add` and the pointwise group law,
reindexed so the multiplication-by-`n` API of `AbelianVariety.End.Basic` is directly applicable. -/

/-- An endomorphism paired with the multiplication-by-`n` endomorphism, followed by addition, is
multiplication by `n + 1`, when the first component is the identity. -/
lemma lift_id_mulBy_comp_add (A : AbelianVariety K) (n : ℤ) :
    prod.lift (𝟙 A) (mulBy A n) ≫ add A = mulBy A (n + 1) := by
  rw [add_comm n 1, ← mulBy_one A]
  simp

/-- The multiplication-by-`n` endomorphism paired with an endomorphism, followed by addition, is
multiplication by `n + 1`, when the second component is the identity. -/
lemma lift_mulBy_id_comp_add (A : AbelianVariety K) (n : ℤ) :
    prod.lift (mulBy A n) (𝟙 A) ≫ add A = mulBy A (n + 1) := by
  rw [← mulBy_one A]
  simp

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
