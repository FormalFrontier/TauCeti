/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Weil divisors on schemes

This file specializes the combinatorial type `WeilDivisor` to schemes. A prime divisor is
represented by its generic point, which is a point of codimension one, and a scheme-theoretic
Weil divisor is a finite formal integer sum of such points.

Mathlib's `AlgebraicCycle X ℤ` allows locally finite support in every codimension. The map
`SchemeWeilDivisor.toAlgebraicCycle` extends a Weil divisor by zero away from codimension one.
Its image is characterized by `finiteCodimensionOneCycles`, the subgroup of algebraic cycles
with finite support entirely in codimension one, and
`SchemeWeilDivisor.equivFiniteCodimensionOneCycles` identifies the two descriptions.

The coefficient, support, effectivity, and point-divisor API is inherited directly from
`WeilDivisor`; no scheme-specific copies of those declarations are introduced.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve:
Weil divisors `⊕_x ℤ`", by supplying the scheme-theoretic codimension-one specialization needed
before principal divisors can be constructed from `Scheme.ord`.
-/

public section

open Order AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A codimension-one point of a scheme. Such a point is the generic point of a prime divisor. -/
abbrev CodimensionOnePoint (X : Scheme.{u}) : Type u :=
  {x : X // coheight x = 1}

/-- A Weil divisor on a scheme is a finite formal integer sum of its codimension-one points. -/
abbrev SchemeWeilDivisor (X : Scheme.{u}) : Type u :=
  WeilDivisor (CodimensionOnePoint X)

namespace SchemeWeilDivisor

variable {X : Scheme.{u}}

noncomputable section

/-- Regard a finitely supported function as an algebraic cycle. -/
private def algebraicCycleOfFinsupp : (X →₀ ℤ) →+ AlgebraicCycle X ℤ where
  toFun D :=
    { toFun := D
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, Filter.univ_mem, by simp⟩ }
  map_zero' := by
    ext
    simp
  map_add' D E := by
    ext
    simp

@[simp]
private lemma algebraicCycleOfFinsupp_apply (D : X →₀ ℤ) (x : X) :
    algebraicCycleOfFinsupp D x = D x :=
  rfl

/-- Extend a scheme-theoretic Weil divisor by zero away from codimension one, obtaining
an algebraic cycle on the underlying scheme. -/
def toAlgebraicCycle : SchemeWeilDivisor X →+ AlgebraicCycle X ℤ :=
  algebraicCycleOfFinsupp.comp <|
    Finsupp.embDomain.addMonoidHom (Function.Embedding.subtype fun x : X ↦ coheight x = 1)

/-- Extension by zero preserves the coefficient at a codimension-one point. -/
@[simp]
lemma toAlgebraicCycle_apply (D : SchemeWeilDivisor X) (x : CodimensionOnePoint X) :
    toAlgebraicCycle D x = D x :=
  Finsupp.embDomain_apply_self _ D x

/-- Extension by zero vanishes at points whose codimension is not one. -/
@[simp]
lemma toAlgebraicCycle_apply_of_coheight_ne_one (D : SchemeWeilDivisor X) (x : X)
    (hx : coheight x ≠ 1) :
    toAlgebraicCycle D x = 0 := by
  rw [toAlgebraicCycle, AddMonoidHom.comp_apply, algebraicCycleOfFinsupp_apply]
  exact Finsupp.embDomain_of_notMem_range _ _ _ (by simpa)

/-- The support of a scheme-theoretic Weil divisor viewed as an algebraic cycle is the image of
its finite support under the inclusion of codimension-one points. -/
lemma support_toAlgebraicCycle (D : SchemeWeilDivisor X) : (toAlgebraicCycle D).support =
      Subtype.val '' (D.support : Set (CodimensionOnePoint X)) := by
  ext x
  constructor
  · intro hx
    by_cases hx₁ : coheight x = 1
    · refine ⟨⟨x, hx₁⟩, ?_, rfl⟩
      exact Finsupp.mem_support_iff.mpr <| by
        rwa [← toAlgebraicCycle_apply D ⟨x, hx₁⟩]
    · exact (hx (toAlgebraicCycle_apply_of_coheight_ne_one D x hx₁)).elim
  · rintro ⟨x, hx, rfl⟩
    simpa [Function.mem_support] using hx

/-- A scheme-theoretic Weil divisor has finite support when regarded as an algebraic cycle. -/
lemma finite_support_toAlgebraicCycle (D : SchemeWeilDivisor X) :
    (toAlgebraicCycle D).support.Finite := by
  rw [support_toAlgebraicCycle]
  exact D.support.finite_toSet.image Subtype.val

/-- The cycle associated to a scheme-theoretic Weil divisor is supported in codimension one. -/
lemma coheight_eq_one_of_mem_support_toAlgebraicCycle (D : SchemeWeilDivisor X) {x : X}
    (hx : x ∈ (toAlgebraicCycle D).support) :
    coheight x = 1 := by
  rw [support_toAlgebraicCycle] at hx
  obtain ⟨x, _, rfl⟩ := hx
  exact x.property

/-- Extension by zero embeds scheme-theoretic Weil divisors into algebraic cycles. -/
lemma toAlgebraicCycle_injective :
    Function.Injective (toAlgebraicCycle : SchemeWeilDivisor X → AlgebraicCycle X ℤ) := by
  intro D E h
  apply Finsupp.ext
  intro x
  have hx := congrArg (fun C : AlgebraicCycle X ℤ ↦ C x) h
  simpa only [toAlgebraicCycle_apply] using hx

/-- Two scheme-theoretic Weil divisors have the same associated cycle exactly when they are
equal. -/
@[simp]
lemma toAlgebraicCycle_inj {D E : SchemeWeilDivisor X} :
    toAlgebraicCycle D = toAlgebraicCycle E ↔ D = E :=
  toAlgebraicCycle_injective.eq_iff

/-- Algebraic cycles with finite support contained in codimension one. -/
def finiteCodimensionOneCycles (X : Scheme.{u}) : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier C := C.support.Finite ∧ ∀ x ∈ C.support, coheight x = 1
  zero_mem' :=
    ⟨by simp [Function.locallyFinsuppWithin.support],
      fun _ hx ↦ by simp at hx⟩
  add_mem' {C D} hC hD := by
    refine ⟨(hC.1.union hD.1).subset (Function.support_add (C : X → ℤ) D), ?_⟩
    intro x hx
    rcases Function.support_add (C : X → ℤ) D hx with hx | hx
    · exact hC.2 x hx
    · exact hD.2 x hx
  neg_mem' {C} hC := by
    constructor
    · simpa only [Function.locallyFinsuppWithin.support_neg] using hC.1
    · intro x hx
      rw [Function.locallyFinsuppWithin.support_neg] at hx
      exact hC.2 x hx

/-- Membership in `finiteCodimensionOneCycles` means finite support contained in codimension
one. -/
@[simp]
lemma mem_finiteCodimensionOneCycles_iff {C : AlgebraicCycle X ℤ} :
    C ∈ finiteCodimensionOneCycles X ↔
      C.support.Finite ∧ ∀ x ∈ C.support, coheight x = 1 :=
  Iff.rfl

/-- Restrict a finite codimension-one cycle to its codimension-one points. -/
private def ofFiniteCodimensionOneCycle (C : finiteCodimensionOneCycles X) :
    SchemeWeilDivisor X :=
  Finsupp.ofSupportFinite (fun x ↦ (C : AlgebraicCycle X ℤ) x) <| by
    convert Set.Finite.preimage_embedding
      (Function.Embedding.subtype fun x : X ↦ coheight x = 1) C.property.1 using 1
    ext
    rfl

@[simp]
private lemma ofFiniteCodimensionOneCycle_apply
    (C : finiteCodimensionOneCycles X) (x : CodimensionOnePoint X) :
    ofFiniteCodimensionOneCycle C x = C.1 x :=
  congrFun Finsupp.ofSupportFinite_coe x

/-- Scheme-theoretic Weil divisors are additively equivalent to the finite algebraic cycles
supported entirely in codimension one. -/
def equivFiniteCodimensionOneCycles :
    SchemeWeilDivisor X ≃+ finiteCodimensionOneCycles X where
  toFun D :=
    ⟨toAlgebraicCycle D,
      finite_support_toAlgebraicCycle D,
      fun _ hx ↦ coheight_eq_one_of_mem_support_toAlgebraicCycle D hx⟩
  invFun := ofFiniteCodimensionOneCycle
  left_inv D := by
    apply Finsupp.ext
    intro x
    calc
      ofFiniteCodimensionOneCycle
          ⟨toAlgebraicCycle D, finite_support_toAlgebraicCycle D,
            fun _ hx ↦ coheight_eq_one_of_mem_support_toAlgebraicCycle D hx⟩ x =
          toAlgebraicCycle D x :=
        ofFiniteCodimensionOneCycle_apply _ x
      _ = D x := toAlgebraicCycle_apply D x
  right_inv C := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    by_cases hx : coheight x = 1
    · calc
        toAlgebraicCycle (ofFiniteCodimensionOneCycle C) x =
            ofFiniteCodimensionOneCycle C ⟨x, hx⟩ :=
          toAlgebraicCycle_apply _ ⟨x, hx⟩
        _ = C.1 x := ofFiniteCodimensionOneCycle_apply C ⟨x, hx⟩
    · rw [toAlgebraicCycle_apply_of_coheight_ne_one _ _ hx]
      exact (Function.notMem_support.mp fun h ↦ hx (C.property.2 x h)).symm
  map_add' D E := by
    apply Subtype.ext
    exact (toAlgebraicCycle : SchemeWeilDivisor X →+ AlgebraicCycle X ℤ).map_add D E

/-- The forward direction of `equivFiniteCodimensionOneCycles` is extension by zero. -/
@[simp]
lemma coe_equivFiniteCodimensionOneCycles_apply (D : SchemeWeilDivisor X) :
    ((equivFiniteCodimensionOneCycles D : finiteCodimensionOneCycles X) :
      AlgebraicCycle X ℤ) =
      toAlgebraicCycle D :=
  (rfl)

/-- The inverse of `equivFiniteCodimensionOneCycles` recovers coefficients by restriction to
codimension-one points. -/
@[simp]
lemma equivFiniteCodimensionOneCycles_symm_apply_apply
    (C : finiteCodimensionOneCycles X) (x : CodimensionOnePoint X) :
    equivFiniteCodimensionOneCycles.symm C x = C.1 x :=
  ofFiniteCodimensionOneCycle_apply C x

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
