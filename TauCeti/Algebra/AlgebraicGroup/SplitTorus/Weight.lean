/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus

/-!
# Weights of the split torus as characters

The character lattice of the rank-`σ` split torus is `σ →₀ ℤ`, while a weight of a
representation written in a basis is an exponent vector `μ : σ → ℤ`, the datum
`TauCeti.torusCharacter` evaluates at a point. For finite `σ` these are the same thing, and this
file records the translation:

* `TauCeti.SplitTorus.weightCharacter` turns an exponent vector into a character;
* `TauCeti.SplitTorus.charOfPoint_weightCharacter` says that evaluating that character at a point
  of the torus gives the monomial `∏ j, s j ^ μ j` in the coordinates `s` of the point;
* `TauCeti.SplitTorus.closure_range_weightCharacter_eq_top` says that a family of weights
  generates the character group exactly when it spans the lattice of exponent vectors.

The last statement is the hypothesis under which a diagonal representation with these weights is
faithful, so it is what turns a spanning set of weights into a closed immersion of the torus.

## Main declarations

* `TauCeti.SplitTorus.weightCharacter`: the character of `𝔾ₘ^σ` with a prescribed exponent
  vector.

## Main results

* `TauCeti.SplitTorus.charOfPoint_weightCharacter`: the value of a weight character at a point.
* `TauCeti.SplitTorus.closure_range_weightCharacter_eq_top`: spanning weights generate the
  character group.

## References

Milne, *Algebraic Groups* (2017), §12.c, describes the character lattice of a split torus.
-/

public section

open WithConv

namespace TauCeti

namespace SplitTorus

universe u v w

variable {R : Type u} {A : Type v} {σ : Type w}
variable [CommRing R] [CommRing A] [Algebra R A] [Fintype σ]

/-- The character of the rank-`σ` split torus with exponent vector `μ`, that is, the Laurent
monomial `∏ j, x_j ^ μ j`. -/
@[expose] noncomputable def weightCharacter (μ : σ → ℤ) : Multiplicative (σ →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm μ)

@[simp]
theorem toAdd_weightCharacter (μ : σ → ℤ) (j : σ) :
    Multiplicative.toAdd (weightCharacter μ) j = μ j := by
  simp [weightCharacter]

/-- **The value of a weight character at a point of the split torus** is the corresponding
monomial in the coordinates of the point. -/
theorem charOfPoint_weightCharacter
    (q : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] A)) (μ : σ → ℤ) :
    DiagonalizableGroup.charOfPoint q.ofConv (weightCharacter μ) =
      torusCharacter (pointsMulEquiv q) μ := by
  have hcoord : pointsMulEquiv (R := R) (A := A) q =
      freeAbelianCharEquiv (DiagonalizableGroup.charOfPoint q.ofConv) := by
    funext i
    refine Units.ext ?_
    rw [pointsMulEquiv_apply_coe, freeAbelianCharEquiv_apply,
      DiagonalizableGroup.charOfPoint_apply_coe]
  have hchar : DiagonalizableGroup.charOfPoint q.ofConv =
      (freeAbelianCharEquiv (M := Aˣ)).symm (pointsMulEquiv (R := R) (A := A) q) := by
    rw [hcoord, MulEquiv.symm_apply_apply]
  rw [hchar, weightCharacter, freeAbelianCharEquiv_symm_apply_ofAdd, torusCharacter_def,
    Finsupp.prod_fintype _ _ fun _ => zpow_zero _]
  exact Finset.prod_congr rfl fun j _ => by simp

/-- **A family of weights generates the character group of the split torus exactly when it spans
the lattice of exponent vectors.** -/
theorem closure_range_weightCharacter_eq_top {η : Type*} (wt : η → σ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    Subgroup.closure (Set.range fun x => weightCharacter (wt x)) = ⊤ := by
  set f : η → (σ →₀ ℤ) := fun x => Finsupp.equivFunOnFinite.symm (wt x) with hf
  have hspan : Submodule.span ℤ (Set.range f) = ⊤ := by
    have hmap : Submodule.map (Finsupp.linearEquivFunOnFinite ℤ ℤ σ).symm.toLinearMap
        (Submodule.span ℤ (Set.range wt)) = Submodule.span ℤ (Set.range f) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hmap, hwt, Submodule.map_top, LinearMap.range_eq_top.2
      (Finsupp.linearEquivFunOnFinite ℤ ℤ σ).symm.surjective]
  have hadd : AddSubgroup.closure (Set.range f) = ⊤ := by
    refine AddSubgroup.toIntSubmodule.injective ?_
    rw [AddSubgroup.toIntSubmodule_closure, hspan]
    rfl
  have hpre : Multiplicative.toAdd ⁻¹' Set.range f =
      Set.range fun x => weightCharacter (wt x) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_range, weightCharacter, hf]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Multiplicative.ofAdd hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  rw [← hpre, ← AddSubgroup.toSubgroup_closure, hadd]
  rfl

end SplitTorus

end TauCeti
