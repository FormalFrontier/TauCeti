/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.Geometry.Hodge.Conjugation
public import TauCeti.RingTheory.IsTensorProduct

/-!
# Rational subspaces in an abstract complexification

This file develops the `ℤ → ℚ → ℂ` base-change tower used by pure and mixed Hodge structures.
Given abstract models `Vℚ` and `Vℂ` of the rational and complex scalar extensions of an integral
module `Vℤ`, `TauCeti.Hodge.rationalToComplexLinearEquiv` canonically identifies `ℂ ⊗[ℚ] Vℚ` with
`Vℂ`. Rational subspaces and rational linear maps can therefore be complexified directly inside
the chosen ambient complex spaces.

The constructions use Mathlib's `IsBaseChange` interface rather than requiring the ambient spaces
to be definitionally equal to concrete tensor products. This is essential for geometric Hodge
structures, whose rational and complex cohomology spaces arrive as abstract base-change models.

Rationality of a subspace is what makes its complexification stable under the lattice-induced
conjugation, so that stability is proved here, for an arbitrary rational subspace, rather than
imposed later as structure data.

## Main declarations

* `TauCeti.Hodge.rationalToComplexLinearEquiv`: the canonical tower equivalence from an abstract
  rationalification to an abstract complexification.
* `TauCeti.Hodge.rationalToComplexSubmodule`: the complexification of a rational subspace inside
  the chosen ambient complexification.
* `TauCeti.Hodge.rationalToComplexSubmoduleEquiv`: the canonical identification of the concrete
  complexification `ℂ ⊗[ℚ] W` of a rational subspace with that complexified subspace.
* `TauCeti.Hodge.rationalMapToComplex`: scalar extension of a rational linear map between two
  abstract base-change models.
* `TauCeti.Hodge.rationalMapToComplex_commutes_conj`: that scalar extension commutes with lattice
  conjugation, for arbitrary complex models.
* `TauCeti.Hodge.latticeConj_rationalToComplexLinearEquiv_one_tmul`: lattice conjugation fixes
  every purely rational vector of the ambient complexification.
* `TauCeti.Hodge.rationalToComplexSubmodule_conj`: the complexification of a rational subspace is
  stable under lattice-induced conjugation.
* `TauCeti.Hodge.rationalToComplexSubmodule_sup`: complexification preserves joins of rational
  subspaces.
* `TauCeti.Hodge.rationalToComplexSubmodule_eq_bot_iff`: only the zero subspace has trivial
  complexification.
* `TauCeti.Hodge.rationalToComplexSubmodule_le_iff`: an inclusion of rational subspaces can be
  tested on their complexifications.

The design follows the base-change interface specified in the Hodge structures roadmap. Its only
nontrivial comparison map is Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which cancels the middle `ℚ` in the concrete
tower before the result is transported to the two abstract models.

## References

The signatures are adapted from the proposed definitions in
[`HodgeStructures/Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/HodgeStructures/Suggested.lean),
whose definitive mathematical specification is the accompanying Hodge structures roadmap. In
particular the statements of `latticeConj_rationalToComplexLinearEquiv_one_tmul` and
`rationalToComplexSubmodule_conj` are that file's `rationalToComplexLinearEquiv_one_tmul_fixed` and
`rationalToComplexSubmodule_conj`; the proofs given here are different, being run against the
abstract base-change interface rather than the concrete tensor model.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w u' v' w'

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

/-- Lattice conjugation on the complexification `ℂ ⊗[ℚ] U` of a rational vector space conjugates
the scalar factor of a pure tensor. It is the unique conjugate-linear map fixing `1 ⊗ₜ u`. -/
@[simp]
theorem latticeConj_ratTensorMap_tmul (U : Type*) [AddCommGroup U] [Module ℚ U]
    (z : ℂ) (u : U) :
    latticeConj (isBaseChange_ratTensorMap ℂ U) (z ⊗ₜ[ℚ] u) =
      (starRingEnd ℂ) z ⊗ₜ[ℚ] u := by
  have hz : z ⊗ₜ[ℚ] u = z • ratTensorMap ℂ U u := by
    rw [ratTensorMap_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hz, map_smulₛₗ, latticeConj_ι, ratTensorMap_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

/-- On the canonical complexification `ℂ ⊗[ℚ] U` of a rational vector space, the complexification
of a `ℚ`-linear map read as an integral map is its rational base change. -/
theorem integralMapToComplex_ratTensorMap {U U' : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup U'] [Module ℚ U'] (g : U →ₗ[ℚ] U') :
    integralMapToComplex (isBaseChange_ratTensorMap ℂ U) (ratTensorMap ℂ U')
        (g.restrictScalars ℤ) = g.baseChange ℂ :=
  (isBaseChange_ratTensorMap ℂ U).algHom_ext _ _ fun u ↦ by
    rw [integralMapToComplex_apply_ι, ratTensorMap_apply, ratTensorMap_apply,
      LinearMap.restrictScalars_apply, LinearMap.baseChange_tmul]

/-- The canonical tower equivalence from an abstract rational base change to an abstract complex
base change of the same integral module. -/
noncomputable def rationalToComplexLinearEquiv (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) : ℂ ⊗[ℚ] Vℚ ≃ₗ[ℂ] Vℂ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) hℚ.equiv.symm).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ Vℤ).trans hℂ.equiv)

/-- The tower equivalence carries an integral vector through the rationalification to the same
integral vector in the complexification. -/
@[simp]
theorem rationalToComplexLinearEquiv_one_tmul_ι (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (x : Vℤ) :
    rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] ιℚ x) = ιℂ x := by
  simp [rationalToComplexLinearEquiv]

/-- The complexification of a rational subspace, realized inside the chosen ambient
complexification. -/
noncomputable def rationalToComplexSubmodule (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W : Submodule ℚ Vℚ) : Submodule ℂ Vℂ :=
  (W.baseChange ℂ).map (rationalToComplexLinearEquiv hℚ hℂ).toLinearMap

/-- The complexification of a rational subspace is the complex span of its rational vectors in
the ambient complexification. -/
theorem rationalToComplexSubmodule_eq_span (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W : Submodule ℚ Vℚ) :
    rationalToComplexSubmodule hℚ hℂ W =
      Submodule.span ℂ
        ((fun x : Vℚ ↦ rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x)) '' (W : Set Vℚ)) := by
  rw [rationalToComplexSubmodule, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨1 ⊗ₜ[ℚ] y, ⟨y, hy, rfl⟩, by simp⟩

/-- A rational vector belonging to a rational subspace belongs to its complexification. -/
theorem rationalToComplexLinearEquiv_one_tmul_mem (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) {W : Submodule ℚ Vℚ} {x : Vℚ} (hx : x ∈ W) :
    rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x) ∈
      rationalToComplexSubmodule hℚ hℂ W := by
  rw [rationalToComplexSubmodule_eq_span]
  exact Submodule.subset_span ⟨x, hx, rfl⟩

/-- Complexification of rational subspaces reflects inclusions: `ℂ` is faithfully flat over `ℚ`,
so an inclusion of rational subspaces may be tested on the complexifications. -/
@[simp]
theorem rationalToComplexSubmodule_le_iff (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W₁ W₂ : Submodule ℚ Vℚ) :
    rationalToComplexSubmodule hℚ hℂ W₁ ≤ rationalToComplexSubmodule hℚ hℂ W₂ ↔ W₁ ≤ W₂ := by
  rw [rationalToComplexSubmodule, rationalToComplexSubmodule,
    Submodule.map_le_map_iff_of_injective
      (f := (rationalToComplexLinearEquiv hℚ hℂ).toLinearMap)
      (rationalToComplexLinearEquiv hℚ hℂ).injective,
    Submodule.baseChange_le_iff]

/-- Complexification of rational subspaces is monotone. -/
theorem rationalToComplexSubmodule_mono (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) :
    Monotone (rationalToComplexSubmodule hℚ hℂ) := fun _ _ h ↦
  (rationalToComplexSubmodule_le_iff hℚ hℂ _ _).2 h

@[simp]
theorem rationalToComplexSubmodule_bot (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) :
    rationalToComplexSubmodule hℚ hℂ (⊥ : Submodule ℚ Vℚ) = ⊥ := by
  simp [rationalToComplexSubmodule]

/-- A rational subspace is trivial as soon as its complexification is: `ℂ` is faithfully flat
over `ℚ`. -/
@[simp]
theorem rationalToComplexSubmodule_eq_bot_iff (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W : Submodule ℚ Vℚ) :
    rationalToComplexSubmodule hℚ hℂ W = ⊥ ↔ W = ⊥ := by
  rw [← le_bot_iff, ← rationalToComplexSubmodule_bot hℚ hℂ,
    rationalToComplexSubmodule_le_iff, le_bot_iff]

@[simp]
theorem rationalToComplexSubmodule_top (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) :
    rationalToComplexSubmodule hℚ hℂ (⊤ : Submodule ℚ Vℚ) = ⊤ := by
  simp [rationalToComplexSubmodule]

/-- Complexification of rational subspaces preserves joins. -/
@[simp]
theorem rationalToComplexSubmodule_sup (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W₁ W₂ : Submodule ℚ Vℚ) :
    rationalToComplexSubmodule hℚ hℂ (W₁ ⊔ W₂) =
      rationalToComplexSubmodule hℚ hℂ W₁ ⊔ rationalToComplexSubmodule hℚ hℂ W₂ := by
  refine le_antisymm ?_ (sup_le (rationalToComplexSubmodule_mono hℚ hℂ le_sup_left)
    (rationalToComplexSubmodule_mono hℚ hℂ le_sup_right))
  rw [rationalToComplexSubmodule_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  simp only [TensorProduct.tmul_add, map_add, SetLike.mem_coe]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (rationalToComplexLinearEquiv_one_tmul_mem hℚ hℂ hy))
    (Submodule.mem_sup_right (rationalToComplexLinearEquiv_one_tmul_mem hℚ hℂ hz))

/-- The canonical equivalence from the concrete complexification `ℂ ⊗[ℚ] W` of a rational
subspace onto the complexification of `W` inside the ambient complexification. -/
noncomputable def rationalToComplexSubmoduleEquiv (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W : Submodule ℚ Vℚ) :
    ℂ ⊗[ℚ] W ≃ₗ[ℂ] rationalToComplexSubmodule hℚ hℂ W :=
  (Submodule.toBaseChange.toLinearEquiv ℂ W).trans
    ((rationalToComplexLinearEquiv hℚ hℂ).ofSubmodules (W.baseChange ℂ)
      (rationalToComplexSubmodule hℚ hℂ W) (by rw [rationalToComplexSubmodule]))

/-- The equivalence onto the complexification of a rational subspace is the tower equivalence
applied to the base change of the inclusion of that subspace. -/
@[simp]
theorem coe_rationalToComplexSubmoduleEquiv (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W : Submodule ℚ Vℚ) (x : ℂ ⊗[ℚ] W) :
    (rationalToComplexSubmoduleEquiv hℚ hℂ W x : Vℂ) =
      rationalToComplexLinearEquiv hℚ hℂ (W.subtype.baseChange ℂ x) := by
  rw [rationalToComplexSubmoduleEquiv, LinearEquiv.trans_apply,
    LinearEquiv.ofSubmodules_apply, Submodule.toBaseChange.toLinearEquiv_apply]
  rfl

/-- Lattice conjugation fixes the image in `Vℂ` of a purely rational vector `1 ⊗ₜ x`. -/
theorem latticeConj_rationalToComplexLinearEquiv_one_tmul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (x : Vℚ) :
    latticeConj hℂ (rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x)) =
      rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] x) := by
  induction x using hℚ.inductionOn with
  | zero => simp
  | tmul x => simp
  | smul q x hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul ℂ q, map_smul, map_smulₛₗ, hx]
      simp
  | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- Lattice conjugation of the image in `Vℂ` of a pure tensor `z ⊗ₜ x` with `x` rational
conjugates the scalar. -/
theorem latticeConj_rationalToComplexLinearEquiv_tmul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (z : ℂ) (x : Vℚ) :
    latticeConj hℂ (rationalToComplexLinearEquiv hℚ hℂ (z ⊗ₜ[ℚ] x)) =
      rationalToComplexLinearEquiv hℚ hℂ ((starRingEnd ℂ) z ⊗ₜ[ℚ] x) := by
  have hz : ∀ w : ℂ, w ⊗ₜ[ℚ] x = w • (1 : ℂ) ⊗ₜ[ℚ] x := by
    intro w
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hz z, hz ((starRingEnd ℂ) z), map_smul, map_smulₛₗ, map_smul,
    latticeConj_rationalToComplexLinearEquiv_one_tmul]

/-- The complexification of a rational subspace is stable under lattice-induced conjugation. -/
@[simp]
theorem rationalToComplexSubmodule_conj (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (W : Submodule ℚ Vℚ) :
    (rationalToComplexSubmodule hℚ hℂ W).map (latticeConj hℂ) =
      rationalToComplexSubmodule hℚ hℂ W := by
  have hle : (rationalToComplexSubmodule hℚ hℂ W).map (latticeConj hℂ) ≤
      rationalToComplexSubmodule hℚ hℂ W := by
    rw [rationalToComplexSubmodule_eq_span, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨x, hx, rfl⟩
    rw [latticeConj_rationalToComplexLinearEquiv_one_tmul]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  apply le_antisymm hle
  intro x hx
  refine ⟨latticeConj hℂ x, hle ⟨x, hx, rfl⟩, ?_⟩
  simp

section Map

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup V'ℤ]
variable [AddCommGroup V'ℚ] [Module ℚ V'ℚ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}

/-- The complexification of a rational linear map between abstract rational and complex
base-change models. -/
noncomputable def rationalMapToComplex (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f : Vℚ →ₗ[ℚ] V'ℚ) : Vℂ →ₗ[ℂ] V'ℂ :=
  (rationalToComplexLinearEquiv h'ℚ h'ℂ).toLinearMap ∘ₗ
    f.baseChange ℂ ∘ₗ (rationalToComplexLinearEquiv hℚ hℂ).symm.toLinearMap

/-- Complexification of a rational map sends the image of the pure tensor `z ⊗ₜ x` to the image
of `z ⊗ₜ f x`. -/
@[simp]
theorem rationalMapToComplex_rationalToComplexLinearEquiv_tmul
    (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (h'ℚ : IsBaseChange ℚ ι'ℚ) (h'ℂ : IsBaseChange ℂ ι'ℂ)
    (f : Vℚ →ₗ[ℚ] V'ℚ) (z : ℂ) (x : Vℚ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f
        (rationalToComplexLinearEquiv hℚ hℂ (z ⊗ₜ[ℚ] x)) =
      rationalToComplexLinearEquiv h'ℚ h'ℂ (z ⊗ₜ[ℚ] f x) := by
  simp [rationalMapToComplex]

/-- Complexification sends the identity rational map to the identity complex map. -/
@[simp]
theorem rationalMapToComplex_id (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) :
    rationalMapToComplex hℚ hℂ hℚ hℂ (LinearMap.id : Vℚ →ₗ[ℚ] Vℚ) = LinearMap.id := by
  ext x
  simp [rationalMapToComplex]

/-- Complexification sends the zero rational map to the zero complex map. -/
@[simp]
theorem rationalMapToComplex_zero (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ (0 : Vℚ →ₗ[ℚ] V'ℚ) = 0 := by
  simp [rationalMapToComplex]

/-- Complexification preserves addition of rational linear maps. -/
@[simp]
theorem rationalMapToComplex_add (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f g : Vℚ →ₗ[ℚ] V'ℚ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ (f + g) =
      rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f +
        rationalMapToComplex hℚ hℂ h'ℚ h'ℂ g := by
  simp [rationalMapToComplex, LinearMap.comp_add, LinearMap.add_comp]

/-- Complexification of rational linear maps, bundled as a homomorphism of additive groups. -/
noncomputable def rationalMapToComplexAddHom (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ) (h'ℂ : IsBaseChange ℂ ι'ℂ) :
    (Vℚ →ₗ[ℚ] V'ℚ) →+ (Vℂ →ₗ[ℂ] V'ℂ) where
  toFun := rationalMapToComplex hℚ hℂ h'ℚ h'ℂ
  map_zero' := rationalMapToComplex_zero hℚ hℂ h'ℚ h'ℂ
  map_add' := rationalMapToComplex_add hℚ hℂ h'ℚ h'ℂ

@[simp]
theorem rationalMapToComplexAddHom_apply (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ) (h'ℂ : IsBaseChange ℂ ι'ℂ)
    (f : Vℚ →ₗ[ℚ] V'ℚ) :
    rationalMapToComplexAddHom hℚ hℂ h'ℚ h'ℂ f = rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f :=
  (rfl)

/-- Complexification preserves negation of rational linear maps. -/
@[simp]
theorem rationalMapToComplex_neg (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f : Vℚ →ₗ[ℚ] V'ℚ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ (-f) = -rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f :=
  map_neg (rationalMapToComplexAddHom hℚ hℂ h'ℚ h'ℂ) f

/-- Complexification preserves subtraction of rational linear maps. -/
@[simp]
theorem rationalMapToComplex_sub (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f g : Vℚ →ₗ[ℚ] V'ℚ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ (f - g) =
      rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f - rationalMapToComplex hℚ hℂ h'ℚ h'ℂ g :=
  map_sub (rationalMapToComplexAddHom hℚ hℂ h'ℚ h'ℂ) f g

/-- Complexification preserves natural-number multiples of rational linear maps. -/
@[simp]
theorem rationalMapToComplex_nsmul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (k : ℕ) (f : Vℚ →ₗ[ℚ] V'ℚ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ (k • f) = k • rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f :=
  map_nsmul (rationalMapToComplexAddHom hℚ hℂ h'ℚ h'ℂ) k f

/-- Complexification preserves integer multiples of rational linear maps. -/
@[simp]
theorem rationalMapToComplex_zsmul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (k : ℤ) (f : Vℚ →ₗ[ℚ] V'ℚ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ (k • f) = k • rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f :=
  map_zsmul (rationalMapToComplexAddHom hℚ hℂ h'ℚ h'ℂ) k f

/-- Complexification preserves rational multiples of rational linear maps, the rational scalar
acting on the complexification through `ℚ → ℂ`. -/
@[simp]
theorem rationalMapToComplex_smul (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (q : ℚ) (f : Vℚ →ₗ[ℚ] V'ℚ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ (q • f) =
      (q : ℂ) • rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨t, rfl⟩ := (rationalToComplexLinearEquiv hℚ hℂ).surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z y =>
      rw [rationalMapToComplex_rationalToComplexLinearEquiv_tmul, LinearMap.smul_apply,
        LinearMap.smul_apply, rationalMapToComplex_rationalToComplexLinearEquiv_tmul,
        ← TensorProduct.smul_tmul, Rat.smul_def, ← map_smul,
        TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The complexification of a rational map commutes with lattice conjugation.** The abstract
base-change interface makes this a statement about arbitrary complex models, not only about the
concrete tensor product. -/
@[simp]
theorem rationalMapToComplex_commutes_conj (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f : Vℚ →ₗ[ℚ] V'ℚ) (x : Vℂ) :
    rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f (latticeConj hℂ x) =
      latticeConj h'ℂ (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f x) := by
  induction x using hℂ.inductionOn with
  | zero => simp
  | tmul v =>
      rw [latticeConj_ι, ← rationalToComplexLinearEquiv_one_tmul_ι hℚ hℂ,
        rationalMapToComplex_rationalToComplexLinearEquiv_tmul,
        latticeConj_rationalToComplexLinearEquiv_one_tmul]
  | smul z x hx => simp only [map_smulₛₗ, RingHom.id_apply, hx]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The complexification of a rational map commutes with lattice conjugation, as an identity of
conjugate-linear maps. -/
theorem rationalMapToComplex_comp_latticeConj (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f : Vℚ →ₗ[ℚ] V'ℚ) :
    (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f).comp (latticeConj hℂ) =
      (latticeConj h'ℂ).comp (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f) :=
  LinearMap.ext (rationalMapToComplex_commutes_conj hℚ hℂ h'ℚ h'ℂ f)

section Comp

variable {V''ℤ V''ℚ V''ℂ : Type*}
variable [AddCommGroup V''ℤ]
variable [AddCommGroup V''ℚ] [Module ℚ V''ℚ]
variable [AddCommGroup V''ℂ] [Module ℂ V''ℂ]
variable {ι''ℚ : V''ℤ →ₗ[ℤ] V''ℚ} {ι''ℂ : V''ℤ →ₗ[ℤ] V''ℂ}

/-- Complexification preserves composition of rational linear maps. -/
theorem rationalMapToComplex_comp
    (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (h'ℚ : IsBaseChange ℚ ι'ℚ) (h'ℂ : IsBaseChange ℂ ι'ℂ)
    (h''ℚ : IsBaseChange ℚ ι''ℚ) (h''ℂ : IsBaseChange ℂ ι''ℂ)
    (f : Vℚ →ₗ[ℚ] V'ℚ) (g : V'ℚ →ₗ[ℚ] V''ℚ) :
    rationalMapToComplex hℚ hℂ h''ℚ h''ℂ (g ∘ₗ f) =
      rationalMapToComplex h'ℚ h'ℂ h''ℚ h''ℂ g ∘ₗ
        rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f := by
  ext x
  simp [rationalMapToComplex, LinearMap.baseChange_comp]

end Comp

/-- Complexifying the image of a rational subspace is the image of its complexification. -/
theorem map_rationalToComplexSubmodule (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f : Vℚ →ₗ[ℚ] V'ℚ) (W : Submodule ℚ Vℚ) :
    (rationalToComplexSubmodule hℚ hℂ W).map
        (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f) =
      rationalToComplexSubmodule h'ℚ h'ℂ (W.map f) := by
  rw [rationalToComplexSubmodule_eq_span, Submodule.map_span,
    rationalToComplexSubmodule_eq_span]
  congr 1
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨rationalToComplexLinearEquiv hℚ hℂ (1 ⊗ₜ[ℚ] y), ⟨y, hy, rfl⟩, by simp⟩

/-- A rational map carrying one rational subspace into another carries their complexifications
into one another. -/
theorem map_rationalToComplexSubmodule_le (hℚ : IsBaseChange ℚ ιℚ)
    (hℂ : IsBaseChange ℂ ιℂ) (h'ℚ : IsBaseChange ℚ ι'ℚ)
    (h'ℂ : IsBaseChange ℂ ι'ℂ) (f : Vℚ →ₗ[ℚ] V'ℚ)
    {W : Submodule ℚ Vℚ} {W' : Submodule ℚ V'ℚ} (hW : W.map f ≤ W') :
    (rationalToComplexSubmodule hℚ hℂ W).map
        (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f) ≤
      rationalToComplexSubmodule h'ℚ h'ℂ W' := by
  rw [map_rationalToComplexSubmodule]
  exact rationalToComplexSubmodule_mono h'ℚ h'ℂ hW

end Map

end TauCeti.Hodge
