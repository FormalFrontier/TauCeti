/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.Geometry.Hodge.Dual
public import TauCeti.Geometry.Hodge.TensorProduct

/-!
# Internal Homs of pure Hodge structures

For finite-dimensional complex vector spaces, the internal Hom is the tensor product
`W₁^* ⊗ W₂`.  We use Mathlib's canonical equivalence between this tensor product and the space of
complex-linear maps, and transport the Hodge structure on the tensor product.  Thus the
construction has weight `n₂ - n₁`, as expected.

The conjugation on a linear map is the twisted conjugate
`f ↦ ω₂ ∘ f ∘ ω₁`.  The main component theorem records the grading carried by the transported
structure, while `hom_tmul_mem` gives the useful elementary generators of its Hodge pieces.

This is the `Hom` companion in Layer L0 of `TauCetiRoadmap/HodgeStructures/README.md`.  The
finite-dimensional hypothesis is the precise hypothesis needed by the tensor--Hom equivalence;
the pure Hodge structure itself remains unrestricted in dimension.

The construction follows Peters--Steenbrink, *Mixed Hodge Structures*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v

namespace HodgeStructureOn

variable {W₁ : Type u} {W₂ : Type v} [AddCommGroup W₁] [Module ℂ W₁]
  [AddCommGroup W₂] [Module ℂ W₂]
variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

/-- Conjugation on the internal Hom, given pointwise by `ω₂ (f (ω₁ x))`. -/
def homConjugation (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂) :
    Conjugation (W₁ →ₗ[ℂ] W₂) where
  toEquiv := LinearEquiv.arrowCongr ω₁.toEquiv ω₂.toEquiv
  involutive := by
    intro f
    ext x
    simp only [LinearEquiv.arrowCongr_apply, Conjugation.toEquiv_symm,
      Conjugation.apply_apply]

@[simp]
theorem homConjugation_apply (f : W₁ →ₗ[ℂ] W₂) (x : W₁) :
    (homConjugation ω₁ ω₂).toEquiv f x =
      ω₂.toEquiv (f (ω₁.toEquiv x)) :=
  by simp [homConjugation, LinearEquiv.arrowCongr_apply, Conjugation.toEquiv_symm]

section Finite

variable [FiniteDimensional ℂ W₁]

private theorem dualTensorHomEquiv_conj (x : Module.Dual ℂ W₁ ⊗[ℂ] W₂) :
    dualTensorHomEquiv ℂ W₁ W₂
        ((ω₁.dual.tensorProduct ω₂).toEquiv x) =
      (homConjugation ω₁ ω₂).toEquiv (dualTensorHomEquiv ℂ W₁ W₂ x) := by
  refine TensorProduct.induction_on x (by simp) ?_ (by
    intro x y hx hy
    simp only [map_add, hx, hy])
  intro φ y
  ext x
  simp only [dualTensorHomEquiv, Conjugation.tensorProduct_toEquiv_tmul,
    LinearEquiv.ofBijective_apply, dualTensorHom_apply,
    Conjugation.dual_toEquiv_apply, Complex.star_def, homConjugation_apply]
  -- The tensor--Hom equivalence unfolds to `dualTensorHom` only after extensionality.
  change (starRingEnd ℂ) (φ (ω₁.toEquiv x)) • ω₂.toEquiv y =
    ω₂.toEquiv (φ (ω₁.toEquiv x) • y)
  rw [map_smulₛₗ]

private theorem homEquiv_conj (f : W₁ →ₗ[ℂ] W₂) :
    (dualTensorHomEquiv ℂ W₁ W₂).symm
        ((homConjugation ω₁ ω₂).toEquiv f) =
      (ω₁.dual.tensorProduct ω₂).toEquiv
        ((dualTensorHomEquiv ℂ W₁ W₂).symm f) := by
  apply (dualTensorHomEquiv ℂ W₁ W₂).injective
  rw [LinearEquiv.apply_symm_apply]
  simpa using
    (dualTensorHomEquiv_conj (ω₁ := ω₁) (ω₂ := ω₂)
      (x := (dualTensorHomEquiv ℂ W₁ W₂).symm f)).symm

/-! ### The transported Hodge structure -/

/-- The internal Hom of two pure Hodge structures, of weight `-n₁ + n₂` (that is, `n₂ - n₁`).

The source is assumed finite-dimensional so that the canonical tensor--Hom map is an equivalence.
The filtration is transported from the tensor product of the dual of the source with the target;
in particular, this definition inherits the full opposed-filtration proof from the tensor-product
construction. -/
noncomputable def hom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (homConjugation ω₁ ω₂) (-n₁ + n₂) :=
  (hs₁.dual.tensorProduct hs₂).comap
    (dualTensorHomEquiv ℂ W₁ W₂).symm
      (homEquiv_conj (ω₁ := ω₁) (ω₂ := ω₂))

/-- The internal-Hom piece is the comap of the corresponding dual-tensor-product piece under the
inverse tensor--Hom equivalence. -/
@[simp]
theorem hom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂)
    (p : ℤ) :
    (hs₁.hom hs₂).piece p =
      ((hs₁.dual.tensorProduct hs₂).piece p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  exact HodgeStructureOn.comap_piece _ _ _ _

/-- A pure tensor `φ ⊗ y` gives a homogeneous map in the internal Hom. -/
theorem hom_tmul_mem (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂)
    {a b : ℤ} {φ : Module.Dual ℂ W₁} {y : W₂}
    (hφ : φ ∈ (hs₁.dual).piece a) (hy : y ∈ hs₂.piece b) :
    dualTensorHomEquiv ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y) ∈ (hs₁.hom hs₂).piece (a + b) := by
  rw [hom_piece]
  -- The comap membership is the tensor membership after applying the inverse equivalence.
  change (dualTensorHomEquiv ℂ W₁ W₂).symm
      (dualTensorHomEquiv ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y)) ∈
    (hs₁.dual.tensorProduct hs₂).piece (a + b)
  rw [LinearEquiv.symm_apply_apply]
  exact hs₁.dual.tmul_mem_tensorProduct hs₂ hφ hy

end Finite

end HodgeStructureOn

end TauCeti.Hodge
