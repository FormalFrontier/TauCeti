/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.TensorSquare
public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower

/-!
# The first decomposition of the standard representation

When `2` is invertible, the tensor square of a representation splits into its symmetric and
exterior squares. This file establishes the representation equivalence and specializes it to the
standard representation of the general linear group. Over a field, it also records the resulting
character identity.

## Main definitions

* `Representation.tensorSquareEquivSymmetricExterior` is the natural representation equivalence.
* `TauCeti.tensorSquareRepEquiv` specializes it to the standard representation of `GL n k`.
* `TauCeti.tensorSquare_char` is the associated character identity.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “The first decomposition”.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6.
-/

public section

open CategoryTheory
open Matrix
open scoped TensorProduct

universe v w

variable {R : Type} {G : Type v} {M : Type w}

namespace Representation

section CommRing

variable [CommRing R] [Invertible (2 : R)] [Monoid G]
variable [AddCommGroup M] [Module R M]

/-- The tensor square of a representation is equivalent to the product of its symmetric and
exterior squares when `2` is invertible. -/
noncomputable def tensorSquareEquivSymmetricExterior (ρ : Representation R G M) :
    (ρ.tensorPower 2).Equiv ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) :=
  .mk (TauCeti.tensorSquareEquivSymmetricExterior R M) fun g ↦ by
    apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
    rintro _ ⟨f, rfl⟩
    simp only [LinearMap.comp_apply, tensorPower_apply, PiTensorProduct.map_tprod]
    change TauCeti.tensorSquareEquivSymmetricExterior R M
        (PiTensorProduct.tprod R fun i ↦ ρ g (f i)) =
      ((ρ.symmetricPower 2).prod (ρ.exteriorPower 2)) g
        (TauCeti.tensorSquareEquivSymmetricExterior R M (PiTensorProduct.tprod R f))
    have h₁ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M
      (fun i ↦ ρ g (f i))
    have h₂ := TauCeti.tensorSquareEquivSymmetricExterior_tprod R M f
    rw [h₁, h₂]
    simp only [prod_apply_apply, symmetricPower_apply, SymmetricPower.map_tprod,
      exteriorPower_apply, exteriorPower.map_apply_ιMulti, Prod.mk.injEq, true_and]
    apply congrArg (exteriorPower.ιMulti R 2)
    funext i
    rfl

/-- The underlying linear equivalence of the tensor-square decomposition is the natural
linear-algebraic decomposition. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_toLinearEquiv (ρ : Representation R G M) :
    ρ.tensorSquareEquivSymmetricExterior.toLinearEquiv =
      TauCeti.tensorSquareEquivSymmetricExterior R M :=
  (rfl)

end CommRing

section Field

variable [Field R] [Monoid G]
variable [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- The character of a product of finite-dimensional representations is the sum of their
characters. -/
theorem char_prod (ρ : Representation R G M) {N : Type*}
    [AddCommGroup N] [Module R N] [FiniteDimensional R N]
    (σ : Representation R G N) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g := by
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

/-- The tensor-square character is the sum of the symmetric-square and exterior-square
characters. -/
theorem char_tensorSquare [NeZero (2 : R)] (ρ : Representation R G M) (g : G) :
    (ρ.character g) ^ 2 =
      (ρ.symmetricPower 2).character g + (ρ.exteriorPower 2).character g := by
  letI : Invertible (2 : R) := invertibleOfNonzero (NeZero.ne _)
  rw [← char_tensorPower ρ 2 g,
    Representation.char_iso ρ.tensorSquareEquivSymmetricExterior,
    char_prod]

end Field

end Representation

namespace TauCeti

variable (k : Type) (n : ℕ)

section Field

variable [Field k] [NeZero (2 : k)]

/-- The tensor square of the standard representation is equivalent to the product of its
symmetric and exterior squares. -/
noncomputable abbrev tensorSquareRepEquiv :
    (tensorPowerRep k n 2).Equiv
      ((symPowerRep k n 2).prod (extPowerRep k n 2)) :=
  letI : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
  (stdRep k n).tensorSquareEquivSymmetricExterior

/-- The tensor-square decomposition bundled as an isomorphism in `FDRep`. The product
representation is the direct sum of the symmetric and exterior squares. -/
noncomputable def tensorSquareFDRepIso :
    tensorPowerFDRep k n 2 ≅
      FDRep.of ((symPowerRep k n 2).prod (extPowerRep k n 2)) :=
  Action.mkIso
    (tensorSquareRepEquiv k n).toLinearEquiv.toFGModuleCatIso
    fun g ↦ by
      apply FGModuleCat.hom_ext
      exact (tensorSquareRepEquiv k n).isIntertwining' g

/-- The square of the standard character is the sum of the symmetric-square and
exterior-square characters. -/
theorem tensorSquare_char (g : GL (Fin n) k) :
    Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ 2 =
      (symPowerRep k n 2).character g + (extPowerRep k n 2).character g := by
  rw [← char_stdRep]
  exact Representation.char_tensorSquare (stdRep k n) g

end Field

end TauCeti
