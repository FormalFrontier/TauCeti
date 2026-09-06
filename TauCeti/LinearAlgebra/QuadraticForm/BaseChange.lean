/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Prod
import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Base change of quadratic forms

This file supplies the functorial API for extending quadratic spaces along a commutative algebra.
It lifts isometries and isometric equivalences by extending their underlying linear maps, records
the interaction with the additive operations on forms, and proves that finite-dimensional
nondegenerate forms remain nondegenerate over a field extension.

These results complement Mathlib's construction `QuadraticForm.baseChange` and its pure-tensor
evaluation theorem.  They allow localizations of a quadratic space to inherit maps and regularity
from the original space without choosing bases in each completion.
-/

public section
noncomputable section

open scoped TensorProduct

namespace TauCeti.QuadraticForm

universe uR uA uM uN

section CommRing

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
variable [Invertible (2 : R)]
variable {M : Type uM} {N : Type uN}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {Q₁ : _root_.QuadraticForm R M} {Q₂ : _root_.QuadraticForm R N}

/-- Base change of an isometry of quadratic forms. -/
def Isometry.baseChange (f : Q₁ →qᵢ Q₂) (A : Type uA) [CommRing A] [Algebra R A] :
    Q₁.baseChange A →qᵢ Q₂.baseChange A where
  toLinearMap := f.toLinearMap.baseChange A
  map_app' x := by
    have h : (Q₂.baseChange A).comp (f.toLinearMap.baseChange A) = Q₁.baseChange A := by
      apply _root_.baseChange_ext
      intro m
      simp
    exact DFunLike.congr_fun h x

/-- On pure tensors, base change of an isometry applies the original isometry to the vector. -/
@[simp]
theorem Isometry.baseChange_tmul (f : Q₁ →qᵢ Q₂) (a : A) (m : M) :
    Isometry.baseChange f A (a ⊗ₜ m) = a ⊗ₜ f m :=
  LinearMap.baseChange_tmul f.toLinearMap a m

/-- Base change of an isometric equivalence of quadratic forms. -/
def IsometryEquiv.baseChange (f : Q₁.IsometryEquiv Q₂) (A : Type uA)
    [CommRing A] [Algebra R A] : (Q₁.baseChange A).IsometryEquiv (Q₂.baseChange A) where
  toLinearEquiv := f.toLinearEquiv.baseChange R A
  map_app' x := (Isometry.baseChange f.toIsometry A).map_app x

/-- On pure tensors, base change of an isometric equivalence applies the original equivalence to
the vector. -/
@[simp]
theorem IsometryEquiv.baseChange_tmul (f : Q₁.IsometryEquiv Q₂) (a : A) (m : M) :
    IsometryEquiv.baseChange f A (a ⊗ₜ m) = a ⊗ₜ f m := by
  exact _root_.LinearEquiv.baseChange_tmul R A M N (e := f.toLinearEquiv) a m

/-- Isometric quadratic forms remain isometric after base change. -/
theorem Equivalent.baseChange (h : Q₁.Equivalent Q₂) (A : Type uA)
    [CommRing A] [Algebra R A] : (Q₁.baseChange A).Equivalent (Q₂.baseChange A) :=
  h.elim fun f ↦ ⟨IsometryEquiv.baseChange f A⟩

/-- The canonical equivalence distributing tensor product over a product identifies the base
change of an orthogonal sum with the orthogonal sum of the base changes. -/
def baseChangeProd (Q : _root_.QuadraticForm R M) (Q' : _root_.QuadraticForm R N) :
    (_root_.QuadraticForm.baseChange A (Q.prod Q')).IsometryEquiv
      ((Q.baseChange A).prod (Q'.baseChange A)) where
  toLinearEquiv := TensorProduct.prodRight R A A M N
  map_app' x := by
    have h : ((Q.baseChange A).prod (Q'.baseChange A)).comp
        (TensorProduct.prodRight R A A M N).toLinearMap =
          _root_.QuadraticForm.baseChange A (Q.prod Q') := by
      apply _root_.baseChange_ext
      intro m
      simp [Algebra.smul_def]
    exact DFunLike.congr_fun h x

/-- On pure tensors, the equivalence identifying base change with an orthogonal sum separates the
two components. -/
@[simp]
theorem baseChangeProd_tmul (Q : _root_.QuadraticForm R M)
    (Q' : _root_.QuadraticForm R N) (a : A) (m : M × N) :
    baseChangeProd (A := A) Q Q' (a ⊗ₜ m) = (a ⊗ₜ m.1, a ⊗ₜ m.2) :=
  TensorProduct.prodRight_tmul R A A M N a m

/-- Base change sends the zero quadratic form to the zero quadratic form. -/
@[simp]
theorem baseChange_zero : (0 : _root_.QuadraticForm R M).baseChange A = 0 := by
  apply _root_.baseChange_ext
  simp

/-- Base change commutes with addition of quadratic forms. -/
@[simp]
theorem baseChange_add (Q Q' : _root_.QuadraticForm R M) :
    (Q + Q').baseChange A = Q.baseChange A + Q'.baseChange A := by
  apply _root_.baseChange_ext
  simp [Algebra.smul_def]

/-- Base change commutes with negation of quadratic forms. -/
@[simp]
theorem baseChange_neg (Q : _root_.QuadraticForm R M) :
    (-Q).baseChange A = -(Q.baseChange A) := by
  apply _root_.baseChange_ext
  simp

/-- Base change commutes with subtraction of quadratic forms. -/
@[simp]
theorem baseChange_sub (Q Q' : _root_.QuadraticForm R M) :
    (Q - Q').baseChange A = Q.baseChange A - Q'.baseChange A := by
  apply _root_.baseChange_ext
  simp [Algebra.smul_def]

/-- Scaling before base change agrees with scaling by the image of the scalar afterward. -/
@[simp]
theorem baseChange_smul (r : R) (Q : _root_.QuadraticForm R M) :
    (r • Q).baseChange A = algebraMap R A r • Q.baseChange A := by
  apply _root_.baseChange_ext
  simp [Algebra.smul_def, mul_comm]

end CommRing

section Field

variable {K : Type uR} {L : Type uA} [Field K] [Field L] [Algebra K L]
variable {V : Type uM} [AddCommGroup V] [Module K V]

/-- A finite-dimensional nondegenerate quadratic form stays nondegenerate after extending its
base field. -/
theorem Nondegenerate.baseChange [Invertible (2 : K)] [Invertible (2 : L)]
    [FiniteDimensional K V] {Q : _root_.QuadraticForm K V} (hQ : Q.Nondegenerate) :
    (Q.baseChange L).Nondegenerate := by
  let b := Module.Free.chooseBasis K V
  rw [← QuadraticMap.nondegenerate_associated_iff]
  rw [_root_.QuadraticForm.associated_baseChange]
  exact (TauCeti.nondegenerate_baseChange_iff (QuadraticMap.associated Q) b).2
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ)

end Field

end TauCeti.QuadraticForm
