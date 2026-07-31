/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Subalgebra.Center
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite products of matrix algebras

The dimension and the center of a product `Π i, Matₙᵢ(k)` of matrix algebras over a field, both
read off the sizes `nᵢ` alone. Such a product is what a structure theorem of Artin--Wedderburn type
presents an algebra as, and these are the invariants such a presentation transports.

* `TauCeti.finrank_pi_matrix`: the dimension of the product is `∑ᵢ nᵢ²`;
* `TauCeti.centerPiMatrixAlgEquiv`: when every size is nonzero the center consists of the tuples of
  scalar matrices, so it is the algebra `ι → k` of functions on the index, whose dimension is the
  number of factors (`TauCeti.finrank_center_pi_matrix`).
-/

public section

namespace TauCeti

open scoped BigOperators

variable (k : Type*) [Field k] {ι : Type*} (d : ι → ℕ)

/-- The center of a product of nonzero matrix algebras over a field consists of the tuples of
scalar matrices, so it is the algebra of functions on the index. -/
noncomputable def centerPiMatrixAlgEquiv [∀ i, NeZero (d i)] :
    Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) ≃ₐ[k] (ι → k) :=
  centerPiAlgEquiv.trans (AlgEquiv.piCongrRight fun i =>
    haveI : Nonempty (Fin (d i)) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne (d i)))
    centerAlgEquivOfIsCentral k _)

/-- `centerPiMatrixAlgEquiv` reads off the scalar of each component: the `i`-th component of a
central tuple is the scalar matrix on the `i`-th value of the corresponding function. -/
@[simp]
theorem algebraMap_centerPiMatrixAlgEquiv_apply [∀ i, NeZero (d i)]
    (x : Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) (i : ι) :
    algebraMap k (Matrix (Fin (d i)) (Fin (d i)) k) (centerPiMatrixAlgEquiv k d x i) =
      (x : Π i, Matrix (Fin (d i)) (Fin (d i)) k) i := by
  simp [centerPiMatrixAlgEquiv]

/-- The inverse of `centerPiMatrixAlgEquiv` assembles a function on the index into the tuple of the
corresponding scalar matrices. -/
@[simp]
theorem centerPiMatrixAlgEquiv_symm_apply_coe [∀ i, NeZero (d i)] (f : ι → k) (i : ι) :
    ((centerPiMatrixAlgEquiv k d).symm f : Π i, Matrix (Fin (d i)) (Fin (d i)) k) i =
      algebraMap k (Matrix (Fin (d i)) (Fin (d i)) k) (f i) := by
  simp [centerPiMatrixAlgEquiv]

variable [Fintype ι]

/-- The dimension of a finite product of matrix algebras is the sum of the squares of the sizes. -/
theorem finrank_pi_matrix :
    Module.finrank k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) = ∑ i, d i ^ 2 := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_matrix]
  simp [sq]

/-- The center of a finite product of nonzero matrix algebras over a field has dimension the number
of factors. -/
theorem finrank_center_pi_matrix [∀ i, NeZero (d i)] :
    Module.finrank k (Subalgebra.center k (Π i, Matrix (Fin (d i)) (Fin (d i)) k)) =
      Fintype.card ι := by
  rw [(centerPiMatrixAlgEquiv k d).toLinearEquiv.finrank_eq, Module.finrank_pi]

end TauCeti
