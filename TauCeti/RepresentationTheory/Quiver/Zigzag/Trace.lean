/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Multiplication

/-!
# The symmetric Frobenius trace of a zigzag algebra

The zigzag algebra of a simple graph with no isolated vertex is a symmetric Frobenius algebra. This
file constructs the trace that witnesses it: the linear functional `TauCeti.zigzagTrace` which is
`1` on every volume class and `0` on the vertex idempotents and on the arrows, and proves that the
pairing `(x, y) ↦ tr (x * y)` is symmetric, associative and nondegenerate.

Both the symmetry and the nondegeneracy come from one computation. Write `ι` for the involution
`TauCeti.zigzagDualIndex` of the basis indices, which exchanges the idempotent and the volume class
at a vertex and reverses a dart. The multiplication table shows that the trace of a product of two
basis classes is `1` when the second index is `ι` of the first and `0` otherwise: the only products
with a volume component are `e_i x_i = x_i = x_i e_i` and `a_d a_{d.symm} = x_{d.snd}`. So the Gram
matrix of the pairing in the vertex, arrow and volume basis is the permutation matrix of `ι`.
Symmetry is then the fact that `ι` is an involution, and nondegeneracy is the fact that `ι` is a
bijection: pairing an element against `ι b` reads off its `b`-th coordinate, so an element
orthogonal to everything has all coordinates zero.

That the pairing is symmetric, associative and nondegenerate is exactly the statement that the
zigzag algebra is a symmetric Frobenius algebra; no `k` is assumed beyond a commutative ring, since
the Gram matrix argument never inverts a scalar. What is *not* proved here is self-injectivity,
which needs the induced isomorphism onto the dual bimodule and an injectivity criterion for modules
over a general base.

## Main definitions

* `TauCeti.zigzagDualIndex`: the involution of the basis indices pairing an idempotent with a volume
  class and a dart with its reverse.
* `TauCeti.zigzagTrace`: the Frobenius trace, the sum of the volume coordinates.
* `TauCeti.zigzagTracePairing`: the bilinear form `(x, y) ↦ tr (x * y)`.

## Main results

* `TauCeti.zigzagTrace_mul_comm`: the trace is a trace, `tr (x * y) = tr (y * x)`.
* `TauCeti.zigzagTracePairing_isSymm` and `TauCeti.zigzagTracePairing_nondegenerate`: the pairing is
  symmetric and nondegenerate.
* `TauCeti.zigzagTracePairing_mul_left`: the pairing is associative, `(xy, z) = (x, yz)`.
* `TauCeti.zigzagTracePairing_apply_zigzagBasisFun_zigzagDualIndex`: the classes indexed by `ι` are
  the dual basis of the pairing.

## References

This is the third clause of Layer 2 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, whose target
signatures `zigzagTrace`, `zigzagTracePairing`, `zigzagTracePairing_isSymm` and
`zigzagTracePairing_nondegenerate` appear in `TauCetiRoadmap/ZigzagPreprojective/Suggested.lean`.
See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-! ### The pairing involution of the basis indices -/

/-- The involution of the zigzag basis indices under which the trace pairing is a permutation
matrix: it exchanges the idempotent and the volume class at a vertex, and sends a dart to its
reverse. The basis class it names is the one pairing to `1` with the given basis class. -/
def zigzagDualIndex : ZigzagBasisIndex G → ZigzagBasisIndex G
  | .inl i => .inr (.inr i)
  | .inr (.inl d) => .inr (.inl d.symm)
  | .inr (.inr i) => .inl i

@[simp]
theorem zigzagDualIndex_inl (i : V) :
    zigzagDualIndex G (.inl i) = .inr (.inr i) := (rfl)

@[simp]
theorem zigzagDualIndex_inr_inl (d : G.Dart) :
    zigzagDualIndex G (.inr (.inl d)) = .inr (.inl d.symm) := (rfl)

@[simp]
theorem zigzagDualIndex_inr_inr (i : V) :
    zigzagDualIndex G (.inr (.inr i)) = .inl i := (rfl)

@[simp]
theorem zigzagDualIndex_zigzagDualIndex (b : ZigzagBasisIndex G) :
    zigzagDualIndex G (zigzagDualIndex G b) = b := by
  rcases b with i | d | i
  · rfl
  · rw [zigzagDualIndex_inr_inl, zigzagDualIndex_inr_inl, SimpleGraph.Dart.symm_symm]
  · rfl

theorem zigzagDualIndex_involutive : Function.Involutive (zigzagDualIndex G) :=
  zigzagDualIndex_zigzagDualIndex G

theorem zigzagDualIndex_injective : Function.Injective (zigzagDualIndex G) :=
  (zigzagDualIndex_involutive G).injective

/-- Naming the dual index is a symmetric relation, because it is an involution. -/
theorem eq_zigzagDualIndex_comm {b c : ZigzagBasisIndex G} :
    c = zigzagDualIndex G b ↔ b = zigzagDualIndex G c := by
  constructor <;> · rintro rfl; rw [zigzagDualIndex_zigzagDualIndex]

/-! ### The trace -/

variable [Finite V] (hns : ∀ i : V, ∃ j, G.Adj i j)

/-- **The Frobenius trace of a zigzag algebra**: the sum of the coordinates of an element in the
volume classes. It is `1` on each volume class and `0` on the vertex idempotents and the arrows. -/
noncomputable def zigzagTrace : nonisolatedZigzagQuotient k G →ₗ[k] k :=
  (zigzagBasis k G hns).constr k (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1))

/-- The trace on the vertex, arrow and volume basis: it is `1` on the volume block and `0` on the
other two. -/
theorem zigzagTrace_zigzagBasisFun (b : ZigzagBasisIndex G) :
    zigzagTrace k G hns (zigzagBasisFun k G b)
      = Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1) b := by
  rw [← zigzagBasis_apply k G hns b]
  exact (zigzagBasis k G hns).constr_basis k
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1)) b

/-- The trace vanishes on a vertex idempotent. -/
@[simp]
theorem zigzagTrace_zigzagMk_vertexIdempotent (i : V) :
    zigzagTrace k G hns (zigzagMk k G (vertexIdempotent k (vertex G i))) = 0 := by
  simpa using zigzagTrace_zigzagBasisFun k G hns (.inl i)

/-- The trace vanishes on an arrow. -/
theorem zigzagTrace_zigzagMk_ofArrow (d : G.Dart) :
    zigzagTrace k G hns (zigzagMk k G (ofArrow (arrow G d.adj))) = 0 := by
  simpa using zigzagTrace_zigzagBasisFun k G hns (.inr (.inl d))

/-- The trace is one on every volume class. -/
@[simp]
theorem zigzagTrace_zigzagVolume (i : V) : zigzagTrace k G hns (zigzagVolume k G i) = 1 := by
  simpa using zigzagTrace_zigzagBasisFun k G hns (.inr (.inr i))

/-! ### The trace pairing -/

/-- **The Frobenius pairing of a zigzag algebra**, `(x, y) ↦ tr (x * y)`. -/
noncomputable def zigzagTracePairing : LinearMap.BilinForm k (nonisolatedZigzagQuotient k G) :=
  LinearMap.mk₂ k (fun x y => zigzagTrace k G hns (x * y))
    (fun _ _ _ => by rw [add_mul, map_add]) (fun _ _ _ => by rw [smul_mul_assoc, map_smul])
    (fun _ _ _ => by rw [mul_add, map_add]) (fun _ _ _ => by rw [mul_smul_comm, map_smul])

@[simp]
theorem zigzagTracePairing_apply (x y : nonisolatedZigzagQuotient k G) :
    zigzagTracePairing k G hns x y = zigzagTrace k G hns (x * y) := (rfl)

/-- **The trace pairing is associative**: it is computed from the product of all three factors, so
the bracketing is immaterial. Together with symmetry and nondegeneracy this is what makes the
zigzag algebra a symmetric Frobenius algebra. -/
theorem zigzagTracePairing_mul_left (x y z : nonisolatedZigzagQuotient k G) :
    zigzagTracePairing k G hns (x * y) z = zigzagTracePairing k G hns x (y * z) := by
  rw [zigzagTracePairing_apply, zigzagTracePairing_apply, mul_assoc]

/-! ### The Gram matrix of the pairing -/

open scoped Classical in
/-- **The Gram matrix of the trace pairing is the permutation matrix of `zigzagDualIndex`.** The
trace of a product of two basis classes is `1` exactly when the second index is the dual of the
first, and `0` otherwise. -/
theorem zigzagTracePairing_zigzagBasisFun (b c : ZigzagBasisIndex G) :
    zigzagTracePairing k G hns (zigzagBasisFun k G b) (zigzagBasisFun k G c)
      = if c = zigzagDualIndex G b then 1 else 0 := by
  rw [zigzagTracePairing_apply]
  rcases b with i | d | i <;> rcases c with i' | d' | i' <;>
    simp only [zigzagBasisFun_inl, zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
      zigzagDualIndex_inl, zigzagDualIndex_inr_inl, zigzagDualIndex_inr_inr]
  · rcases eq_or_ne i i' with rfl | h
    · rw [zigzagMk_vertexIdempotent_mul_self, zigzagTrace_zigzagMk_vertexIdempotent]
      simp
    · rw [zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G h, map_zero]
      simp
  · rcases eq_or_ne i d'.snd with rfl | h
    · rw [zigzagMk_vertexIdempotent_mul_ofArrow, zigzagTrace_zigzagMk_ofArrow]
      simp
    · rw [zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G d' h, map_zero]
      simp
  · rcases eq_or_ne i i' with rfl | h
    · rw [zigzagMk_vertexIdempotent_mul_zigzagVolume, zigzagTrace_zigzagVolume]
      simp
    · rw [zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G h, map_zero]
      simp [Ne.symm h]
  · rcases eq_or_ne i' d.fst with rfl | h
    · rw [zigzagMk_ofArrow_mul_vertexIdempotent, zigzagTrace_zigzagMk_ofArrow]
      simp
    · rw [zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G d h, map_zero]
      simp
  · rcases eq_or_ne d' d.symm with rfl | h
    · rw [zigzagMk_ofArrow_mul_ofArrow_symm, zigzagTrace_zigzagVolume]
      simp
    · rw [zigzagMk_ofArrow_mul_ofArrow_of_ne k G h, map_zero]
      simp [h]
  · rw [zigzagMk_ofArrow_mul_zigzagVolume, map_zero]
    simp
  · rcases eq_or_ne i' i with rfl | h
    · rw [zigzagVolume_mul_zigzagMk_vertexIdempotent, zigzagTrace_zigzagVolume]
      simp
    · rw [zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G h, map_zero]
      simp [h]
  · rw [zigzagVolume_mul_zigzagMk_ofArrow, map_zero]
    simp
  · rw [zigzagVolume_mul_zigzagVolume, map_zero]
    simp

/-! ### Symmetry, the dual basis, and nondegeneracy -/

/-- **The trace is a trace**: `tr (x * y) = tr (y * x)`. The Gram matrix of the pairing is the
permutation matrix of an involution, hence symmetric. -/
theorem zigzagTrace_mul_comm (x y : nonisolatedZigzagQuotient k G) :
    zigzagTrace k G hns (x * y) = zigzagTrace k G hns (y * x) := by
  classical
  have key : zigzagTracePairing k G hns = (zigzagTracePairing k G hns).flip := by
    refine (zigzagBasis k G hns).ext fun b => (zigzagBasis k G hns).ext fun c => ?_
    have hflip : (zigzagTracePairing k G hns).flip (zigzagBasis k G hns b)
          (zigzagBasis k G hns c)
        = zigzagTracePairing k G hns (zigzagBasis k G hns c) (zigzagBasis k G hns b) := rfl
    rw [hflip, zigzagBasis_apply, zigzagBasis_apply, zigzagTracePairing_zigzagBasisFun,
      zigzagTracePairing_zigzagBasisFun]
    exact if_congr (eq_zigzagDualIndex_comm G) rfl rfl
  exact LinearMap.congr_fun₂ key x y

/-- **The trace pairing is symmetric.** -/
theorem zigzagTracePairing_isSymm : (zigzagTracePairing k G hns).IsSymm :=
  ⟨fun x y => zigzagTrace_mul_comm k G hns x y⟩

/-- **The dual basis of the trace pairing.** Pairing an element against the basis class of the dual
index of `b` reads off its `b`-th coordinate. -/
theorem zigzagTracePairing_apply_zigzagBasisFun_zigzagDualIndex
    (x : nonisolatedZigzagQuotient k G) (b : ZigzagBasisIndex G) :
    zigzagTracePairing k G hns x (zigzagBasisFun k G (zigzagDualIndex G b))
      = (zigzagBasis k G hns).repr x b := by
  classical
  have key : (zigzagTracePairing k G hns).flip (zigzagBasisFun k G (zigzagDualIndex G b))
      = (zigzagBasis k G hns).coord b := by
    refine (zigzagBasis k G hns).ext fun c => ?_
    have hflip : (zigzagTracePairing k G hns).flip
          (zigzagBasisFun k G (zigzagDualIndex G b)) (zigzagBasis k G hns c)
        = zigzagTracePairing k G hns (zigzagBasis k G hns c)
            (zigzagBasisFun k G (zigzagDualIndex G b)) := rfl
    rw [hflip, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      zigzagBasis_apply, zigzagTracePairing_zigzagBasisFun]
    refine if_congr ?_ rfl rfl
    rw [(zigzagDualIndex_injective G).eq_iff]
    exact eq_comm
  have hx := LinearMap.congr_fun key x
  rw [Module.Basis.coord_apply] at hx
  exact hx

/-- **The trace pairing is nondegenerate.** Its Gram matrix is the permutation matrix of a
bijection, so an element orthogonal to every basis class has every coordinate zero. -/
theorem zigzagTracePairing_nondegenerate : (zigzagTracePairing k G hns).Nondegenerate := by
  have hleft : (zigzagTracePairing k G hns).SeparatingLeft := by
    intro x hx
    refine (zigzagBasis k G hns).forall_coord_eq_zero_iff.mp fun b => ?_
    rw [Module.Basis.coord_apply, ← zigzagTracePairing_apply_zigzagBasisFun_zigzagDualIndex]
    exact hx _
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  rw [zigzagTracePairing_apply, zigzagTrace_mul_comm, ← zigzagTracePairing_apply]
  exact hy x

end TauCeti
