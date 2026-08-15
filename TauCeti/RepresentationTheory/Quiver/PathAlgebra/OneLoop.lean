/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The path algebra of the one-loop quiver

This file defines the quiver with one vertex and one loop and identifies its path algebra with the
additive monoid algebra on `ℕ`, equivalently the polynomial algebra in one variable. It also shows
that this path algebra is infinite-dimensional over a division ring.

## Main declarations

* `TauCeti.Quiver.OneLoop`: the quiver with one vertex and one loop.
* `TauCeti.PathAlgebra.oneLoopAlgEquiv`: its path algebra is `AddMonoidAlgebra k ℕ`.
* `TauCeti.not_finiteDimensional_pathAlgebra_oneLoop`: the one-loop path algebra is
  infinite-dimensional.
-/

public section

namespace TauCeti

open _root_.Quiver

universe v w

namespace Quiver

/-- The quiver with one vertex and one loop. -/
inductive OneLoop : Type
  | vertex
  deriving DecidableEq

namespace OneLoop

instance : Fintype OneLoop where
  elems := {vertex}
  complete x := by cases x; simp

instance : Unique OneLoop where
  default := vertex
  uniq x := by cases x; rfl

instance : _root_.Quiver OneLoop where
  Hom _ _ := PUnit

instance (a b : OneLoop) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The unique loop in the one-loop quiver. -/
def loop : (vertex : OneLoop) ⟶ vertex := PUnit.unit

private def pathOfLength : ℕ → _root_.Quiver.Path (vertex : OneLoop) vertex
  | 0 => .nil
  | n + 1 => (pathOfLength n).cons loop

@[simp]
private theorem length_pathOfLength (n : ℕ) : (pathOfLength n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathOfLength, ih]

private theorem length_toList {a b : OneLoop}
    (p : _root_.Quiver.Path a b) : p.toList.length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

private theorem path_eq_pathOfLength (p : _root_.Quiver.Path (vertex : OneLoop) vertex) :
    p = pathOfLength p.length := by
  apply (_root_.Quiver.Path.toList_injective vertex vertex)
  apply List.length_injective
  rw [length_toList, length_toList, length_pathOfLength]

/-- Paths in the one-loop quiver are classified by their length. -/
private def totalPathEquivNat : Quiver.TotalPath OneLoop ≃ ℕ where
  toFun x := x.2.2.length
  invFun n := ⟨vertex, vertex, pathOfLength n⟩
  left_inv x := by
    obtain ⟨a, b, p⟩ := x
    cases a
    cases b
    simp only
    exact congrArg (fun q => (⟨vertex, vertex, q⟩ : Quiver.TotalPath OneLoop))
      (path_eq_pathOfLength p).symm
  right_inv := length_pathOfLength

end OneLoop

end Quiver

namespace PathAlgebra

variable (k : Type w) [CommSemiring k]

private noncomputable def oneLoopLinearEquiv :
    pathAlgebra k Quiver.OneLoop ≃ₗ[k] AddMonoidAlgebra k ℕ :=
  ((pathAlgebraBasis k Quiver.OneLoop).repr.trans
      (Finsupp.domLCongr Quiver.OneLoop.totalPathEquivNat)).trans
    (AddMonoidAlgebra.coeffLinearEquiv k).symm

private theorem oneLoopLinearEquiv_ofPath (x : Quiver.TotalPath Quiver.OneLoop) :
    oneLoopLinearEquiv k (PathAlgebra.ofPath x) =
      AddMonoidAlgebra.single (Quiver.OneLoop.totalPathEquivNat x) 1 := by
  have hb : pathAlgebraBasis k Quiver.OneLoop x = ofPath x :=
    congrFun (coe_pathAlgebraBasis k Quiver.OneLoop) x
  rw [← hb]
  simp only [oneLoopLinearEquiv, LinearEquiv.trans_apply, Module.Basis.repr_self]
  simp

private theorem oneLoopLinearEquiv_single (x : Quiver.TotalPath Quiver.OneLoop) (c : k) :
    oneLoopLinearEquiv k (single x c) =
      AddMonoidAlgebra.single (Quiver.OneLoop.totalPathEquivNat x) c := by
  rw [← mul_one c, ← smul_single, ← ofPath_eq_single, map_smul,
    oneLoopLinearEquiv_ofPath]
  simp

private theorem oneLoopLinearEquiv_map_one :
    oneLoopLinearEquiv k (1 : pathAlgebra k Quiver.OneLoop) = 1 := by
  rw [one_def]
  simp [vertexIdempotent_eq_single, oneLoopLinearEquiv_single,
    Quiver.OneLoop.totalPathEquivNat, ← AddMonoidAlgebra.one_def]

private theorem oneLoopLinearEquiv_map_mul (f g : pathAlgebra k Quiver.OneLoop) :
    oneLoopLinearEquiv k (f * g) = oneLoopLinearEquiv k f * oneLoopLinearEquiv k g := by
  induction f using induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂, add_mul]
  | single x a =>
    induction g using induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ => simp [ih₁, ih₂, mul_add]
    | single y b =>
      obtain ⟨x₁, x₂, p⟩ := x
      obtain ⟨y₁, y₂, q⟩ := y
      cases x₁
      cases x₂
      cases y₁
      cases y₂
      simp [oneLoopLinearEquiv_single, Quiver.OneLoop.totalPathEquivNat,
        _root_.Quiver.Path.length_comp, Nat.add_comm]

/-- The path algebra of the quiver with one vertex and one loop is the additive monoid algebra on
`ℕ` (equivalently, the polynomial algebra in one variable). -/
noncomputable def oneLoopAlgEquiv :
    pathAlgebra k Quiver.OneLoop ≃ₐ[k] AddMonoidAlgebra k ℕ :=
  AlgEquiv.ofLinearEquiv (oneLoopLinearEquiv k) (oneLoopLinearEquiv_map_one k)
    (oneLoopLinearEquiv_map_mul k)

end PathAlgebra

/-- Over a division ring, the path algebra of the one-loop quiver is infinite-dimensional. -/
theorem not_finiteDimensional_pathAlgebra_oneLoop (k : Type w) [DivisionRing k] :
    ¬ FiniteDimensional k (pathAlgebra k Quiver.OneLoop) := by
  let : Infinite (Quiver.TotalPath Quiver.OneLoop) :=
    Quiver.OneLoop.totalPathEquivNat.infinite_iff.mpr inferInstance
  intro h
  let : Module.Finite k (pathAlgebra k Quiver.OneLoop) := h
  exact Module.Finite.not_linearIndependent_of_infinite
    (⇑(pathAlgebraBasis k Quiver.OneLoop))
    (pathAlgebraBasis k Quiver.OneLoop).linearIndependent

end TauCeti

end
