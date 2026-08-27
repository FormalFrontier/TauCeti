/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.RootSpace
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.Basic

/-!
# Coordinate roots for the diagonal torus in the general linear group

This file specializes `SplitTorus.coordinateRootDatum` to the coordinate lattice
`ULift (Fin n)`. Its roots and coroots are the vectors `e_i - e_j`, and reflections transpose the
two coordinates indexed by the reflecting root.

The construction supplies the expected coordinate root datum and proves that each of its roots,
viewed as a multiplicative character, occurs among the nontrivial adjoint weights of `GL_n`.
Only this inclusion into `Derivation.nontrivialAdjointWeights` is proved here; the converse
identification with the packaged root set is proved in `GeneralLinear.Root.Adjoint`.

The character and cocharacter lattices are the established split-torus coordinate models

```text
X*(T) = ULift (Fin n) →₀ ℤ,    X_*(T) = ULift (Fin n) → ℤ.
```

## Main declarations

* `TauCeti.GeneralLinear.DiagonalRootIndex`: ordered off-diagonal coordinate pairs.
* `TauCeti.GeneralLinear.diagonalRoot` and `diagonalCoroot`: the vectors `e_i - e_j`, defined for
  arbitrary pairs of matrix indices.
* `TauCeti.GeneralLinear.diagonalRootDatum`: the coordinate-difference root datum specialized to
  the diagonal torus lattice of `GL_n`.
* `TauCeti.GeneralLinear.diagonalRootDatum_pairing_apply`: the closed Cartan-integer formula.
* `TauCeti.GeneralLinear.diagonalRootDatum_reflection_apply` and
  `diagonalRootDatum_coreflection_apply`: reflections transpose arbitrary character and
  cocharacter coordinates.
* `TauCeti.GeneralLinear.diagonalRootDatum_reflectionPerm`: reflections act by simultaneous
  coordinate transposition on the two indices.
* `TauCeti.GeneralLinear.ofAdd_root_mem_nontrivialAdjointWeights`: every packaged root occurs as
  a nontrivial adjoint weight.
* `TauCeti.GeneralLinear.diagonalCorootCocharacter`: the genuine split-torus cocharacter with a
  prescribed coordinate coroot.
* `TauCeti.GeneralLinear.pairing_matrixUnitWeight_diagonalCorootCocharacter`: evaluation of a
  matrix-unit weight on such a cocharacter agrees with the root-datum pairing.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This advances Layer 7, "Root datum of `(G, T)`", of the ReductiveGroups roadmap through its
standard `GL_n` split-coordinate example.
-/

public section

open Set Function

namespace TauCeti.GeneralLinear

universe u

noncomputable section

/-- Ordered pairs of distinct lifted matrix coordinates indexing the packaged roots. -/
abbrev DiagonalRootIndex (n : ℕ) :=
  SplitTorus.CoordinateRootIndex (ULift.{u} (Fin n))

/-- The character-lattice vector `e_i - e_j`, defined for arbitrary matrix indices. -/
noncomputable def diagonalRoot {n : ℕ} (i j : Fin n) : ULift.{u} (Fin n) →₀ ℤ :=
  Multiplicative.toAdd (matrixUnitWeight i j)

/-- The cocharacter-lattice vector `e_i - e_j`, defined for arbitrary matrix indices. -/
noncomputable def diagonalCoroot {n : ℕ} (i j : Fin n) : ULift.{u} (Fin n) → ℤ :=
  ⇑(diagonalRoot i j)

/-- Evaluation of a diagonal root at a torus coordinate. -/
@[simp]
theorem diagonalRoot_apply {n : ℕ} (i j : Fin n) (a : ULift.{u} (Fin n)) :
    diagonalRoot i j a =
      (if a = ULift.up i then 1 else 0) - (if a = ULift.up j then 1 else 0) :=
  toAdd_matrixUnitWeight_apply i j a

/-- Evaluation of a diagonal coroot at a torus coordinate. -/
@[simp]
theorem diagonalCoroot_apply {n : ℕ} (i j : Fin n) (a : ULift.{u} (Fin n)) :
    diagonalCoroot i j a =
      (if a = ULift.up i then 1 else 0) - (if a = ULift.up j then 1 else 0) := by
  rw [diagonalCoroot, diagonalRoot_apply]

/-- A diagonal coroot is the function underlying the corresponding diagonal root. -/
theorem coe_diagonalRoot {n : ℕ} (i j : Fin n) :
    ⇑(diagonalRoot i j : ULift.{u} (Fin n) →₀ ℤ) = diagonalCoroot i j :=
  by rw [diagonalCoroot]

/-- The coordinate root datum on the diagonal split-torus lattices of `GL_n`.

This package is constructed directly from the coordinate differences. The theorem
`ofAdd_root_mem_nontrivialAdjointWeights` proves that its roots are adjoint weights; the converse
classification is `mem_nontrivialAdjointWeights_iff_exists_diagonalRoot` in
`GeneralLinear.Root.Adjoint`. -/
noncomputable def diagonalRootDatum (n : ℕ) :
    RootDatum (DiagonalRootIndex n) (ULift.{u} (Fin n) →₀ ℤ) (ULift.{u} (Fin n) → ℤ) :=
  SplitTorus.coordinateRootDatum (ULift.{u} (Fin n))

/-- The diagonal root datum is the coordinate root datum on the universe-lifted indices. -/
theorem diagonalRootDatum_eq_coordinateRootDatum (n : ℕ) :
    diagonalRootDatum.{u} n = SplitTorus.coordinateRootDatum (ULift.{u} (Fin n)) :=
  -- `(rfl)` opts out of exporting the definitional equality, so the definition can remain opaque
  -- while this theorem provides the downstream rewriting interface.
  (rfl)

/-- The underlying bilinear map is the split-torus character--cocharacter dot pairing. -/
@[simp]
theorem diagonalRootDatum_toLinearMap (n : ℕ) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).toLinearMap =
      SplitTorus.dotPairing := by
  rw [diagonalRootDatum, SplitTorus.coordinateRootDatum_toLinearMap]

/-- The roots of `diagonalRootDatum` are the matrix-coordinate differences `e_i - e_j`. -/
@[simp]
theorem diagonalRootDatum_root {n : ℕ} (p : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p =
      diagonalRoot p.1.1.down p.1.2.down := by
  rw [diagonalRootDatum, SplitTorus.coordinateRootDatum_root]
  ext a
  rw [SplitTorus.coordinateRoot_apply, diagonalRoot_apply]
  rw [ULift.up_down, ULift.up_down]
  split_ifs <;> rfl

/-- The coroots of `diagonalRootDatum` are the matrix-coordinate differences `e_i - e_j`. -/
@[simp]
theorem diagonalRootDatum_coroot {n : ℕ} (p : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ _ (ULift.{u} (Fin n) → ℤ)).coroot p =
      diagonalCoroot p.1.1.down p.1.2.down := by
  rw [diagonalRootDatum, SplitTorus.coordinateRootDatum_coroot]
  ext a
  rw [SplitTorus.coordinateCoroot_apply, diagonalCoroot_apply]
  rw [ULift.up_down, ULift.up_down]
  split_ifs <;> rfl

/-- The root-datum pairing is the split-torus dot product on diagonal root and coroot vectors.
This bridge is not a simp lemma; `diagonalRootDatum_pairing_apply` is the normal form. -/
theorem diagonalRootDatum_pairing {n : ℕ} (p q : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).pairing p q =
      SplitTorus.dotPairing (σ := ULift.{u} (Fin n))
        (diagonalRoot p.1.1.down p.1.2.down)
        (diagonalCoroot q.1.1.down q.1.2.down) := by
  rw [← RootPairing.root_coroot_eq_pairing, diagonalRootDatum_root,
    diagonalRootDatum_coroot, diagonalRootDatum_toLinearMap]

open Classical in
/-- Closed formula for the Cartan integers of the diagonal coordinate root datum. -/
@[simp]
theorem diagonalRootDatum_pairing_apply {n : ℕ} (p q : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).pairing p q =
      (if p.1.1 = q.1.1 then 1 else 0) - (if p.1.1 = q.1.2 then 1 else 0) -
        ((if p.1.2 = q.1.1 then 1 else 0) - (if p.1.2 = q.1.2 then 1 else 0)) := by
  rw [diagonalRootDatum, SplitTorus.coordinateRootDatum_pairing_apply]
  split_ifs <;> rfl

/-- The index of the root obtained by applying the reflection in the root indexed by `p` to the
root indexed by `q`: both entries of `q` are transposed by `Equiv.swap p.1.1 p.1.2`. -/
noncomputable def diagonalReflectionIndex {n : ℕ} (p q : DiagonalRootIndex n) :
    DiagonalRootIndex n :=
  SplitTorus.coordinatePermRootIndex (Equiv.swap p.1.1 p.1.2) q

open Classical in
/-- The two entries of `diagonalReflectionIndex p q` are the corresponding coordinate swaps. -/
@[simp]
theorem diagonalReflectionIndex_coe {n : ℕ} (p q : DiagonalRootIndex n) :
    (diagonalReflectionIndex p q).1 =
      ((Equiv.swap p.1.1 p.1.2) q.1.1, (Equiv.swap p.1.1 p.1.2) q.1.2) := by
  rw [diagonalReflectionIndex, SplitTorus.coordinatePermRootIndex_coe]

/-- The reflection associated to a root acts on indices by transposing both coordinates. -/
@[simp]
theorem diagonalRootDatum_reflectionPerm {n : ℕ} (p q : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).reflectionPerm p q =
      diagonalReflectionIndex p q := by
  rw [diagonalRootDatum, SplitTorus.coordinateRootDatum_reflectionPerm,
    diagonalReflectionIndex]

/-- Reflection in the diagonal root indexed by `p` precomposes an arbitrary character with the
corresponding coordinate transposition. -/
@[simp]
theorem diagonalRootDatum_reflection_apply {n : ℕ} (p : DiagonalRootIndex n)
    (x : ULift.{u} (Fin n) →₀ ℤ) (a : ULift.{u} (Fin n)) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).reflection p x a =
      x ((Equiv.swap p.1.1 p.1.2) a) := by
  rw [diagonalRootDatum, SplitTorus.coordinateRootDatum_reflection_apply]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> rfl

/-- Coreflection in the diagonal root indexed by `p` precomposes an arbitrary cocharacter with the
corresponding coordinate transposition. -/
@[simp]
theorem diagonalRootDatum_coreflection_apply {n : ℕ} (p : DiagonalRootIndex n)
    (x : ULift.{u} (Fin n) → ℤ) (a : ULift.{u} (Fin n)) :
    (diagonalRootDatum n : RootDatum _ _ (ULift.{u} (Fin n) → ℤ)).coreflection p x a =
      x ((Equiv.swap p.1.1 p.1.2) a) := by
  rw [diagonalRootDatum, SplitTorus.coordinateRootDatum_coreflection_apply]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> rfl

/-- The diagonal coordinate root datum is reduced. -/
instance isReduced_diagonalRootDatum (n : ℕ) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).IsReduced := by
  rw [diagonalRootDatum]
  infer_instance

/-- A diagonal root, viewed multiplicatively, is the corresponding matrix-unit weight. -/
@[simp]
theorem ofAdd_diagonalRoot {n : ℕ} (i j : Fin n) :
    Multiplicative.ofAdd (diagonalRoot i j : ULift.{u} (Fin n) →₀ ℤ) =
      matrixUnitWeight i j :=
  ofAdd_toAdd _

/-- Every root in the diagonal coordinate root datum occurs as a nontrivial adjoint weight of
`GL_n`. This is the proved inclusion from the packaged root set into the adjoint weight set. -/
theorem ofAdd_root_mem_nontrivialAdjointWeights {k : Type u} [Field k] {n : ℕ}
    (p : DiagonalRootIndex n) :
    Multiplicative.ofAdd
        ((diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p) ∈
      Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom := by
  rw [diagonalRootDatum_root, ofAdd_diagonalRoot]
  rcases p with ⟨⟨⟨i⟩, ⟨j⟩⟩, hij⟩
  exact matrixUnitWeight_mem_nontrivialAdjointWeights (k := k)
    (fun h ↦ hij (congrArg ULift.up h))

/-- The genuine cocharacter whose coordinate vector is the coroot `e_i - e_j`. -/
noncomputable def diagonalCorootCocharacter {n : ℕ} (i j : Fin n) :
    Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →* Multiplicative ℤ :=
  SplitTorus.cocharEquiv.symm (diagonalCoroot i j)

/-- The coordinates of `diagonalCorootCocharacter i j` are the coroot `e_i - e_j`. -/
@[simp]
theorem cocharEquiv_diagonalCorootCocharacter {n : ℕ} (i j : Fin n) :
    SplitTorus.cocharEquiv (diagonalCorootCocharacter i j :
      Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →* Multiplicative ℤ) = diagonalCoroot i j :=
  Equiv.apply_symm_apply _ _

/-- Evaluation of a matrix-unit weight on a diagonal coroot cocharacter is the pairing of the
diagonal coordinate root datum. -/
theorem pairing_matrixUnitWeight_diagonalCorootCocharacter {n : ℕ}
    (p q : DiagonalRootIndex n) :
    DiagonalizableGroup.pairing (matrixUnitWeight p.1.1.down p.1.2.down)
        (diagonalCorootCocharacter q.1.1.down q.1.2.down :
          Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →* Multiplicative ℤ) =
      (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).pairing p q := by
  rw [← ofAdd_diagonalRoot, SplitTorus.pairing_eq_dotPairing,
    cocharEquiv_diagonalCorootCocharacter, diagonalRootDatum_pairing]

end


end TauCeti.GeneralLinear
