/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.RootSpace
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.Basic

/-!
# The root datum of the diagonal torus in the general linear group

The roots of `GL_n` relative to its diagonal torus are the characters `e_i - e_j` indexed by
ordered pairs `i ≠ j`. Their coroots are the cocharacters with the same coordinate vectors.
This file packages these roots and coroots with the character--cocharacter pairing as a
`RootDatum` over `ℤ`.

The reflection attached to `(i, j)` interchanges coordinates `i` and `j`. Consequently it sends
the root indexed by `(a, b)` to the one indexed by `(swap i j a, swap i j b)`, and does the same
to coroots. The resulting root datum uses the coordinate models already established for the
diagonal split torus:

```text
X*(T) = ULift (Fin n) →₀ ℤ,    X_*(T) = ULift (Fin n) → ℤ.
```

The roots are connected to the adjoint calculation by `diagonalRoot_toMultiplicative`: their
multiplicative characters are exactly `GeneralLinear.matrixUnitWeight`. The coroot coordinates
are connected to genuine cocharacters through `SplitTorus.cocharEquiv`.

## Main declarations

* `TauCeti.GeneralLinear.DiagonalRootIndex`: ordered off-diagonal pairs indexing the roots.
* `TauCeti.GeneralLinear.diagonalRoot` and `diagonalCoroot`: the root and coroot coordinate maps.
* `TauCeti.GeneralLinear.diagonalRootDatum`: the root datum of `GL_n` relative to its diagonal
  torus.
* `TauCeti.GeneralLinear.diagonalRootDatum_reflectionPerm`: reflections act by simultaneous
  coordinate transposition on the two indices.
* `TauCeti.GeneralLinear.isReduced_diagonalRootDatum`: the diagonal root datum is reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 16.1 and 26.3.

This advances Layer 7, "Root datum of `(G, T)`", of the ReductiveGroups roadmap. It supplies the
root datum for the standard split pair consisting of `GL_n` and its diagonal torus; the existing
adjoint calculation identifies each root character with the weight of the corresponding matrix
unit.
-/

public section

open Set Function
open Module hiding reflection

namespace TauCeti.GeneralLinear

universe u

noncomputable section

/-- The roots of the diagonal torus in `GL_n` are indexed by ordered pairs of distinct matrix
indices. The pair `(i, j)` labels the root `e_i - e_j`. -/
abbrev DiagonalRootIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- The character-lattice vector `e_i - e_j` attached to an off-diagonal matrix entry. -/
def diagonalRoot {n : ℕ} (p : DiagonalRootIndex n) : ULift.{u} (Fin n) →₀ ℤ :=
  Finsupp.single (ULift.up p.1.1) 1 - Finsupp.single (ULift.up p.1.2) 1

/-- The cocharacter-lattice vector `e_i - e_j` attached to an off-diagonal matrix entry. -/
def diagonalCoroot {n : ℕ} (p : DiagonalRootIndex n) : ULift.{u} (Fin n) → ℤ :=
  Pi.single (ULift.up p.1.1) 1 - Pi.single (ULift.up p.1.2) 1

/-- Evaluation of a diagonal root at a torus coordinate. -/
@[simp]
theorem diagonalRoot_apply {n : ℕ} (p : DiagonalRootIndex n) (a : ULift.{u} (Fin n)) :
    diagonalRoot p a =
      (if a = ULift.up p.1.1 then 1 else 0) -
        (if a = ULift.up p.1.2 then 1 else 0) := by
  classical
  simp [diagonalRoot, Finsupp.single_apply, eq_comm]

/-- Evaluation of a diagonal coroot at a torus coordinate. -/
@[simp]
theorem diagonalCoroot_apply {n : ℕ} (p : DiagonalRootIndex n) (a : ULift.{u} (Fin n)) :
    diagonalCoroot p a =
      (if a = ULift.up p.1.1 then 1 else 0) -
        (if a = ULift.up p.1.2 then 1 else 0) := by
  classical
  simp [diagonalCoroot, Pi.single_apply]

private theorem diagonalRoot_injective {n : ℕ} :
    Injective (diagonalRoot : DiagonalRootIndex n → ULift.{u} (Fin n) →₀ ℤ) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨a, b⟩, hab⟩ h
  have hi := congrArg (fun x : ULift.{u} (Fin n) →₀ ℤ ↦ x (ULift.up i)) h
  have hj := congrArg (fun x : ULift.{u} (Fin n) →₀ ℤ ↦ x (ULift.up j)) h
  have hia : i = a := by
    by_contra hne
    by_cases hib : i = b
    · subst b
      simp [diagonalRoot_apply, hij, hne] at hi
    · simp [diagonalRoot_apply, hij, hne, hib] at hi
  subst a
  have hjb : j = b := by
    by_contra hne
    simp [diagonalRoot_apply, hne] at hj
  subst b
  rfl

private theorem diagonalCoroot_injective {n : ℕ} :
    Injective (diagonalCoroot : DiagonalRootIndex n → ULift.{u} (Fin n) → ℤ) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨a, b⟩, hab⟩ h
  have hi := congrArg (fun x : ULift.{u} (Fin n) → ℤ ↦ x (ULift.up i)) h
  have hj := congrArg (fun x : ULift.{u} (Fin n) → ℤ ↦ x (ULift.up j)) h
  have hia : i = a := by
    by_contra hne
    by_cases hib : i = b
    · subst b
      simp [diagonalCoroot_apply, hij, hne] at hi
    · simp [diagonalCoroot_apply, hij, hne, hib] at hi
  subst a
  have hjb : j = b := by
    by_contra hne
    simp [diagonalCoroot_apply, hne] at hj
  subst b
  rfl

/-- The roots `e_i - e_j`, as an embedding of the off-diagonal index set into the character
lattice of the diagonal torus. -/
def diagonalRootEmbedding (n : ℕ) :
    DiagonalRootIndex n ↪ ULift.{u} (Fin n) →₀ ℤ :=
  ⟨diagonalRoot, diagonalRoot_injective⟩

/-- The coroots `e_i - e_j`, as an embedding of the off-diagonal index set into the cocharacter
lattice of the diagonal torus. -/
def diagonalCorootEmbedding (n : ℕ) :
    DiagonalRootIndex n ↪ ULift.{u} (Fin n) → ℤ :=
  ⟨diagonalCoroot, diagonalCoroot_injective⟩

@[simp]
theorem diagonalRootEmbedding_apply {n : ℕ} (p : DiagonalRootIndex n) :
    (diagonalRootEmbedding n : DiagonalRootIndex n ↪ ULift.{u} (Fin n) →₀ ℤ) p =
      diagonalRoot p :=
  (rfl)

@[simp]
theorem diagonalCorootEmbedding_apply {n : ℕ} (p : DiagonalRootIndex n) :
    (diagonalCorootEmbedding n : DiagonalRootIndex n ↪ ULift.{u} (Fin n) → ℤ) p =
      diagonalCoroot p :=
  (rfl)

/-- Simultaneously transposing the two entries of a root index by the reflection associated to
`p`. Distinctness is preserved because a transposition is injective. -/
def diagonalReflectionIndex {n : ℕ} (p q : DiagonalRootIndex n) : DiagonalRootIndex n :=
  ⟨⟨(Equiv.swap p.1.1 p.1.2) q.1.1, (Equiv.swap p.1.1 p.1.2) q.1.2⟩, by
    exact (Equiv.swap p.1.1 p.1.2).injective.ne q.2⟩

private theorem diagonalPairing_apply {n : ℕ} (p q : DiagonalRootIndex n) :
    SplitTorus.dotPairing (diagonalRoot p) (diagonalCoroot q) =
      (if p.1.1 = q.1.1 then 1 else 0) - (if p.1.1 = q.1.2 then 1 else 0) -
        ((if p.1.2 = q.1.1 then 1 else 0) - (if p.1.2 = q.1.2 then 1 else 0)) := by
  classical
  rw [diagonalRoot, map_sub]
  simp [SplitTorus.dotPairing_apply, diagonalCoroot_apply, eq_comm]

private theorem diagonalRoot_coroot_two {n : ℕ} (p : DiagonalRootIndex n) :
    SplitTorus.dotPairing (diagonalRoot p) (diagonalCoroot p) = 2 := by
  rw [diagonalPairing_apply]
  simp [p.2, p.2.symm]

private theorem diagonalPairing_comm {n : ℕ} (p q : DiagonalRootIndex n) :
    SplitTorus.dotPairing (diagonalRoot p) (diagonalCoroot q) =
      SplitTorus.dotPairing (diagonalRoot q) (diagonalCoroot p) := by
  rw [diagonalPairing_apply, diagonalPairing_apply]
  simp only [eq_comm]
  ring

private theorem diagonalRoot_reflection {n : ℕ} (p q : DiagonalRootIndex n) :
    preReflection (diagonalRoot p) (SplitTorus.dotPairing.flip (diagonalCoroot p))
        (diagonalRoot q) =
      diagonalRoot (diagonalReflectionIndex p q) := by
  classical
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨a, b⟩, hab⟩
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j
  all_goals
    simp_all [preReflection_apply, diagonalRoot, diagonalReflectionIndex,
      Equiv.swap_apply_of_ne_of_ne] <;> module

private theorem diagonalCoroot_reflection {n : ℕ} (p q : DiagonalRootIndex n) :
    preReflection (diagonalCoroot p : ULift.{u} (Fin n) → ℤ)
        (SplitTorus.dotPairing (diagonalRoot p : ULift.{u} (Fin n) →₀ ℤ))
        (diagonalCoroot q : ULift.{u} (Fin n) → ℤ) =
      diagonalCoroot (diagonalReflectionIndex p q) := by
  ext a
  have h := congrArg (fun f : ULift.{u} (Fin n) →₀ ℤ ↦ f a)
    (diagonalRoot_reflection p q)
  rw [preReflection_apply] at h ⊢
  simp only [LinearMap.flip_apply, Finsupp.sub_apply, Finsupp.smul_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, diagonalRoot_apply, diagonalCoroot_apply] at h ⊢
  rw [diagonalPairing_comm p q]
  exact h

/-- The character--cocharacter root datum of `GL_n` relative to its diagonal torus.

Its roots and coroots are both indexed by ordered pairs `i ≠ j`; the underlying perfect pairing
is the split-torus dot product. -/
noncomputable def diagonalRootDatum (n : ℕ) :
    RootDatum (DiagonalRootIndex n) (ULift.{u} (Fin n) →₀ ℤ) (ULift.{u} (Fin n) → ℤ) :=
  RootPairing.mk' SplitTorus.dotPairing (diagonalRootEmbedding n)
    (diagonalCorootEmbedding n) diagonalRoot_coroot_two
    (fun p x ⟨q, hq⟩ ↦ ⟨diagonalReflectionIndex p q, by
      simp only [diagonalRootEmbedding_apply] at hq ⊢
      rw [← hq]
      exact (diagonalRoot_reflection p q).symm⟩)
    (fun p x ⟨q, hq⟩ ↦ ⟨diagonalReflectionIndex p q, by
      simp only [diagonalCorootEmbedding_apply] at hq ⊢
      rw [← hq]
      exact (diagonalCoroot_reflection p q).symm⟩)

/-- The roots of `diagonalRootDatum` are the vectors `e_i - e_j`. -/
@[simp]
theorem diagonalRootDatum_root {n : ℕ} (p : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p = diagonalRoot p :=
  (rfl)

/-- The coroots of `diagonalRootDatum` are the vectors `e_i - e_j`. -/
@[simp]
theorem diagonalRootDatum_coroot {n : ℕ} (p : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ _ (ULift.{u} (Fin n) → ℤ)).coroot p = diagonalCoroot p :=
  (rfl)

/-- The root-datum pairing is the split-torus character--cocharacter dot product. -/
@[simp]
theorem diagonalRootDatum_pairing {n : ℕ} (p q : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).pairing p q =
      SplitTorus.dotPairing (diagonalRoot p : ULift.{u} (Fin n) →₀ ℤ)
        (diagonalCoroot q : ULift.{u} (Fin n) → ℤ) :=
  by
    rw [← RootPairing.root_coroot_eq_pairing, diagonalRootDatum_root,
      diagonalRootDatum_coroot]
    rw [diagonalRootDatum]
    simp only [RootPairing.mk']

/-- The root--coroot pairing of the diagonal root datum is symmetric. -/
theorem diagonalRootDatum_pairing_comm {n : ℕ} (p q : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).pairing p q =
      (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).pairing q p := by
  rw [diagonalRootDatum_pairing, diagonalRootDatum_pairing]
  exact diagonalPairing_comm p q

/-- The root datum of the diagonal torus in `GL_n` is reduced. -/
instance isReduced_diagonalRootDatum (n : ℕ) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ diagonalRootDatum_pairing_comm

/-- The reflection associated to `(i, j)` acts on root indices by transposing `i` and `j` in
both entries. -/
@[simp]
theorem diagonalRootDatum_reflectionPerm {n : ℕ} (p q : DiagonalRootIndex n) :
    (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).reflectionPerm p q =
      diagonalReflectionIndex p q := by
  apply (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root.injective
  rw [(diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root_reflectionPerm]
  exact diagonalRoot_reflection p q

/-- A root of the diagonal root datum, viewed multiplicatively, is the adjoint weight of the
corresponding matrix unit. -/
@[simp]
theorem diagonalRoot_toMultiplicative {n : ℕ} (p : DiagonalRootIndex n) :
    Multiplicative.ofAdd (diagonalRoot p : ULift.{u} (Fin n) →₀ ℤ) =
      matrixUnitWeight p.1.1 p.1.2 :=
  by
    apply Multiplicative.toAdd.injective
    ext a
    simp [diagonalRoot_apply, toAdd_matrixUnitWeight_apply]

/-- Every root in the diagonal root datum occurs as a nontrivial weight in the adjoint
representation of `GL_n`. -/
theorem diagonalRoot_mem_nontrivialAdjointWeights {k : Type u} [Field k] {n : ℕ}
    (p : DiagonalRootIndex n) :
    Multiplicative.ofAdd
        ((diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).root p) ∈
      Derivation.nontrivialAdjointWeights
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom := by
  rw [diagonalRootDatum_root, diagonalRoot_toMultiplicative]
  exact matrixUnitWeight_mem_nontrivialAdjointWeights (k := k) p.2

/-- The genuine cocharacter whose coordinate vector is the coroot `e_i - e_j`. -/
noncomputable def diagonalCorootCocharacter {n : ℕ} (p : DiagonalRootIndex n) :
    Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →* Multiplicative ℤ :=
  SplitTorus.cocharEquiv.symm (diagonalCoroot p)

/-- The coordinates of `diagonalCorootCocharacter p` are the coroot `e_i - e_j`. -/
@[simp]
theorem cocharEquiv_diagonalCorootCocharacter {n : ℕ} (p : DiagonalRootIndex n) :
    SplitTorus.cocharEquiv (diagonalCorootCocharacter p :
      Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →* Multiplicative ℤ) = diagonalCoroot p :=
  Equiv.apply_symm_apply _ _

/-- Evaluation of a root on a coroot is the pairing of the diagonal root datum. -/
theorem pairing_diagonalRoot_diagonalCoroot {n : ℕ} (p q : DiagonalRootIndex n) :
    DiagonalizableGroup.pairing (matrixUnitWeight p.1.1 p.1.2)
        (diagonalCorootCocharacter q :
          Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →* Multiplicative ℤ) =
      (diagonalRootDatum n : RootDatum _ (ULift.{u} (Fin n) →₀ ℤ) _).pairing p q := by
  rw [← diagonalRoot_toMultiplicative p,
    SplitTorus.pairing_eq_dotPairing, cocharEquiv_diagonalCorootCocharacter,
    diagonalRootDatum_pairing]

end

end TauCeti.GeneralLinear
