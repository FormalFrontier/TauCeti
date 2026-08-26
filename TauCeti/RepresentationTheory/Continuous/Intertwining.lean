/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous and algebraic intertwiners

For finite-dimensional normed spaces, automatic continuity identifies continuous intertwiners and
equivalences with their algebraic counterparts. The object and character side is already supplied
by the universe-polymorphic `FDRep.ofShrink`, `FDRep.ofShrinkEquiv`, and
`FDRep.character_ofShrink`; this file adds only the missing intertwiner side.

## Main declarations

* `ContRepresentation.intertwiningMapEquiv`: continuous intertwiners are linearly equivalent to
  algebraic intertwiners.
* `ContRepresentation.nonempty_equiv_iff`: continuous and algebraic representation equivalence
  agree.

## References

* [Representations of compact groups and the Peter-Weyl theorem](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  continuous-representation-to-`FDRep` correspondence.
-/

public section

namespace ContRepresentation

section Intertwiners

universe u v w x

variable {𝕜 : Type u} {G : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  {V : Type w} {W : Type x}
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- In finite dimensions, forgetting continuity identifies continuous intertwining maps with
algebraic intertwining maps. The inverse equips the underlying linear map with its automatic
continuity. -/
noncomputable def intertwiningMapEquiv :
    ContIntertwiningMap π ρ ≃ₗ[𝕜]
      Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation where
  toFun f := f.toIntertwiningMap
  invFun f :=
    { toContinuousLinearMap := LinearMap.toContinuousLinearMap f.toLinearMap
      isIntertwining' := fun g => by
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ f g v }
  left_inv f := by
    apply ContIntertwiningMap.ext
    rfl
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    rfl

/-- The forward intertwiner identification is the existing forgetful map. -/
@[simp]
theorem intertwiningMapEquiv_apply (f : ContIntertwiningMap π ρ) :
    intertwiningMapEquiv f = f.toIntertwiningMap :=
  (rfl)

/-- The inverse intertwiner identification preserves pointwise evaluation. -/
@[simp]
theorem intertwiningMapEquiv_symm_apply_apply
    (f : Representation.IntertwiningMap π.toRepresentation ρ.toRepresentation) (v : V) :
    intertwiningMapEquiv.symm f v = f v :=
  (rfl)

end Intertwiners

section Equivalence

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- Two finite-dimensional continuous representations over a complete field are continuously
equivalent exactly when their underlying algebraic representations are equivalent. -/
theorem nonempty_equiv_iff :
    Nonempty (_root_.ContRepresentation.Equiv π ρ) ↔
      Nonempty (Representation.Equiv π.toRepresentation ρ.toRepresentation) := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨Representation.Equiv.mk φ.toContinuousLinearEquiv.toLinearEquiv fun g ↦ ?_⟩
    ext v
    exact congr($(φ.isIntertwining g) v)
  · rintro ⟨φ⟩
    refine ⟨_root_.ContRepresentation.Equiv.mk φ.toLinearEquiv.toContinuousLinearEquiv fun g ↦ ?_⟩
    ext v
    exact congr($(φ.isIntertwining' g) v)

end Equivalence

end ContRepresentation
