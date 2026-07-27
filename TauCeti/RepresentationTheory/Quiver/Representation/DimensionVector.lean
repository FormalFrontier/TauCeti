/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Dimension vectors of quiver representations

The dimension vector of a pointwise finite-dimensional representation records the dimension of its
vector space at each vertex. This file defines dimension vectors and proves their fundamental
functorial properties: invariance under isomorphism and additivity on biproducts and short exact
sequences.

## References

This implements Layer 4, item “Dimension vectors”, of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

variable {k : Type u} {Q : Type v} [Field k] [Quiver Q]

/-- The dimension vector of a pointwise finite-dimensional quiver representation, indexed by the
vertices of the quiver. -/
noncomputable def dimVector (M : QuiverRep k Q)
    (_hM : ∀ i : Q, FiniteDimensional k (M.obj ((Paths.of Q).obj i))) : Q → ℕ :=
  fun i ↦ Module.finrank k (M.obj ((Paths.of Q).obj i))

/-- The value of the dimension vector at a vertex is the dimension of the corresponding vector
space. -/
@[simp]
theorem dimVector_apply (M : QuiverRep k Q)
    (hM : ∀ i : Q, FiniteDimensional k (M.obj ((Paths.of Q).obj i))) (i : Q) :
    dimVector M hM i = Module.finrank k (M.obj ((Paths.of Q).obj i)) :=
  (rfl)

/-- Isomorphic quiver representations have the same dimension vector. -/
theorem dimVector_eq_of_iso {M N : QuiverRep k Q}
    (hM : ∀ i : Q, FiniteDimensional k (M.obj ((Paths.of Q).obj i)))
    (hN : ∀ i : Q, FiniteDimensional k (N.obj ((Paths.of Q).obj i))) (e : M ≅ N) :
    dimVector M hM = dimVector N hN := by
  funext i
  exact (e.app ((Paths.of Q).obj i)).toLinearEquiv.finrank_eq

/-- The zero representation has zero dimension vector. -/
@[simp]
theorem dimVector_zero
    (h : ∀ i : Q, FiniteDimensional k ((0 : QuiverRep k Q).obj ((Paths.of Q).obj i))) :
    dimVector (0 : QuiverRep k Q) h = 0 := by
  funext i
  have hi : IsZero ((0 : QuiverRep k Q).obj ((Paths.of Q).obj i)) :=
    Functor.zero_obj ((Paths.of Q).obj i)
  letI : Subsingleton ((0 : QuiverRep k Q).obj ((Paths.of Q).obj i)) :=
    ModuleCat.subsingleton_of_isZero hi
  exact Module.finrank_zero_of_subsingleton (R := k)

/-- The dimension vector is additive on biproducts of pointwise finite-dimensional
representations. -/
theorem dimVector_biprod (M N : QuiverRep k Q)
    (hM : ∀ i : Q, FiniteDimensional k (M.obj ((Paths.of Q).obj i)))
    (hN : ∀ i : Q, FiniteDimensional k (N.obj ((Paths.of Q).obj i)))
    (hMN : ∀ i : Q, FiniteDimensional k ((M ⊞ N).obj ((Paths.of Q).obj i))) :
    dimVector (M ⊞ N) hMN = dimVector M hM + dimVector N hN := by
  funext i
  letI := hM i
  letI := hN i
  simp only [Pi.add_apply, dimVector_apply]
  let E := (evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)
  letI : PreservesBinaryBiproduct M N E :=
    preservesBinaryBiproduct_of_preservesBiproduct E M N
  let e : (M ⊞ N).obj ((Paths.of Q).obj i) ≅
      ModuleCat.of k (M.obj ((Paths.of Q).obj i) × N.obj ((Paths.of Q).obj i)) :=
    E.mapBiprod M N ≪≫
      ModuleCat.biprodIsoProd
        (M.obj ((Paths.of Q).obj i)) (N.obj ((Paths.of Q).obj i))
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod]

/-- In a short exact sequence of pointwise finite-dimensional quiver representations, the middle
dimension vector is the sum of the outer dimension vectors. -/
theorem dimVector_add_of_shortExact {S : ShortComplex (QuiverRep k Q)} (hS : S.ShortExact)
    (h₁ : ∀ i : Q, FiniteDimensional k (S.X₁.obj ((Paths.of Q).obj i)))
    (h₂ : ∀ i : Q, FiniteDimensional k (S.X₂.obj ((Paths.of Q).obj i)))
    (h₃ : ∀ i : Q, FiniteDimensional k (S.X₃.obj ((Paths.of Q).obj i))) :
    dimVector S.X₂ h₂ = dimVector S.X₁ h₁ + dimVector S.X₃ h₃ := by
  funext i
  let E := (evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i)
  letI : FiniteDimensional k (S.map E).X₁ := h₁ i
  letI : FiniteDimensional k (S.map E).X₃ := h₃ i
  have hSi : (S.map E).ShortExact := hS.map_of_exact E
  simp only [Pi.add_apply, dimVector_apply]
  exact ModuleCat.free_shortExact_finrank_add hSi rfl rfl

end TauCeti
