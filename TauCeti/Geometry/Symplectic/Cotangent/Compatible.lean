/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# A compatible almost complex structure on a cotangent space

A finite-dimensional real inner product space `V` is canonically identified with its algebraic
dual by the Riesz map `v ↦ ⟪v, ·⟫`. Applying this identification to the second factor transports
the standard compatible triple on `V × V` to the linear cotangent space
`V × Module.Dual ℝ V`. The resulting almost complex structure is

`J(v, α) = (-α♯, v♭)`.

This supplies the pointwise compatible geometry of the cotangent-bundle model used in exact
Lagrangian Floer homology. In particular, the zero section and a cotangent fiber are maximal
totally real for this structure as well as Lagrangian for the canonical symplectic form.

## Main declarations

* `TauCeti.cotangentRieszEquiv`: the inner-product identification `V ≃ₗ[ℝ] Module.Dual ℝ V`.
* `TauCeti.cotangentModelEquiv`: the induced identification
  `V × V ≃ₗ[ℝ] V × Module.Dual ℝ V`.
* `TauCeti.cotangentAlmostComplexStructure`: the transported product almost complex structure,
  with formula `J(v, α) = (-α♯, v♭)`.
* `TauCeti.cotangentSymplecticForm_compatible_almostComplexStructure`: compatibility with the
  canonical cotangent symplectic form.
* `TauCeti.SymplecticForm.isMaximalTotallyReal_cotangentZeroSection` and
  `TauCeti.SymplecticForm.isMaximalTotallyReal_cotangentFiber`: the two canonical Lagrangians
  are maximal totally real.

The construction and sign convention follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Sections 2.1 and 3.3. The canonical cotangent
form is the convention `ω = -dλ` already fixed in `Cotangent.Basic`.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The Riesz identification of a finite-dimensional real inner product space with its algebraic
dual, sending `v` to the functional `w ↦ ⟪v, w⟫`. -/
noncomputable def cotangentRieszEquiv : V ≃ₗ[ℝ] Module.Dual ℝ V :=
  (InnerProductSpace.toDual ℝ V).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm

/-- The Riesz functional associated to `v` evaluates at `w` as `⟪v, w⟫`. -/
@[simp]
lemma cotangentRieszEquiv_apply_apply (v w : V) :
    cotangentRieszEquiv (V := V) v w = ⟪v, w⟫_ℝ := by
  exact InnerProductSpace.toDual_apply_apply

/-- The vector dual to `α` under the Riesz identification represents `α` by the inner product. -/
@[simp]
lemma cotangentRieszEquiv_symm_apply (α : Module.Dual ℝ V) (v : V) :
    ⟪(cotangentRieszEquiv (V := V)).symm α, v⟫_ℝ = α v := by
  exact InnerProductSpace.toDual_symm_apply

/-- Identify the standard doubled model `V × V` with the linear cotangent space by applying the
Riesz equivalence in the second coordinate. -/
noncomputable def cotangentModelEquiv :
    (V × V) ≃ₗ[ℝ] (V × Module.Dual ℝ V) :=
  (LinearEquiv.refl ℝ V).prodCongr (cotangentRieszEquiv (V := V))

/-- The cotangent-model equivalence sends `(v, w)` to `(v, w♭)`. -/
@[simp]
lemma cotangentModelEquiv_apply (v : V × V) :
    cotangentModelEquiv (V := V) v =
      (v.1, cotangentRieszEquiv (V := V) v.2) := (rfl)

/-- The inverse cotangent-model equivalence sends `(v, α)` to `(v, α♯)`. -/
@[simp]
lemma cotangentModelEquiv_symm_apply (x : V × Module.Dual ℝ V) :
    (cotangentModelEquiv (V := V)).symm x =
      (x.1, (cotangentRieszEquiv (V := V)).symm x.2) := (rfl)

/-- The Riesz identification is a symplectomorphism from the standard doubled model to the
canonical linear cotangent space. -/
lemma isSymplectomorphism_cotangentModelEquiv :
    SymplecticForm.IsSymplectomorphism (stdSymplecticForm (V := V))
      (cotangentSymplecticForm (V := V)) (cotangentModelEquiv (V := V)) := by
  rw [SymplecticForm.isSymplectomorphism_iff]
  intro v w
  simp [real_inner_comm]

/-- The canonical almost complex structure on a finite-dimensional linear cotangent space,
obtained by transporting `J(v, w) = (-w, v)` through the Riesz identification. -/
noncomputable def cotangentAlmostComplexStructure :
    AlmostComplexStructure (V × Module.Dual ℝ V) :=
  (AlmostComplexStructure.product V).transport (cotangentModelEquiv (V := V))

/-- The canonical cotangent almost complex structure has formula
`J(v, α) = (-α♯, v♭)`. -/
@[simp]
lemma cotangentAlmostComplexStructure_apply (x : V × Module.Dual ℝ V) :
    cotangentAlmostComplexStructure x =
      (-(cotangentRieszEquiv (V := V)).symm x.2, cotangentRieszEquiv (V := V) x.1) := by
  simp [cotangentAlmostComplexStructure, AlmostComplexStructure.product_apply]

/-- The canonical cotangent symplectic form is invariant under the canonical cotangent almost
complex structure. -/
lemma cotangentSymplecticForm_invariant_almostComplexStructure :
    (cotangentSymplecticForm (V := V)).Invariant
      (cotangentAlmostComplexStructure (V := V)) := by
  have h := stdSymplecticForm_invariant_product (V := V) |>.transport
    (cotangentModelEquiv (V := V))
  rw [SymplecticForm.isSymplectomorphism_iff_transport_eq.mp
    isSymplectomorphism_cotangentModelEquiv] at h
  exact h

/-- The canonical cotangent symplectic form tames the canonical cotangent almost complex
structure. -/
lemma cotangentSymplecticForm_tames_almostComplexStructure :
    (cotangentSymplecticForm (V := V)).Tames
      (cotangentAlmostComplexStructure (V := V)) := by
  have h := stdSymplecticForm_tames_product (V := V) |>.transport
    (cotangentModelEquiv (V := V))
  rw [SymplecticForm.isSymplectomorphism_iff_transport_eq.mp
    isSymplectomorphism_cotangentModelEquiv] at h
  exact h

/-- The canonical cotangent symplectic form is compatible with the canonical cotangent almost
complex structure. -/
lemma cotangentSymplecticForm_compatible_almostComplexStructure :
    (cotangentSymplecticForm (V := V)).Compatible
      (cotangentAlmostComplexStructure (V := V)) :=
  SymplecticForm.Compatible.of_tames
    cotangentSymplecticForm_invariant_almostComplexStructure
    cotangentSymplecticForm_tames_almostComplexStructure

/-- The metric associated to the canonical cotangent compatible pair is the orthogonal sum of
the given inner product on `V` and its dual inner product transported by the Riesz map. -/
lemma cotangentSymplecticForm_associatedBilinForm_almostComplexStructure
    (x y : V × Module.Dual ℝ V) :
    (cotangentSymplecticForm (V := V)).associatedBilinForm
      (cotangentAlmostComplexStructure (V := V)) x y =
      ⟪x.1, y.1⟫_ℝ +
        ⟪(cotangentRieszEquiv (V := V)).symm x.2,
          (cotangentRieszEquiv (V := V)).symm y.2⟫_ℝ := by
  simp [SymplecticForm.associatedBilinForm_apply, real_inner_comm]

namespace SymplecticForm

/-- The cotangent zero section is maximal totally real for the canonical cotangent almost complex
structure. -/
lemma isMaximalTotallyReal_cotangentZeroSection :
    IsMaximalTotallyReal (cotangentAlmostComplexStructure (V := V)).toLinearMap
      (cotangentZeroSection (V := V)) :=
  isLagrangian_cotangentZeroSection.isMaximalTotallyReal_of_compatible
    cotangentSymplecticForm_compatible_almostComplexStructure

/-- A cotangent fiber is maximal totally real for the canonical cotangent almost complex
structure. -/
lemma isMaximalTotallyReal_cotangentFiber :
    IsMaximalTotallyReal (cotangentAlmostComplexStructure (V := V)).toLinearMap
      (cotangentFiber (V := V)) :=
  isLagrangian_cotangentFiber.isMaximalTotallyReal_of_compatible
    cotangentSymplecticForm_compatible_almostComplexStructure

end SymplecticForm

end TauCeti
