/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Hyperbolic
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice

/-!
# The split type-`Dₙ` spinor module and its Kostant-stable lattice

`TauCeti.SpinPolarizationData.typeDSpinRep` turns any polarized quadratic space into a
representation of the type-`D` Serre presentation on the exterior algebra of the exterior summand,
and `typeDSpinRep_serreKostantForm_apply_mem_integralLattice` proves that the coordinate lattice of
that exterior algebra is stable under the Serre Kostant form. Both are stated for an arbitrary
`TauCeti.SpinPolarizationData` and an arbitrary basis of its exterior summand, so neither names a
carrier: a consumer that has to exhibit one still has to choose the quadratic space, the
decomposition and the basis.

This file makes that choice, once, in the split model. The quadratic space is Mathlib's hyperbolic
form `QuadraticForm.dualProd ℚ (Fin n → ℚ)` on `Module.Dual ℚ (Fin n → ℚ) × (Fin n → ℚ)`, of
dimension `2 n`; the decomposition is the coordinate one supplied by
`TauCeti.SpinPolarizationData.hyperbolic`; and the basis is the standard basis of `Fin n → ℚ`
carried into the exterior summand. The resulting spinor module is the exterior algebra on `n`
generators, whose `2 ^ n` coordinate basis vectors are indexed by `Finset (Fin n)` and carry the
integral weights `TauCeti.DynkinType.typeDSpinWeight`, and the Kostant stability of its coordinate
lattice becomes a statement with no free parameters other than the rank.

Both half-spin parities occur, which is what makes the weights span the whole simply connected
type-`D` character lattice rather than the root lattice, so this is the admissible full-weight
lattice a simply connected type-`D` carrier is built from.

Nothing here builds a group, a group scheme, or a torus, and nothing asserts smoothness or
reductivity of anything: this file fixes the integral input data those constructions consume.

## Main definitions

* `TauCeti.typeDSplitPolarization`: the split polarization of the `2 n`-dimensional hyperbolic
  quadratic space over `ℚ`.
* `TauCeti.typeDSplitBasis`: the standard basis of its exterior summand.

## Main results

* `TauCeti.typeDSplitPolarization_W`, `typeDSplitPolarization_W'` and
  `typeDSplitPolarization_line`: the summands of the split polarization.
* `TauCeti.finrank_typeDSplitPolarization_W`: the exterior summand has dimension `n`, so the
  quadratic space has dimension `2 n` and the diagram is `Dₙ`.
* `TauCeti.isCartanWeightVector_typeDSplit`: the coordinate basis of the split spinor module is a
  Cartan weight basis, with the integral simply connected type-`D` spin weights.
* `TauCeti.typeDSplit_serreKostantForm_apply_mem_integralLattice`: the Serre Kostant form of
  `CartanMatrix.D n` preserves the coordinate lattice of the split spinor module.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.

## Roadmap

This is the "concrete split-polarization specialization" left open by the type-`D` spinor-lattice
construction in `TauCeti/RepresentationTheory/Spin/Polarization/TypeD/KostantLattice.lean`, and it
serves Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, "The Chevalley--Demazure
construction", which asks for an explicitly constructed group scheme from a Chevalley basis and the
Kostant `ℤ`-form rather than for an existence theorem. What remains of that layer on this branch is
the toral Kostant group-scheme carrier itself, then its base change, root-datum pinning and
diagram automorphism.

The consumer is milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`, "explicit pinned
Chevalley--Demazure groups": the `Dₙ(q)` and `²Dₙ(q)` branches of
`TauCeti.ValidLieTypeIndex.AmbientGroup` need a traceable pinned simply connected type-`D` carrier,
and such a carrier is built from a Kostant-stable full-weight integral representation, which is
what the declarations below fix.
-/

public section

namespace TauCeti

/-! ## The split polarization -/

/-- **The split polarization of the `2 n`-dimensional hyperbolic quadratic space over `ℚ`.** Its
exterior summand is the copy of `Fin n → ℚ` in the second coordinate, its contraction summand is
the copy of the dual in the first, and there is no orthogonal remainder, so the attached spinor
module is the exterior algebra on `n` generators. -/
noncomputable def typeDSplitPolarization (n : ℕ) :
    SpinPolarizationData (QuadraticForm.dualProd ℚ (Fin n → ℚ)) :=
  SpinPolarizationData.hyperbolic fun m h => (Module.forall_dual_apply_eq_zero_iff ℚ m).mp h

/-- The exterior summand of the split model is the copy of `Fin n → ℚ`. -/
@[simp]
theorem typeDSplitPolarization_W (n : ℕ) : (typeDSplitPolarization n).W =
    Submodule.snd ℚ (Module.Dual ℚ (Fin n → ℚ)) (Fin n → ℚ) :=
  SpinPolarizationData.hyperbolic_W _

/-- The contraction summand of the split model is the copy of the dual of `Fin n → ℚ`. -/
@[simp]
theorem typeDSplitPolarization_W' (n : ℕ) : (typeDSplitPolarization n).W' =
    Submodule.fst ℚ (Module.Dual ℚ (Fin n → ℚ)) (Fin n → ℚ) :=
  SpinPolarizationData.hyperbolic_W' _

/-- The split model has no orthogonal remainder. -/
@[simp]
theorem typeDSplitPolarization_line (n : ℕ) : (typeDSplitPolarization n).line = ⊥ :=
  SpinPolarizationData.hyperbolic_line _

/-- **The standard basis of the exterior summand of the split model**, carried from the standard
basis of `Fin n → ℚ`. This is the basis the exterior model of the type-`D` spin representation is
coordinatized by, and the one the Bourbaki numbering of the simple roots is read against. -/
noncomputable def typeDSplitBasis (n : ℕ) :
    Module.Basis (Fin n) ℚ (typeDSplitPolarization n).W :=
  (SpinPolarizationData.hyperbolicBasis (Pi.basisFun ℚ (Fin n))).map
    (LinearEquiv.ofEq _ _ (typeDSplitPolarization_W n).symm)

@[simp]
theorem coe_typeDSplitBasis_apply (n : ℕ) (i : Fin n) :
    (typeDSplitBasis n i : Module.Dual ℚ (Fin n → ℚ) × (Fin n → ℚ)) =
      (0, Pi.basisFun ℚ (Fin n) i) := by
  rw [typeDSplitBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    SpinPolarizationData.coe_hyperbolicBasis_apply]

/-- **The exterior summand of the split model has dimension `n`.** With
`TauCeti.SpinPolarizationData.finrank_eq_two_mul_finrank_W_add_finrank_line` and the vanishing
remainder, this is what says the quadratic space has dimension `2 n`, so that the diagram of the
construction below is `Dₙ` and not another rank. -/
@[simp]
theorem finrank_typeDSplitPolarization_W (n : ℕ) :
    Module.finrank ℚ (typeDSplitPolarization n).W = n := by
  rw [Module.finrank_eq_card_basis (typeDSplitBasis n), Fintype.card_fin]

/-! ## The split spinor module -/

/-- **The coordinate basis of the split spinor module is a Cartan weight basis**, its
`Finset (Fin n)`-indexed exterior basis vector carrying the integral simply connected type-`D` spin
weight of that subset. Both parities occur, so these weights span the whole character lattice. -/
theorem isCartanWeightVector_typeDSplit {n : ℕ} (hn : 4 ≤ n) (s : Finset (Fin n)) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector (serreH ℚ (CartanMatrix.D n))
      ((typeDSplitPolarization n).typeDSpinRep (typeDSplitBasis n) hn)
      (DynkinType.typeDSpinWeight s)
      (((ExteriorAlgebra.integralLatticeBasis (typeDSplitBasis n)) s :
        ExteriorAlgebra.integralLattice (typeDSplitBasis n)) :
        _root_.ExteriorAlgebra ℚ (typeDSplitPolarization n).W) :=
  (typeDSplitPolarization n).isCartanWeightVector_typeDSpinRep_integralLatticeBasis
    (typeDSplitBasis n) hn s

/-- **The coordinate lattice of the split type-`Dₙ` spinor module is stable under the Serre Kostant
form.** This is the admissible full-weight integral representation that a pinned simply connected
type-`D` Chevalley--Demazure carrier is built from, with no data left to choose beyond the rank. -/
theorem typeDSplit_serreKostantForm_apply_mem_integralLattice {n : ℕ} (hn : 4 ≤ n)
    {u : _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n))}
    (hu : u ∈ serreKostantForm (CartanMatrix.D n))
    {v : _root_.ExteriorAlgebra ℚ (typeDSplitPolarization n).W}
    (hv : v ∈ ExteriorAlgebra.integralLattice (typeDSplitBasis n)) :
    (typeDSplitPolarization n).typeDSpinRep (typeDSplitBasis n) hn u v ∈
      ExteriorAlgebra.integralLattice (typeDSplitBasis n) :=
  (typeDSplitPolarization n).typeDSpinRep_serreKostantForm_apply_mem_integralLattice
    (typeDSplitBasis n) hn hu hv

end TauCeti
