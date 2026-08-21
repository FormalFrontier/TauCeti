/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
-- Proof-only: the fraction-field property of the intermediate ring and the two-sided
-- localization comparison of dimensions are used inside the proof, not in the statement.
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Localization.Integral

/-!
# The intermediate ring has rank the degree of the isogeny

For an isogeny `φ : W₁ → W₂`, the intermediate ring — the integral closure of `W₂.CoordinateRing`
in `W₁.FunctionField` — has `Module.finrank` over `W₂.CoordinateRing` equal to `φ.degree`.

Geometrically this is the fibre count: the intermediate ring is the ring of functions regular away
from `φ⁻¹(O₂)`, and it sits over `W₂.CoordinateRing` with rank the degree, so an affine fibre of
`φ` has `deg φ` points counted with multiplicity. `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1
names this the place-free route to fibre counting, the alternative to the point–place dictionary of
Layer 0: "the intermediate ring is locally free of rank `deg φ` over the coordinate ring, so every
fibre over an affine point has `deg φ` points with multiplicity".

## Main results

* `TauCeti.Isogeny.finrank_intermediateRing`: `[φ.intermediateRing : W₂.CoordinateRing] = deg φ`.

## Design

**No separability, and no normality of the base.** The proof compares two dimensions across
fraction fields: `W₂.FunctionField` is the fraction field of `W₂.CoordinateRing` by definition, and
`W₁.FunctionField` is the fraction field of the intermediate ring because the latter is the
integral closure of `W₂.CoordinateRing` in a finite extension of its fraction field
(`IsIntegralClosure.isFractionRing_of_finite_extension`, which takes no separability). Both
one-sided comparisons are `Mathlib/LinearAlgebra/Dimension/Localization.lean`, packaged as
`IsFractionRing.finrank_eq`. So this file's hypotheses are those of `Isogeny.degree_eq_finrank`
alone, and Frobenius and the other purely inseparable isogenies are covered — unlike the sibling
`IntermediateRing/Finite.lean`, whose route through the trace form needs separability.

⚠ The statement is about `Module.finrank`, not local freeness. Over a Dedekind domain a
module-finite torsion-free module *is* projective and this `finrank` is its constant local rank, so
the two agree once `IntermediateRing/Finite.lean`'s hypotheses are in force; but that upgrade needs
finiteness, hence separability, and is not what is proved here. Nothing downstream should read this
as a projectivity statement.

The hypotheses take arbitrary algebra structures whose structure maps are the pullback, matching
`Isogeny.degree_eq_finrank` and the siblings in this directory: registering such a structure
globally would be a diamond, since different isogenies induce different ones.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring of an isogeny has rank its degree.** The integral closure of
`W₂.CoordinateRing` in `W₁.FunctionField` is a `W₂.CoordinateRing`-module of rank `deg φ`, the
degree being the dimension of `W₁.FunctionField` over the pulled-back `W₂.FunctionField`.

Both rings sit inside their fraction fields — `W₂.FunctionField` for the base, and
`W₁.FunctionField` for the intermediate ring, since it is an integral closure inside a finite
extension — so the two dimensions are the same number.

No separability is assumed: Frobenius and the other purely inseparable isogenies are covered. -/
theorem finrank_intermediateRing (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.finrank W₂.CoordinateRing φ.intermediateRing = φ.degree := by
  have hfield := φ.algebraMap_functionField_eq_fieldPullback h
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  have := φ.finiteDimensional_functionField hfield
  have : IsFractionRing φ.intermediateRing W₁.FunctionField :=
    IsIntegralClosure.isFractionRing_of_finite_extension W₂.CoordinateRing W₂.FunctionField
      W₁.FunctionField φ.intermediateRing
  rw [φ.degree_eq_finrank hfield]
  exact (IsFractionRing.finrank_eq W₂.CoordinateRing W₂.FunctionField φ.intermediateRing
    W₁.FunctionField).symm

end Isogeny

end TauCeti
