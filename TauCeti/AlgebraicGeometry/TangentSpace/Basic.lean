/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Zariski tangent spaces of schemes

For a point `x` of a scheme `X`, the Zariski cotangent space is
`𝔪ₓ / 𝔪ₓ²`, where `𝔪ₓ` is the maximal ideal of the local ring `𝒪_{X,x}`. The Zariski tangent
space is its dual over the residue field `κ(x)`.

Mathlib supplies the local-ring cotangent space as `IsLocalRing.CotangentSpace`; this file gives
it the scheme-level interface needed by the Jacobian roadmap:

* `ZariskiCotangentSpace X x` is `𝔪ₓ / 𝔪ₓ²` over `κ(x)`;
* `ZariskiTangentSpace X x` is its `κ(x)`-linear dual;
* both spaces are finite-dimensional when `X` is locally Noetherian;
* at a regular point, the dimension of the tangent space is the coheight of the point.

The last statement combines Mathlib's cotangent-space criterion for regular local rings with its
identification of the Krull dimension of `𝒪_{X,x}` and the coheight of `x`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, milestone
"Tangent space `T₀ Pic⁰ ≅ H¹(X, 𝒪_X)`, hence `dim (Jac X) = g`" by providing the scheme-level
tangent-space type in which its left-hand side lives. No formalization is vendored; the
construction reuses Mathlib's `IsLocalRing.CotangentSpace`, `Module.Dual`,
`IsRegularLocalRing.iff_finrank_cotangentSpace`, and `ringKrullDim_stalk_eq_coheight`.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

/-- The Zariski cotangent space `𝔪ₓ / 𝔪ₓ²` of a scheme `X` at a point `x`, as a vector space
over the residue field `κ(x)`. -/
abbrev ZariskiCotangentSpace (X : Scheme.{u}) (x : X) : Type u :=
  IsLocalRing.CotangentSpace (X.presheaf.stalk x)

/-- The Zariski tangent space of a scheme `X` at a point `x`: the dual over `κ(x)` of the
cotangent space `𝔪ₓ / 𝔪ₓ²`. -/
abbrev ZariskiTangentSpace (X : Scheme.{u}) (x : X) : Type u :=
  Module.Dual (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (ZariskiCotangentSpace X x)

/-- The cotangent space at a point of a locally Noetherian scheme is finite-dimensional over the
residue field. -/
instance zariskiCotangentSpace_finiteDimensional (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) : FiniteDimensional (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (ZariskiCotangentSpace X x) :=
  inferInstance

/-- The tangent space at a point of a locally Noetherian scheme is finite-dimensional over the
residue field. -/
instance zariskiTangentSpace_finiteDimensional (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) : FiniteDimensional (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (ZariskiTangentSpace X x) :=
  inferInstance

/-- The tangent and cotangent spaces of a scheme have the same dimension. -/
@[simp]
lemma finrank_zariskiTangentSpace_eq (X : Scheme.{u}) (x : X) :
    Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (ZariskiTangentSpace X x) =
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (ZariskiCotangentSpace X x) :=
  Subspace.dual_finrank_eq

/-- At a regular point of a locally Noetherian scheme, the dimension of the Zariski tangent
space is the coheight of the point. Both sides are compared in `WithBot ℕ∞`, the codomain of
Krull dimension. -/
lemma finrank_zariskiTangentSpace_eq_coheight (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    (Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (ZariskiTangentSpace X x) : WithBot ℕ∞) = Order.coheight x := by
  rw [finrank_zariskiTangentSpace_eq, ← ringKrullDim_stalk_eq_coheight]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp inferInstance

end

end AlgebraicGeometry

end TauCeti
