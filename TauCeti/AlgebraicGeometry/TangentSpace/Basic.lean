/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* Mathlib's existing instances make both spaces finite-dimensional when the stalk is Noetherian;
* at a regular point, the dimension of the tangent space is the coheight of the point.

The last statement combines Mathlib's cotangent-space criterion for regular local rings with its
identification of the Krull dimension of `𝒪_{X,x}` and the coheight of `x`.

This is the tangent space of a scheme at a point, over the residue field there. For an affine
group scheme the library also carries a Hopf-algebra description of the tangent space at the
identity: `TauCeti.Bialgebra.CotangentSpace` in
`TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent` is the augmentation ideal modulo its square,
and `TauCeti.Algebra.AlgebraicGroup.Tangent.Basic` describes that tangent space by counit-valued
derivations. The two interfaces are independent here; no comparison between them is made.

This supplies the scheme-level foundation for the tangent-space infrastructure explicitly listed
in `TauCetiRoadmap/JacobianChallenge/README.md` under "Inventory: what is missing (build here)"
and Layer E. It does not construct `Pic⁰` or prove the later comparison
`T₀ Pic⁰ ≅ H¹(X, 𝒪_X)`. No formalization is vendored; the construction reuses Mathlib's
`IsLocalRing.CotangentSpace`, `Module.Dual`, `IsRegularLocalRing.iff_finrank_cotangentSpace`, and
`ringKrullDim_stalk_eq_coheight`.
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

/-- At a regular point of a scheme, the dimension of the Zariski tangent space is the coheight of
the point. Both sides are compared in `WithBot ℕ∞`, the codomain of Krull dimension. -/
lemma finrank_zariskiTangentSpace_eq_coheight (X : Scheme.{u}) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    (Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (ZariskiTangentSpace X x) : WithBot ℕ∞) = Order.coheight x := by
  rw [Subspace.dual_finrank_eq, ← ringKrullDim_stalk_eq_coheight]
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp inferInstance

end

end AlgebraicGeometry

end TauCeti
