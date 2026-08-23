/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Smooth algebras over fields are geometrically reduced

This file proves that a smooth algebra over a field is geometrically reduced. The main argument
first treats a standard-smooth algebra `A`. Such an algebra admits an étale map from a polynomial
ring `P`; after extending scalars from `P` to its fraction field, the resulting algebra is étale
over a field and hence reduced. Flatness of `A` over `P` makes the natural map from `A` into this
generic fibre injective, so `A` itself is reduced.

An arbitrary smooth algebra is covered by standard-smooth basic localizations. Reducedness on
this cover detects nilpotents in the original algebra. Applying the result after extension to an
algebraic closure gives geometric reducedness.

## Main declarations

* `TauCeti.isReduced_of_standardSmooth_of_field`: a standard-smooth algebra over a field is
  reduced.
* `TauCeti.isReduced_of_smooth_of_field`: a smooth algebra over a field is reduced.
* `TauCeti.isGeometricallyReduced_of_smooth`: a smooth algebra over a field is geometrically
  reduced.

## References

* The Stacks Project, Section 10.140, *Smooth algebras over fields*.

This is the commutative-algebra input for the equivalence between smoothness and geometric
reducedness of finite-type affine group schemes in Layer 2 of the ReductiveGroups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

/-- A standard-smooth algebra over a field is reduced.

The algebra embeds into the base change along the fraction field of a polynomial ring over which
it is étale. The base change is reduced because it is étale over a field. -/
theorem isReduced_of_standardSmooth_of_field
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmooth k A] : IsReduced A := by
  by_cases hA : Nontrivial A
  · let _ : Nontrivial A := hA
    have hs : (algebraMap k A).IsStandardSmooth := by
      rw [RingHom.isStandardSmooth_algebraMap]
      infer_instance
    obtain ⟨n, g, _, hg⟩ := hs.exists_etale_mvPolynomial
    let _ : Algebra (MvPolynomial (Fin n) k) A := g.toAlgebra
    let _ : Algebra.Etale (MvPolynomial (Fin n) k) A := hg.toAlgebra
    let F := FractionRing (MvPolynomial (Fin n) k)
    let B := F ⊗[MvPolynomial (Fin n) k] A
    let _ : Algebra.Etale F B :=
      Algebra.Etale.baseChange (MvPolynomial (Fin n) k) A F
    let _ : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field F B
    exact isReduced_of_injective
      (Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin n) k) (A := F) (B := A))
      (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective _ F))
  · let _ : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    infer_instance

/-- A smooth algebra over a field is reduced. -/
theorem isReduced_of_smooth_of_field
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsReduced A := by
  obtain ⟨s, hs, hsmooth⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth k A
  constructor
  intro x hx
  apply Module.eq_zero_of_isLocalized_span s hs
    (fun r : s ↦ Localization.Away r.1)
    (fun r : s ↦ Algebra.linearMap A (Localization.Away r.1))
  intro r
  let _ : Algebra.IsStandardSmooth k (Localization.Away r.1) := hsmooth r.1 r.2
  let _ : IsReduced (Localization.Away r.1) :=
    isReduced_of_standardSmooth_of_field k (Localization.Away r.1)
  exact (hx.map (algebraMap A (Localization.Away r.1))).eq_zero

/-- A smooth algebra over a field is geometrically reduced. -/
theorem isGeometricallyReduced_of_smooth
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_of_smooth_of_field (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)

end TauCeti
