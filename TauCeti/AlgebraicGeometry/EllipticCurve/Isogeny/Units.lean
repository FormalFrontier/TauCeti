/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom

/-!
# The units of the endomorphism monoid

An endomorphism of `W` is invertible exactly when it has degree one. Degree one means the
function-field pullback is onto, and the factorisation theorem turns a surjective pullback into
an isogeny inverting it on both sides; conversely degree is multiplicative and the identity has
degree one, so a unit's degree divides one.

`Units` is defined for a monoid, so `(Hom W W)ˣ` is determined by the multiplicative structure
alone: the group described here is the same one the endomorphism ring will have.

## Main results

* `TauCeti.Isogeny.Hom.isUnit_iff_degree_eq_one`: a unit is exactly a degree-one endomorphism.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.4.1.
-/

public section

namespace TauCeti.Isogeny.Hom

variable {F : Type*} [Field F] {W₁ : WeierstrassCurve.Affine F}

/-- **The units of the endomorphism monoid are exactly the degree-one endomorphisms**, an
isogeny of degree one being an isomorphism. `Units` depends only on the multiplicative
structure, so this describes the whole unit group of the endomorphism monoid. -/
@[simp]
theorem isUnit_iff_degree_eq_one {f : Hom W₁ W₁} : IsUnit f ↔ f.degree = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h : (u : Hom W₁ W₁).degree * (↑u⁻¹ : Hom W₁ W₁).degree = 1 := by
      rw [← degree_comp, ← mul_def, u.mul_inv, one_def, degree_id]
    exact Nat.eq_one_of_mul_eq_one_right h
  · intro hd
    obtain ⟨φ, rfl⟩ := f.eq_zero_or_exists_ofIsogeny.resolve_left fun h => by simp [h] at hd
    rw [degree_ofIsogeny] at hd
    obtain ⟨χ, h1, h2⟩ := Isogeny.exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one φ hd
    exact ⟨⟨ofIsogeny φ, ofIsogeny χ,
      by rw [mul_def, ofIsogeny_comp_ofIsogeny, h2, one_def, id_def],
      by rw [mul_def, ofIsogeny_comp_ofIsogeny, h1, one_def, id_def]⟩, rfl⟩

/-- **An automorphism has degree one.** -/
@[simp]
theorem degree_coe_units (u : (Hom W₁ W₁)ˣ) : (u : Hom W₁ W₁).degree = 1 :=
  isUnit_iff_degree_eq_one.mp u.isUnit

end TauCeti.Isogeny.Hom

end
