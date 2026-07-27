/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import TauCeti.Algebra.AlgebraicGroup.Cocharacter

/-!
# Power endomorphisms of `𝔾ₘ` and the ring map `ℤ → End(𝔾ₘ)`

`TauCeti.Algebra.AlgebraicGroup.Cocharacter` introduces, for the multiplicative group
`𝔾ₘ = D(Multiplicative ℤ)`, the `n`th power endomorphism `DiagonalizableGroup.powEnd n`, defined
through the diagonalizable-group functoriality as the character of `𝔾ₘ` at the generator power
`Multiplicative.ofAdd n`. It records that these power endomorphisms compose by multiplying
exponents (`powEnd_comp`) with `powEnd 1 = id` (`powEnd_one`) — the multiplicative half of the
ring `End(𝔾ₘ) ≅ ℤ` "on the level of power maps".

This file completes that picture. The key bridge is that the abstractly-defined endomorphism
`powEnd z` acts on the convolution group of points as the genuine `z`th power map:
`powEnd z f = f ^ z` (`DiagonalizableGroup.powEnd_apply`). From this the remaining ring structure
follows: `powEnd 0` is the trivial homomorphism (`powEnd_zero`), the exponent-additive law
`powEnd (a + b) = powEnd a * powEnd b` holds for the pointwise product of endomorphisms
(`powEnd_add`), and `powEnd (-a)` inverts pointwise (`powEnd_neg`). Passing to additive notation
on the abelian group of `𝔾ₘ`-points, the family realizes the canonical integer action
(`toAdditive_powEnd_eq_intCast`), i.e. the power endomorphisms are the power-map realization of
Mathlib's canonical ring homomorphism `Int.castRingHom` into `End(𝔾ₘ(A))`. On
the group of points of a *fixed* algebra `A` this map need not be injective (for instance when
`Aˣ` has finite exponent), so it is honestly only a ring homomorphism, not an isomorphism.

The power-map description also reads off the character–cocharacter pairing directly: composing
a character `m` after a cocharacter `ψ` of `D(M)` raises a `𝔾ₘ`-point to the `⟨m, ψ⟩` power
(`DiagonalizableGroup.charPoints_cocharPoints_apply`).

This improves the existing power-endomorphism and character–cocharacter pairing API supporting
the reductive-groups roadmap (`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 4: "Tori ...
the character lattice `X*(T)` and cocharacter lattice `X_*(T)` with their perfect pairing").

## Main results

* `TauCeti.DiagonalizableGroup.powEnd_apply`: `powEnd z f = f ^ z`, the power endomorphism as the
  genuine power map on the convolution group of points.
* `TauCeti.DiagonalizableGroup.powEnd_zero`, `TauCeti.DiagonalizableGroup.powEnd_add`,
  `TauCeti.DiagonalizableGroup.powEnd_neg`: the additive-in-the-exponent structure of the power
  endomorphisms, complementing the existing multiplicative `powEnd_comp` / `powEnd_one`.
* `TauCeti.DiagonalizableGroup.toAdditive_powEnd_eq_intCast`: the additive form of `powEnd z`
  is the value of Mathlib's canonical integer ring homomorphism.
* `TauCeti.DiagonalizableGroup.charPoints_cocharPoints_apply`: the character–cocharacter pairing
  is the exponent of the power map obtained by composing a character after a cocharacter.

## References

The power endomorphism `DiagonalizableGroup.powEnd`, the `𝔾ₘ`-points extensionality
`DiagonalizableGroup.pointsMulEquiv_ext`, and the character–cocharacter pairing are Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.Cocharacter`. The additive reinterpretation
`MonoidHom.toAdditive` and `ofMul_zpow` are Mathlib's.
-/

public section

open WithConv

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The convolution group structure on the points of `𝔾ₘ`. -/
noncomputable local instance multiplicativeGroupPointsCommGroup :
    CommGroup (WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :=
  AlgHom.instCommGroup

/-- **The power endomorphism is the power map.** The `z`th power endomorphism of
`𝔾ₘ = D(Multiplicative ℤ)`, defined through the diagonalizable-group functoriality, acts on the
convolution group of points as the genuine `z`th power `f ↦ f ^ z`. -/
@[simp]
theorem powEnd_apply (z : ℤ) (f : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    powEnd z f = f ^ z := by
  apply pointsMulEquiv_ext
  rw [pointsMulEquiv_powEnd, map_zpow, MonoidHom.zpow_apply]

/-- The zeroth power endomorphism is the trivial homomorphism. This is the additive unit of the
endomorphism ring, complementing `powEnd_one` (its multiplicative unit). -/
@[simp]
theorem powEnd_zero :
    powEnd (R := R) (A := A) 0 = 1 := by
  ext f
  rw [powEnd_apply, zpow_zero, MonoidHom.one_apply]

/-- **Power endomorphisms add exponents under the pointwise product.** In the abelian group of
endomorphisms of `𝔾ₘ` (pointwise multiplication of homomorphisms into the commutative group of
points), `powEnd (a + b) = powEnd a * powEnd b`. This is the addition of the endomorphism ring
`End(𝔾ₘ) ≅ ℤ`, complementing the multiplication `powEnd_comp`. -/
@[simp]
theorem powEnd_add (a b : ℤ) :
    powEnd (R := R) (A := A) (a + b) = powEnd a * powEnd b := by
  ext f
  rw [MonoidHom.mul_apply, powEnd_apply, powEnd_apply, powEnd_apply, zpow_add]

/-- The power endomorphism of a negated exponent is the pointwise inverse endomorphism:
`powEnd (-a)` sends a point to the inverse of its image under `powEnd a`. -/
@[simp]
theorem powEnd_neg (a : ℤ) :
    powEnd (R := R) (A := A) (-a) = (powEnd (R := R) (A := A) a)⁻¹ := by
  ext f
  simp [powEnd_apply]

/-- **The power endomorphism is the canonical integer action.** The additive form of `powEnd z`
is the canonical integer endomorphism. Together with `powEnd_zero`, `powEnd_one`, `powEnd_add`,
and `powEnd_comp`, this
exhibits `z ↦ powEnd z` as the power-endomorphism realization of the canonical ring homomorphism
`Int.castRingHom` into `End(𝔾ₘ(A))`; on a fixed algebra `A` this map need not be injective, for
example when `Aˣ` has finite exponent. -/
@[simp]
theorem toAdditive_powEnd_eq_intCast (z : ℤ) :
    MonoidHom.toAdditive (powEnd (R := R) (A := A) z) =
      Int.castRingHom
        (AddMonoid.End (Additive (WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)))) z := by
  apply AddMonoidHom.ext
  intro a
  rw [MonoidHom.toAdditive_apply_apply, powEnd_apply, ofMul_zpow, ofMul_toMul]
  exact (AddMonoid.End.intCast_apply z a).symm

variable {M : Type w} [CommGroup M]

/-- **The character–cocharacter pairing is the exponent of a power map.** For a character `m : M`
and a cocharacter `ψ : M →* Multiplicative ℤ` of the diagonalizable group `D(M)`, composing the
character after the cocharacter raises a `𝔾ₘ`-point to the `⟨m, ψ⟩` power, where
`⟨m, ψ⟩ = pairing m ψ`. This is the pointwise form of `charPoints_comp_cocharPoints`, reading the
pairing off as the power to which the composite endomorphism raises a point. -/
@[simp]
theorem charPoints_cocharPoints_apply (m : M) (ψ : M →* Multiplicative ℤ)
    (f : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    charPoints (R := R) (A := A) m (cocharPoints ψ f) = f ^ pairing m ψ := by
  have h := DFunLike.congr_fun (charPoints_comp_cocharPoints (R := R) (A := A) m ψ) f
  rw [MonoidHom.comp_apply] at h
  rw [h, powEnd_apply]

end DiagonalizableGroup

end TauCeti
