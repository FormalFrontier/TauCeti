/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic

/-!
# `αₚ` is the kernel of the Frobenius endomorphism of the additive group

Over a base ring `R` of prime characteristic `p`, the additive group `𝔾ₐ = Spec R[x]` (here
`x = ι R R 1` in `SymmetricAlgebra R R`) carries the **Frobenius endomorphism** `F : 𝔾ₐ → 𝔾ₐ`
(`TauCeti.AdditiveGroup.frobeniusEnd`, of
`TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Frobenius`), which on every commutative `R`-algebra
`A` raises a point to its `p`-th power, `a ↦ aᵖ`.

`TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic` builds the Frobenius kernel group
scheme `αₚ = Spec R[x]/(xᵖ)` and identifies its functor of points with the `p`-nilpotent elements
of the additive group. This file exhibits the inclusion `αₚ ↪ 𝔾ₐ` on the functor of points and
proves that `αₚ` is exactly the kernel of the Frobenius endomorphism: as subgroups of the group of
`𝔾ₐ`-points, the image of the inclusion `αₚ ↪ 𝔾ₐ` equals the kernel of the Frobenius endomorphism.
This realizes `αₚ = ker(𝔾ₐ --a ↦ aᵖ--> 𝔾ₐ)` on the functor of points, the additive companion of the
identification of `μ_n` with the kernel of the `n`th power endomorphism of `𝔾ₘ`
(`TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Kernel`).

The mechanism is the worked-example points dictionary. A point of `𝔾ₐ = Spec R[x]` reads off the
element `F(x) : A` (`TauCeti.AdditiveGroup.gaPointsMulEquiv`); the Frobenius endomorphism raises
that element to the `p`-th power (`TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd`),
while an included `αₚ`-point reads off a `p`-nilpotent element (`aᵖ = 0`), whose `p`-th power
vanishes. Conversely a `𝔾ₐ`-point read off as an element `a` with `aᵖ = 0` is a `p`-nilpotent
element, hence the image of the `αₚ`-point attached to it
(`TauCeti.AlphaP.mem_range_pointsHom_iff`).

This is a worked-example check for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap): the standing hypotheses flag `αₚ` as one of the
non-smooth / non-reduced groups an affine group scheme of finite type must admit, described there
as "the kernel of the Frobenius endomorphism", and Layer 3 develops "Hopf ideals ↔ closed
subgroup schemes" with their kernels.

## Main declarations

* `TauCeti.AlphaP.inclusion`: the inclusion `αₚ ↪ 𝔾ₐ` on points, the contravariant image of the
  quotient map `R[x] ↠ R[x]/(xᵖ)`.
* `TauCeti.AlphaP.inclusion_injective`: the inclusion `αₚ ↪ 𝔾ₐ` is injective on points.
* `TauCeti.AlphaP.mapValue_inclusion`: the inclusion `αₚ ↪ 𝔾ₐ` is natural in the value algebra.
* `TauCeti.AlphaP.frobeniusEnd_comp_inclusion`: the Frobenius endomorphism annihilates `αₚ`.
* `TauCeti.AlphaP.mem_range_inclusion_iff`: a `𝔾ₐ`-point lies in the image of `αₚ` iff the
  Frobenius endomorphism kills it.
* `TauCeti.AlphaP.range_inclusion`: as subgroups of the `𝔾ₐ`-points, the image of `αₚ ↪ 𝔾ₐ` is
  the kernel of the Frobenius endomorphism of `𝔾ₐ`.

## References

The Frobenius endomorphism `TauCeti.AdditiveGroup.frobeniusEnd` of `𝔾ₐ` is Tau Ceti's
`TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Frobenius`; the Frobenius kernel `αₚ` and its
`p`-nilpotent functor of points are `TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic`.
The additive-group points dictionary `TauCeti.AdditiveGroup.gaPointsMulEquiv` and the
coordinate-Hopf-algebra functoriality `TauCeti.AlgHom.mapDomain` (with its naturality
`TauCeti.AlgHom.mapValue_mapDomain`) are Tau Ceti's. This realizes `αₚ = ker(Frobenius)` on the
functor of points, the additive companion of `TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Kernel`.
-/

public section

open Coalgebra HopfAlgebra SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w

/-! ### `αₚ` as the kernel of the Frobenius endomorphism -/

namespace AlphaP

variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
variable {A : Type v} [CommRing A] [Algebra R A]

/-- **The inclusion `αₚ ↪ 𝔾ₐ` on the functor of points.** It is the homomorphism of convolution
groups of points induced (contravariantly) by the quotient bialgebra map `R[x] ↠ R[x]/(xᵖ)`, i.e.
pre-composition of a point of `αₚ` with the quotient map. It agrees with the underlying-element map
`TauCeti.AlphaP.pointsHom` through `TauCeti.AdditiveGroup.gaPointsMulEquiv`. -/
noncomputable def inclusion :
    WithConv (CoordinateRing (R := R) p →ₐ[R] A) →*
      WithConv (SymmetricAlgebra R R →ₐ[R] A) :=
  (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm.toMonoidHom.comp (pointsHom p)

/-- Reading an included `αₚ`-point off as an element of the additive group is the underlying-element
map `TauCeti.AlphaP.pointsHom`: both pre-compose the point with the quotient map `R[x] ↠ R[x]/(xᵖ)`
and evaluate at the generator. -/
@[simp]
theorem gaPointsMulEquiv_inclusion (F : WithConv (CoordinateRing (R := R) p →ₐ[R] A)) :
    AdditiveGroup.gaPointsMulEquiv (inclusion p F) = pointsHom p F := by
  simp [inclusion]

/-- **The inclusion `αₚ ↪ 𝔾ₐ` is injective on the functor of points.** It agrees through
`TauCeti.AdditiveGroup.gaPointsMulEquiv` with the injective underlying-element map
`TauCeti.AlphaP.pointsHom`, so distinct `αₚ`-points include to distinct `𝔾ₐ`-points. -/
theorem inclusion_injective : Function.Injective (inclusion (R := R) (A := A) p) := by
  intro F F' h
  apply pointsHom_injective (R := R) p (A := A)
  rw [← gaPointsMulEquiv_inclusion, ← gaPointsMulEquiv_inclusion, h]

variable {B : Type w} [CommRing B] [Algebra R B]

/-- **Naturality in the value algebra.** The inclusion `αₚ ↪ 𝔾ₐ` commutes with the value-algebra
functoriality `AlgHom.mapValue`. -/
theorem mapValue_inclusion (χ : A →ₐ[R] B) :
    (inclusion (R := R) (A := B) p).comp
        (AlgHom.mapValue (H := CoordinateRing (R := R) p) χ) =
      (AlgHom.mapValue (H := SymmetricAlgebra R R) χ).comp (inclusion (R := R) (A := A) p) := by
  refine MonoidHom.ext fun F => ?_
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := B)).injective
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, gaPointsMulEquiv_inclusion,
    AdditiveGroup.gaPointsMulEquiv_mapValue, gaPointsMulEquiv_inclusion]
  apply Multiplicative.toAdd.injective
  simp

/-- **The Frobenius endomorphism annihilates `αₚ`.** Composing the Frobenius endomorphism of `𝔾ₐ`
after the inclusion `αₚ ↪ 𝔾ₐ` is the trivial homomorphism of group functors: every `αₚ`-point maps
to a `p`-nilpotent element, whose `p`-th power is `0`. -/
theorem frobeniusEnd_comp_inclusion :
    (AdditiveGroup.frobeniusEnd R p (A := A)).comp (inclusion p) = 1 := by
  refine MonoidHom.ext fun F => ?_
  rw [MonoidHom.comp_apply, MonoidHom.one_apply]
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
  apply Multiplicative.toAdd.injective
  rw [AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd, gaPointsMulEquiv_inclusion, map_one,
    toAdd_one]
  exact (mem_range_pointsHom_iff p _).mp ⟨F, rfl⟩

/-- The Frobenius endomorphism annihilates every `αₚ`-point, in element form. -/
@[simp]
theorem frobeniusEnd_inclusion (F : WithConv (CoordinateRing (R := R) p →ₐ[R] A)) :
    AdditiveGroup.frobeniusEnd R p (inclusion p F) = 1 := by
  have := DFunLike.congr_fun (frobeniusEnd_comp_inclusion (R := R) (A := A) p) F
  simpa using this

/-- **Membership in the image of `αₚ ↪ 𝔾ₐ`.** A `𝔾ₐ`-point lies in the image of the `αₚ` inclusion
exactly when the Frobenius endomorphism kills it: `g` comes from `αₚ` iff `gᵖ = 0` in the additive
group of points. -/
theorem mem_range_inclusion_iff {g : WithConv (SymmetricAlgebra R R →ₐ[R] A)} :
    g ∈ MonoidHom.range (inclusion (R := R) (A := A) p) ↔
      AdditiveGroup.frobeniusEnd R p g = 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨F, rfl⟩
    exact frobeniusEnd_inclusion p F
  · intro hg
    have hval : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g) ^ p = 0 := by
      have hpow := AdditiveGroup.toAdd_gaPointsMulEquiv_frobeniusEnd (R := R) (A := A) p g
      rw [hg, map_one, toAdd_one] at hpow
      exact hpow.symm
    obtain ⟨F, hF⟩ :=
      (mem_range_pointsHom_iff (R := R) p (AdditiveGroup.gaPointsMulEquiv g)).mpr hval
    refine ⟨F, ?_⟩
    apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
    rw [gaPointsMulEquiv_inclusion, hF]

/-- **`αₚ` is the kernel of the Frobenius endomorphism of `𝔾ₐ`.** As subgroups of the group of
`𝔾ₐ`-points, the image of the inclusion `αₚ ↪ 𝔾ₐ` equals the kernel of the Frobenius endomorphism:
a `𝔾ₐ`-point comes from `αₚ` exactly when its `p`-th power is trivial. This realizes
`αₚ = ker(𝔾ₐ --a ↦ aᵖ--> 𝔾ₐ)` on the functor of points. -/
theorem range_inclusion :
    MonoidHom.range (inclusion (R := R) (A := A) p) =
      MonoidHom.ker (AdditiveGroup.frobeniusEnd R p (A := A)) := by
  ext g
  rw [MonoidHom.mem_ker, mem_range_inclusion_iff]

end AlphaP

end TauCeti
