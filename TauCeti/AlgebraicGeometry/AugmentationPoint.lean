/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import TauCeti.RingTheory.Idempotents.Connected.Component

/-!
# The spectrum point and connected component defined by an augmentation

An algebra homomorphism from a commutative algebra to its ground field determines a rational point
of the algebra's prime spectrum. This file records that point, its underlying prime ideal, and the
factorization of the augmentation through the quotient cutting out its connected component when
the prime spectrum is locally connected.

## Main declarations

* `TauCeti.AlgHom.kernelPoint`: the point cut out by the kernel of an augmentation.
* `TauCeti.AlgHom.kernelPointConnectedComponentAlgHom`: the augmentation factored through the
  quotient cutting out the connected component of its kernel point.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 2.a.
* The Stacks Project, Tags 00EE and 022R.

The connected-component factorization supplies a prerequisite for Layer 3, "Identity component
`G°` and component group `π₀(G)`", of the ReductiveGroups roadmap. It concerns only the ordinary
connected component over the ground field and asserts no compatibility with base change.
-/

public section

open AlgebraicGeometry IsLocalRing

namespace TauCeti.AlgHom

universe u v

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Algebra k H]
variable (f : H →ₐ[k] k)

/-- The point of `Spec H` defined by an augmentation `f : H →ₐ[k] k`. Its prime ideal is
`ker f`. -/
def kernelPoint : Spec (CommRingCat.of H) :=
  PrimeSpectrum.comap (f : H →+* k) (closedPoint k)

/-- The prime ideal of an augmentation point is the kernel of the augmentation. -/
@[simp]
theorem kernelPoint_asIdeal :
    (kernelPoint f).asIdeal = RingHom.ker (f : H →+* k) := by
  rw [kernelPoint, PrimeSpectrum.comap_asIdeal]
  dsimp only [closedPoint]
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

variable [LocallyConnectedSpace (PrimeSpectrum H)]

/-- An augmentation takes the idempotent selecting the connected component of its kernel point to
one. -/
@[simp]
theorem map_connectedComponentIdempotent_kernelPoint :
    f (PrimeSpectrum.connectedComponentIdempotent (kernelPoint f)) = 1 := by
  have hnot : PrimeSpectrum.connectedComponentIdempotent (kernelPoint f) ∉
      (kernelPoint f).asIdeal :=
    PrimeSpectrum.connectedComponentIdempotent_notMem (kernelPoint f)
  rw [kernelPoint_asIdeal, RingHom.mem_ker] at hnot
  have hidempotent : IsIdempotentElem
      (f (PrimeSpectrum.connectedComponentIdempotent (kernelPoint f))) :=
    (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent (kernelPoint f)).map
      f.toRingHom
  exact (IsIdempotentElem.iff_eq_zero_or_one.mp hidempotent).resolve_left hnot

/-- The ideal cutting out the connected component of an augmentation's kernel point is contained
in the kernel of the augmentation. -/
theorem connectedComponentIdeal_kernelPoint_le_ker :
    PrimeSpectrum.connectedComponentIdeal (kernelPoint f) ≤
      RingHom.ker (f : H →+* k) := by
  simpa only [kernelPoint_asIdeal] using
    PrimeSpectrum.connectedComponentIdeal_le_asIdeal (kernelPoint f)

/-- The augmentation factored through the quotient cutting out the connected component of its
kernel point. -/
noncomputable def kernelPointConnectedComponentAlgHom :
    (H ⧸ PrimeSpectrum.connectedComponentIdeal (kernelPoint f)) →ₐ[k] k :=
  Ideal.Quotient.liftₐ (PrimeSpectrum.connectedComponentIdeal (kernelPoint f)) f
    (connectedComponentIdeal_kernelPoint_le_ker f)

/-- The factored augmentation composed with the quotient map is the original augmentation. -/
@[simp]
theorem kernelPointConnectedComponentAlgHom_comp_mk :
    (kernelPointConnectedComponentAlgHom f).comp
      (Ideal.Quotient.mkₐ k (PrimeSpectrum.connectedComponentIdeal (kernelPoint f))) = f :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The factored augmentation evaluates a quotient constructor as the original augmentation. -/
@[simp]
theorem kernelPointConnectedComponentAlgHom_mk (h : H) :
    kernelPointConnectedComponentAlgHom f
        (Ideal.Quotient.mk (PrimeSpectrum.connectedComponentIdeal (kernelPoint f)) h) = f h := by
  unfold kernelPointConnectedComponentAlgHom
  exact Ideal.Quotient.lift_mk _ _ _

end TauCeti.AlgHom
