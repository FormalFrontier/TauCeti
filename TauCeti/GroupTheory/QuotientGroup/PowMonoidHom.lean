/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Power classes of a commutative group under equivalences and products

The group of `n`-th power classes of a commutative group `G` is the quotient
`G ⧸ (powMonoidHom n).range`, the spelling `Mathlib.RingTheory.DedekindDomain.SelmerGroup` uses.
This file transports that quotient along a multiplicative equivalence, and identifies the power
classes of the units of a product with the product of the power classes of the units of the
factors.

## Main definitions

* `QuotientGroup.congrRangePowMonoidHom`: an equivalence `G ≃* H` induces
  `G ⧸ (powMonoidHom n).range ≃* H ⧸ (powMonoidHom n).range`.
* `Units.modPowPiEquiv`: taking `n`-th power classes of units commutes with products.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `modPow`, where the two are stated for the source's
`Units.modPow` abbreviation. Mathlib's `QuotientGroup.mulEquivPiModRangePowMonoidHom` and
`MulEquiv.piUnits` do the work of the source's `Units.modPow.piEquiv`; what is left here is the
transport along an equivalence and the composition of those two. The source is written against
Lean `v4.32.0`; this is a forward port.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil): the `2`-descent map of the weak
Mordell–Weil theorem lands in the square classes of an étale algebra and is controlled one field
factor at a time, which is `Units.modPowPiEquiv` composed with the Chinese Remainder
decomposition of that algebra (`TauCeti.RingTheory.AdjoinRoot.Factors`). Nothing here mentions a
polynomial or a curve.
-/

public section

namespace QuotientGroup

/-- A multiplicative equivalence of commutative groups induces one on the quotients by the
subgroups of `n`-th powers. -/
def congrRangePowMonoidHom {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e (e.map_range_powMonoidHom n)

@[simp]
lemma congrRangePowMonoidHom_mk {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ)
    (g : G) :
    congrRangePowMonoidHom e n (QuotientGroup.mk g) = QuotientGroup.mk (e g) :=
  (rfl)

end QuotientGroup

namespace Units

/-- Taking `n`-th power classes of units commutes with products. -/
noncomputable def modPowPiEquiv {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)]
    (n : ℕ) :
    ((i : ι) → α i)ˣ ⧸ (powMonoidHom n : ((i : ι) → α i)ˣ →* _).range ≃*
      ((i : ι) → (α i)ˣ ⧸ (powMonoidHom n : (α i)ˣ →* _).range) :=
  (QuotientGroup.congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    QuotientGroup.mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n

/-- On the class of a unit, `Units.modPowPiEquiv` is componentwise projection to the factors. -/
@[simp]
lemma modPowPiEquiv_mk {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ)
    (u : ((i : ι) → α i)ˣ) (i : ι) :
    modPowPiEquiv α n (QuotientGroup.mk u) i = QuotientGroup.mk (MulEquiv.piUnits u i) := by
  simp [modPowPiEquiv, QuotientGroup.mulEquivPiModRangePowMonoidHom_apply]

end Units

end
