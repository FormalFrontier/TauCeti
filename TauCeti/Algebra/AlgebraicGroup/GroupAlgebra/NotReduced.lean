/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Nilpotent.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic

/-!
# The coordinate ring of a diagonalizable group is non-reduced in the presence of `p`-torsion

For a commutative group `G`, the diagonalizable group `D(G)` over `R` is `Spec R[G]`, with
coordinate Hopf algebra the group algebra `R[G]`. This file records the failure of `R[G]` to be
reduced whenever `R` has prime characteristic `p` and `G` has a nontrivial element killed by `p`.

The mechanism is the freshman's dream: if `g ≠ 1` with `g ^ p = 1`, then in characteristic `p`
the group-like element `single g 1` and the identity `1 = single 1 1` satisfy
`(single g 1 - 1) ^ p = single (g ^ p) 1 - 1 = single 1 1 - 1 = 0` by `sub_pow_char`, while
`single g 1 - 1 ≠ 0` because `single` is injective in its index. So `single g 1 - 1` is a nonzero
nilpotent and `R[G]` is not reduced.

The headline application is the **non-smooth example `μ_p` in characteristic `p`** from the
reductive-groups roadmap: `μ_p = D(ℤ/p)` has coordinate Hopf algebra
`R[Multiplicative (ZMod p)]`, whose `A`-points are the `p`-th roots of unity in `A`
(`TauCeti.RootsOfUnityGroup.pointsMulEquiv`), yet which is non-reduced over a base of
characteristic `p`. Geometric reducedness of the coordinate ring is exactly smoothness for a
group scheme of finite type over a field, so this exhibits `μ_p` as a non-smooth (non-reduced)
affine group scheme, the canonical example the roadmap flags for admitting non-smooth groups.

## Main declarations

* `TauCeti.single_sub_one_pow_eq_zero`: `(single g 1 - 1) ^ p = 0` when `g ^ p = 1`, in
  characteristic `p`.
* `TauCeti.isNilpotent_single_sub_one`: the element `single g 1 - 1` is nilpotent.
* `TauCeti.single_sub_one_ne_zero`: `single g 1 - 1` is nonzero when `g ≠ 1`.
* `TauCeti.not_isReduced_monoidAlgebra`: `R[G]` is not reduced when `G` has nontrivial
  `p`-torsion and `R` has characteristic `p`.
* `TauCeti.RootsOfUnityGroup.coordinateRing_not_isReduced`: the coordinate Hopf algebra of
  `μ_p = D(ℤ/p)` is not reduced over a nontrivial base of characteristic `p`.

This is a worked-example check for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap): the standing hypotheses note that an affine
group scheme of finite type "admits `μ_p`, `αₚ`, and other non-smooth / non-reduced groups", and
Layer 4 names "the non-smooth example `μ_p` in characteristic `p`" in the diagonalizable-groups
lane.

## References

The freshman's-dream identity `(x - y) ^ p = x ^ p - y ^ p` in characteristic `p` is Mathlib's
`sub_pow_char`; the monomial power law `single m r ^ n = single (m ^ n) (r ^ n)` is Mathlib's
`MonoidAlgebra.single_pow`; injectivity of `single` in its index is
`MonoidAlgebra.single_left_injective`.
The characteristic of the group algebra is transported from that of `R` along the injective
`algebraMap` (`charP_of_injective_algebraMap` with `FaithfulSMul.algebraMap_injective`). The
roots-of-unity group `μ_n = D(ℤ/n)` and its standard generator are Tau Ceti's
`TauCeti.RootsOfUnityGroup`.
-/

public section

namespace TauCeti

section MonoidAlgebra

variable {R : Type*} [CommRing R] {G : Type*} [CommMonoid G]
variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- In characteristic `p`, the `p`-th power of `single g 1 - 1` collapses by the freshman's
dream to `single (g ^ p) 1 - 1`; when `g ^ p = 1` this is `single 1 1 - 1 = 0`. -/
theorem single_sub_one_pow_eq_zero {g : G} (hgp : g ^ p = 1) :
    (MonoidAlgebra.single g (1 : R) - 1) ^ p = 0 := by
  have : Nonempty G := ⟨1⟩
  have : CharP (MonoidAlgebra R G) p :=
    charP_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective R (MonoidAlgebra R G)) p
  rw [sub_pow_char, MonoidAlgebra.single_pow, one_pow, hgp, one_pow,
    ← MonoidAlgebra.one_def, sub_self]

/-- The group-like difference `single g 1 - 1` is nilpotent when `g ^ p = 1` in characteristic
`p`: its `p`-th power vanishes. -/
theorem isNilpotent_single_sub_one {g : G} (hgp : g ^ p = 1) :
    IsNilpotent (MonoidAlgebra.single g (1 : R) - 1) :=
  ⟨p, single_sub_one_pow_eq_zero p hgp⟩

/-- The group-like difference `single g 1 - 1` is nonzero when `g ≠ 1`, since `single` is
injective in its index (the coefficient `1` is nonzero over a nontrivial base). -/
theorem single_sub_one_ne_zero [Nontrivial R] {g : G} (hg : g ≠ 1) :
    MonoidAlgebra.single g (1 : R) - 1 ≠ 0 := by
  rw [sub_ne_zero, MonoidAlgebra.one_def]
  intro h
  exact hg (MonoidAlgebra.single_left_injective one_ne_zero h)

/-- **A diagonalizable group with `p`-torsion is non-reduced in characteristic `p`.** If `R` has
characteristic `p` and `G` has a nontrivial element `g` with `g ^ p = 1`, then the coordinate
Hopf algebra `R[G]` of `D(G)` is not reduced: `single g 1 - 1` is a nonzero nilpotent. -/
theorem not_isReduced_monoidAlgebra [Nontrivial R] {g : G} (hg : g ≠ 1) (hgp : g ^ p = 1) :
    ¬ IsReduced (MonoidAlgebra R G) := by
  intro h
  have := h
  exact single_sub_one_ne_zero hg
    (isNilpotent_iff_eq_zero.mp (isNilpotent_single_sub_one (R := R) p hgp))

end MonoidAlgebra

namespace RootsOfUnityGroup

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- The standard generator of `μ_p = D(ℤ/p)` is nontrivial: `ofAdd 1 ≠ 1` because `1 ≠ 0` in the
field `ZMod p`. -/
theorem generator_ne_one : generator p ≠ 1 := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [show generator p = Multiplicative.ofAdd (1 : ZMod p) from rfl, ne_eq, ofAdd_eq_one]
  exact one_ne_zero

omit hp in
/-- The standard generator of `μ_p = D(ℤ/p)` is `p`-torsion: `(ofAdd 1) ^ p = ofAdd (p • 1) = 1`
since `p = 0` in `ZMod p`. -/
theorem generator_pow_eq_one : generator p ^ p = 1 := by
  rw [show generator p = Multiplicative.ofAdd (1 : ZMod p) from rfl, ← ofAdd_nsmul, ofAdd_eq_one]
  simp

/-- **The coordinate Hopf algebra of `μ_p` is non-reduced in characteristic `p`.** Over a
nontrivial base `R` of characteristic `p`, the group algebra `R[Multiplicative (ZMod p)]`
representing `μ_p = D(ℤ/p)` is not reduced: the group-like difference
`single (ofAdd 1) 1 - 1` is a nonzero nilpotent. Geometrically this exhibits `μ_p` as a
non-smooth affine group scheme, the canonical non-reduced example admitted by the
finite-type theory. -/
theorem coordinateRing_not_isReduced [Nontrivial R] :
    ¬ IsReduced (MonoidAlgebra R (Multiplicative (ZMod p))) :=
  not_isReduced_monoidAlgebra p (generator_ne_one p) (generator_pow_eq_one p)

/-- The explicit nonzero nilpotent in the coordinate Hopf algebra of `μ_p`: the difference
`single (ofAdd 1) 1 - 1` of the group-like generator and the identity. -/
theorem isNilpotent_single_generator_sub_one :
    IsNilpotent (MonoidAlgebra.single (generator p) (1 : R) - 1) :=
  isNilpotent_single_sub_one p (generator_pow_eq_one p)

end RootsOfUnityGroup

end TauCeti
