/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.GeckCarrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius

/-!
# The prime Frobenius of a Lie-type index

Two different Frobenius maps occur in the classification list. The one already attached to a valid
Lie-type index is `Frob_q`, at the field order `q` the index records: it is
`TauCeti.ValidLieTypeIndex.geckFrobenius` on the points of the Geck carrier, and it is the
Steinberg map of the untwisted families. The other is `Frob_p`, at the defining characteristic. It
is not the Steinberg map of any family, and it is what the Suzuki--Ree convention is stated
against: milestone L2 of `TauCetiRoadmap/CFSGStatement/README.md` selects the special isogeny `τ`
by

```text
τ ^ 2 = Frob_p,     steinberg (m) = τ ^ (2 * m + 1),
```

so on the four half-Frobenius indices the exponent separating the two maps is the odd number
`2 * m + 1`, which by `TauCeti.SuzukiReeIndex.halfExponent_eq_zero_iff` is `1` exactly on the Tits
index. This file defines `Frob_p` on the Geck carrier as
`TauCeti.ValidLieTypeIndex.geckPrimeFrobenius`, gives it the equations `Frob_q` already has, and
records the two relations that connect the two maps: `Frob_q` is the `fieldExponent`-th iterate of
`Frob_p` on every index, and on a half-Frobenius index that exponent is the odd number `2 * m + 1`.

The second of those is the scalar that a group-level `steinberg (m) ^ 2` will have to equal, and
the reason this map is worth naming: `TauCeti.SuzukiReeIndex.datumSpecialIsogeny_comp_self` states
the square relation on the root datum against `TauCeti.RootPairingIsogeny.smulId` at the
characteristic, and no group-level `Frob_p` was available to state its companion. That companion is
still not stated here, because `τ` itself is a Layer 9 target of
`TauCetiRoadmap/ReductiveGroups/README.md`; what this file removes is the missing right-hand side.

Everything carries the `geck` prefix required by
`TauCeti/GroupTheory/SpecificGroups/CFSG/GeckCarrier.lean`: Geck's module is the adjoint module, so
this carrier is not claimed to be the pinned simply connected Chevalley--Demazure group that
milestone L0 asks for, and the name `TauCeti.ValidLieTypeIndex.primeFrobenius` is left free for it.
Nothing below asserts that a group is finite, perfect or simple.

## Main definitions

* `TauCeti.ValidLieTypeIndex.geckPrimeFrobenius`: the `p`-power Frobenius endomorphism of the Geck
  point group, for `p` the characteristic recorded by the index.

## Main results

* `TauCeti.ValidLieTypeIndex.coe_geckPrimeFrobenius_apply`: it raises every matrix entry to the
  `p`-th power.
* `TauCeti.ValidLieTypeIndex.geckPrimeFrobenius_geckRootSubgroup`: it raises the parameter of every
  numbered root subgroup to the `p`-th power.
* `TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckPrimeFrobenius_iff`: its fixed points are the
  points of the carrier whose matrix entries lie in the prime field.
* `TauCeti.ValidLieTypeIndex.coe_iterate_geckPrimeFrobenius` and
  `TauCeti.ValidLieTypeIndex.coe_geckFrobenius_eq_iterate_geckPrimeFrobenius`: its `k`-th iterate is
  the Frobenius at exponent `k`, so `Frob_q` is its `fieldExponent`-th iterate.
* `TauCeti.SuzukiReeIndex.coe_geckFrobenius_eq_iterate_geckPrimeFrobenius`: on a half-Frobenius
  index that exponent is `2 * m + 1`.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  [arXiv:2108.06291](https://arxiv.org/abs/2108.06291), for the formulation `τ ^ 2 = Frob_p` and its
  odd powers.
* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247, for the matrix realization of the carrier.

## Roadmap

This supplies the group-level `Frob_p` that milestone L2 of
`TauCetiRoadmap/CFSGStatement/README.md` names in `τ ^ 2 = Frob_p` and in
`steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1))`, on the carrier the three unimodular half-Frobenius
indices `²G₂(3 ^ (2m+1))`, `²F₄(2 ^ (2m+1))` and `²F₄(2)'` already use; the lattice condition that
makes that carrier the right one for them is
`TauCeti.UnimodularLieIndex.span_range_geckWeight_eq_top`. It does not close L2, whose remaining
content is `τ` itself, a Layer 9 target of `TauCetiRoadmap/ReductiveGroups/README.md`, and the odd
power of it; the root-datum shadows of both are already available as
`TauCeti.SuzukiReeIndex.datumSpecialIsogeny` and `TauCeti.SuzukiReeIndex.datumSteinberg`.
-/

public section

namespace TauCeti

namespace ValidLieTypeIndex

noncomputable section

variable (d : ValidLieTypeIndex)

/-- **The `p`-power Frobenius endomorphism of the Geck point group**, for `p` the characteristic
recorded by the index.

It is not the Steinberg map of any family: the untwisted families take `Frob_q` at the recorded
field order, and the Suzuki--Ree and Tits families take an odd power of a half-Frobenius. It is the
map their convention is stated against, `τ ^ 2 = Frob_p`, and by
`TauCeti.ValidLieTypeIndex.coe_geckFrobenius_eq_iterate_geckPrimeFrobenius` every `Frob_q` in the
list is one of its iterates. -/
def geckPrimeFrobenius : GeckGroup d →* GeckGroup d :=
  d.dynkinType.geckFrobenius d.dynkinType_valid d.characteristic 1 d.Closure

/-- The prime Frobenius is that of the pinned Geck carrier at exponent one. This is its unfolding
lemma; the definition itself stays sealed. -/
theorem geckPrimeFrobenius_def : d.geckPrimeFrobenius =
    d.dynkinType.geckFrobenius d.dynkinType_valid d.characteristic 1 d.Closure := by
  rw [geckPrimeFrobenius]

/-- The prime Frobenius acts on the Geck point group by raising every matrix entry to the `p`-th
power. -/
@[simp]
theorem coe_geckPrimeFrobenius_apply (g : GeckGroup d)
    (r c : Fin (d.dynkinType.geckDim d.dynkinType_valid)) :
    ((d.geckPrimeFrobenius g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) :
        Matrix _ _ d.Closure) r c =
      ((g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) :
        Matrix _ _ d.Closure) r c ^ d.characteristic := by
  rw [geckPrimeFrobenius_def, d.dynkinType.coe_geckFrobenius_apply d.dynkinType_valid _ _ _ g r c,
    pow_one]

/-- **The prime Frobenius raises the parameter of every numbered root subgroup to the `p`-th
power.** On a simple root subgroup this is the equation `Frob_p (x_α(t)) = x_α(t ^ p)`, the `k = 1`
member of the family of pinned equations that milestone L1 of
`TauCetiRoadmap/CFSGStatement/README.md` asks of an untwisted Steinberg map. -/
@[simp]
theorem geckPrimeFrobenius_geckRootSubgroup
    (i : Fin d.dynkinType.rank ⊕ Fin d.dynkinType.rank) (u : Multiplicative d.Closure) :
    d.geckPrimeFrobenius (d.geckRootSubgroup i u) =
      d.geckRootSubgroup i (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.characteristic)) := by
  -- The upstream equation is stated on the explicit matrix, so rewrite each root-subgroup point
  -- into that form first; `TauCeti.ValidLieTypeIndex.coe_geckRootSubgroup` is what says they agree.
  have key : ∀ v : Multiplicative d.Closure, d.geckRootSubgroup i v =
      ⟨d.dynkinType.geckRootSubgroupMatrix d.dynkinType_valid i
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm v),
        d.dynkinType.geckRootSubgroupMatrix_mem_geckPoints d.dynkinType_valid d.Closure i
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := d.Closure)).symm v)⟩ :=
    fun v => Subtype.ext (d.coe_geckRootSubgroup i v)
  have h := d.dynkinType.geckFrobenius_geckRootSubgroupMatrix d.dynkinType_valid
    d.characteristic 1 d.Closure i u
  rw [pow_one] at h
  rw [geckPrimeFrobenius_def, key u, key (Multiplicative.ofAdd (Multiplicative.toAdd u ^
    d.characteristic))]
  exact h

/-- **A point of the Geck point group is fixed by the prime Frobenius exactly when all of its
matrix entries lie in the prime field**, that is, satisfy `x ^ p = x`. The prime field is the
smallest of the fields of definition cut out by the Frobenius powers, and by
`TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff` the one belonging to the index
itself is cut out by `Frob_q`. That companion reads its condition as membership in
`TauCeti.ValidLieTypeIndex.fixedField`, which is the subfield at the exponent the index records; no
`Subfield` is attached to an index at exponent one, so the condition is stated elementarily here.

This is deliberately not a `simp` lemma, for the reason recorded at
`TauCeti.ValidLieTypeIndex.mem_fixedSubgroup_geckFrobenius_iff`: `TauCeti.fixedSubgroup` is
`MonoidHom.eqLocus` against the identity, so `simp` rewrites the left-hand side through
`MonoidHom.mem_eqLocus` and the `simpNF` linter rejects the annotation. -/
theorem mem_fixedSubgroup_geckPrimeFrobenius_iff (g : GeckGroup d) :
    g ∈ fixedSubgroup d.geckPrimeFrobenius ↔
      ∀ r c, ((g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) :
        Matrix (Fin (d.dynkinType.geckDim d.dynkinType_valid))
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) r c ^ d.characteristic =
        ((g : Matrix.GeneralLinearGroup
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) :
        Matrix (Fin (d.dynkinType.geckDim d.dynkinType_valid))
          (Fin (d.dynkinType.geckDim d.dynkinType_valid)) d.Closure) r c := by
  rw [mem_fixedSubgroup, geckPrimeFrobenius_def,
    d.dynkinType.geckFrobenius_eq_self_iff d.dynkinType_valid _ _ _ g]
  simp only [mem_frobeniusFixedSubring, pow_one]

/-! ## The Frobenius powers -/

/-- **The `k`-th iterate of the prime Frobenius is the Frobenius at exponent `k`.** So the prime
Frobenius generates the whole family of Frobenius endomorphisms of the Geck carrier, and every
relation the list states at one exponent can be read at another. -/
theorem coe_iterate_geckPrimeFrobenius (k : ℕ) :
    (⇑d.geckPrimeFrobenius)^[k] =
      ⇑(d.dynkinType.geckFrobenius d.dynkinType_valid d.characteristic k d.Closure) := by
  rw [geckPrimeFrobenius_def]
  exact (d.dynkinType.coe_geckFrobenius_eq_iterate d.dynkinType_valid d.characteristic k
    d.Closure).symm

/-- **The Frobenius of an index is the `fieldExponent`-th iterate of its prime Frobenius**, which
is the group-level reading of `q = p ^ e`. On the untwisted families the left-hand side is the
Steinberg map, and on the graph-twisted ones it is the factor of it that is not the diagram
automorphism. -/
theorem coe_geckFrobenius_eq_iterate_geckPrimeFrobenius :
    ⇑d.geckFrobenius = (⇑d.geckPrimeFrobenius)^[d.fieldExponent] := by
  rw [d.coe_iterate_geckPrimeFrobenius d.fieldExponent, geckFrobenius_def]

end

end ValidLieTypeIndex

/-! ## The half-Frobenius indices -/

namespace SuzukiReeIndex

/-- **On a half-Frobenius index the Frobenius is the odd iterate `Frob_p ^ (2 * m + 1)` of the
prime Frobenius.**

This is the group-level form of the scalar in milestone L2's relation
`steinberg (m) ^ 2 = Frob_(p ^ (2 * m + 1))` of `TauCetiRoadmap/CFSGStatement/README.md`: the
Steinberg map of these four indices is the odd power `τ ^ (2 * m + 1)` of a half-Frobenius, so
squaring it gives `(τ ^ 2) ^ (2 * m + 1)`, and this is the right-hand side that identity has to
land on. The map `τ` itself is a Layer 9 target of
`TauCetiRoadmap/ReductiveGroups/README.md`, so the identity is not stated here. -/
theorem coe_geckFrobenius_eq_iterate_geckPrimeFrobenius (e : SuzukiReeIndex) :
    ⇑e.1.geckFrobenius = (⇑e.1.geckPrimeFrobenius)^[2 * e.halfExponent + 1] := by
  rw [← e.fieldExponent_eq_two_mul_halfExponent_add_one]
  exact e.1.coe_geckFrobenius_eq_iterate_geckPrimeFrobenius

end SuzukiReeIndex

/-! ## Worked branches

The two extreme half-Frobenius branches: on the Tits index the recorded field order is the
characteristic itself, so the two Frobenius maps coincide, while on a Suzuki index the Frobenius is
the odd iterate that the constructor's own parameter records. -/

section Branches

/-- On the Tits index `²F₄(2)'` the field order is the characteristic, so `Frob_q` is the prime
Frobenius itself. This is the `m = 0` member of the half-Frobenius family, by
`TauCeti.SuzukiReeIndex.halfExponent_eq_zero_iff` the only one. -/
example (hv : LieTypeIndex.tits.Valid) :
    ⇑(ValidLieTypeIndex.geckFrobenius ⟨_, hv⟩) =
      ⇑(ValidLieTypeIndex.geckPrimeFrobenius ⟨_, hv⟩) := by
  rw [ValidLieTypeIndex.coe_geckFrobenius_eq_iterate_geckPrimeFrobenius,
    ValidLieTypeIndex.fieldExponent, LieTypeIndex.fieldExponent_tits, Function.iterate_one]

/-- On the Suzuki family `²B₂(2 ^ (2m+1))` the Frobenius is the `(2m+1)`-st iterate of the prime
one, the exponent being read off the constructor's own parameter. -/
example {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid) :
    ⇑(ValidLieTypeIndex.geckFrobenius ⟨_, hv⟩) =
      (⇑(ValidLieTypeIndex.geckPrimeFrobenius ⟨_, hv⟩))^[2 * m + 1] := by
  have h := SuzukiReeIndex.coe_geckFrobenius_eq_iterate_geckPrimeFrobenius ⟨⟨_, hv⟩, by simp⟩
  rwa [SuzukiReeIndex.halfExponent_suzuki m hv] at h

end Branches

end TauCeti
