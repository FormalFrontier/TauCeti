/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.AllRootSubgroups.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius

/-!
# The type-A Steinberg maps on every root subgroup

The Frobenius, the pinned graph automorphism, and their composite are explicitly constructed maps of
the full-weight type-`A_r` carrier, already pinned against its `2 * r` numbered simple root
subgroups: on those the equations recorded so far carry the parameter across unchanged. This file
records what the three maps do on the remaining root subgroups, the pair-indexed family
`TauCeti.SlStd.rootSubgroupPointsOfPair` covering all `r * (r + 1)` roots `ε_i - ε_j`:

```text
Frob_q (x_{ij}(c))     = x_{ij}(c ^ q),
γ (x_{ij}(c))          = x_{rev j, rev i}(ε_{ij} c),
γ ∘ Frob_q (x_{ij}(c)) = x_{rev j, rev i}(ε_{ij} c ^ q),      ε_{ij} = (-1) ^ (i + j + 1).
```

The Frobenius keeps each root subgroup and raises the parameter, exactly as on a simple root. The
graph automorphism reverses the two matrix indices, which is the reversal of the Bourbaki
numbering, and rescales the parameter by a sign: that sign is `1` whenever `i + j` is odd, and `-1`
whenever `i + j` is even, and the even case differs from the odd one only when `(-1 : A) ≠ 1`.

That sign comes from the signed conjugator that defines this `γ`. The sum `i + j` is odd on every
numbered simple root, by `TauCeti.SlStd.odd_rootTarget_add_rootSource`, which is why the pinned
equation `TauCeti.SlStd.graphAutomorphismPoints_rootSubgroupPoints` carries no sign; but
as soon as the rank is at least two the root `ε_0 - ε_2` has even index sum, and the automorphism
inverts its parameter there. That inversion is a genuine departure from the sign-free equation
whenever `-1 ≠ 1` in the coefficient ring, which is
`TauCeti.SlStd.exists_graphAutomorphismPoints_rootSubgroupPointsOfPair_ne`; over a ring where
`-1 = 1`, such as `ZMod 2`, the sign is invisible and no such witness exists. Nothing here claims
the stronger statement that no reparametrization of the root subgroups makes this particular `γ`
sign-free on every root at once: that is a statement about compatibility with the Chevalley
commutator constants, and is not proved in this file. The sign does not move the subgroup itself,
only the parameter inside it, which is
`TauCeti.SlStd.map_graphAutomorphismPoints_range_rootSubgroupPointsOfPair`.

Nothing here asserts that the carrier is the pinned simply connected Chevalley--Demazure group
scheme, nor that any of the groups below is finite.

## Main results

* `TauCeti.SlStd.frobenius_rootSubgroupPointsOfPair`: the Frobenius fixes every root subgroup and
  raises its parameter to the `p ^ k`-th power.
* `TauCeti.SlStd.graphAutomorphismPoints_rootSubgroupPointsOfPair`: the graph automorphism carries
  the root subgroup at `ε_i - ε_j` to the one at `ε_{rev j} - ε_{rev i}`, rescaling the parameter
  by `(-1) ^ (i + j + 1)`; `..._of_odd` and `..._of_even` split the two cases.
* `TauCeti.SlStd.exists_graphAutomorphismPoints_rootSubgroupPointsOfPair_eq_inv`: from rank two on,
  the automorphism inverts the parameter of some root subgroup.
* `TauCeti.SlStd.exists_graphAutomorphismPoints_rootSubgroupPointsOfPair_ne`: if moreover `-1 ≠ 1`
  in the coefficient ring, that inversion genuinely moves a point, so the sign-free simple-root
  equation really does fail on some root.
* `TauCeti.SlStd.map_graphAutomorphismPoints_range_rootSubgroupPointsOfPair`: the graph
  automorphism nevertheless permutes the root subgroups themselves.
* `TauCeti.SlStd.twistedFrobenius_rootSubgroupPointsOfPair`: the composite equation, the
  general-root form of the Steinberg map of the family `²A_r(q)`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 12.2, for the sign a graph automorphism
  attaches to a general root.
* R. Steinberg, *Lectures on Chevalley Groups*, §10.
-/

public section

namespace TauCeti.SlStd

noncomputable section

variable (r p k : ℕ)

/-! ## The Frobenius on an arbitrary root subgroup -/

section Frobenius

universe v

variable {A : Type v} [CommRing A] [ExpChar A p] {i j : Fin (r + 1)}

/-- **The Frobenius raises the parameter of every root subgroup to its `p ^ k`-th power**, and
fixes the root. On a numbered simple root this is
`TauCeti.SlStd.frobenius_rootSubgroupPoints`. -/
@[simp]
theorem frobenius_rootSubgroupPointsOfPair (hij : i ≠ j) (u : Multiplicative A) :
    frobenius r p k A (rootSubgroupPointsOfPair r hij u) =
      rootSubgroupPointsOfPair r hij
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ p ^ k)) := by
  apply Subtype.ext
  rw [coe_frobenius, coe_rootSubgroupPointsOfPair, coe_rootSubgroupPointsOfPair,
    map_transvectionUnit]
  simp only [iterateFrobenius_def, toAdd_ofAdd]

end Frobenius

/-! ## The graph automorphism on an arbitrary root subgroup -/

section GraphAutomorphism

variable {A : Type} [CommRing A] {i j : Fin (r + 1)}

/-- **The pinned graph automorphism on an arbitrary root subgroup.** It carries the root subgroup
at `ε_i - ε_j` to the one at `ε_{rev j} - ε_{rev i}` and rescales the parameter by the sign
`(-1) ^ (i + j + 1)`. The reversal of the indices is the reversal of the Bourbaki numbering that
`TauCeti.SlStd.graphAutomorphismPoints_rootSubgroupPoints` records on the simple roots; the sign is
`1` on those roots and can be `-1` on the others. -/
@[simp]
theorem graphAutomorphismPoints_rootSubgroupPointsOfPair (hij : i ≠ j) (u : Multiplicative A) :
    graphAutomorphismPoints r A (rootSubgroupPointsOfPair r hij u) =
      rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm)
        (Multiplicative.ofAdd
          ((-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * Multiplicative.toAdd u)) := by
  apply Subtype.ext
  rw [coe_graphAutomorphismPoints, coe_rootSubgroupPointsOfPair, coe_rootSubgroupPointsOfPair,
    typeAGraphAutomorphism_transvectionUnit_of_ne]
  simp only [toAdd_ofAdd]

/-- On a root whose two matrix indices have odd sum, the graph automorphism carries the parameter
across unchanged. Every numbered simple root is of this kind, by
`TauCeti.SlStd.odd_rootTarget_add_rootSource`. -/
theorem graphAutomorphismPoints_rootSubgroupPointsOfPair_of_odd (hij : i ≠ j)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) (u : Multiplicative A) :
    graphAutomorphismPoints r A (rootSubgroupPointsOfPair r hij u) =
      rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm) u := by
  rw [graphAutomorphismPoints_rootSubgroupPointsOfPair, hodd.add_one.neg_one_pow, one_mul,
    ofAdd_toAdd]

/-- On a root whose two matrix indices have even sum, the graph automorphism inverts the
parameter. -/
theorem graphAutomorphismPoints_rootSubgroupPointsOfPair_of_even (hij : i ≠ j)
    (heven : Even ((i : ℕ) + (j : ℕ))) (u : Multiplicative A) :
    graphAutomorphismPoints r A (rootSubgroupPointsOfPair r hij u) =
      rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm) u⁻¹ := by
  rw [graphAutomorphismPoints_rootSubgroupPointsOfPair, heven.add_one.neg_one_pow, neg_one_mul,
    ofAdd_neg, ofAdd_toAdd]

/-- **The graph automorphism inverts the parameter of some root subgroup.** As soon as the rank is
at least two the root `ε_0 - ε_2` has even index sum, so the sign `(-1) ^ (i + j + 1)` there is
`-1`. This is an equation, not an inequality: whether the two sides differ depends on the
coefficient ring, and
`TauCeti.SlStd.exists_graphAutomorphismPoints_rootSubgroupPointsOfPair_ne` supplies the separation
under `(-1 : A) ≠ 1`. -/
theorem exists_graphAutomorphismPoints_rootSubgroupPointsOfPair_eq_inv (hr : 2 ≤ r) :
    ∃ (i j : Fin (r + 1)) (hij : i ≠ j), ∀ u : Multiplicative A,
      graphAutomorphismPoints r A (rootSubgroupPointsOfPair r hij u) =
        rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm) u⁻¹ := by
  refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_, fun u => ?_⟩
  · simp [Fin.ext_iff]
  -- The two indices are the numerals `0` and `2`, whose sum is `1 + 1`.
  · exact graphAutomorphismPoints_rootSubgroupPointsOfPair_of_even r _ ⟨1, rfl⟩ u

/-- **The sign-free simple-root equation does not extend to every root.** From rank two on, and
whenever `-1` and `1` are distinct in the coefficient ring, there is a root subgroup and a point of
it whose image under the graph automorphism is *not* the point with the same parameter in the
reversed root subgroup. Together with `TauCeti.SlStd.odd_rootTarget_add_rootSource`, which puts
every numbered simple root in the sign-free case, this says that the sign-free equation holding on
the numbered simple roots does not hold on every root. The hypothesis on `A` is needed: over
`ZMod 2` the sign `-1` equals `1` and the equation of
`TauCeti.SlStd.graphAutomorphismPoints_rootSubgroupPointsOfPair` is sign-free on every root. -/
theorem exists_graphAutomorphismPoints_rootSubgroupPointsOfPair_ne (hr : 2 ≤ r)
    (hA : (-1 : A) ≠ 1) :
    ∃ (i j : Fin (r + 1)) (hij : i ≠ j) (u : Multiplicative A),
      graphAutomorphismPoints r A (rootSubgroupPointsOfPair r hij u) ≠
        rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm) u := by
  have hij : (⟨0, by omega⟩ : Fin (r + 1)) ≠ ⟨2, by omega⟩ :=
    Fin.ne_of_val_ne (by omega : (0 : ℕ) ≠ 2)
  refine ⟨_, _, hij, Multiplicative.ofAdd 1, ?_⟩
  intro h
  -- The two indices are the numerals `0` and `2`, whose sum is `1 + 1`.
  rw [graphAutomorphismPoints_rootSubgroupPointsOfPair_of_even r hij ⟨1, rfl⟩] at h
  have h' := rootSubgroupPointsOfPair_injective r _ h
  rw [← ofAdd_neg] at h'
  exact hA (Multiplicative.ofAdd.injective h')

/-- **The graph automorphism permutes the root subgroups.** The sign it introduces rescales the
parameter by a unit and so does not move the subgroup: the image of the root subgroup at
`ε_i - ε_j` is the root subgroup at `ε_{rev j} - ε_{rev i}`. -/
theorem map_graphAutomorphismPoints_range_rootSubgroupPointsOfPair (hij : i ≠ j) :
    Subgroup.map (graphAutomorphismPoints r A).toMonoidHom
        (rootSubgroupPointsOfPair r hij).range =
      (rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm)).range := by
  set ε : A := (-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) with hε
  -- The sign is its own inverse, so rescaling the parameter by it is a surjective endomorphism of
  -- `Multiplicative A`.
  have hεε (a : A) : ε * (ε * a) = a := by
    rw [hε, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  set σ : Multiplicative A →* Multiplicative A :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft ε) with hσ
  have hσrange : σ.range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ fun u =>
      ⟨Multiplicative.ofAdd (ε * Multiplicative.toAdd u), by
        rw [hσ]; exact congrArg Multiplicative.ofAdd (hεε _)⟩
  -- On the root subgroup at `ε_i - ε_j` the graph automorphism is that rescaling followed by the
  -- parametrization of the reversed root subgroup.
  have hcomp : (graphAutomorphismPoints r A).toMonoidHom.comp (rootSubgroupPointsOfPair r hij) =
      (rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm)).comp σ :=
    MonoidHom.ext fun u => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        graphAutomorphismPoints_rootSubgroupPointsOfPair, hσ]
      rfl
  rw [MonoidHom.map_range, hcomp, MonoidHom.range_comp, hσrange, ← MonoidHom.range_eq_map]

end GraphAutomorphism

/-! ## The twisted Frobenius on an arbitrary root subgroup -/

section TwistedFrobenius

variable {A : Type} [CommRing A] [ExpChar A p] {i j : Fin (r + 1)}

/-- **The graph-twisted Frobenius on an arbitrary root subgroup.** It reverses the two matrix
indices, raises the parameter to the `p ^ k`-th power, and rescales it by the sign
`(-1) ^ (i + j + 1)`. This is the general-root form of the Steinberg map of the twisted family
`²A_r(q)`, whose simple-root form is
`TauCeti.SlStd.twistedFrobenius_rootSubgroupPoints`. -/
@[simp]
theorem twistedFrobenius_rootSubgroupPointsOfPair (hij : i ≠ j) (u : Multiplicative A) :
    twistedFrobenius r p k A (rootSubgroupPointsOfPair r hij u) =
      rootSubgroupPointsOfPair r (Fin.rev_injective.ne hij.symm)
        (Multiplicative.ofAdd
          ((-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * Multiplicative.toAdd u ^ p ^ k)) := by
  rw [twistedFrobenius_apply, frobenius_rootSubgroupPointsOfPair,
    graphAutomorphismPoints_rootSubgroupPointsOfPair]
  simp only [toAdd_ofAdd]

end TwistedFrobenius

end

end TauCeti.SlStd
