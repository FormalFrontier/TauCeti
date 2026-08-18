/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.Points
public import TauCeti.Algebra.CharP.FrobeniusFixed
public import TauCeti.GroupTheory.FixedSubgroup

/-!
# Frobenius-fixed points are the points over the fixed subring

Let `H` be a Hopf algebra over `ℤ` and let `A` be a commutative ring of exponential
characteristic `p`. The `p ^ n`-power Frobenius acts on the convolution group of `A`-valued
points of `H` by `TauCeti.Bialgebra.iterateFrobeniusPoints`, and a point is fixed by it exactly
when each of its values is fixed in `A`. Since those values form the subring
`TauCeti.frobeniusFixedSubring A p n`, the fixed points of the Frobenius are precisely the points
of `H` valued in that subring:

```text
fixedSubgroup (iterateFrobeniusPoints p n) ≃* WithConv (H →ₐ[ℤ] frobeniusFixedSubring A p n).
```

This is what makes the fixed-point construction of the finite groups of Lie type a construction of
`𝔽_q`-rational points: for `p` prime, `0 < n`, `A` an algebraic closure of `ZMod p` and `q = p ^ n`
the fixed subring is the field of `q` elements inside `A`, so the fixed subgroup is the group of
`𝔽_q`-points of the affine group scheme `Spec H`. At `n = 0` the Frobenius iterate is the identity
and the fixed subgroup is all of the `A`-valued points. Nothing here needs `A` to be a field,
algebraically closed, or of finite type, and no finiteness is asserted.

## Main definitions

* `TauCeti.Bialgebra.frobeniusFixedInclusion`: the inclusion of the points valued in the
  Frobenius-fixed subring into the points valued in `A`.
* `TauCeti.Bialgebra.frobeniusFixedPointsMulEquiv`: the resulting isomorphism onto the fixed
  subgroup of the Frobenius.

## Main results

* `TauCeti.Bialgebra.iterateFrobeniusPoints_eq_self_iff` and
  `TauCeti.Bialgebra.mem_fixedSubgroup_iterateFrobeniusPoints`: a point is Frobenius-fixed exactly
  when all of its values are.
* `TauCeti.Bialgebra.range_frobeniusFixedInclusion`: the inclusion has the fixed subgroup as its
  range.
* `TauCeti.Bialgebra.frobeniusFixedInclusion_frobeniusFixedPointsMulEquiv_symm` and
  `TauCeti.Bialgebra.frobeniusFixedPointsMulEquiv_symm_apply_apply`: the inverse of that
  isomorphism reads a fixed point as a point over the fixed subring, with the same values.
* `TauCeti.Bialgebra.fixedSubgroup_iterateFrobeniusPoints_le_of_dvd`: the fixed subgroups grow
  along divisibility of the exponent, the inclusion `G(𝔽_q) ⊆ G(𝔽_{q ^ k})` in the motivating
  case.
* `TauCeti.Bialgebra.mapValue_mem_fixedSubgroup_iterateFrobeniusPoints`: a homomorphism of value
  algebras carries Frobenius-fixed points to Frobenius-fixed points.

## References

This advances the target "points over an algebraically closed field as a group, functorially in
the field, so that a field endomorphism induces a group endomorphism of the points" in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, which names the `q`-power Frobenius as the first case
a consumer asks for. The consumer is milestone L3 of `TauCetiRoadmap/CFSGStatement/README.md`,
which sets `H_d = fixedSubgroup d.steinberg`; the construction is standard, see R. W. Carter,
*Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

open WithConv

namespace TauCeti

namespace Bialgebra

universe u v w

variable (p n : ℕ)

section Bialgebra

variable {H : Type u} [Semiring H] [_root_.Bialgebra ℤ H]
variable {A : Type v} [CommRing A] [ExpChar A p]

/-- A point is fixed by the `p ^ n`-power Frobenius exactly when every one of its values lies in
the Frobenius-fixed subring of the value algebra. -/
theorem iterateFrobeniusPoints_eq_self_iff {f : WithConv (H →ₐ[ℤ] A)} :
    iterateFrobeniusPoints p n f = f ↔ ∀ h : H, f.ofConv h ∈ frobeniusFixedSubring A p n := by
  constructor
  · intro hf h
    rw [mem_frobeniusFixedSubring, ← iterateFrobeniusPoints_apply_apply p n f h, hf]
  · intro hf
    refine WithConv.ofConv_injective (AlgHom.ext fun h => ?_)
    rw [iterateFrobeniusPoints_apply_apply]
    exact mem_frobeniusFixedSubring.mp (hf h)

/-- The corestriction of a point all of whose values are Frobenius-fixed to a point valued in the
Frobenius-fixed subring. Private: the public interface is `frobeniusFixedInclusion` together with
`range_frobeniusFixedInclusion`, which say the same thing without exposing a second spelling of a
point. -/
private def corestrictFrobeniusFixed (f : H →ₐ[ℤ] A)
    (hf : ∀ h : H, f h ∈ frobeniusFixedSubring A p n) :
    H →ₐ[ℤ] ↥(frobeniusFixedSubring A p n) :=
  f.codRestrict (subalgebraOfSubring (frobeniusFixedSubring A p n)) hf

/-- The corestriction of a point to the Frobenius-fixed subring has the same values as the point
itself. Private, like the corestriction it describes. -/
private theorem corestrictFrobeniusFixed_apply (f : H →ₐ[ℤ] A)
    (hf : ∀ h : H, f h ∈ frobeniusFixedSubring A p n) (h : H) :
    (corestrictFrobeniusFixed p n f hf h : A) = f h := rfl

/-- The homomorphism of convolution monoids that reads a point valued in the Frobenius-fixed
subring of `A` as a point valued in `A`. It is post-composition with the inclusion of the subring,
so it needs only the bialgebra structure; for a Hopf algebra it is a homomorphism of the
convolution groups. -/
noncomputable def frobeniusFixedInclusion :
    WithConv (H →ₐ[ℤ] ↥(frobeniusFixedSubring A p n)) →* WithConv (H →ₐ[ℤ] A) :=
  AlgHom.mapValue (frobeniusFixedSubring A p n).subtype.toIntAlgHom

/-- Pointwise, the inclusion of the points valued in the Frobenius-fixed subring is the inclusion
of that subring applied to each value. -/
@[simp]
theorem frobeniusFixedInclusion_apply_apply
    (f : WithConv (H →ₐ[ℤ] ↥(frobeniusFixedSubring A p n))) (h : H) :
    (frobeniusFixedInclusion p n f).ofConv h = (f.ofConv h : A) := by
  rw [frobeniusFixedInclusion, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    RingHom.toIntAlgHom_apply, Subring.coe_subtype]

/-- Reading a point valued in the Frobenius-fixed subring as a point valued in `A` loses no
information. -/
theorem frobeniusFixedInclusion_injective :
    Function.Injective (frobeniusFixedInclusion p n (H := H) (A := A)) := by
  intro f g hfg
  refine WithConv.ofConv_injective (AlgHom.ext fun h => Subtype.ext ?_)
  have := congrArg (fun x : WithConv (H →ₐ[ℤ] A) => x.ofConv h) hfg
  simpa using this

end Bialgebra

section HopfAlgebra

variable {H : Type u} [Semiring H] [_root_.HopfAlgebra ℤ H]
variable {A : Type v} [CommRing A] [ExpChar A p]

/-- A point is in the fixed subgroup of the `p ^ n`-power Frobenius exactly when every one of its
values lies in the Frobenius-fixed subring of the value algebra. -/
theorem mem_fixedSubgroup_iterateFrobeniusPoints {f : WithConv (H →ₐ[ℤ] A)} :
    f ∈ fixedSubgroup (iterateFrobeniusPoints p n) ↔
      ∀ h : H, f.ofConv h ∈ frobeniusFixedSubring A p n :=
  iterateFrobeniusPoints_eq_self_iff p n

/-- The points valued in the Frobenius-fixed subring are exactly the Frobenius-fixed points. -/
theorem range_frobeniusFixedInclusion :
    (frobeniusFixedInclusion p n (H := H) (A := A)).range =
      fixedSubgroup (iterateFrobeniusPoints p n) := by
  ext f
  rw [MonoidHom.mem_range, mem_fixedSubgroup_iterateFrobeniusPoints]
  constructor
  · rintro ⟨g, rfl⟩ h
    exact (g.ofConv h).2
  · intro hf
    refine ⟨toConv (corestrictFrobeniusFixed p n f.ofConv hf), ?_⟩
    refine WithConv.ofConv_injective (AlgHom.ext fun h => ?_)
    rw [frobeniusFixedInclusion_apply_apply, ofConv_toConv, corestrictFrobeniusFixed_apply]

/-- The fixed points of the `p ^ n`-power Frobenius on the points of `Spec H` valued in `A` are
the points of `Spec H` valued in the Frobenius-fixed subring of `A`.

For `p` prime, `0 < n`, `A` an algebraic closure of `ZMod p` and `q = p ^ n` the right-hand side is
the group of `𝔽_q`-points, which is why the finite groups of Lie type are defined as fixed points
of a Steinberg endomorphism. -/
noncomputable def frobeniusFixedPointsMulEquiv :
    WithConv (H →ₐ[ℤ] ↥(frobeniusFixedSubring A p n)) ≃*
      ↥(fixedSubgroup (iterateFrobeniusPoints p n (H := H) (A := A))) :=
  (MonoidHom.ofInjective (frobeniusFixedInclusion_injective p n)).trans
    (MulEquiv.subgroupCongr (range_frobeniusFixedInclusion p n))

/-- The isomorphism onto the fixed subgroup is the inclusion of the points valued in the
Frobenius-fixed subring, read in the ambient group of `A`-valued points. -/
@[simp]
theorem coe_frobeniusFixedPointsMulEquiv
    (f : WithConv (H →ₐ[ℤ] ↥(frobeniusFixedSubring A p n))) :
    (frobeniusFixedPointsMulEquiv p n f : WithConv (H →ₐ[ℤ] A)) =
      frobeniusFixedInclusion p n f := by
  rw [frobeniusFixedPointsMulEquiv, MulEquiv.coe_trans, Function.comp_apply,
    MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

/-- The inverse of the isomorphism reads a Frobenius-fixed point as a point valued in the
Frobenius-fixed subring: including it back into the `A`-valued points returns the point one
started from. -/
@[simp]
theorem frobeniusFixedInclusion_frobeniusFixedPointsMulEquiv_symm
    (g : ↥(fixedSubgroup (iterateFrobeniusPoints p n (H := H) (A := A)))) :
    frobeniusFixedInclusion p n ((frobeniusFixedPointsMulEquiv p n).symm g) =
      (g : WithConv (H →ₐ[ℤ] A)) := by
  rw [← coe_frobeniusFixedPointsMulEquiv, MulEquiv.apply_symm_apply]

/-- Pointwise form: the values of the point over the Frobenius-fixed subring produced by the
inverse of the isomorphism are the values of the Frobenius-fixed point it came from. -/
@[simp]
theorem frobeniusFixedPointsMulEquiv_symm_apply_apply
    (g : ↥(fixedSubgroup (iterateFrobeniusPoints p n (H := H) (A := A)))) (h : H) :
    ((((frobeniusFixedPointsMulEquiv p n).symm g).ofConv h : ↥(frobeniusFixedSubring A p n)) : A) =
      (g : WithConv (H →ₐ[ℤ] A)).ofConv h := by
  rw [← frobeniusFixedInclusion_apply_apply,
    frobeniusFixedInclusion_frobeniusFixedPointsMulEquiv_symm]

/-! ### Elementary properties of the fixed subgroup -/

/-- The zeroth Frobenius iterate fixes every point.

Deliberately not `@[simp]`: `iterateFrobeniusPoints_zero` already rewrites the endomorphism to the
identity, after which `MonoidHom.eqLocus_same` closes the goal, so a `simp` attribute here would be
redundant and the `simpNF` linter rejects it. -/
theorem fixedSubgroup_iterateFrobeniusPoints_zero :
    fixedSubgroup (iterateFrobeniusPoints p 0 (H := H) (A := A)) = ⊤ :=
  fixedSubgroup_eq_top_iff.mpr (iterateFrobeniusPoints_zero p)

/-- Fixed subgroups grow along divisibility of the exponent. In the motivating case this is the
inclusion `G(𝔽_{p ^ m}) ⊆ G(𝔽_{p ^ k})` of groups of rational points. -/
theorem fixedSubgroup_iterateFrobeniusPoints_le_of_dvd {m k : ℕ} (hmk : m ∣ k) :
    fixedSubgroup (iterateFrobeniusPoints p m (H := H) (A := A)) ≤
      fixedSubgroup (iterateFrobeniusPoints p k) := fun _ hf =>
  (mem_fixedSubgroup_iterateFrobeniusPoints p k).mpr fun h =>
    frobeniusFixedSubring_le_of_dvd hmk
      ((mem_fixedSubgroup_iterateFrobeniusPoints p m).mp hf h)

variable {B : Type w} [CommRing B] [ExpChar B p]

/-- A homomorphism of value algebras carries Frobenius-fixed points to Frobenius-fixed points, so
the functoriality of the points in the value algebra restricts to the rational points. -/
theorem mapValue_mem_fixedSubgroup_iterateFrobeniusPoints (φ : A →ₐ[ℤ] B)
    {f : WithConv (H →ₐ[ℤ] A)} (hf : f ∈ fixedSubgroup (iterateFrobeniusPoints p n)) :
    AlgHom.mapValue (H := H) φ f ∈ fixedSubgroup (iterateFrobeniusPoints p n) := by
  refine (mem_fixedSubgroup_iterateFrobeniusPoints p n).mpr fun h => ?_
  exact map_mem_frobeniusFixedSubring (φ : A →+* B)
    ((mem_fixedSubgroup_iterateFrobeniusPoints p n).mp hf h)

/-- The subgroup form of `mapValue_mem_fixedSubgroup_iterateFrobeniusPoints`: the image of the
Frobenius-fixed subgroup under a homomorphism of value algebras lands in the Frobenius-fixed
subgroup. -/
theorem map_fixedSubgroup_iterateFrobeniusPoints_le (φ : A →ₐ[ℤ] B) :
    Subgroup.map (AlgHom.mapValue (H := H) φ)
        (fixedSubgroup (iterateFrobeniusPoints p n)) ≤
      fixedSubgroup (iterateFrobeniusPoints p n) := by
  rintro _ ⟨_, hf, rfl⟩
  exact mapValue_mem_fixedSubgroup_iterateFrobeniusPoints p n φ hf

end HopfAlgebra

end Bialgebra

end TauCeti
