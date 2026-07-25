/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Slopes on a framed boundary torus

A *slope* on the boundary torus `T` of a knot or link complement is the datum needed to specify a
Dehn filling: the isotopy class of an unoriented essential simple closed curve on `T`, equivalently
a primitive class in `H₁(T; ℤ)` taken modulo sign (Rolfsen, *Knots and Links*, Chapter 9). This is
*basis-free*: it refers only to the homology group `H₁(T; ℤ)`, an abstract rank-two free `ℤ`-module,
with no coordinates chosen. Once `T` is *framed* by an ordered basis `(μ, λ)` of meridian and
longitude, `H₁(T; ℤ)` is identified with `ℤ × ℤ` (first coordinate the `μ`-coefficient, second the
`λ`-coefficient) and every slope acquires a value `p / q ∈ ℚ ∪ {∞}`, the ratio of its coordinates;
the filling then sends the solid torus's meridian to `p · μ + q · λ`.

This file builds the slope arithmetic for the framed model, the first piece of the
geometric-topology roadmap's Dehn-surgery layer (`TauCetiRoadmap/GeometricTopology/README.md`,
layer 5, "Dehn surgery": "Slopes, with the primitive pinned … give a `FramedBoundaryTorus` an
ordered basis `(μ, λ)` … and the resulting bijection `Slope T ≃ ℚ ∪ {∞}`"). The layer asks for two
objects kept **distinct**: the sign-quotient `Slope` (basis-free) and the `ℚ ∪ {∞}` parametrisation
(basis-dependent). Accordingly `TauCeti.Slope M` is the basis-free set of primitive classes modulo
sign in an abstract `ℤ`-module `M`, and every framing-dependent notion — `meridian`, `longitude`,
`value`, and the bijection `slopeEquiv` — is a field/operation of `TauCeti.FramedBoundaryTorus`,
carrying its own ordered basis. Identifying `H₁(T; ℤ)` with the boundary torus of a genuine link
complement is now expressed through `BoundaryTorus.firstHomology`; constructing that boundary torus
from the complement is later layer-5 work that consumes this arithmetic.

Primitivity of `v : M` is expressed basis-freely: `v` is primitive when some `ℤ`-linear functional
`M →ₗ[ℤ] ℤ` sends it to `1`, so `v` splits off a copy of `ℤ`. Over the standard lattice
`ℤ × ℤ` this is exactly coprimality of the two coordinates, and that concrete arithmetic supplies
the `ℚ ∪ {∞}` bijection through any framing's coordinate isomorphism.

## Main definitions

* `TauCeti.IsPrimitive v`: the class `v : M` is primitive, i.e. some `ℤ`-functional sends it to `1`.
* `TauCeti.Slope M`: primitive classes in `M` modulo the sign action `v ↦ -v` (basis-free).
* `TauCeti.Slope.congr`: transport of `Slope` along a `ℤ`-linear equivalence.
* `TauCeti.slopeValue v`: the value `p / q ∈ ℚ ∪ {∞}` of a class `v = (p, q) : ℤ × ℤ`, being `∞`
  when `q = 0`.
* `TauCeti.slopeEquivStd`: the bijection `Slope (ℤ × ℤ) ≃ ℚ ∪ {∞}` for the standard lattice.
* `TauCeti.BoundaryTorus`: a topological space homeomorphic to the standard two-torus.
* `TauCeti.BoundaryTorus.firstHomology`: its degree-one singular homology with integer coefficients.
* `TauCeti.FramedBoundaryTorus`: a boundary torus with an ordered meridian-longitude basis of that
  homology group.
* `TauCeti.FramedBoundaryTorus.meridian` / `.longitude`: the slopes `(1, 0)` and `(0, 1)` of the
  framing.
* `TauCeti.FramedBoundaryTorus.value`: the framing-dependent `ℚ ∪ {∞}` value of a slope.
* `TauCeti.FramedBoundaryTorus.slopeEquiv`: the bijection `Slope T.H ≃ ℚ ∪ {∞}` a framing produces.

## Main results

* `TauCeti.FramedBoundaryTorus.value_meridian` / `.value_longitude`: the meridian is `∞` and the
  longitude is `0`, fixing the meridian-longitude convention.
* `TauCeti.FramedBoundaryTorus.value_mk` / `.slopeEquiv_symm_apply`: the parametrisation in
  coordinates, in each direction — a primitive class has the value of its `(μ, λ)`-coordinates, and
  a value comes from the slope whose coordinates are the corresponding reduced pair.
* `TauCeti.FramedBoundaryTorus.coord_symm_apply`: a pair of coordinates `(p, q)` names the class
  `p · μ + q · λ`, so the filling class of a slope is reachable without unfolding `coord`.

`ℚ ∪ {∞}` is Mathlib's one-point extension `OnePoint ℚ` from
`Mathlib/Topology/Compactification/OnePoint/Basic.lean`; the reduced-fraction bookkeeping reuses
Mathlib's `Rat` normalisation (`Rat.num_div_den`, `Rat.num_div_eq_of_coprime`,
`Rat.den_div_eq_of_coprime`).
-/

public section

open scoped OnePoint

open Module

namespace TauCeti

/-! ### Primitive classes and the basis-free slope type

The `Quotient` model of `Slope`, and the bodies of the maps into and out of it, are implementation
details: the underlying setoid is `private` and the bodies stay unexposed, so consumers work
through the public defining equations (`Slope.congr_mk`, `Slope.value_mk`, `slopeOfValue_infty`,
`slopeEquivStd_apply`, …). Those equations are proved by a parenthesised `(rfl)`, which keeps them
ordinary propositional lemmas instead of implicitly `@[defeq]` ones; an exported `@[defeq]` theorem
would have to expose every definition it unfolds. -/

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]

/-- A homology class `v : M` on a boundary torus is **primitive** when some `ℤ`-linear functional
`M →ₗ[ℤ] ℤ` sends it to `1`, so the span of `v` splits off a copy of `ℤ`. Over the standard
lattice `ℤ × ℤ` this is coprimality of the two coordinates (`TauCeti.isPrimitive_prod_iff`). The
definition mentions no basis, so it is preserved by every `ℤ`-linear equivalence
(`TauCeti.isPrimitive_congr`). -/
def IsPrimitive (v : M) : Prop := ∃ f : M →ₗ[ℤ] ℤ, f v = 1

/-- Primitivity is unchanged by the sign action `v ↦ -v`. -/
theorem IsPrimitive.neg {v : M} (h : IsPrimitive v) : IsPrimitive (-v) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨-f, by simp [hf]⟩

/-- Primitivity transports along a `ℤ`-linear equivalence: it is a basis-free property. -/
theorem isPrimitive_congr (φ : M ≃ₗ[ℤ] N) {v : M} : IsPrimitive (φ v) ↔ IsPrimitive v := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.comp (φ : M →ₗ[ℤ] N), by simpa using hg⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.comp (φ.symm : N →ₗ[ℤ] M), by simpa using hf⟩

/-- Two primitive classes represent the same slope when they agree up to sign. This is an
equivalence relation on primitive classes. -/
private def slopeSetoid (M : Type*) [AddCommGroup M] [Module ℤ M] :
    Setoid {v : M // IsPrimitive v} where
  r a b := a.1 = b.1 ∨ a.1 = -b.1
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun {a b} h => h.imp Eq.symm fun hab => by rw [hab, neg_neg]
      trans := fun {a b c} hab hbc => by
        rcases hab with hab | hab <;> rcases hbc with hbc | hbc
        · exact Or.inl (hab.trans hbc)
        · exact Or.inr (hab.trans hbc)
        · exact Or.inr (by rw [hab, hbc])
        · exact Or.inl (by rw [hab, hbc, neg_neg]) }

/-- Characterization of the relation defining slopes: representatives agree up to sign. This is
internal to the quotient construction; consumers use `Slope.mk_eq_mk_iff`. -/
private theorem slopeSetoid_rel_iff {a b : {v : M // IsPrimitive v}} :
    slopeSetoid M a b ↔ a.1 = b.1 ∨ a.1 = -b.1 :=
  Iff.rfl

/-- A **slope** on a boundary torus with homology `M`: a primitive homology class taken modulo the
sign action, i.e. an unoriented essential simple closed curve up to isotopy. This is basis-free — it
refers only to the abstract module `M`, not to any choice of meridian-longitude basis. -/
def Slope (M : Type*) [AddCommGroup M] [Module ℤ M] : Type _ :=
  Quotient (slopeSetoid M)

namespace Slope

/-- The slope represented by a primitive class `v : M`. -/
def mk (v : M) (h : IsPrimitive v) : Slope M := Quotient.mk (slopeSetoid M) ⟨v, h⟩

theorem mk_eq_mk {v w : M} (hv : IsPrimitive v) (hw : IsPrimitive w)
    (h : v = w ∨ v = -w) : mk v hv = mk w hw :=
  Quotient.sound h

/-- Two primitive representatives define the same slope exactly when they agree up to sign. -/
@[simp]
theorem mk_eq_mk_iff {v w : M} (hv : IsPrimitive v) (hw : IsPrimitive w) :
    mk v hv = mk w hw ↔ v = w ∨ v = -w := by
  constructor
  · exact Quotient.exact
  · exact mk_eq_mk hv hw

@[elab_as_elim]
theorem induction_on {C : Slope M → Prop} (s : Slope M)
    (h : ∀ (v : M) (hv : IsPrimitive v), C (mk v hv)) : C s :=
  Quotient.inductionOn s fun v => h v.1 v.2

/-- A `ℤ`-linear equivalence `M ≃ₗ[ℤ] N` transports slopes bijectively; a framing's coordinate
isomorphism uses this to carry a slope to the standard lattice. -/
def congr (φ : M ≃ₗ[ℤ] N) : Slope M ≃ Slope N :=
  Quotient.congr
    { toFun := fun v => ⟨φ v.1, (isPrimitive_congr φ).mpr v.2⟩
      invFun := fun w => ⟨φ.symm w.1, (isPrimitive_congr φ.symm).mpr w.2⟩
      left_inv := fun v => Subtype.ext (φ.symm_apply_apply v.1)
      right_inv := fun w => Subtype.ext (φ.apply_symm_apply w.1) }
    fun a b => by
      simp only [slopeSetoid_rel_iff, Equiv.coe_fn_mk]
      constructor
      · rintro (h | h)
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h, map_neg])
      · rintro (h | h)
        · exact Or.inl (φ.injective h)
        · exact Or.inr (φ.injective (by rw [map_neg]; exact h))

@[simp]
theorem congr_mk (φ : M ≃ₗ[ℤ] N) (v : M) (h : IsPrimitive v) :
    congr φ (mk v h) = mk (φ v) ((isPrimitive_congr φ).mpr h) :=
  (rfl)

/-- Transporting slopes along `φ` and along `φ.symm` are inverse to one another. -/
@[simp]
theorem congr_symm (φ : M ≃ₗ[ℤ] N) : (congr φ).symm = congr φ.symm := by
  ext s
  induction s using Slope.induction_on with
  | h w hw =>
    rw [Equiv.symm_apply_eq, congr_mk, congr_mk]
    exact mk_eq_mk _ _ (Or.inl (φ.apply_symm_apply w).symm)

end Slope

/-! ### The standard lattice `ℤ × ℤ`

For the standard lattice `ℤ × ℤ`, primitivity is coprimality of the coordinates, and the reduced
fraction `p / q` supplies the `ℚ ∪ {∞}` parametrisation. Every framing produces its own copy of this
bijection through its coordinate isomorphism. -/

/-- Over `ℤ × ℤ`, a class is primitive exactly when its two coordinates are coprime. -/
theorem isPrimitive_prod_iff {v : ℤ × ℤ} : IsPrimitive v ↔ IsCoprime v.1 v.2 := by
  constructor
  · rintro ⟨f, hf⟩
    have hv : v = v.1 • ((1 : ℤ), (0 : ℤ)) + v.2 • ((0 : ℤ), (1 : ℤ)) := by
      simp
    rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hf
    exact ⟨f (1, 0), f (0, 1), by rw [mul_comm (f (1, 0)), mul_comm (f (0, 1))]; exact hf⟩
  · rintro ⟨a, b, hab⟩
    refine ⟨a • LinearMap.fst ℤ ℤ ℤ + b • LinearMap.snd ℤ ℤ ℤ, ?_⟩
    simpa [smul_eq_mul] using hab

/-- The first standard basis vector of `ℤ × ℤ` is primitive. -/
theorem isPrimitive_prod_one_zero : IsPrimitive ((1, 0) : ℤ × ℤ) :=
  isPrimitive_prod_iff.mpr isCoprime_one_left

/-- The second standard basis vector of `ℤ × ℤ` is primitive. -/
theorem isPrimitive_prod_zero_one : IsPrimitive ((0, 1) : ℤ × ℤ) :=
  isPrimitive_prod_iff.mpr isCoprime_one_right

/-- The reduced form `(r.num, r.den)` of a rational is a primitive class. -/
theorem isPrimitive_num_den (r : ℚ) : IsPrimitive ((r.num, (r.den : ℤ)) : ℤ × ℤ) := by
  rw [isPrimitive_prod_iff, Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
  exact r.reduced

/-- A primitive class of `ℤ × ℤ` with vanishing second coordinate has first coordinate `±1`. -/
theorem isPrimitive_prod_fst_eq_one_or_neg_one_of_snd_eq_zero {v : ℤ × ℤ} (h : IsPrimitive v)
    (hq : v.2 = 0) : v.1 = 1 ∨ v.1 = -1 := by
  rw [isPrimitive_prod_iff, hq, isCoprime_zero_right, Int.isUnit_iff] at h
  exact h

/-- The value `p / q ∈ ℚ ∪ {∞}` of a class `v = (p, q)`, taken to be `∞` when `q = 0`. This is the
ratio of the meridian- and longitude-coordinates in a framing. -/
def slopeValue (v : ℤ × ℤ) : OnePoint ℚ :=
  if v.2 = 0 then ∞ else ((v.1 : ℚ) / (v.2 : ℚ) : ℚ)

@[simp]
theorem slopeValue_of_snd_eq_zero {v : ℤ × ℤ} (hq : v.2 = 0) : slopeValue v = ∞ := if_pos hq

@[simp]
theorem slopeValue_of_snd_ne_zero {v : ℤ × ℤ} (hq : v.2 ≠ 0) :
    slopeValue v = ((v.1 : ℚ) / (v.2 : ℚ) : ℚ) := if_neg hq

/-- The value of a class is unchanged by the sign action `v ↦ -v`. -/
theorem slopeValue_neg (v : ℤ × ℤ) : slopeValue (-v) = slopeValue v := by
  simp only [slopeValue, Prod.fst_neg, Prod.snd_neg, neg_eq_zero]
  split_ifs with h
  · rfl
  · congr 1
    push_cast
    rw [neg_div_neg_eq]

/-- The `ℚ ∪ {∞}` value of a standard-lattice slope, the ratio of its coordinates. -/
def Slope.value : Slope (ℤ × ℤ) → OnePoint ℚ :=
  Quotient.lift (fun v => slopeValue v.1) fun _ _ h => by
    rcases h with h | h
    · rw [h]
    · rw [h, slopeValue_neg]

@[simp]
theorem Slope.value_mk (v : ℤ × ℤ) (h : IsPrimitive v) :
    Slope.value (Slope.mk v h) = slopeValue v := (rfl)

/-- The primitive class attached to a value in `ℚ ∪ {∞}`: the class `(1, 0)` for `∞`, and the
reduced fraction `(r.num, r.den)` for a rational `r`. -/
def slopeOfValue : OnePoint ℚ → Slope (ℤ × ℤ)
  | ∞ => Slope.mk (1, 0) isPrimitive_prod_one_zero
  | (r : ℚ) => Slope.mk (r.num, (r.den : ℤ)) (isPrimitive_num_den r)

@[simp]
theorem slopeOfValue_infty : slopeOfValue ∞ = Slope.mk (1, 0) isPrimitive_prod_one_zero := (rfl)

@[simp]
theorem slopeOfValue_coe (r : ℚ) :
    slopeOfValue (r : OnePoint ℚ) = Slope.mk (r.num, (r.den : ℤ)) (isPrimitive_num_den r) := (rfl)

/-- Reading off the value of a standard-lattice slope and rebuilding a slope from it recovers the
original slope. -/
theorem slopeOfValue_value (s : Slope (ℤ × ℤ)) : slopeOfValue (Slope.value s) = s := by
  induction s using Slope.induction_on with
  | h v hv =>
    obtain ⟨p, q⟩ := v
    by_cases hq : q = 0
    · subst hq
      rw [Slope.value_mk, slopeValue_of_snd_eq_zero rfl, slopeOfValue_infty]
      rcases isPrimitive_prod_fst_eq_one_or_neg_one_of_snd_eq_zero hv rfl with hp | hp <;> subst hp
      · rfl
      · exact Slope.mk_eq_mk _ _ (Or.inr rfl)
    · rw [Slope.value_mk, slopeValue_of_snd_ne_zero hq, slopeOfValue_coe]
      have hcop : Nat.Coprime p.natAbs q.natAbs :=
        Int.isCoprime_iff_nat_coprime.mp (isPrimitive_prod_iff.mp hv)
      rcases lt_or_gt_of_ne hq with hqneg | hqpos
      · -- `q < 0`: the reduced form of `p / q` is `(-p, -q)`, agreeing with `(p, q)` up to sign.
        have hpos : (0 : ℤ) < -q := by omega
        have hcop' : Nat.Coprime (-p).natAbs (-q).natAbs := by
          rwa [Int.natAbs_neg, Int.natAbs_neg]
        have hval : ((p : ℚ) / (q : ℚ)) = ((-p : ℤ) : ℚ) / ((-q : ℤ) : ℚ) := by
          push_cast; rw [neg_div_neg_eq]
        rw [hval]
        refine Slope.mk_eq_mk _ _ (Or.inr ?_)
        rw [Rat.num_div_eq_of_coprime hpos hcop', Rat.den_div_eq_of_coprime hpos hcop']
        simp
      · -- `q > 0`: the reduced form of `p / q` is exactly `(p, q)`.
        refine Slope.mk_eq_mk _ _ (Or.inl ?_)
        rw [Rat.num_div_eq_of_coprime hqpos hcop, Rat.den_div_eq_of_coprime hqpos hcop]

/-- The standard-lattice slope built from a value in `ℚ ∪ {∞}` has that value again. -/
theorem value_slopeOfValue (x : OnePoint ℚ) : Slope.value (slopeOfValue x) = x := by
  induction x with
  | infty => rw [slopeOfValue_infty, Slope.value_mk, slopeValue_of_snd_eq_zero rfl]
  | coe r =>
    have hd : ((r.den : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr r.den_ne_zero
    rw [slopeOfValue_coe, Slope.value_mk, slopeValue_of_snd_ne_zero hd,
      Int.cast_natCast, Rat.num_div_den]

/-- **The standard slope parametrisation.** For the standard lattice `ℤ × ℤ`, primitive homology
classes modulo sign biject with `ℚ ∪ {∞}`: a reduced fraction `p / q` corresponds to the primitive
class `(p, q)`, with `∞` the class `(1, 0)`. A framing produces the corresponding bijection on
any boundary torus through its coordinate isomorphism (`TauCeti.FramedBoundaryTorus.slopeEquiv`). -/
def slopeEquivStd : Slope (ℤ × ℤ) ≃ OnePoint ℚ where
  toFun := Slope.value
  invFun := slopeOfValue
  left_inv := slopeOfValue_value
  right_inv := value_slopeOfValue

@[simp]
theorem slopeEquivStd_apply (s : Slope (ℤ × ℤ)) : slopeEquivStd s = Slope.value s := (rfl)

@[simp]
theorem slopeEquivStd_symm_apply (x : OnePoint ℚ) : slopeEquivStd.symm x = slopeOfValue x := (rfl)

/-! ### Boundary tori and framings

A framing supplies the coordinate isomorphism `H₁(T; ℤ) ≃ ℤ × ℤ` that turns the basis-free `Slope`
into the `ℚ ∪ {∞}` parametrisation. The homology object and the ordered meridian-longitude basis are
carried explicitly, keeping the basis-dependent notions (`meridian`, `longitude`, `value`,
`slopeEquiv`) genuinely parametrised by the framing rather than globally canonical. -/

/-- A **boundary torus** is a topological space that is homeomorphic to the standard two-torus; no
particular homeomorphism is chosen. Its first homology, rather than an unrelated abstract lattice,
is the carrier on which slopes are defined. -/
structure BoundaryTorus where
  /-- The underlying topological space. -/
  carrier : Type
  [topologicalSpace : TopologicalSpace carrier]
  /-- The assertion that the space is homeomorphic to the standard two-torus. Only the existence of
  such a homeomorphism is recorded, keeping this field a `Prop`, so it never obstructs equality:
  two boundary tori with the same carrier and the same topology are equal. -/
  parametrization : Nonempty (carrier ≃ₜ UnitAddTorus (Fin 2))

namespace BoundaryTorus

attribute [instance] BoundaryTorus.topologicalSpace

/-- The first singular homology of a boundary torus with integer coefficients. -/
abbrev firstHomology (T : BoundaryTorus) : Type :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of T.carrier)

end BoundaryTorus

/-- A **framed boundary torus**: a boundary torus together with an ordered
meridian-longitude basis `(μ, λ) = (basis 0, basis 1)` of its actual singular homology group.
The framing is exactly this ordered basis; it is what identifies `H₁(T; ℤ)` with `ℤ × ℤ` and so
what the `ℚ ∪ {∞}` parametrisation depends on. -/
structure FramedBoundaryTorus where
  /-- The boundary torus being framed. -/
  torus : BoundaryTorus
  /-- The ordered meridian-longitude basis `(μ, λ)` framing the torus. -/
  basis : Basis (Fin 2) ℤ torus.firstHomology

namespace FramedBoundaryTorus

/-- The first singular homology group of the underlying boundary torus. -/
abbrev H (T : FramedBoundaryTorus) := T.torus.firstHomology

variable (T : FramedBoundaryTorus)

/-- The coordinate isomorphism `H₁(T; ℤ) ≃ ℤ × ℤ` induced by the ordered basis `(μ, λ)`, sending a
class to its `(μ, λ)`-coordinates. This is the data that makes the parametrisation
basis-dependent. -/
noncomputable def coord : T.H ≃ₗ[ℤ] ℤ × ℤ :=
  T.basis.equivFun ≪≫ₗ LinearEquiv.finTwoArrow ℤ ℤ

@[simp]
theorem coord_basis_zero : T.coord (T.basis 0) = (1, 0) := by
  simp [coord, LinearEquiv.finTwoArrow_apply]

@[simp]
theorem coord_basis_one : T.coord (T.basis 1) = (0, 1) := by
  simp [coord, LinearEquiv.finTwoArrow_apply]

/-- The inverse coordinate isomorphism reads a pair of coordinates as the corresponding
combination `p · μ + q · λ` of the framing basis. -/
@[simp]
theorem coord_symm_apply (v : ℤ × ℤ) : T.coord.symm v = v.1 • T.basis 0 + v.2 • T.basis 1 := by
  -- the statement's `•` is the `AddCommGroup` `zsmul`, while the basis expansion produces the
  -- `Module ℤ` action of the homology object; the two agree by `Int.cast_smul_eq_zsmul`
  rw [← Int.cast_smul_eq_zsmul ℤ v.1 (T.basis 0), ← Int.cast_smul_eq_zsmul ℤ v.2 (T.basis 1)]
  simp [coord, Basis.equivFun_symm_apply, Fin.sum_univ_two]

theorem isPrimitive_basis_zero : IsPrimitive (T.basis 0) :=
  (isPrimitive_congr T.coord).mp (by rw [T.coord_basis_zero]; exact isPrimitive_prod_one_zero)

theorem isPrimitive_basis_one : IsPrimitive (T.basis 1) :=
  (isPrimitive_congr T.coord).mp (by rw [T.coord_basis_one]; exact isPrimitive_prod_zero_one)

/-- The meridian slope `μ = basis 0` of the framing. -/
noncomputable def meridian : Slope T.H := Slope.mk (T.basis 0) T.isPrimitive_basis_zero

/-- The longitude slope `λ = basis 1` of the framing. -/
noncomputable def longitude : Slope T.H := Slope.mk (T.basis 1) T.isPrimitive_basis_one

/-- The framing-dependent value `p / q ∈ ℚ ∪ {∞}` of a slope: the ratio of its `(μ, λ)`-coordinates.
Different framings give different values, which is why this is an operation of the framing rather
than of the basis-free `Slope`. -/
noncomputable def value (s : Slope T.H) : OnePoint ℚ :=
  Slope.value (Slope.congr T.coord s)

/-- **The framed slope parametrisation.** A framing makes primitive homology classes modulo sign
biject with `ℚ ∪ {∞}`, a reduced fraction `p / q` corresponding to the class with
`(μ, λ)`-coordinates `(p, q)` and `∞` to the meridian. -/
noncomputable def slopeEquiv : Slope T.H ≃ OnePoint ℚ :=
  (Slope.congr T.coord).trans slopeEquivStd

@[simp]
theorem slopeEquiv_apply (s : Slope T.H) : T.slopeEquiv s = T.value s := (rfl)

/-- The value of the slope of a primitive class is the ratio of its `(μ, λ)`-coordinates. -/
@[simp]
theorem value_mk (v : T.H) (hv : IsPrimitive v) :
    T.value (Slope.mk v hv) = slopeValue (T.coord v) := (rfl)

/-- **The framed parametrisation in the inverse direction.** The slope with value `x ∈ ℚ ∪ {∞}` is
the one whose `(μ, λ)`-coordinates are the standard reduced pair `slopeOfValue x`; for a rational
`p / q` in lowest terms that is the class `p · μ + q · λ`, by
`TauCeti.FramedBoundaryTorus.coord_symm_apply`. -/
@[simp]
theorem slopeEquiv_symm_apply (x : OnePoint ℚ) :
    T.slopeEquiv.symm x = Slope.congr T.coord.symm (slopeOfValue x) := by
  simp [slopeEquiv]

/-- The framed meridian has slope value `∞`. -/
@[simp]
theorem value_meridian : T.value T.meridian = ∞ := by
  unfold value meridian
  rw [Slope.congr_mk, Slope.value_mk, T.coord_basis_zero]
  exact slopeValue_of_snd_eq_zero rfl

/-- The framed longitude has slope value `0`. -/
@[simp]
theorem value_longitude : T.value T.longitude = (0 : ℚ) := by
  unfold value longitude
  rw [Slope.congr_mk, Slope.value_mk, T.coord_basis_one, slopeValue_of_snd_ne_zero one_ne_zero]
  norm_num

end FramedBoundaryTorus

end TauCeti
