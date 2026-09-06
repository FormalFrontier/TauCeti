/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupWithZero.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree

/-!
# The carrier of `Hom(W₁, W₂)`

An `Isogeny` is nonzero by construction: its pullback is injective, so there is no isogeny
representing the zero morphism. The zero morphism has no pullback of functions at all — it sends
every point to the target's point at infinity, which is not a point of the affine coordinate ring's
spectrum — so it cannot be added to the isogenies as another pullback.

This file carves the hom carrier out of a slightly larger mapping type instead, **adjoining
nothing**: the `F`-linear *multiplicative* maps `R(W₂) → K(W₁)`, which include the zero map because
multiplicativity does not force `1 ↦ 1`. Into a field there is nothing else new — `p 1` is
idempotent, so `MulHomClass.forall_apply_eq_zero_or_map_one` splits the type as the zero
map together with
the unital maps, and a unital map with the pointedness condition is exactly an `Isogeny`. So the
carrier is `{0} ⊔ Isogeny W₁ W₂` as a *set*, obtained by weakening unitality rather than by a
`WithZero` adjunction.

The zero element is a formal tag: the pullback identity a nonzero morphism satisfies is vacuous
at zero, every point landing at infinity. Composition is therefore *defined* by cases, with the
zero map absorbing, rather than derived from a pullback identity that does not hold there.

Addition is not defined here, so `Hom W W` is a monoid with zero rather than a ring. A sum of
multiplicative maps is not multiplicative, so the carrier is not an additive subgroup of the
linear maps; an additive structure on it has to be built from the elliptic-curve group law, which
needs the rational addition formulas rather than anything in this file.

## Main definitions

* `NonUnitalAlgHom.MapsInfinityOfMapOne`: the condition carving the carrier out — a map that is
  unital is pointed. It is vacuous at the zero map, which is how that map enters.
* `TauCeti.Isogeny.Hom`: the carrier of `Hom(W₁, W₂)`, with `0` its zero map and
  `TauCeti.Isogeny.Hom.ofIsogeny` its nonzero elements.
* `TauCeti.Isogeny.Hom.degree`: the degree, extended by the stipulation `degree 0 = 0`.
* `TauCeti.Isogeny.Hom.comp` and `TauCeti.Isogeny.Hom.id`: composition and the identity, making
  `Hom W W` a `MonoidWithZero`.

## Main results

* `TauCeti.Isogeny.Hom.eq_zero_or_exists_ofIsogeny`: every element is the zero map or comes from
  an isogeny.
* `TauCeti.Isogeny.Hom.degree_eq_zero_iff`: the degree vanishes exactly at the zero map.
* `TauCeti.Isogeny.Hom.degree_comp`: `deg (g ∘ f) = deg g · deg f` on the whole carrier, the zero
  map included — which is what the value `degree 0 = 0` is chosen for.
* `TauCeti.Isogeny.Hom.comp_eq_zero_iff`: a composite vanishes exactly when a factor does, so the
  endomorphism monoid has no zero divisors.
* `TauCeti.Isogeny.Hom.instNontrivial`: the carrier has more than one element, which is what
  lets Mathlib's theory of nontrivial monoids with zero apply to it.

## Implementation notes

`degree 0 = 0` is a stipulation, not a theorem: the zero map's image generates no field, so there
is no extension whose dimension could be measured. `0` is the value that makes `degree` vanish
exactly at the zero map, which is what `degree_eq_zero_iff` records.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.6.
-/

-- Design source, for whoever maintains this: the three decisions that shape the carrier — no
-- `WithZero` adjunction, the zero map as the unique non-unital element, `degree 0 = 0`
-- stipulated — are specified in `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, "The
-- hom-group and the degree form". This is provenance for the implementer, not part of the
-- interface, so it sits here rather than in the module docstring.

public section

namespace TauCeti.Isogeny

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- The condition carving the hom carrier out of the non-unital pullbacks: if the map is unital,
it is pointed. At the zero map the hypothesis is unsatisfiable, so the condition is vacuous
there — which is what lets the zero map into the carrier without a pointedness claim about it. -/
def _root_.NonUnitalAlgHom.MapsInfinityOfMapOne
    (p : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField) : Prop :=
  ∀ h : p 1 = 1,
    CoordinatePullback.MapsInfinity (AlgHom.ofLinearMap ⟨⟨p, map_add p⟩, map_smul p⟩ h (map_mul p))

/-- The condition unfolded, so a consumer can introduce and eliminate it without the definition's
body: `MapsInfinityOfMapOne p` is exactly the implication it is defined to be. -/
@[simp]
theorem _root_.NonUnitalAlgHom.mapsInfinityOfMapOne_iff
    {p : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField} :
    p.MapsInfinityOfMapOne ↔ ∀ h : p 1 = 1,
      CoordinatePullback.MapsInfinity
        (AlgHom.ofLinearMap ⟨⟨p, map_add p⟩, map_smul p⟩ h (map_mul p)) :=
  (Iff.rfl)

/-- **The carrier of `Hom(W₁, W₂)`**: an `F`-linear multiplicative map out of the target
coordinate ring, pointed wherever it is unital. Its zero map is the zero morphism's formal
representative and its unital elements are the isogenies. -/
@[ext]
structure Hom (W₁ W₂ : WeierstrassCurve.Affine F) where
  /-- The underlying multiplicative map. Not an `AlgHom`: unitality is what the zero map fails. -/
  toNonUnitalAlgHom : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField
  /-- Pointedness, required only of the unital maps. -/
  mapsInfinity_of_map_one : toNonUnitalAlgHom.MapsInfinityOfMapOne

namespace Hom

noncomputable instance : Zero (Hom W₁ W₂) where
  -- The condition is an implication out of `(0 : _ →ₙₐ[F] _) 1 = 1`, which fails in a field, so
  -- it is vacuous at the zero map — which is exactly how that map enters the carrier.
  zero := ⟨0, by simp [NonUnitalAlgHom.MapsInfinityOfMapOne]⟩

@[simp]
theorem toNonUnitalAlgHom_zero : (0 : Hom W₁ W₂).toNonUnitalAlgHom = 0 := (rfl)

/-- An isogeny, as an element of the carrier. -/
noncomputable def ofIsogeny (φ : Isogeny W₁ W₂) : Hom W₁ W₂ where
  toNonUnitalAlgHom := (φ.pullback : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField)
  mapsInfinity_of_map_one _ := φ.mapsInfinity

@[simp]
theorem ofIsogeny_apply (φ : Isogeny W₁ W₂) (x : W₂.CoordinateRing) :
    (ofIsogeny φ).toNonUnitalAlgHom x = φ.pullback x :=
  (rfl)

/-- The underlying map of an embedded isogeny is its pullback. -/
theorem toNonUnitalAlgHom_ofIsogeny (φ : Isogeny W₁ W₂) :
    (ofIsogeny φ).toNonUnitalAlgHom = (φ.pullback : W₂.CoordinateRing →ₙₐ[F] W₁.FunctionField) :=
  (rfl)

/-- **The isogenies sit in the carrier as distinct elements.** -/
theorem ofIsogeny_injective : Function.Injective (ofIsogeny (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h => Isogeny.ext (AlgHom.ext fun x => congrArg (fun g => g.toNonUnitalAlgHom x) h)

/-- **No isogeny is the zero map**, since a pullback sends `1` to `1`. -/
@[simp]
theorem ofIsogeny_ne_zero (φ : Isogeny W₁ W₂) : ofIsogeny φ ≠ 0 := fun h => by
  refine one_ne_zero (α := W₁.FunctionField) ?_
  calc (1 : W₁.FunctionField)
      = φ.pullback 1 := (map_one _).symm
    _ = (ofIsogeny φ).toNonUnitalAlgHom 1 := (ofIsogeny_apply φ 1).symm
    _ = (0 : Hom W₁ W₂).toNonUnitalAlgHom 1 := by rw [h]
    _ = 0 := by rw [toNonUnitalAlgHom_zero, NonUnitalAlgHom.zero_apply]

/-- The isogeny a nonzero element of the carrier comes from: it is unital, so its underlying
map promotes to a pullback, and pointedness is the carrier's own condition. -/
noncomputable def toIsogeny {h : Hom W₁ W₂} (hz : h ≠ 0) : Isogeny W₁ W₂ :=
  ⟨_, h.mapsInfinity_of_map_one
    (MulHomClass.map_one_of_exists_apply_ne_zero (by
      by_contra hall
      rw [not_exists] at hall
      refine hz (Hom.ext (NonUnitalAlgHom.ext fun x => ?_))
      rw [not_not.mp (hall x), toNonUnitalAlgHom_zero, NonUnitalAlgHom.zero_apply]))⟩

/-- The pullback of the isogeny read off a nonzero element is that element's own map. -/
-- The one place the two bundlings are identified; the lemmas below rewrite through it.
@[simp]
theorem toIsogeny_pullback_apply {h : Hom W₁ W₂} (hz : h ≠ 0) (x : W₂.CoordinateRing) :
    (toIsogeny hz).pullback x = h.toNonUnitalAlgHom x :=
  (rfl)

/-- **`toIsogeny` is a section of `ofIsogeny`**: a nonzero element read as an isogeny and put
back is unchanged. -/
@[simp]
theorem ofIsogeny_toIsogeny {h : Hom W₁ W₂} (hz : h ≠ 0) : ofIsogeny (toIsogeny hz) = h :=
  Hom.ext (NonUnitalAlgHom.ext fun x =>
    (ofIsogeny_apply _ x).trans (toIsogeny_pullback_apply hz x))

/-- **`toIsogeny` is a retraction of `ofIsogeny`**: an embedded isogeny read back is unchanged. -/
@[simp]
theorem toIsogeny_ofIsogeny (φ : Isogeny W₁ W₂) :
    toIsogeny (ofIsogeny_ne_zero φ) = φ :=
  ofIsogeny_injective (ofIsogeny_toIsogeny _)

/-- **Every element of the carrier is the zero map or an isogeny.** This is the dichotomy the
carrier is built for: weakening unitality admits the zero map and nothing else. -/
theorem eq_zero_or_exists_ofIsogeny (h : Hom W₁ W₂) :
    h = 0 ∨ ∃ φ : Isogeny W₁ W₂, h = ofIsogeny φ := by
  by_cases hz : h = 0
  · exact Or.inl hz
  · exact Or.inr ⟨toIsogeny hz, (ofIsogeny_toIsogeny hz).symm⟩

/-- **The degree**, extended to the carrier by stipulating `degree 0 = 0`: the zero map's image
generates no field, so there is no extension for a dimension to measure. -/
noncomputable def degree (h : Hom W₁ W₂) : ℕ := by
  classical exact if hz : h = 0 then 0 else (toIsogeny hz).degree

@[simp]
theorem degree_zero : (0 : Hom W₁ W₂).degree = 0 := by
  classical simp [degree]

@[simp]
theorem degree_ofIsogeny (φ : Isogeny W₁ W₂) : (ofIsogeny φ).degree = φ.degree := by
  classical
  rw [degree]
  split
  · exact absurd ‹ofIsogeny φ = 0› (ofIsogeny_ne_zero φ)
  · rw [ofIsogeny_injective (ofIsogeny_toIsogeny _)]

/-- **The degree vanishes exactly at the zero map**: every isogeny has positive degree, so the
stipulated value at zero is the only one. -/
@[simp]
theorem degree_eq_zero_iff (h : Hom W₁ W₂) : h.degree = 0 ↔ h = 0 := by
  refine ⟨fun hd => ?_, fun hz => hz ▸ degree_zero⟩
  rcases h.eq_zero_or_exists_ofIsogeny with hz | ⟨φ, hφ⟩
  · exact hz
  · rw [hφ, degree_ofIsogeny] at hd
    exact absurd hd φ.degree_ne_zero

/-- **Composition on the carrier.** At a zero argument the composite is the zero map: the zero
morphism composed either way is the zero morphism, and it has no pullback of functions to
compose with the other side's, so the value there is stipulated rather than derived. -/
noncomputable def comp (g : Hom W₂ W₃) (f : Hom W₁ W₂) : Hom W₁ W₃ := by
  classical
  exact if hg : g = 0 then 0 else if hf : f = 0 then 0 else
    ofIsogeny ((toIsogeny hg).comp (toIsogeny hf))

/-- **The zero map absorbs on the left.** -/
@[simp]
theorem zero_comp (f : Hom W₁ W₂) : (0 : Hom W₂ W₃).comp f = 0 := by
  classical
  rw [comp]
  split
  · rfl
  · exact absurd rfl ‹(0 : Hom W₂ W₃) ≠ 0›

/-- **The zero map absorbs on the right.** -/
@[simp]
theorem comp_zero (g : Hom W₂ W₃) : g.comp (0 : Hom W₁ W₂) = 0 := by
  classical
  rw [comp]
  split
  · rfl
  · split
    · rfl
    · exact absurd rfl ‹(0 : Hom W₁ W₂) ≠ 0›

/-- **The embedding carries `Isogeny.comp` to carrier composition.** -/
@[simp]
theorem ofIsogeny_comp_ofIsogeny (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ofIsogeny ψ).comp (ofIsogeny φ) = ofIsogeny (ψ.comp φ) := by
  classical
  rw [comp]
  split
  · exact absurd ‹ofIsogeny ψ = 0› (ofIsogeny_ne_zero ψ)
  · split
    · exact absurd ‹ofIsogeny φ = 0› (ofIsogeny_ne_zero φ)
    · rw [toIsogeny_ofIsogeny, toIsogeny_ofIsogeny]

/-- **A composite vanishes exactly when one of its factors does.** -/
@[simp]
theorem comp_eq_zero_iff {g : Hom W₂ W₃} {f : Hom W₁ W₂} :
    g.comp f = 0 ↔ g = 0 ∨ f = 0 := by
  refine ⟨fun hc => ?_, fun h => h.elim (fun hg => hg ▸ zero_comp f) fun hf => hf ▸ comp_zero g⟩
  by_contra hn
  rw [not_or] at hn
  obtain ⟨hg, hf⟩ := hn
  obtain ⟨ψ, rfl⟩ := g.eq_zero_or_exists_ofIsogeny.resolve_left hg
  obtain ⟨φ, rfl⟩ := f.eq_zero_or_exists_ofIsogeny.resolve_left hf
  rw [ofIsogeny_comp_ofIsogeny] at hc
  exact ofIsogeny_ne_zero _ hc

/-- **`deg (g ∘ f) = deg g · deg f`, on the whole carrier.** The tower formula holds at the zero
map too, and that is what the stipulation `degree 0 = 0` buys: both sides are `0` there. -/
@[simp]
theorem degree_comp (g : Hom W₂ W₃) (f : Hom W₁ W₂) :
    (g.comp f).degree = g.degree * f.degree := by
  rcases g.eq_zero_or_exists_ofIsogeny with rfl | ⟨ψ, rfl⟩
  · rw [zero_comp, degree_zero, degree_zero, zero_mul]
  · rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
    · rw [comp_zero, degree_zero, degree_zero, mul_zero]
    · rw [ofIsogeny_comp_ofIsogeny, degree_ofIsogeny, degree_ofIsogeny, degree_ofIsogeny,
        Isogeny.degree_comp]

/-- **Carrier composition is associative**, the zero map included. -/
@[simp]
theorem comp_assoc {W₄ : WeierstrassCurve.Affine F} (h : Hom W₃ W₄) (g : Hom W₂ W₃)
    (f : Hom W₁ W₂) : (h.comp g).comp f = h.comp (g.comp f) := by
  rcases h.eq_zero_or_exists_ofIsogeny with rfl | ⟨χ, rfl⟩
  · simp
  · rcases g.eq_zero_or_exists_ofIsogeny with rfl | ⟨ψ, rfl⟩
    · simp
    · rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
      · simp
      · simp [Isogeny.comp_assoc]

/-- The identity, as an element of the carrier. -/
noncomputable def id (W : WeierstrassCurve.Affine F) : Hom W W :=
  ofIsogeny (Isogeny.id W)

/-- The defining equation of `id`. -/
-- Needed as a lemma rather than left to unfolding: `id`'s body is not exposed across a module
-- boundary, so `rw [id]` in a downstream file fails with "Invalid rewrite argument".
theorem id_def (W : WeierstrassCurve.Affine F) :
    id W = ofIsogeny (Isogeny.id W) := (rfl)

/-- **The identity is a left unit for composition.** -/
@[simp]
theorem id_comp (f : Hom W₁ W₂) : (id W₂).comp f = f := by
  rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
  · rw [comp_zero]
  · rw [id, ofIsogeny_comp_ofIsogeny, Isogeny.id_comp]

/-- **The identity is a right unit for composition.** -/
@[simp]
theorem comp_id (f : Hom W₁ W₂) : f.comp (id W₁) = f := by
  rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
  · rw [zero_comp]
  · rw [id, ofIsogeny_comp_ofIsogeny, Isogeny.comp_id]

/-- **The identity has degree one**, its pullback being onto. -/
@[simp]
theorem degree_id (W : WeierstrassCurve.Affine F) : (id W).degree = 1 := by
  rw [id, degree_ofIsogeny, Isogeny.degree_id]

/-- **The endomorphisms of `W` form a monoid with zero** under composition: the identity is its
unit and the zero map is absorbing. The additive structure that would make it a ring is not
built here. -/
noncomputable instance : MonoidWithZero (Hom W₁ W₁) where
  mul g f := g.comp f
  one := id W₁
  mul_assoc h g f := comp_assoc h g f
  one_mul := id_comp
  mul_one := comp_id
  zero_mul := zero_comp
  mul_zero := comp_zero

/-- **The endomorphism monoid has no zero divisors**: a composite of nonzero endomorphisms is
nonzero, since a composite of isogenies is an isogeny. -/
instance : NoZeroDivisors (Hom W₁ W₁) where
  eq_zero_or_eq_zero_of_mul_eq_zero := comp_eq_zero_iff.mp

/-- The monoid's multiplication is composition. -/
@[simp]
theorem mul_def (g f : Hom W₁ W₁) : g * f = g.comp f := (rfl)

/-- The monoid's unit is the identity endomorphism. -/
@[simp]
theorem one_def : (1 : Hom W₁ W₁) = id W₁ := (rfl)

/-- **The carrier has more than one element**: the zero map has degree `0` and the identity
degree `1`. Supplying this makes Mathlib's generic theory of nontrivial monoids with zero apply,
`not_isUnit_zero` among it. -/
instance : Nontrivial (Hom W₁ W₁) :=
  ⟨⟨0, id W₁, fun h => zero_ne_one (α := ℕ) (by rw [← degree_zero (W₁ := W₁) (W₂ := W₁), h,
    degree_id])⟩⟩

end Hom

end TauCeti.Isogeny

end
