/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
public import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Pointedness at the place at infinity, and the factorisation of an isogeny

`TauCeti.Isogeny.isEquiv_comap_infinityPlace` reads the integrality condition `MapsInfinity` of an
isogeny off as a statement about places: the place at infinity of the source restricts to the
place at infinity of the target. This file proves the converse, and puts it to work.

The converse is what packages a bare embedding of function fields as an isogeny. Let
`σ : F(W₂) → F(W₁)` be an `F`-algebra map for which `σ x₂` has a pole at the place at infinity of
`W₁`. Then the coordinate `x₁` is integral over the pulled-back coordinate ring: if it were not,
Mathlib's `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn` would produce a valuation
subring `V` of `F(W₁)` containing every integral element but not `x₁`, and a proper valuation
subring of an algebraic function field containing the constants is the valuation ring of a place
(`TauCeti.Place.ofValuationSubring`). At that place `x₁` has a pole, so it is the place at
infinity — where `σ x₂` also has a pole, contradicting `σ x₂ ∈ V`. Every element of `F[W₁]` is
integral over `F[X]`, and `x₁` is integral over the pulled-back ring, so `MapsInfinity` follows.

That criterion discharges the pointedness of a factor. If two isogenies `φ : W₁ → W₂` and
`ψ : W₁ → W₃` satisfy `ψ^*F(W₃) ⊆ φ^*F(W₂)` as subfields of `F(W₁)`, then inverting `φ^*` on its
image gives an embedding `σ : F(W₃) → F(W₂)` with `φ^* ∘ σ = ψ^*`. Restricting the place at
infinity of `W₁` along `φ^*` and `ψ^*` gives the places at infinity of `W₂` and `W₃`, so
restricting along `σ` carries the one to the other; the criterion then makes `σ` an isogeny
`λ : W₂ → W₃`, and `λ ∘ φ = ψ`. Uniqueness is `TauCeti.Isogeny.comp_right_injective`, and the
degree formula `deg ψ = deg λ · deg φ` is the tower formula `TauCeti.Isogeny.degree_comp`.

The criterion is stated on subfields, not on kernels: over `ℚ` a curve with no rational
`2`-torsion has `ker [2](ℚ) = ker (id)(ℚ) = {O}` while `id` does not factor through `[2]`, and
relative Frobenius has trivial geometric point kernel while `id` does not factor through it. Both
are correctly excluded here, the subfield containment failing in each case.

## Main results

* `TauCeti.CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace`: **the pointedness
  criterion**, `MapsInfinity σ ↔ σ_*(O₁) = O₂`, for an embedding `σ` of function fields.
* `TauCeti.Isogeny.existsUnique_comp_eq_iff_fieldRange_le`: **the factorisation theorem**, that
  `ψ` factors through `φ` by a unique isogeny exactly when `ψ^*F(W₃) ⊆ φ^*F(W₂)`.
* `TauCeti.Isogeny.exists_comp_eq_id_of_degree_eq_one`: **a degree-one isogeny is an
  isomorphism**, the first consequence of the factorisation theorem.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, "The factorisation theorem — made a
milestone in its own right, because it is what the dual is built from": for isogenies
`φ : W₁ → W₂` and `ψ : W₁ → W₃`, `ψ` factors as `ψ = λ ∘ φ` for a unique isogeny `λ` iff
`ψ^*K(W₃) ⊆ φ^*K(W₂)` as subfields of `K(W₁)`, with `deg ψ = deg φ · deg λ`. The same layer's
dual-isogeny bullet asks for the route taken here — "an **unpointed induced-place map** for
finite function-field embeddings, with the named criterion `MapsInfinity λ ↔ λ_*(O₂) = O₃`
(equivalently its valuation/integral-closure form), and functoriality of induced places along
`λ ∘ φ = ψ`".

## Provenance

Not ported. Silverman's III.4.11 is stated for separable isogenies and proved by Galois theory of
the function-field extension; the subfield criterion here subsumes it and needs no separability,
and the pointedness of the factor — which the classical account does not have to address, its
morphisms being maps of projective curves — is discharged by the place criterion above.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.4, III.4.11.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.1.13.
-/

public section

open Polynomial WeierstrassCurve.Affine

namespace TauCeti

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

namespace CoordinatePullback

/-- **An embedding of function fields under which `x` acquires a pole at infinity maps infinity
to infinity.**

The proof is the valuation-theoretic form of "the poles of `σ x₂` are where `σ` sends the point
at infinity". If `x₁` were not integral over the pulled-back coordinate ring, some valuation
subring of `F(W₁)` would contain that ring but not `x₁`; being proper and containing the
constants, it is the valuation ring of a place, and `x₁` has a pole there, so that place is the
one at infinity. But `σ x₂` lies in the ring, so it has no pole there — against the hypothesis.
Integrality of `F[W₁]` over `F[X]` then upgrades `x₁` to the whole coordinate ring. -/
theorem mapsInfinity_of_one_lt_infinityPlace (σ : W₂.FunctionField →ₐ[F] W₁.FunctionField)
    (h : 1 < infinityPlace W₁ (σ (algebraMap F[X] W₂.FunctionField X))) :
    MapsInfinity (σ.comp (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField)) := by
  rw [mapsInfinity_iff]
  let _ := (σ.comp
    (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField)).toRingHom.toAlgebra
  have hcoord : ∀ c : W₂.CoordinateRing,
      algebraMap W₂.CoordinateRing W₁.FunctionField c = σ (algebraMap _ _ c) := fun _ ↦ rfl
  set C := integralClosure W₂.CoordinateRing W₁.FunctionField
  -- The affine coordinate of `W₁` is integral over the pulled-back coordinate ring.
  have hx₁ : algebraMap F[X] W₁.FunctionField X ∈ C := by
    by_contra hmem
    obtain ⟨V, hCV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := C.toSubring) (x := algebraMap F[X] W₁.FunctionField X) hmem
    have hmemV : ∀ c : W₂.CoordinateRing,
        algebraMap W₂.CoordinateRing W₁.FunctionField c ∈ V :=
      fun c ↦ hCV (Subalgebra.algebraMap_mem C c)
    have hFV : ∀ c : F, algebraMap F W₁.FunctionField c ∈ V := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply F W₂.CoordinateRing W₁.FunctionField]
      exact hmemV _
    have hVne : V ≠ ⊤ := fun hV ↦ hxV (hV ▸ trivial)
    set P := Place.ofValuationSubring W₁.isFunctionField hFV hVne
    have hPint : P.integers = V := Place.integers_ofValuationSubring _ hFV hVne
    have hpole : 1 < P.valuation (algebraMap F[X] W₁.FunctionField X) :=
      not_le.1 fun hle ↦ hxV (hPint ▸ P.mem_integers_iff.2 hle)
    -- A place at which `x₁` has a pole is the place at infinity.
    have hequiv := isEquiv_infinityPlace_of_one_lt (W := W₁) (v := P.valuation) hpole
    have hσx : σ (algebraMap F[X] W₂.FunctionField X) =
        algebraMap W₂.CoordinateRing W₁.FunctionField (algebraMap F[X] W₂.CoordinateRing X) := by
      rw [hcoord, ← IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField]
    refine absurd ((Valuation.isEquiv_iff_val_le_one.1 hequiv).1 ?_) (not_le.2 h)
    rw [hσx]
    exact P.mem_integers_iff.1 (hPint ▸ hmemV _)
  -- Every polynomial in that coordinate is then integral, so `F[X]` acts on the integral closure.
  have hmemq : ∀ q : F[X], algebraMap F[X] W₁.FunctionField q ∈ C := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply F F[X] W₁.FunctionField,
        IsScalarTower.algebraMap_apply F W₂.CoordinateRing W₁.FunctionField]
      exact Subalgebra.algebraMap_mem C _
    | add p q hp hq => simpa using C.add_mem hp hq
    | monomial n a hn =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact C.mul_mem hn hx₁
  let _ := ((algebraMap F[X] W₁.FunctionField).codRestrict C hmemq).toAlgebra
  have : IsScalarTower F[X] C W₁.FunctionField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- The coordinate ring of `W₁` is integral over `F[X]`, hence over the integral closure.
  intro z
  refine isIntegral_trans (A := C) _ (IsIntegral.tower_top (R := F[X]) ?_)
  exact (Algebra.IsIntegral.isIntegral (R := F[X]) z).map
    (IsScalarTower.toAlgHom F[X] W₁.CoordinateRing W₁.FunctionField)

/-- **The pointedness criterion.** An embedding `σ : F(W₂) → F(W₁)` of function fields restricts
to a coordinate pullback which maps infinity to infinity exactly when restricting the place at
infinity of `W₁` along `σ` gives the place at infinity of `W₂` — that is, exactly when
`σ_*(O₁) = O₂`.

The forward direction is `TauCeti.Isogeny.isEquiv_comap_infinityPlace`, applied to the isogeny
that `σ` then is; the converse is `mapsInfinity_of_one_lt_infinityPlace`, since `x₂` has a pole
at the place at infinity of `W₂`. -/
theorem mapsInfinity_iff_isEquiv_comap_infinityPlace
    (σ : W₂.FunctionField →ₐ[F] W₁.FunctionField) :
    MapsInfinity (σ.comp (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField)) ↔
      ((infinityPlace W₁).comap σ.toRingHom).IsEquiv (infinityPlace W₂) := by
  constructor
  · intro hσ
    have hfield : ({ pullback := _, mapsInfinity := hσ } :
        Isogeny W₁ W₂).fieldPullback = σ :=
      (Isogeny.fieldPullback_unique _ σ fun _ ↦ rfl).symm
    exact hfield ▸ Isogeny.isEquiv_comap_infinityPlace ⟨_, hσ⟩
  · intro hσ
    refine mapsInfinity_of_one_lt_infinityPlace σ (not_le.1 fun hle ↦ ?_)
    exact absurd ((Valuation.isEquiv_iff_val_le_one.1 hσ).1 hle)
      (not_le.2 (one_lt_infinityPlace_X W₂))

end CoordinatePullback

namespace Isogeny

/-- **The factorisation theorem** (Silverman, *The Arithmetic of Elliptic Curves*, III.4.11 in its
separable form): an isogeny `ψ : W₁ → W₃` factors through an isogeny `φ : W₁ → W₂`, by a unique
isogeny `λ : W₂ → W₃`, exactly when the function field `ψ` pulls back sits inside the one `φ`
pulls back.

The criterion is on subfields of `F(W₁)`, not on kernels of point maps, and that is what makes it
correct in general: over `ℚ`, a curve with no rational `2`-torsion has `ker [2](ℚ) = {O}` without
the identity factoring through `[2]`, and relative Frobenius has trivial *geometric* point kernel
without the identity factoring through it. In both cases the subfield containment fails, as it
should. -/
theorem existsUnique_comp_eq_iff_fieldRange_le (φ : Isogeny W₁ W₂) (ψ : Isogeny W₁ W₃) :
    (∃! χ : Isogeny W₂ W₃, χ.comp φ = ψ) ↔
      ψ.fieldPullback.fieldRange ≤ φ.fieldPullback.fieldRange := by
  constructor
  · rintro ⟨χ, rfl, -⟩
    rintro z ⟨w, rfl⟩
    exact ⟨χ.fieldPullback w, by simp⟩
  · intro hle
    -- Invert `φ^*` on its image to get `σ : F(W₃) → F(W₂)` with `φ^* ∘ σ = ψ^*`.
    set σ : W₃.FunctionField →ₐ[F] W₂.FunctionField :=
      (AlgEquiv.ofInjectiveField φ.fieldPullback).symm.toAlgHom.comp
        (ψ.fieldPullback.codRestrict φ.fieldPullback.fieldRange.toSubalgebra
          fun z ↦ hle ⟨z, rfl⟩)
    have hcomp : ∀ z, φ.fieldPullback (σ z) = ψ.fieldPullback z := fun z ↦ by
      have := (AlgEquiv.ofInjectiveField φ.fieldPullback).apply_symm_apply
        ⟨ψ.fieldPullback z, hle ⟨z, rfl⟩⟩
      exact congrArg Subtype.val this
    -- The place at infinity restricts along `σ` to the place at infinity, by functoriality.
    have hplace : ((infinityPlace W₂).comap σ.toRingHom).IsEquiv (infinityPlace W₃) := by
      refine Valuation.IsEquiv.trans (Valuation.IsEquiv.comap σ.toRingHom
        (Isogeny.isEquiv_comap_infinityPlace φ).symm) ?_
      have : ((infinityPlace W₁).comap φ.fieldPullback.toRingHom).comap σ.toRingHom
          = (infinityPlace W₁).comap ψ.fieldPullback.toRingHom := by
        ext z
        exact congrArg (infinityPlace W₁) (hcomp z)
      exact this ▸ Isogeny.isEquiv_comap_infinityPlace ψ
    -- The criterion packages `σ` as an isogeny, and it is a factor of `ψ` by construction.
    set χ : Isogeny W₂ W₃ :=
      ⟨σ.comp (IsScalarTower.toAlgHom F W₃.CoordinateRing W₃.FunctionField),
        (CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace σ).2 hplace⟩
    have hfactor : χ.comp φ = ψ := by
      refine Isogeny.ext (AlgHom.ext fun c ↦ ?_)
      rw [comp_pullback]
      exact (hcomp _).trans (fieldPullback_algebraMap ψ c)
    exact ⟨χ, hfactor, fun _ h ↦ comp_right_injective φ (h.trans hfactor.symm)⟩

/-- **An isogeny of degree one is an isomorphism** (Silverman, *The Arithmetic of Elliptic
Curves*, II.2.4.1): it has a two-sided inverse isogeny.

Degree one says the function-field pullback is onto, so every isogeny out of `W₁` — the identity
in particular — factors through `φ`. The factor of the identity is a right inverse, and it is a
left inverse because precomposition by `φ` is injective. -/
theorem exists_comp_eq_id_of_degree_eq_one (φ : Isogeny W₁ W₂) (hφ : φ.degree = 1) :
    ∃ χ : Isogeny W₂ W₁, χ.comp φ = id W₁ ∧ φ.comp χ = id W₂ := by
  have htop : φ.fieldPullback.fieldRange = ⊤ :=
    AlgHom.fieldRange_eq_top.2 ((degree_eq_one_iff φ).1 hφ)
  obtain ⟨χ, hχ, -⟩ :=
    (existsUnique_comp_eq_iff_fieldRange_le φ (id W₁)).2 (htop ▸ le_top)
  refine ⟨χ, hχ, comp_right_injective φ ?_⟩
  change (φ.comp χ).comp φ = (id W₂).comp φ
  rw [comp_assoc, hχ, comp_id, id_comp]

end Isogeny

end TauCeti

end
