/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank

/-!
# Function-field pullbacks of isogenies

This file proves that the coordinate pullback of an isogeny is injective and extends it uniquely
to the function fields. Both rest on one nonconstancy statement: the pulled-back target
coordinate is transcendental over the base field, since otherwise pointedness would make the
source coordinate algebraic as well, against its transcendence. Injectivity is then the
observation that a nonzero element of the kernel has a nonzero norm over the target's polynomial
subring, and that norm is a polynomial relation killing the pulled-back coordinate.

That extension is what lets isogenies be composed: a coordinate pullback lands in a *function*
field, so composing two of them needs the outer one extended across the inner one's fraction
field. `TauCeti.Isogeny.comp` therefore lives here rather than beside `TauCeti.Isogeny.id` in
`Isogeny/Basic.lean` — this is the first file where it can be stated.

## Main results

* `TauCeti.Isogeny.transcendental_pullback_X`: the pullback of the affine coordinate `x` is
  transcendental over the base field. This is the nonconstancy step, and the source of a
  transcendental element inside the pulled-back function field.
* `TauCeti.Isogeny.pullback_injective`: a coordinate pullback satisfying `MapsInfinity` is
  injective.
* `TauCeti.Isogeny.fieldPullback`: the induced embedding of function fields.
* `TauCeti.Isogeny.comp`: composition of isogenies, with `TauCeti.Isogeny.comp_fieldPullback`
  its function-field law and `TauCeti.Isogeny.id_comp`, `TauCeti.Isogeny.comp_id`,
  `TauCeti.Isogeny.comp_assoc` the unit and associativity laws. The pointedness obligation is
  discharged privately when `comp` is defined.

The degree of an isogeny — the dimension of `W₁.FunctionField` over the image of `fieldPullback`
— is `TauCeti.Isogeny.degree`, in `Isogeny/Degree.lean`; it is stated there rather than here
because the finiteness that makes it honest is proved from `transcendental_pullback_X` together
with the degree of the function field over the rational function field.

The construction is the coordinate-ring form of D. Angdinata's function-field definition of an
isogeny and follows the nonconstancy argument described in the elliptic-curves roadmap. The
composition definition follows the seed in `TauCetiRoadmap/EllipticCurves/Suggested.lean`,
discharging the `mapsInfinity` obligation the seed leaves open. The geometric interpretation is
Silverman, *The Arithmetic of Elliptic Curves*, II.2.4.
-/

public section

namespace TauCeti

open Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F]

namespace Isogeny

variable {W₁ W₂ : WeierstrassCurve.Affine F}

private theorem isIntegral_eval_of_isIntegral {K : Type*} [CommRing K] [Algebra F K]
    {x : K} (hx : IsIntegral F x) (p : F[X]) : IsIntegral F (aeval x p) := by
  rw [← mem_integralClosure_iff]
  exact adjoin_le_integralClosure hx (Polynomial.aeval_mem_adjoin_singleton F x)

-- Integrality descends along a ring hom with integral image. Kept here rather than exported,
-- since the pullback-integrality arguments in this file are its only consumers.
private theorem isIntegral_of_isIntegral_map {R A K : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R K] (f : A →+* K) (hf : ∀ a, IsIntegral R (f a)) {x : K}
    (hx : @IsIntegral A K _ _ f.toAlgebra x) : IsIntegral R x :=
  let _ := f.toAlgebra
  isIntegral_trans x (hx.map_of_comp_eq (f.codRestrict (integralClosure R K) hf) (RingHom.id K) rfl)

private theorem isIntegral_pullback_of_isIntegral_X (φ : Isogeny W₁ W₂)
    (hX : IsIntegral F (φ.pullback (algebraMap F[X] W₂.CoordinateRing X)))
    (a : W₂.CoordinateRing) : IsIntegral F (φ.pullback a) := by
  obtain ⟨P, hPmonic, hPa⟩ :=
    (Algebra.IsIntegral.isIntegral (R := F[X]) a : IsIntegral F[X] a)
  let e : F[X] →ₐ[F] W₁.FunctionField :=
    φ.pullback.comp (IsScalarTower.toAlgHom F F[X] W₂.CoordinateRing)
  have he_ring : e.toRingHom =
      φ.pullback.toRingHom.comp (algebraMap F[X] W₂.CoordinateRing) := by
    ext r
    · exact congr_arg φ.pullback
        (IsScalarTower.toAlgHom_apply F F[X] W₂.CoordinateRing (C r))
    · exact congr_arg φ.pullback
        (IsScalarTower.toAlgHom_apply F F[X] W₂.CoordinateRing X)
  have he : e = aeval (φ.pullback (algebraMap F[X] W₂.CoordinateRing X)) := by
    apply Polynomial.algHom_ext
    simp [e]
  apply isIntegral_of_isIntegral_map e.toRingHom (x := φ.pullback a)
  · intro p
    rw [he]
    exact isIntegral_eval_of_isIntegral hX p
  · refine ⟨P, hPmonic, ?_⟩
    rw [e.toRingHom.algebraMap_toAlgebra, he_ring]
    exact
      (Polynomial.hom_eval₂ P (algebraMap F[X] W₂.CoordinateRing)
        φ.pullback.toRingHom a).symm.trans (by rw [hPa, map_zero])

/-- **The pullback of the affine coordinate is transcendental.** If `φ^*x₂` were algebraic over
`F`, then every pullback would be integral over `F`, because the target coordinate ring is
integral over `F[x₂]`; pointedness would carry that to the source coordinate `x₁`, which is
transcendental.

This is the nonconstancy of an isogeny, in the form later files consume: it exhibits a
transcendental element of the pulled-back function field, which is what makes the extension it
sits under finite. -/
theorem transcendental_pullback_X (φ : Isogeny W₁ W₂) :
    Transcendental F (φ.pullback (algebraMap F[X] W₂.CoordinateRing X)) := by
  intro ht_algebraic
  have himage : ∀ a : W₂.CoordinateRing, IsIntegral F (φ.pullback a) :=
    isIntegral_pullback_of_isIntegral_X φ ht_algebraic.isIntegral
  let x₁ : W₁.FunctionField :=
    algebraMap W₁.CoordinateRing W₁.FunctionField
      (algebraMap F[X] W₁.CoordinateRing X)
  have hx₁_over_target :
      @IsIntegral W₂.CoordinateRing W₁.FunctionField _ _
        φ.pullback.toRingHom.toAlgebra x₁ :=
    (CoordinatePullback.mapsInfinity_iff φ.pullback).1 φ.mapsInfinity
      (algebraMap F[X] W₁.CoordinateRing X)
  have hx₁ : IsIntegral F x₁ :=
    isIntegral_of_isIntegral_map φ.pullback.toRingHom himage hx₁_over_target
  have hx₁_transcendental : Transcendental F x₁ := by
    have hx₁_eq : x₁ = algebraMap F[X] W₁.FunctionField X :=
      (IsScalarTower.algebraMap_apply F[X] W₁.CoordinateRing W₁.FunctionField X).symm
    rw [hx₁_eq]
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective F[X] W₁.FunctionField)).2
        (Polynomial.transcendental_X F)
  exact hx₁_transcendental hx₁.isAlgebraic

/-- The coordinate pullback of any isogeny of affine Weierstrass curves over a field is
injective. A nonzero element of the kernel has nonzero norm over `F[x₂]`, and that norm is a
polynomial relation killing `φ^*x₂` — which `transcendental_pullback_X` forbids. -/
theorem pullback_injective (φ : Isogeny W₁ W₂) : Function.Injective φ.pullback := by
  apply (injective_iff_map_eq_zero φ.pullback).2
  intro z hz
  by_contra hz₀
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq z
  let N : F[X] := Algebra.norm F[X] z
  have hN₀ : N ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis W₂)).2 hz₀
  let x₂ : W₂.CoordinateRing := algebraMap F[X] W₂.CoordinateRing X
  let t : W₁.FunctionField := φ.pullback x₂
  have hnorm : algebraMap F[X] W₂.CoordinateRing N =
      z * CoordinateRing.mk W₂
        (C p + C q * (-(Y : F[X][Y]) - C (C W₂.a₁ * X + C W₂.a₃))) := by
    dsimp only [N]
    rw [← hpq]
    simpa [N, CoordinateRing.smul] using CoordinateRing.coe_norm_smul_basis (W' := W₂) p q
  have hN : aeval t N = 0 := by
    have heval : aeval t N = φ.pullback (algebraMap F[X] W₂.CoordinateRing N) := by
      have hhom : aeval t =
          φ.pullback.comp (IsScalarTower.toAlgHom F F[X] W₂.CoordinateRing) := by
        apply Polynomial.algHom_ext
        simp [t, x₂]
      exact AlgHom.congr_fun hhom N
    rw [heval, hnorm, map_mul, hz, zero_mul]
  exact φ.transcendental_pullback_X ⟨N, hN₀, hN⟩

/-- The function-field pullback induced by an isogeny. It is the unique extension of the
coordinate pullback across the target fraction field. -/
noncomputable def fieldPullback (φ : Isogeny W₁ W₂) :
    W₂.FunctionField →ₐ[F] W₁.FunctionField :=
  IsFractionRing.liftAlgHom φ.pullback_injective

/-- The function-field pullback restricts to the original coordinate pullback. -/
@[simp]
theorem fieldPullback_algebraMap (φ : Isogeny W₁ W₂) (x : W₂.CoordinateRing) :
    φ.fieldPullback (algebraMap W₂.CoordinateRing W₂.FunctionField x) = φ.pullback x := by
  simp [fieldPullback, IsFractionRing.liftAlgHom_apply]

/-- A function-field algebra homomorphism agreeing with an isogeny's coordinate pullback is its
function-field pullback. -/
theorem fieldPullback_unique (φ : Isogeny W₁ W₂)
    (f : W₂.FunctionField →ₐ[F] W₁.FunctionField)
    (hf : ∀ x : W₂.CoordinateRing,
      f (algebraMap W₂.CoordinateRing W₂.FunctionField x) = φ.pullback x) :
    f = φ.fieldPullback := by
  exact AlgHom.coe_ringHom_injective <| IsFractionRing.ringHom_ext
    (A := W₂.CoordinateRing) (K := W₂.FunctionField) (L := W₁.FunctionField) fun x ↦ by
      exact (hf x).trans (fieldPullback_algebraMap φ x).symm

/-- The identity isogeny induces the identity pullback on the function field. -/
@[simp]
theorem id_fieldPullback (W : WeierstrassCurve.Affine F) :
    (id W).fieldPullback = AlgHom.id F W.FunctionField := by
  symm
  apply (id W).fieldPullback_unique
  intro x
  simp

variable {W₃ : WeierstrassCurve.Affine F}

/-- **Composition maps infinity to infinity**: the composite pullback of two isogenies again
satisfies `CoordinatePullback.MapsInfinity`. Private: it exists to fill `comp`'s `mapsInfinity`
field, and consumers read the same fact off `(ψ.comp φ).mapsInfinity`. -/
private theorem mapsInfinity_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    CoordinatePullback.MapsInfinity (φ.fieldPullback.comp ψ.pullback) := by
  rw [CoordinatePullback.mapsInfinity_iff]
  let _ := (φ.fieldPullback.comp ψ.pullback).toRingHom.toAlgebra
  let _ := ψ.pullback.toRingHom.toAlgebra
  -- split the tower: `x` is integral over `φ.pullback`'s copy of `W₂.CoordinateRing` by
  -- `φ.mapsInfinity`, leaving each value of `φ.pullback` integral over the composite's copy
  -- of `W₃.CoordinateRing`
  refine fun x ↦ isIntegral_of_isIntegral_map φ.pullback.toRingHom (fun a ↦ ?_)
    ((CoordinatePullback.mapsInfinity_iff φ.pullback).1 φ.mapsInfinity x)
  -- `ψ.mapsInfinity` carried across `φ.fieldPullback` — legitimate because the composite
  -- pullback *is* `φ.fieldPullback ∘ ψ.pullback`
  simpa using ((CoordinatePullback.mapsInfinity_iff ψ.pullback).1 ψ.mapsInfinity a).map_of_comp_eq
    (RingHom.id W₃.CoordinateRing) φ.fieldPullback.toRingHom rfl

/-- **Composition of isogenies**: pull back along `ψ` into `W₂.FunctionField`, then carry that
across to `W₁.FunctionField` by `φ.fieldPullback`. -/
noncomputable def comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) : Isogeny W₁ W₃ where
  pullback := φ.fieldPullback.comp ψ.pullback
  mapsInfinity := mapsInfinity_comp ψ φ

/-- The equation lemma for `comp`'s coordinate pullback: the definition's body is not exposed
across the module boundary, so this is how downstream modules compute with it. -/
@[simp]
theorem comp_pullback (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).pullback = φ.fieldPullback.comp ψ.pullback := (rfl)

/-- The function-field pullback of a composite is the composite of the function-field
pullbacks. -/
@[simp]
theorem comp_fieldPullback (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).fieldPullback = φ.fieldPullback.comp ψ.fieldPullback :=
  ((ψ.comp φ).fieldPullback_unique _ fun x ↦ by simp).symm

/-- The identity isogeny is a left unit for composition. -/
@[simp]
theorem id_comp (φ : Isogeny W₁ W₂) : (id W₂).comp φ = φ :=
  Isogeny.ext <| AlgHom.ext fun x ↦ by simp

/-- The identity isogeny is a right unit for composition. -/
@[simp]
theorem comp_id (φ : Isogeny W₁ W₂) : φ.comp (id W₁) = φ :=
  Isogeny.ext <| by simp

/-- Composition of isogenies is associative; the right-associated form is the simp-normal one,
as for `CategoryTheory.Category.assoc`. -/
@[simp]
theorem comp_assoc {W₄ : WeierstrassCurve.Affine F} (χ : Isogeny W₃ W₄) (ψ : Isogeny W₂ W₃)
    (φ : Isogeny W₁ W₂) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  Isogeny.ext <| AlgHom.ext fun x ↦ by simp

end Isogeny

end TauCeti
