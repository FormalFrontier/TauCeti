/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Function-field pullbacks of isogenies

This file proves that the coordinate pullback of an isogeny is injective and extends it uniquely
to the function fields. Injectivity is the algebraic form of nonconstancy: a nonzero element in the
kernel would make the pulled-back target coordinate algebraic over the base field. Pointedness
would then make the source coordinate algebraic as well, contradicting its transcendence.

## Main results

* `TauCeti.Isogeny.pullback_injective`: a coordinate pullback satisfying `MapsInfinity` is
  injective.
* `TauCeti.Isogeny.fieldPullback`: the induced embedding of function fields.

The construction is the coordinate-ring form of D. Angdinata's function-field definition of an
isogeny and follows the nonconstancy argument described in the elliptic-curves roadmap. The
geometric interpretation is Silverman, *The Arithmetic of Elliptic Curves*, II.2.4.
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
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n a =>
      rw [aeval_def, eval₂_monomial]
      exact (isIntegral_algebraMap (R := F) (A := K)).mul (hx.pow n)

/-- The coordinate pullback of an isogeny is injective.

If a nonzero coordinate-ring element vanished under the pullback, its nonzero norm over `F[X]`
would give an algebraic relation for the pulled-back target `X`-coordinate. Since the target
coordinate ring is integral over `F[X]`, every pulled-back target function would then be integral
over `F`. The `MapsInfinity` condition would make the source `X`-coordinate integral over `F`,
contradicting the injectivity of `F[X] → F(W₁)`. -/
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
  have ht_algebraic : IsAlgebraic F t := ⟨N, hN₀, hN⟩
  have ht : IsIntegral F t := ht_algebraic.isIntegral
  let _ : Module.Finite F[X] W₂.CoordinateRing :=
    Module.Finite.of_basis (CoordinateRing.basis W₂)
  have himage : ∀ a : W₂.CoordinateRing, IsIntegral F (φ.pullback a) := by
    intro a
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
    have he : e = aeval t := by
      apply Polynomial.algHom_ext
      simp [e, t, x₂]
    have hPdegree : P.natDegree ≠ 0 := by
      exact Nat.ne_of_gt <| natDegree_pos_of_aeval_root hPmonic.ne_zero hPa
        ((injective_iff_map_eq_zero _).1
          (FaithfulSMul.algebraMap_injective F[X] W₂.CoordinateRing))
    apply IsIntegral.of_aeval_monic_of_isIntegral_coeff
        (p := P.map e.toRingHom) (x := φ.pullback a)
    · exact hPmonic.map _
    · rw [hPmonic.natDegree_map]
      exact hPdegree
    · have hroot : (P.map e.toRingHom).eval (φ.pullback a) = 0 := by
        rw [eval_map, he_ring]
        exact
          (Polynomial.hom_eval₂ P (algebraMap F[X] W₂.CoordinateRing)
            φ.pullback.toRingHom a).symm.trans (by rw [hPa, map_zero])
      rw [hroot]
      exact isIntegral_zero
    · intro i
      rw [coeff_map]
      rw [he]
      exact isIntegral_eval_of_isIntegral ht (P.coeff i)
  let x₁ : W₁.FunctionField :=
    algebraMap W₁.CoordinateRing W₁.FunctionField
      (algebraMap F[X] W₁.CoordinateRing X)
  have hx₁_over_target :
      @IsIntegral W₂.CoordinateRing W₁.FunctionField _ _
        φ.pullback.toRingHom.toAlgebra x₁ := by
    exact (CoordinatePullback.mapsInfinity_iff φ.pullback).1 φ.mapsInfinity
      (algebraMap F[X] W₁.CoordinateRing X)
  obtain ⟨Q, hQmonic, hQx⟩ := hx₁_over_target
  have hx₁ : IsIntegral F x₁ := by
    have hroot : eval₂ φ.pullback.toRingHom x₁ Q = 0 := by
      simpa only [RingHom.algebraMap_toAlgebra] using hQx
    have hQdegree : Q.natDegree ≠ 0 := by
      intro hdegree
      have hQ : Q = 1 := hQmonic.natDegree_eq_zero.mp hdegree
      rw [hQ] at hroot
      simp at hroot
    apply IsIntegral.of_aeval_monic_of_isIntegral_coeff
        (p := Q.map φ.pullback.toRingHom) (x := x₁)
    · exact hQmonic.map _
    · rw [hQmonic.natDegree_map]
      exact hQdegree
    · rw [eval_map]
      rw [hroot]
      exact isIntegral_zero
    · intro i
      rw [coeff_map]
      exact himage (Q.coeff i)
  have hx₁_transcendental : Transcendental F x₁ := by
    have hx₁_eq : x₁ = algebraMap F[X] W₁.FunctionField X :=
      (IsScalarTower.algebraMap_apply F[X] W₁.CoordinateRing W₁.FunctionField X).symm
    rw [hx₁_eq]
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective F[X] W₁.FunctionField)).2
        (Polynomial.transcendental_X F)
  exact hx₁_transcendental hx₁.isAlgebraic

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

end Isogeny

end TauCeti
