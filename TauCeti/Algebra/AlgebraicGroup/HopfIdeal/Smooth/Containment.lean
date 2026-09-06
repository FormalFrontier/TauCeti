/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.RingTheory.Ideal.IdempotentFG

/-!
# Smooth connected closed subgroups with equal tangent spaces

A surjective map of coordinate Hopf algebras represents a closed immersion of affine groups.
When both groups are smooth and connected, surjectivity on tangent spaces forces this closed
immersion to be an isomorphism.

The proof uses the conormal module of the surjection. Smoothness makes it finite projective over
the target. Its fibre at the identity is zero, because its split injection into the relative
cotangent space is zero there. Projective-module rank is locally constant, so connectedness of
the target makes the conormal module vanish globally. The kernel is then idempotent; connectedness
of the source and the counit condition force it to be zero.

## Main declaration

* `TauCeti.HopfIdeal.ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot`: a surjective
  Hopf map between smooth connected affine groups is injective when its conormal space vanishes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a and 10.a.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This is the global equality step in Layer 5, "The unipotent radical", of the ReductiveGroups
roadmap. It upgrades the infinitesimal equality supplied by the maximal-dimension construction to
equality of closed subgroups.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

open TensorProduct

variable {k H K : Type u} [Field k] [CommRing H] [CommRing K]
variable [HopfAlgebra k H] [HopfAlgebra k K]

/-- A surjective Hopf map between smooth connected affine groups is injective if its conormal
space at the identity vanishes.

Equivalently, a smooth connected closed affine subgroup whose differential is surjective is the
whole ambient group. -/
theorem ker_eq_bot_of_smooth_of_connected_of_conormalSubspace_eq_bot
    [Algebra.FiniteType k H] (f : H →ₐc[k] K) (hf : Function.Surjective f)
    (hH_smooth : smoothCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (hH_connected : ConnectedSpace (PrimeSpectrum H))
    (hK_smooth : smoothCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k K))
    (hK_connected : ConnectedSpace (PrimeSpectrum K))
    (hconormal : conormalSubspace (HopfIdeal.ker f) = ⊥) : HopfIdeal.ker f = ⊥ := by
  let _ : Algebra H K := f.toAlgHom.toAlgebra
  let _ : IsScalarTower k H K :=
    IsScalarTower.of_algebraMap_eq' f.toAlgHom.comp_algebraMap.symm
  let P : Algebra.Extension k K :=
    { Ring := H
      σ := Function.surjInv hf
      algebraMap_σ := Function.surjInv_eq hf }
  let _ : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff _).mp hH_smooth
  let _ : Algebra.Smooth k K := (smoothCommHopfAlgProperty_iff _).mp hK_smooth
  let _ : ConnectedSpace (PrimeSpectrum H) := hH_connected
  let _ : ConnectedSpace (PrimeSpectrum K) := hK_connected
  let _ : Algebra.Smooth k P.Ring := by
    simpa only [P] using (inferInstance : Algebra.Smooth k H)
  let _ : IsNoetherianRing P.Ring := by
    simpa only [P] using (Algebra.FiniteType.isNoetherianRing k H)
  have hf_algebraMap : algebraMap H K = f.toAlgHom.toRingHom := by
    ext x
    rfl
  have hPmap : algebraMap P.Ring K = f.toAlgHom.toRingHom := by
    simpa only [P] using hf_algebraMap
  have hPker : P.ker = (HopfIdeal.ker f).toIdeal := by
    rw [HopfIdeal.ker_toIdeal]
    exact congrArg RingHom.ker hPmap
  have hker_aug : (HopfIdeal.ker f).toIdeal ≤
      Bialgebra.AugmentationIdeal k H := by
    intro x hx
    rw [Bialgebra.AugmentationIdeal, RingHom.mem_ker]
    have hxker : x ∈ RingHom.ker (f : H →ₐ[k] K) := by
      simpa only [HopfIdeal.ker_toIdeal] using hx
    have hcounit := CoalgHomClass.counit_comp_apply f x
    calc
      Coalgebra.counit (R := k) x = Coalgebra.counit (R := k) (f x) := hcounit.symm
      _ = Coalgebra.counit (R := k) 0 := congrArg _ (RingHom.mem_ker.mp hxker)
      _ = 0 := map_zero (Bialgebra.counitAlgHom k K)
  have hker_fg : P.ker.FG := by
    exact P.ker.fg_of_isNoetherianRing
  have _ : Module.Finite P.Ring P.Cotangent := by
    have _ : Module.Finite P.Ring P.ker := Module.Finite.of_fg hker_fg
    exact Module.Finite.of_surjective _ Algebra.Extension.Cotangent.mk_surjective
  have _ : Module.Finite K P.Cotangent :=
    Module.Finite.of_restrictScalars_finite P.Ring K P.Cotangent
  obtain ⟨l, hl⟩ := (P.formallySmooth_iff_split_injection).mp
    (inferInstance : Algebra.FormallySmooth k K)
  let _ : Module.Projective K P.CotangentSpace := inferInstance
  let _ : Module.Projective K P.Cotangent :=
    Module.Projective.of_split P.cotangentComplex l hl
  let _ : Module.Flat K P.Cotangent := inferInstance
  let _ : Module.FinitePresentation K P.Cotangent :=
    Module.finitePresentation_of_projective K P.Cotangent
  let p : Ideal K := Bialgebra.AugmentationIdeal k K
  let _ : p.IsMaximal := by
    dsimp [p, Bialgebra.AugmentationIdeal]
    exact RingHom.ker_isMaximal_of_surjective _ fun x ↦
      ⟨algebraMap k K x, by simp⟩
  let κ := p.ResidueField
  let g : H →ₐ[k] κ :=
    (IsScalarTower.toAlgHom k K κ).comp f.toAlgHom
  have hgker : RingHom.ker g = Bialgebra.AugmentationIdeal k H := by
    ext x
    rw [RingHom.mem_ker]
    simp only [g, AlgHom.coe_comp, Function.comp_apply, IsScalarTower.toAlgHom_apply]
    rw [Ideal.algebraMap_residueField_eq_zero]
    simp only [p, Bialgebra.AugmentationIdeal, RingHom.mem_ker]
    constructor
    · exact fun hx ↦ (CoalgHomClass.counit_comp_apply f x).symm.trans hx
    · exact fun hx ↦ (CoalgHomClass.counit_comp_apply f x).trans hx
  have hbaseChange_zero : P.cotangentComplex.lTensor κ = 0 := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul a m =>
      obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P) m
      have hxker : (x : H) ∈ RingHom.ker g := by
        rw [hgker]
        exact hker_aug (hPker ▸ x.property)
      have hxsq : (x : H) ∈ RingHom.ker g ^ 2 := by
        rw [hgker]
        exact (conormalSubspace_eq_bot_iff_toIdeal_le_sq_augmentationIdeal _).mp
          hconormal (hPker ▸ x.property)
      have hdx : (1 : κ) ⊗ₜ[H] KaehlerDifferential.D k H (x : H) = 0 := by
        have hgMap : algebraMap H κ = g.toRingHom := by
          ext y
          rw [IsScalarTower.algebraMap_apply H K κ]
          simp only [g]
          exact congrArg (algebraMap K κ)
            (congrArg (fun φ : H →+* K => φ y) hf_algebraMap)
        have hker_eq : RingHom.ker (algebraMap H κ) = RingHom.ker g :=
          congrArg RingHom.ker hgMap
        let xg : RingHom.ker (algebraMap H κ) :=
          ⟨x, hker_eq.symm ▸ hxker⟩
        have hxsq' : (x : H) ∈ RingHom.ker (algebraMap H κ) ^ 2 := by
          rw [hker_eq]
          exact hxsq
        have hxzero : (RingHom.ker (algebraMap H κ)).toCotangent xg = 0 :=
          (Ideal.toCotangent_eq_zero _ xg).2 hxsq'
        simpa only [xg, map_zero,
          KaehlerDifferential.kerCotangentToTensor_toCotangent] using
          congrArg (KaehlerDifferential.kerCotangentToTensor k H κ) hxzero
      rw [LinearMap.lTensor_tmul, P.cotangentComplex_mk]
      -- `Extension.CotangentSpace` is an abbreviation for this nested tensor product; exposing
      -- it is necessary to apply the associativity equivalence `cancelBaseChange` below.
      change a ⊗ₜ[K] (1 ⊗ₜ[H] KaehlerDifferential.D k H (x : H)) = 0
      apply (AlgebraTensorModule.cancelBaseChange H K κ κ
        (KaehlerDifferential k H)).injective
      simpa only [map_zero, AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one, smul_zero] using
        congrArg (a • ·) hdx
  have hfiber : Subsingleton (p.Fiber P.Cotangent) := by
    have hinjective : Function.Injective (P.cotangentComplex.lTensor κ) := by
      intro x y hxy
      have h := congrArg (l.lTensor κ) hxy
      simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hl,
        LinearMap.lTensor_id, LinearMap.id_apply] using h
    constructor
    intro x y
    apply hinjective
    rw [hbaseChange_zero]
    rfl
  have hrank_identity : Module.rankAtStalk (R := K) P.Cotangent
      ⟨p, (inferInstance : p.IsMaximal).isPrime⟩ = 0 := by
    rw [Module.rankAtStalk_eq]
    exact Module.finrank_zero_of_subsingleton
  have hrank : Module.rankAtStalk (R := K) P.Cotangent = 0 := by
    apply funext
    intro q
    simp only [Pi.zero_apply]
    calc
      Module.rankAtStalk P.Cotangent q =
          Module.rankAtStalk P.Cotangent ⟨p, (inferInstance : p.IsMaximal).isPrime⟩ :=
        IsLocallyConstant.apply_eq_of_preconnectedSpace
          (Module.isLocallyConstant_rankAtStalk (R := K) (M := P.Cotangent)) _ _
      _ = 0 := hrank_identity
  have hcotangent : Subsingleton P.Cotangent :=
    (Module.rankAtStalk_eq_zero_iff_subsingleton (R := K) (M := P.Cotangent)).mp hrank
  have hI_idempotent : IsIdempotentElem (HopfIdeal.ker f).toIdeal := by
    rw [← hPker]
    have hcotangentKer : Subsingleton P.ker.Cotangent := by
      constructor
      intro x y
      apply P.cotangentEquivCotangentKer.symm.injective
      exact Subsingleton.elim _ _
    exact (Ideal.cotangent_subsingleton_iff (I := P.ker)).mp
      hcotangentKer
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨e, he, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg (HopfIdeal.ker f).toIdeal
      (HopfIdeal.ker f).toIdeal.fg_of_isNoetherianRing).mp hI_idempotent
  rcases eq_zero_or_eq_one_of_isIdempotentElem he with rfl | rfl
  · apply HopfIdeal.ext
    intro x
    rw [← mem_toIdeal, ← mem_toIdeal, bot_toIdeal]
    simpa using SetLike.ext_iff.mp hspan x
  · exfalso
    apply RingHom.ker_ne_top (Bialgebra.counitAlgHom k H).toRingHom
    apply top_unique
    intro x _
    apply hker_aug
    rw [hspan]
    simp

end HopfIdeal

end

end TauCeti
