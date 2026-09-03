/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Algebraically closed points of faithfully flat algebras

Let `K` be an algebraically closed field over a commutative ring `k`, and let `f : A →ₐ[k] B`
be faithfully flat and of finite type. Every `K`-point of `A` lifts to a `K`-point of `B`.

Faithful flatness first gives a prime of `B` over the kernel of the prescribed point. The affine
Nullstellensatz then gives a `K`-point of `B` whose kernel contains that prime. Its restriction to
`A` agrees with the prescribed point. This last step is carried out in the fiber over the
prescribed point, which is a nontrivial finite-type `K`-algebra and therefore has a `K`-point.

## Main declarations

* `AlgHom.surjective_comp_right_of_comap_surjective`: a map surjective on prime spectra is
  surjective on algebraically closed points when the map is of finite type.
* `AlgHom.surjective_comp_right_of_faithfullyFlat`: precomposition along a faithfully flat
  map of finite type is surjective on algebraically closed points.

## References

* The Stacks Project, Tag 00HQ, Lemma 10.39.16.
* The Stacks Project, Tag 00FV, *Hilbert Nullstellensatz*.

This is the algebraically-closed-point lifting prerequisite for Layer 5, "The unipotent radical",
of the ReductiveGroups roadmap. It is the pointwise bridge needed to transfer unipotence from a
finite-type affine group onto the scheme-theoretic image of a faithfully flat group morphism.
-/

public section

open scoped TensorProduct

namespace AlgHom

universe u v w x

variable {k : Type u} {A : Type v} {B : Type w} {K : Type x}
variable [CommRing k]
variable [CommRing A] [Algebra k A]
variable [CommRing B] [Algebra k B]
variable [Field K] [Algebra k K] [IsAlgClosed K]

/-- A point of `A` lifts through `f` if a prime of `B` lies over its kernel. -/
private theorem exists_comp_eq_of_comap_eq_ker (f : A →ₐ[k] B) (hft : f.FiniteType)
    (p : A →ₐ[k] K)
    (P : PrimeSpectrum B)
    (hP : PrimeSpectrum.comap f.toRingHom P =
      ⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime p.toRingHom⟩) :
    ∃ q : B →ₐ[k] K, q.comp f = p := by
  have hPcomap : P.asIdeal.comap f.toRingHom = RingHom.ker p.toRingHom := by
    simpa only [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hP
  let D := A ⧸ RingHom.ker p.toRingHom
  let C := B ⧸ P.asIdeal
  let g : D →ₐ[k] C :=
    Ideal.quotientMapₐ P.asIdeal f (le_of_eq hPcomap.symm)
  let p' : D →ₐ[k] K := Ideal.kerLiftAlg p
  have hgcomp :
      g.comp (Ideal.Quotient.mkₐ k (RingHom.ker p.toRingHom)) =
        (Ideal.Quotient.mkₐ k P.asIdeal).comp f :=
    Ideal.quotient_map_comp_mkₐ P.asIdeal f (le_of_eq hPcomap.symm)
  have hg : Function.Injective g := by
    apply Ideal.quotientMap_injective' (H := le_of_eq hPcomap.symm)
    exact le_of_eq hPcomap
  have hp' : Function.Injective p' := Ideal.kerLiftAlg_injective p
  have hgFiniteType : g.FiniteType := by
    apply AlgHom.FiniteType.of_comp_finiteType
      (f := Ideal.Quotient.mkₐ k (RingHom.ker p.toRingHom)) (g := g)
    rw [hgcomp]
    exact hft.comp_surjective (Ideal.Quotient.mkₐ_surjective k P.asIdeal)
  algebraize [g.toRingHom, p'.toRingHom]
  let _ : IsScalarTower k D C :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let _ : IsScalarTower k D K :=
    IsScalarTower.of_algebraMap_eq' p'.comp_algebraMap.symm
  let _ : Algebra.FiniteType D C := hgFiniteType
  let _ : Nontrivial (K ⊗[D] C) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      D K C hp' hg
  obtain ⟨q', -⟩ :=
    TauCeti.exists_algHom_apply_ne_zero_of_not_isNilpotent
      (k := K) (A := K ⊗[D] C) (K := K) (x := 1) not_isNilpotent_one
  let q'' : C →ₐ[D] K := (AlgHom.liftEquiv D K C K).symm q'
  let q : B →ₐ[k] K :=
    (q''.restrictScalars k).comp (Ideal.Quotient.mkₐ k P.asIdeal)
  refine ⟨q, AlgHom.ext fun a ↦ ?_⟩
  calc
    q (f a) = q'' ((Ideal.Quotient.mkₐ k P.asIdeal) (f a)) := by
      simp only [q, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    _ = q'' (g ((Ideal.Quotient.mkₐ k (RingHom.ker p.toRingHom)) a)) := by
      have ha := DFunLike.congr_fun hgcomp a
      simp only [AlgHom.comp_apply] at ha
      rw [← ha]
    _ = q'' (g (Ideal.Quotient.mk (RingHom.ker p.toRingHom) a)) := by
      rw [Ideal.Quotient.mkₐ_eq_mk]
    _ = p' (Ideal.Quotient.mk (RingHom.ker p.toRingHom) a) := q''.commutes _
    _ = p a := Ideal.kerLiftAlg_mk p a

/-- Precomposition is surjective on algebraically closed points when the underlying map is of
finite type and surjective on prime spectra. -/
theorem surjective_comp_right_of_comap_surjective (f : A →ₐ[k] B) (hft : f.FiniteType)
    (hf : Function.Surjective (PrimeSpectrum.comap f.toRingHom)) :
    Function.Surjective (fun q : B →ₐ[k] K ↦ q.comp f) := by
  intro p
  obtain ⟨P, hP⟩ := hf
    ⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime p.toRingHom⟩
  exact exists_comp_eq_of_comap_eq_ker f hft p P hP

/-- Precomposition along a faithfully flat morphism is surjective on points valued in an
algebraically closed field over the base ring, provided the morphism is of finite type.

In scheme language, a faithfully flat morphism of finite type `Spec B ⟶ Spec A` is surjective
on `K`-points for every algebraically closed field `K` with a `k`-algebra structure. -/
theorem surjective_comp_right_of_faithfullyFlat (f : A →ₐ[k] B) (hft : f.FiniteType)
    (hf : f.toRingHom.FaithfullyFlat) :
    Function.Surjective (fun q : B →ₐ[k] K ↦ q.comp f) :=
  surjective_comp_right_of_comap_surjective f hft
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hf).2

end AlgHom
