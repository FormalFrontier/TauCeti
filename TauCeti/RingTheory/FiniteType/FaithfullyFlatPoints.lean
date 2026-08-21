/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Algebraically closed points of faithfully flat algebras

Let `k` be algebraically closed and let `f : A →ₐ[k] B` be faithfully flat, with `B` of
finite type over `k`. Every `k`-point of `A` lifts to a `k`-point of `B`.

Faithful flatness first gives a prime of `B` over the kernel of the prescribed point. The affine
Nullstellensatz then gives a `k`-point of `B` whose kernel contains that prime. Its restriction to
`A` agrees with the prescribed point because both maps are `k`-linear and the latter is
surjective.

## Main declaration

* `AlgHom.comp_surjective_of_comap_surjective`: a map surjective on prime spectra is
  surjective on algebraically closed points when its codomain algebra is of finite type.
* `AlgHom.comp_surjective_of_faithfullyFlat`: precomposition along a faithfully flat map
  is surjective on algebraically closed points when the source algebra is of finite type.

## References

* The Stacks Project, Tag 00HB, *Faithfully flat modules*.
* The Stacks Project, Tag 00FV, *Hilbert Nullstellensatz*.

This is the algebraically-closed-point lifting prerequisite for Layer 5, "The unipotent radical",
of the ReductiveGroups roadmap. It is the pointwise bridge needed to transfer unipotence from a
finite-type affine group onto the scheme-theoretic image of a faithfully flat group morphism.
-/

public section

namespace AlgHom

universe u v w

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [IsAlgClosed k]
variable [CommRing A] [Algebra k A]
variable [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

/-- A point of `A` lifts through `f` if a prime of `B` lies over its kernel. -/
private theorem exists_comp_eq_of_exists_prime_over (f : A →ₐ[k] B) (p : A →ₐ[k] k)
    (P : PrimeSpectrum B)
    (hP : PrimeSpectrum.comap f.toRingHom P =
      ⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime p.toRingHom⟩) :
    ∃ q : B →ₐ[k] k, q.comp f = p := by
  have hradical : P.asIdeal.radical = P.asIdeal := P.isPrime.radical
  have hone : (1 : B) ∉ P.asIdeal.radical := by
    rw [hradical]
    intro hone
    exact P.isPrime.ne_top (P.asIdeal.eq_top_iff_one.mpr hone)
  obtain ⟨q, hPq, -⟩ :=
    TauCeti.exists_algHom_apply_ne_zero_of_notMem_radical
      (k := k) (K := k) P.asIdeal hone
  refine ⟨q, AlgHom.ext fun a ↦ ?_⟩
  have hker : a - algebraMap k A (p a) ∈ RingHom.ker p.toRingHom := by
    rw [RingHom.mem_ker]
    simp
  have hPcomap : P.asIdeal.comap f.toRingHom = RingHom.ker p.toRingHom := by
    simpa only [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hP
  have hzero : q (f (a - algebraMap k A (p a))) = 0 := by
    rw [← RingHom.mem_ker]
    apply hPq
    exact Ideal.mem_comap.mp (hPcomap.symm ▸ hker)
  have hzero' : q (f a) - p a = 0 := by
    calc
      q (f a) - p a = q (f a) - q (f (algebraMap k A (p a))) := by
        rw [f.commutes, q.commutes, Algebra.algebraMap_self_apply]
      _ = q (f (a - algebraMap k A (p a))) := by rw [map_sub, map_sub]
      _ = 0 := hzero
  exact sub_eq_zero.mp hzero'

/-- Precomposition is surjective on algebraically closed points when the underlying map is
surjective on prime spectra and its codomain is of finite type over the field. -/
theorem comp_surjective_of_comap_surjective (f : A →ₐ[k] B)
    (hf : Function.Surjective (PrimeSpectrum.comap f.toRingHom)) :
    Function.Surjective (fun q : B →ₐ[k] k ↦ q.comp f) := by
  intro p
  obtain ⟨P, hP⟩ := hf
    ⟨RingHom.ker p.toRingHom, RingHom.ker_isPrime p.toRingHom⟩
  exact exists_comp_eq_of_exists_prime_over f p P hP

/-- Precomposition along a faithfully flat morphism is surjective on points valued in an
algebraically closed field, provided its codomain algebra is of finite type over that field.

In scheme language, a faithfully flat morphism `Spec B ⟶ Spec A` with `B` of finite type over
`k` is surjective on `k`-points when `k` is algebraically closed. -/
theorem comp_surjective_of_faithfullyFlat (f : A →ₐ[k] B)
    (hf : f.toRingHom.FaithfullyFlat) :
    Function.Surjective (fun q : B →ₐ[k] k ↦ q.comp f) :=
  comp_surjective_of_comap_surjective f
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hf).2

end AlgHom
