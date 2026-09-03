/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import TauCeti.Algebra.Module.ProjectiveCover.Basic

/-!
# Existence of projective covers over a semiprimary ring

`TauCeti/Algebra/Module/ProjectiveCover/Basic.lean` develops the projective cover of a module as a
*given* datum: it is unique, and it receives every projective presentation, but nothing there
produces one. This file supplies the existence theorem. Over a **semiprimary** ring — Mathlib's
`IsSemiprimaryRing`, a ring whose Jacobson radical is nilpotent and whose radical quotient is
semisimple, as a finite-dimensional algebra over a field is — **every** module has a projective
cover (`TauCeti.exists_isProjectiveCover`), with no finiteness hypothesis on the module.

Some hypothesis on the ring is genuinely needed: `ℤ ⧸ 2ℤ` has no projective cover as a `ℤ`-module,
although it has finite length.

## The construction

Write `J` for the radical and `M ↦ M ⧸ J • M` for passage to the radical quotient. Fix a free
module `N` with a surjection `p : N ↠ M` — the free module on the underlying set of `M` will do —
and let `q : N ⧸ J • N ↠ M ⧸ J • M` be the induced surjection. The cover is cut out of `N` by an
idempotent, in three steps.

* **The radical quotient is semisimple.** `N ⧸ J • N` is a module over `R ⧸ J`, which is a
  semisimple ring, so it is a semisimple `R ⧸ J`-module and hence a semisimple `R`-module
  (`TauCeti.isSemisimpleModule_quotient_jacobson_smul_top`). Therefore `ker q` has a complement
  `C`, and the projection onto `C` along `ker q` is an idempotent `ē` of `End (N ⧸ J • N)` with
  `range ē = C`.
* **The idempotent lifts.** Reduction of endomorphisms modulo `J • N` is a ring homomorphism
  `TauCeti.endMapQ J N : End N →+* End (N ⧸ J • N)`. It is surjective because `N` is projective
  (`TauCeti.endMapQ_surjective`), and every element of its kernel is nilpotent because `J` is
  (`TauCeti.isNilpotent_of_mem_ker_endMapQ`): a map with image inside `J • N` has `k`-th power with
  image inside `J ^ k • N`. Mathlib's `exists_isIdempotentElem_eq_of_ker_isNilpotent` therefore
  lifts `ē` to an idempotent `e` of `End N`.
* **The cover is the image of the lift.** `P = range e` is a direct summand of the free module `N`,
  so it is projective, and `π = p|_P` is the cover. It is onto because its image spans `M` modulo
  `J • M` — that is what `ker ē = ker q` says — and `J • M` is superfluous
  (`TauCeti.isSuperfluous_smul_top_of_isNilpotent`, Nakayama for a nilpotent ideal). Its kernel is
  superfluous because an element of it reduces into `C ⊓ ker q = ⊥`, hence lies in `J • N`, hence,
  being fixed by `e`, lies in `J • P`.

Nilpotence of `J` is used twice, and differently: once to make `J • M` superfluous in an arbitrary
module — which is what removes every finiteness hypothesis, and is why a semiprimary ring covers
*all* modules and not only the finitely generated ones a semiperfect ring covers — and once to make
the kernel of the reduction map nil, which is what lets the idempotent lift.

## Main statements

* `TauCeti.endMapQ`: reduction of endomorphisms modulo `I • M`, as a ring homomorphism, with
  `TauCeti.endMapQ_surjective` and `TauCeti.isNilpotent_of_mem_ker_endMapQ` the two properties that
  make idempotents lift along it, the latter refining
  `TauCeti.range_pow_le_of_mem_ker_endMapQ`.
* `TauCeti.isSemisimpleModule_quotient_jacobson_smul_top`: the radical quotient of any module over
  a semiprimary ring is a semisimple module.
* `TauCeti.exists_isProjectiveCover`: **every module over a semiprimary ring has a projective
  cover**, realized as a direct summand of a free module.
* `TauCeti.exists_isProjectiveCover_of_finiteDimensional`: the finite-dimensional-algebra reading,
  which is the form the roadmap states.

## References

This is the existence half of the "projective covers and injective envelopes" bullet of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose uniqueness half is
`TauCeti/Algebra/Module/ProjectiveCover/Basic.lean`; the roadmap asks for existence over a
finite-dimensional algebra, "existing because `A` is semiperfect (finite-dimensional)".

See T. Y. Lam, *A First Course in Noncommutative Rings*, §24 (semiperfect and semiprimary rings,
idempotent lifting, and projective covers), and I. Assem, D. Simson, A. Skowroński, *Elements of
the Representation Theory of Associative Algebras, Vol. 1*, Section I.5.
-/

public section

namespace TauCeti

universe u v w

section Reduction

variable {R : Type u} [Ring R]

/-- **Reduction of endomorphisms modulo `I • M`.** An endomorphism of `M` carries `I • M` into
itself, so it descends to the quotient `M ⧸ I • M`, and the descent is a ring homomorphism. -/
def endMapQ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Module.End R M →+* Module.End R (M ⧸ I • (⊤ : Submodule R M)) where
  toFun f := Submodule.mapQ _ _ f (Submodule.map_le_iff_le_comap.mp
    (by rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top))
  -- Each law is checked on the classes `Submodule.Quotient.mk x`, where it is definitional.
  map_one' := Submodule.linearMap_qext _ (rfl)
  map_mul' _ _ := Submodule.linearMap_qext _ (rfl)
  map_zero' := Submodule.linearMap_qext _ (rfl)
  map_add' _ _ := Submodule.linearMap_qext _ (rfl)

variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

@[simp]
theorem endMapQ_mk (f : Module.End R M) (x : M) :
    endMapQ I M f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  (rfl)

/-- Every endomorphism of `M ⧸ I • M` is the reduction of an endomorphism of `M`, provided `M` is
projective: lift the composite `M ↠ M ⧸ I • M → M ⧸ I • M` through the quotient map. -/
theorem endMapQ_surjective [Module.Projective R M] : Function.Surjective (endMapQ I M) := by
  intro g
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ
    (g ∘ₗ (I • (⊤ : Submodule R M)).mkQ) (Submodule.mkQ_surjective _)
  refine ⟨f, LinearMap.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact LinearMap.congr_fun hf y

/-- An endomorphism killed by the reduction map has image inside `I • M`, hence `k`-th power with
image inside `I ^ k • M`. -/
theorem range_pow_le_of_mem_ker_endMapQ {f : Module.End R M}
    (hf : f ∈ RingHom.ker (endMapQ I M)) (k : ℕ) :
    LinearMap.range (f ^ k) ≤ I ^ k • (⊤ : Submodule R M) := by
  have hrange : LinearMap.range f ≤ I • (⊤ : Submodule R M) := by
    rintro _ ⟨y, rfl⟩
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    rw [← endMapQ_mk I M f y, RingHom.mem_ker.mp hf, LinearMap.zero_apply]
  induction k with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact le_top
  | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      calc Submodule.map f (LinearMap.range (f ^ k))
          ≤ Submodule.map f (I ^ k • (⊤ : Submodule R M)) := Submodule.map_mono ih
        _ = I ^ k • Submodule.map f ⊤ := by rw [Submodule.map_smul'']
        _ = I ^ k • LinearMap.range f := by rw [Submodule.map_top]
        _ ≤ I ^ k • (I • (⊤ : Submodule R M)) := Submodule.smul_mono le_rfl hrange
        _ = I ^ (k + 1) • (⊤ : Submodule R M) := by
            rw [Submodule.pow_succ, Submodule.mul_smul]

/-- **The kernel of the reduction map is nil** when `I` is nilpotent: an endomorphism with image in
`I • M` has a vanishing power, because `I ^ k • M` vanishes. -/
theorem isNilpotent_of_mem_ker_endMapQ (hI : IsNilpotent I) {f : Module.End R M}
    (hf : f ∈ RingHom.ker (endMapQ I M)) : IsNilpotent f := by
  obtain ⟨m, hm⟩ := hI
  refine ⟨m, LinearMap.range_eq_bot.mp (le_bot_iff.mp ?_)⟩
  simpa [hm] using range_pow_le_of_mem_ker_endMapQ I M hf m

end Reduction

section Semiprimary

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

/-- **The radical quotient of a module over a semiprimary ring is semisimple.** It is a module over
the semisimple ring `R ⧸ Ring.jacobson R`, and semisimplicity is insensitive to which of the two
rings the scalars are read in. -/
theorem isSemisimpleModule_quotient_jacobson_smul_top [IsSemiprimaryRing R] :
    IsSemisimpleModule R (M ⧸ Ring.jacobson R • (⊤ : Submodule R M)) :=
  (Module.isTorsionBySet_quotient_ideal_smul M (Ring.jacobson R)).isSemisimpleModule_iff.mp
    inferInstance

variable {R M}

/-- **A projective cover is cut out of any projective presentation by an idempotent.** Over a
semiprimary ring, a surjection `p : N ↠ M` from a projective module restricts to a projective cover
of `M` on a suitable submodule `P` of `N` — a direct summand, the image of an idempotent lifted
from the radical quotient. See the module docstring for the argument. -/
theorem exists_isProjectiveCover_comp_subtype [IsSemiprimaryRing R] {N : Type w} [AddCommGroup N]
    [Module R N] [Module.Projective R N] (p : N →ₗ[R] M) (hp : Function.Surjective p) :
    ∃ P : Submodule R N, IsProjectiveCover (p ∘ₗ P.subtype) := by
  classical
  -- `p` descends to a surjection of radical quotients.
  have hcomap : Ring.jacobson R • (⊤ : Submodule R N) ≤
      (Ring.jacobson R • (⊤ : Submodule R M)).comap p := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  set q : (N ⧸ Ring.jacobson R • (⊤ : Submodule R N)) →ₗ[R]
      M ⧸ Ring.jacobson R • (⊤ : Submodule R M) := Submodule.mapQ _ _ p hcomap
  have hq : ∀ n : N, q (Submodule.Quotient.mk n) = Submodule.Quotient.mk (p n) := fun _ => rfl
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨n, rfl⟩ := hp x
    exact ⟨Submodule.Quotient.mk n, rfl⟩
  -- The kernel of `q` splits off, because the radical quotient of `N` is semisimple.
  have hss := isSemisimpleModule_quotient_jacobson_smul_top R N
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker q)
  set ebar : Module.End R (N ⧸ Ring.jacobson R • (⊤ : Submodule R N)) :=
    C.projection (LinearMap.ker q) hC.symm
  have hebar : IsIdempotentElem ebar := Submodule.isIdempotentElem_projection _
  have hrangebar : LinearMap.range ebar = C := Submodule.range_projection _
  have hsub : ∀ x, x - ebar x ∈ LinearMap.ker q := fun x => Submodule.sub_projection_mem hC.symm x
  -- Lift `ebar`: the reduction map is onto with nil kernel.
  obtain ⟨e, he, hee⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (endMapQ (Ring.jacobson R) N)
    (fun _ hg => isNilpotent_of_mem_ker_endMapQ _ N IsSemiprimaryRing.isNilpotent hg)
    ebar (RingHom.mem_range.mpr (endMapQ_surjective _ N ebar)) hebar
  have hfix : ∀ x ∈ LinearMap.range e, e x = x := by
    rintro _ ⟨y, rfl⟩
    exact (Module.End.mul_apply e e y).symm.trans (DFunLike.congr_fun he.eq y)
  have hebar_mk : ∀ n : N, ebar (Submodule.Quotient.mk n) = Submodule.Quotient.mk (e n) := by
    intro n
    rw [← hee]
    exact endMapQ_mk _ N e n
  -- Nakayama: the radical multiple of any module is superfluous in it.
  have hsuperM : IsSuperfluous (Ring.jacobson R • (⊤ : Submodule R M)) :=
    isSuperfluous_smul_top_of_isNilpotent IsSemiprimaryRing.isNilpotent
  refine ⟨LinearMap.range e, ?_, ?_, ?_⟩
  · -- `range e` is a direct summand of the projective module `N`, hence projective.
    exact Module.Projective.of_split (LinearMap.range e).subtype
      (e.codRestrict (LinearMap.range e) fun x => LinearMap.mem_range_self e x)
      (LinearMap.ext fun x => Subtype.ext (hfix _ x.2))
  · -- The image of `P` spans `M` modulo the superfluous `J • M`, hence is all of `M`.
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    refine hsuperM.eq_top_of_sup_eq_top (top_le_iff.mp fun x _ => ?_)
    obtain ⟨z, hz⟩ := hqsurj (Submodule.Quotient.mk x)
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hzz : (Submodule.Quotient.mk x : M ⧸ Ring.jacobson R • (⊤ : Submodule R M))
        = Submodule.Quotient.mk (p (e n)) := by
      rw [← hq, ← hebar_mk, ← hz]
      have hker := hsub (Submodule.Quotient.mk n)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hker
      exact hker
    exact Submodule.mem_sup.mpr ⟨x - p (e n), (Submodule.Quotient.eq _).mp hzz,
      p (e n), Submodule.mem_map_of_mem ⟨n, rfl⟩, by abel⟩
  · -- An element of the kernel reduces into `C ⊓ ker q = ⊥`, so lies in `J • N`, so in `J • P`.
    refine (isSuperfluous_smul_top_of_isNilpotent
      (M := ↥(LinearMap.range e)) IsSemiprimaryRing.isNilpotent).mono ?_
    rintro ⟨x, hx⟩ hker
    have hpx : p x = 0 := LinearMap.mem_ker.mp hker
    have hmemC : (Submodule.Quotient.mk x : N ⧸ Ring.jacobson R • (⊤ : Submodule R N)) ∈ C := by
      obtain ⟨y, rfl⟩ := hx
      exact hrangebar ▸ ⟨Submodule.Quotient.mk y, hebar_mk y⟩
    have hmemker : (Submodule.Quotient.mk x : N ⧸ Ring.jacobson R • (⊤ : Submodule R N))
        ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, hq, hpx]
      exact Submodule.Quotient.mk_zero _
    have hinf : (Submodule.Quotient.mk x : N ⧸ Ring.jacobson R • (⊤ : Submodule R N))
        ∈ C ⊓ LinearMap.ker q := ⟨hmemC, hmemker⟩
    rw [hC.symm.inf_eq_bot, Submodule.mem_bot] at hinf
    have hxJN : x ∈ Ring.jacobson R • (⊤ : Submodule R N) :=
      (Submodule.Quotient.mk_eq_zero _).mp hinf
    rw [Submodule.mem_smul_top_iff]
    have hmap : x ∈ Submodule.map e (Ring.jacobson R • (⊤ : Submodule R N)) :=
      ⟨x, hxJN, hfix x hx⟩
    rwa [Submodule.map_smul'', Submodule.map_top] at hmap

variable (R M)

/-- **Every module over a semiprimary ring has a projective cover.**

The cover is a direct summand of the free module on the underlying set of `M`. No finiteness is
assumed of `M`: a semiprimary ring is left perfect, so it covers every module, not only the
finitely generated ones. -/
theorem exists_isProjectiveCover [IsSemiprimaryRing R] :
    ∃ P : Submodule R (M →₀ R),
      IsProjectiveCover (Finsupp.linearCombination R id ∘ₗ P.subtype) :=
  exists_isProjectiveCover_comp_subtype _ fun x => ⟨Finsupp.single x 1, by simp⟩

end Semiprimary

section FiniteDimensional

/-- **Every module over a finite-dimensional algebra has a projective cover**, the form in which the
roadmap states the theorem. A finite-dimensional algebra is an Artinian ring, hence semiprimary, so
this is `TauCeti.exists_isProjectiveCover` read through that instance; in particular no finiteness
is required of the module. -/
theorem exists_isProjectiveCover_of_finiteDimensional (k : Type w) [Field k] (A : Type u) [Ring A]
    [Algebra k A] [FiniteDimensional k A] (V : Type v) [AddCommGroup V] [Module A V] :
    ∃ P : Submodule A (V →₀ A),
      IsProjectiveCover (Finsupp.linearCombination A id ∘ₗ P.subtype) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact exists_isProjectiveCover A V

end FiniteDimensional

end TauCeti
