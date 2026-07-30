/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# The double centralizer theorem

Mathlib's Jacobson density theorem (`Module.Finite.toModuleEnd_moduleEnd_surjective`) says that for
a semisimple `R`-module `M` which is finite over its endomorphism ring `D = Module.End R M`, the
natural map `R → Module.End D M` is **surjective**. This file sharpens that to a **bijection** for
a faithful such `M`, so that `R` is recovered from its action: `R ≃+* Module.End D M`.

The half that is missing upstream is injectivity, and injectivity is exactly faithfulness of `M`.
Faithfulness is not automatic, but it is automatic in the case the structure theory cares about:
a nontrivial module over a **simple** ring is faithful, because the elements killing `M` form a
two-sided ideal not containing `1`. So over a simple ring every simple module finite over `D`
gives `R ≃+* Module.End D M`, which is the Wedderburn presentation of a simple ring in
module-internal form -- no ambient base field is involved, only finiteness over `D`.

## Main results

* `TauCeti.faithfulSMul_of_isSimpleRing`: a nontrivial module over a simple ring is faithful.
* `TauCeti.toModuleEnd_bijective`: **the double centralizer theorem**. For a faithful semisimple
  module `M` finite over `D = Module.End R M`, the map `R → Module.End D M` is bijective;
  `TauCeti.ringEquivEndEnd` packages it as a ring isomorphism, and
  `TauCeti.algEquivEndEnd` as an algebra isomorphism over a compatible base ring.
* `TauCeti.toModuleEnd_bijective_of_isSimpleRing`: the specialization to a simple module over a
  simple ring, where faithfulness is automatic.
* `TauCeti.exists_smul_eq_of_linearIndependent`: the Jacobson-Chevalley form of density. Over a
  simple module, a single element of `R` carries any `D`-linearly independent family to an
  arbitrary family of targets.
* `TauCeti.finite_end_of_smulCommClass`: the finiteness hypothesis is supplied by finiteness over
  any commutative base ring acting compatibly, which is how it arises for a finite-dimensional
  algebra; `TauCeti.algEquivEndEndOfIsSimpleRing` assembles that case.

## Implementation notes

The finiteness hypothesis is `Module.Finite (Module.End R M) M`, finiteness over the endomorphism
ring itself, rather than finite-dimensionality over an unrelated base ring. That is the hypothesis
density actually needs, and `TauCeti.finite_end_of_smulCommClass` derives it from a base-ring
hypothesis when one is available.

A faithful simple module makes `R` a *primitive* ring, not necessarily a simple one, so
`TauCeti.toModuleEnd_bijective` is genuinely more general than its simple-ring corollary. It is
also stated for a merely semisimple `M`, which is all that Mathlib's surjectivity needs.

## References

This implements the Layer 3 target `toModuleEnd_bijective` of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
together with its Jacobson-Chevalley corollary. See T. Y. Lam, *A First Course in Noncommutative
Rings*, GTM 131, Chapter 4, and N. Jacobson, *Basic Algebra II*, Chapter 4.
-/

public section

namespace TauCeti

open Module

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Faithfulness over a simple ring -/

/-- A nontrivial module over a simple ring is faithful: the elements of `R` killing `M` are the
kernel of a ring homomorphism out of `R`, a two-sided ideal not containing `1`, hence `⊥`. -/
theorem faithfulSMul_of_isSimpleRing [IsSimpleRing R] [Nontrivial M] : FaithfulSMul R M where
  eq_of_smul_eq_smul {_ _} h :=
    (Module.toModuleEnd (Module.End R M) M (S := R)).injective (LinearMap.ext h)

/-- Over a simple ring the annihilator of a nontrivial module vanishes. -/
theorem annihilator_eq_bot_of_isSimpleRing [IsSimpleRing R] [Nontrivial M] :
    Module.annihilator R M = ⊥ :=
  Module.annihilator_eq_bot.mpr faithfulSMul_of_isSimpleRing

/-! ### The double centralizer theorem -/

section Density

variable (R M)

/-- **The double centralizer theorem.** Let `M` be a faithful semisimple `R`-module which is finite
over its endomorphism ring `D = Module.End R M`. Then the natural map `R → Module.End D M` is
bijective: `R` is exactly the ring of `D`-linear endomorphisms of `M`.

This sharpens Mathlib's `Module.Finite.toModuleEnd_moduleEnd_surjective` from surjectivity to
bijectivity; the extra input is faithfulness, which is what makes the map injective. -/
theorem toModuleEnd_bijective [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    Function.Bijective (Module.toModuleEnd (Module.End R M) M (S := R)) :=
  ⟨fun _ _ h ↦ eq_of_smul_eq_smul (α := M) fun m ↦ LinearMap.congr_fun h m,
    Module.Finite.toModuleEnd_moduleEnd_surjective⟩

/-- The double centralizer theorem as a ring isomorphism: a faithful semisimple module finite over
its endomorphism ring `D` identifies `R` with `Module.End D M`. -/
noncomputable def ringEquivEndEnd [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    R ≃+* Module.End (Module.End R M) M :=
  RingEquiv.ofBijective _ (toModuleEnd_bijective R M)

variable {R M}

@[simp]
theorem ringEquivEndEnd_apply [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (r : R) (m : M) :
    ringEquivEndEnd R M r m = r • m := by
  simp [ringEquivEndEnd]

@[simp]
theorem smul_ringEquivEndEnd_symm [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (f : Module.End (Module.End R M) M) (m : M) :
    (ringEquivEndEnd R M).symm f • m = f m := by
  rw [← ringEquivEndEnd_apply ((ringEquivEndEnd R M).symm f) m, RingEquiv.apply_symm_apply]

variable (R M)

/-- The double centralizer isomorphism as an isomorphism of `K`-algebras, for a commutative base
ring `K` acting on `M` compatibly with `R`. -/
noncomputable def algEquivEndEnd (K : Type*) [CommRing K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] :
    R ≃ₐ[K] Module.End (Module.End R M) M :=
  AlgEquiv.ofRingEquiv (f := ringEquivEndEnd R M) fun k ↦ by
    ext m
    rw [ringEquivEndEnd_apply, algebraMap_smul, Module.algebraMap_end_apply]

variable {R M}

@[simp]
theorem algEquivEndEnd_apply (K : Type*) [CommRing K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [IsSemisimpleModule R M] [FaithfulSMul R M]
    [Module.Finite (Module.End R M) M] (r : R) (m : M) :
    algEquivEndEnd R M K r m = r • m :=
  ringEquivEndEnd_apply r m

variable (R M)

/-- **The double centralizer theorem for a simple ring.** Over a simple ring every simple module is
automatically faithful, so a simple module finite over its endomorphism ring `D` presents `R` as
`Module.End D M`. This is Wedderburn's theorem for a simple ring, stated without reference to any
base ring. -/
theorem toModuleEnd_bijective_of_isSimpleRing [IsSimpleRing R] [IsSimpleModule R M]
    [Module.Finite (Module.End R M) M] :
    Function.Bijective (Module.toModuleEnd (Module.End R M) M (S := R)) :=
  have := IsSimpleModule.nontrivial R M
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  toModuleEnd_bijective R M

end Density

/-! ### Jacobson-Chevalley density -/

/-- **Jacobson-Chevalley density.** For a simple module `M` finite over `D = Module.End R M`, a
`D`-linearly independent family in `M` can be carried to an arbitrary family of targets by a single
scalar from `R`.

Linear independence is essential: a `D`-linear relation among the `v i` is inherited by the
`r • v i`, so the targets could not be arbitrary. -/
theorem exists_smul_eq_of_linearIndependent [IsSimpleModule R M]
    [Module.Finite (Module.End R M) M] {ι : Type*} {v : ι → M}
    (hv : LinearIndependent (Module.End R M) v) (w : ι → M) :
    ∃ r : R, ∀ i, r • v i = w i := by
  classical
  -- Extend `v` to a `D`-linear map `f` with the prescribed values, by splitting off a complement
  -- of the span of `v`; then density realizes `f` by a scalar.
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span (Module.End R M) (Set.range v))
  set f : Module.End (Module.End R M) M :=
    ((Basis.span hv).constr ℕ w).comp (Submodule.projectionOnto _ q hq) with hf
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) f
  refine ⟨r, fun i ↦ ?_⟩
  have hmem : v i ∈ Submodule.span (Module.End R M) (Set.range v) :=
    Submodule.subset_span ⟨i, rfl⟩
  have hproj := Submodule.projectionOnto_apply_left hq (⟨v i, hmem⟩ :
    Submodule.span (Module.End R M) (Set.range v))
  have hvi : f (v i) = w i := by
    rw [hf, LinearMap.comp_apply, hproj,
      show (⟨v i, hmem⟩ : Submodule.span (Module.End R M) (Set.range v)) = (Basis.span hv) i from
        Subtype.ext (Basis.coe_span_apply hv i).symm,
      Basis.constr_basis]
  rw [← hvi, ← hr]
  rfl

/-! ### Supplying the finiteness hypothesis -/

/-- The finiteness hypothesis of the density theorem, `Module.Finite (Module.End R M) M`, follows
from finiteness over any commutative base ring `K` whose action on `M` commutes with that of `R`:
the scalars from `K` are themselves `R`-linear endomorphisms, so a `K`-generating set of `M`
generates it over `Module.End R M`.

In particular a finite-dimensional module over an algebra is finite over its endomorphism ring,
which is how the hypothesis is met in the finite-dimensional-algebra setting. -/
theorem finite_end_of_smulCommClass (K : Type*) [CommSemiring K] [Module K M]
    [SMulCommClass R K M] [Module.Finite K M] :
    Module.Finite (Module.End R M) M :=
  .of_restrictScalars_finite K (Module.End R M) M

variable (R M)

/-- **The double centralizer theorem for a finite module over a simple algebra.** If `R` is a
simple `K`-algebra and `M` a simple `R`-module which is finite as a `K`-module, then `M` presents
`R` as the algebra of `D`-linear endomorphisms of `M`, where `D = Module.End R M`. This is the form
in which Layer 3 of the roadmap is consumed by the central-simple theory. -/
noncomputable def algEquivEndEndOfIsSimpleRing (K : Type*) [CommRing K] [Algebra K R] [Module K M]
    [IsScalarTower K R M] [Module.Finite K M] [IsSimpleRing R] [IsSimpleModule R M] :
    R ≃ₐ[K] Module.End (Module.End R M) M :=
  have := IsSimpleModule.nontrivial R M
  have := faithfulSMul_of_isSimpleRing (R := R) (M := M)
  have := finite_end_of_smulCommClass (R := R) (M := M) K
  algEquivEndEnd R M K

end TauCeti
