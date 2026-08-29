/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Transporting a composition series along a linear map

An injective linear map `f : M →ₗ[R] N` carries the submodules of `M` to submodules of `N` and
preserves coverings (`Submodule.map_covBy_of_injective`), and a surjective one pulls the submodules
of `N` back and preserves coverings (`Submodule.comap_covBy_of_surjective`), so each carries a
composition series to a composition series: `TauCeti.mapCompositionSeriesOfInjective` and
`TauCeti.comapCompositionSeriesOfSurjective`.  That the transported series keeps the *factors*
themselves, and not just their number, is the identification of subquotients
`TauCeti.mapSubquotientEquivOfInjective`, respectively
`TauCeti.comapSubquotientEquivOfSurjective`, of `TauCeti.Algebra.Module.Submodule.Quotient`.

Taking `f` to be a linear equivalence, this is what makes an invariant read off a composition
series an invariant of the isomorphism class of the ambient module; the Jordan-Hölder
multiplicities of `TauCeti.RingTheory.CompositionSeries.Multiplicity` are the consumer this was
written for, and `TauCeti.RingTheory.CompositionSeries.Additivity` is the consumer that needs the
two one-sided forms, for the inclusion of a submodule and the projection onto a quotient.

## Main definitions

* `TauCeti.mapCompositionSeriesOfInjective`: the image of a composition series under an injective
  linear map.
* `TauCeti.comapCompositionSeriesOfSurjective`: the preimage of a composition series under a
  surjective linear map.

## References

The two transports are exactly the anonymous `let`s inside the proof of Mathlib's
`Module.length_eq_add_of_exact` (`Mathlib/RingTheory/Length.lean`, by Andrew Yang), packaged here
as named definitions with an API so that they can be shown to preserve the factors themselves and
not just their number.
-/

public section

namespace TauCeti

universe u v v'

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v'} [AddCommGroup N] [Module R N]

/-- The image of a composition series of `M` under an injective linear map `f : M →ₗ[R] N`. -/
def mapCompositionSeriesOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) : CompositionSeries (Submodule R N) :=
  s.map ⟨fun A => A.map f, Submodule.map_covBy_of_injective hf⟩

@[simp]
theorem mapCompositionSeriesOfInjective_length (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).length = s.length :=
  (rfl)

/-- The term of the transported series at an index is the image of the term of `s` at that same
index, transported along `TauCeti.mapCompositionSeriesOfInjective_length`. -/
@[simp]
theorem mapCompositionSeriesOfInjective_apply (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M))
    (i : Fin ((mapCompositionSeriesOfInjective f hf s).length + 1)) :
    mapCompositionSeriesOfInjective f hf s i =
      (s (i.cast (by rw [mapCompositionSeriesOfInjective_length]))).map f :=
  (rfl)

@[simp]
theorem head_mapCompositionSeriesOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).head = s.head.map f :=
  (rfl)

@[simp]
theorem last_mapCompositionSeriesOfInjective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeriesOfInjective f hf s).last = s.last.map f :=
  (rfl)

/-- The preimage of a composition series of `N` under a surjective linear map `f : M →ₗ[R] N`. -/
def comapCompositionSeriesOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) : CompositionSeries (Submodule R M) :=
  s.map ⟨fun A => A.comap f, Submodule.comap_covBy_of_surjective hf⟩

@[simp]
theorem comapCompositionSeriesOfSurjective_length (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) :
    (comapCompositionSeriesOfSurjective f hf s).length = s.length :=
  (rfl)

/-- The term of the transported series at an index is the preimage of the term of `s` at that same
index, transported along `TauCeti.comapCompositionSeriesOfSurjective_length`. -/
@[simp]
theorem comapCompositionSeriesOfSurjective_apply (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N))
    (i : Fin ((comapCompositionSeriesOfSurjective f hf s).length + 1)) :
    comapCompositionSeriesOfSurjective f hf s i =
      (s (i.cast (by rw [comapCompositionSeriesOfSurjective_length]))).comap f :=
  (rfl)

@[simp]
theorem head_comapCompositionSeriesOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) :
    (comapCompositionSeriesOfSurjective f hf s).head = s.head.comap f :=
  (rfl)

@[simp]
theorem last_comapCompositionSeriesOfSurjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (s : CompositionSeries (Submodule R N)) :
    (comapCompositionSeriesOfSurjective f hf s).last = s.last.comap f :=
  (rfl)

end TauCeti
