/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Transporting a composition series along a linear equivalence

A linear equivalence `e : M ≃ₗ[R] N` carries the submodules of `M` to the submodules of `N` by the
order isomorphism `Submodule.orderIsoMapComap e`, so it carries a composition series of `M` to one
of `N` (`TauCeti.mapCompositionSeries`) and identifies the two series factor by factor
(`TauCeti.factorEquivMapCompositionSeries`).  This is what makes an invariant read off a composition
series an invariant of the isomorphism class of the ambient module; the Jordan-Hölder multiplicities
of `TauCeti.RingTheory.CompositionSeries.Multiplicity` are the consumer this was written for.

## Main definitions

* `TauCeti.mapCompositionSeries`: the image of a composition series under a linear equivalence of
  the ambient module.
* `TauCeti.factorEquivMapCompositionSeries`: the identification of the factor of a composition
  series at an index with the factor of its image at the same index.
-/

public section

namespace TauCeti

universe u v v'

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v'} [AddCommGroup N] [Module R N]

/-- The image of a composition series of `M` under a linear equivalence `M ≃ₗ[R] N`: the image of
the series under the order isomorphism `Submodule.orderIsoMapComap e`, which preserves coverings.

The body is `@[expose]`d on purpose: `mapCompositionSeries e s i` is definitionally
`Submodule.map ↑e (s i)` — the content of `TauCeti.mapCompositionSeries_apply` below — and the
*statements* of that lemma, of `TauCeti.factorEquivMapCompositionSeries`, and of the transport
lemmas downstream all rest on that definitional identity, which without `@[expose]` would have to be
carried by `Fin.cast`s and dependent rewrites. -/
@[expose] def mapCompositionSeries (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M)) :
    CompositionSeries (Submodule R N) :=
  s.map ⟨fun A => Submodule.map (e : M →ₗ[R] N) A,
    fun h => (apply_covBy_apply_iff (Submodule.orderIsoMapComap e)).mpr h⟩

@[simp]
theorem mapCompositionSeries_apply (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M))
    (i : Fin (s.length + 1)) :
    mapCompositionSeries e s i = Submodule.map (e : M →ₗ[R] N) (s i) :=
  rfl

@[simp]
theorem mapCompositionSeries_length (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeries e s).length = s.length :=
  rfl

@[simp]
theorem head_mapCompositionSeries (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeries e s).head = Submodule.map (e : M →ₗ[R] N) s.head :=
  rfl

@[simp]
theorem last_mapCompositionSeries (e : M ≃ₗ[R] N) (s : CompositionSeries (Submodule R M)) :
    (mapCompositionSeries e s).last = Submodule.map (e : M →ₗ[R] N) s.last :=
  rfl

/-- Restricting a linear equivalence to a submodule carries the trace of another submodule to the
trace of its image.  This is the compatibility that lets a linear equivalence be pushed through the
subquotients of a composition series. -/
theorem map_submoduleMap_comap_subtype (e : M ≃ₗ[R] N) (A B : Submodule R M) :
    Submodule.map (e.submoduleMap B).toLinearMap (Submodule.comap B.subtype A)
      = Submodule.comap (Submodule.map (e : M →ₗ[R] N) B).subtype
          (Submodule.map (e : M →ₗ[R] N) A) := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : M), hx, rfl⟩
  · rintro ⟨a, ha, hay⟩
    obtain ⟨b, hb, hby⟩ := y.2
    have hab : a = b := e.injective (hay.trans hby.symm)
    exact ⟨⟨a, by rw [hab]; exact hb⟩, ha, Subtype.ext hay⟩

/-- A linear equivalence identifies the factors of a composition series with those of its image:
`LinearEquiv.submoduleMap` carries the trace of `s i.castSucc` in `s i.succ` onto the trace of its
image, by `TauCeti.map_submoduleMap_comap_subtype`, so it descends to the subquotients.  Its target
is spelled with `TauCeti.mapCompositionSeries`, which is definitionally `Submodule.map ↑e` applied
termwise. -/
noncomputable def factorEquivMapCompositionSeries (e : M ≃ₗ[R] N)
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (↥(s i.succ) ⧸ Submodule.comap (s i.succ).subtype (s i.castSucc)) ≃ₗ[R]
      (↥(mapCompositionSeries e s i.succ) ⧸
        Submodule.comap (mapCompositionSeries e s i.succ).subtype
          (mapCompositionSeries e s i.castSucc)) :=
  Submodule.Quotient.equiv _ _ (e.submoduleMap (s i.succ))
    (map_submoduleMap_comap_subtype e (s i.castSucc) (s i.succ))

-- Not `@[simp]`: the implicit type arguments of the left-hand side mention
-- `mapCompositionSeries e s i.succ`, which `mapCompositionSeries_apply` rewrites, so the statement
-- is not in simp-normal form and `simpNF` rejects the tag.
theorem factorEquivMapCompositionSeries_apply (e : M ≃ₗ[R] N)
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) (x : ↥(s i.succ)) :
    factorEquivMapCompositionSeries e s i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e.submoduleMap (s i.succ) x) :=
  (rfl)

end TauCeti
