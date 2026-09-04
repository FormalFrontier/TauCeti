/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Over

/-!
# Transporting ideals along algebra equivalences

An algebra equivalence preserves the contraction of an ideal to the base ring. This file records
that compatibility for ideals in commutative algebras.
-/

public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **Mapping an ideal along an algebra equivalence preserves its contraction.** For an
`R`-algebra equivalence `e : S ≃ₐ[R] T`, the ideal `Q.map e` of `T` has the same contraction to
`R` as `Q`. -/
@[simp]
theorem under_mapAlgEquiv (e : S ≃ₐ[R] T) (Q : Ideal S) :
    (Q.map e).under R = Q.under R := by
  rw [under_def, under_def]
  -- `Ideal.map` is applied via `RingHomClass`, so the `AlgEquiv` and `RingEquiv`
  -- coercions give syntactically different terms; they coincide definitionally
  -- (Mathlib proves the underlying `RingHom` equality
  -- `AlgEquiv.toRingEquiv_toRingHom` itself by `rfl`), hence this `rfl`.
  have hmap : Q.map e = Q.map (e.toRingEquiv : S →+* T) := rfl
  rw [hmap, map_comap_of_equiv]
  ext x
  simp only [mem_comap]
  rw [← e.commutes]
  simp

end Ideal
