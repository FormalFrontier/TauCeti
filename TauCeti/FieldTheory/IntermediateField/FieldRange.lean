/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.FieldTheory.SeparableDegree

/-!
# The degree above the range of a field embedding

An `F`-algebra map `f : K →ₐ[F] L` of fields is injective, so it identifies `K` with the
intermediate field `f.fieldRange`. This file records that the two therefore support the same
degree: `[L : f.fieldRange] = [L : K]`, whenever `L` is a `K`-algebra through `f`.

Both dimensions are needed in practice. A degree over `K` is what an abstract extension
supplies, while a degree over `f.fieldRange` is what any argument comparing two subfields of
`L` — a tower, or a relative degree — must work with, since those subfields are intermediate
fields of one extension rather than separate types.

The `K`-algebra structure on `L` is a hypothesis rather than `f.toRingHom.toAlgebra`, because
the structure the caller already has need only agree with `f`, and for a fixed pair `K`, `L`
different embeddings `f` induce different structures, so none can be registered globally.

## Main results

* `TauCeti.AlgHom.finrank_fieldRange`: `[L : f.fieldRange] = [L : K]`.
* `TauCeti.AlgHom.finiteDimensional_of_fieldRange`: finiteness over the range transfers to the
  source — the same identification read for the property rather than the number.
* `TauCeti.AlgHom.finSepDegree_fieldRange` and `TauCeti.AlgHom.finInsepDegree_fieldRange`: the
  same for the separable and inseparable degrees. These are the `f.fieldRange` cases of the
  general transports in `TauCeti.FieldTheory.SeparableDegree`, which is where a caller holding
  some other surjectively-presented intermediate field should look.
-/

public section

namespace TauCeti.AlgHom

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/-- **The degree above the range of a field embedding equals the degree above its source.**
Stated for an arbitrary `K`-algebra structure on `L` whose structure map is `f`, rather than for
`f.toRingHom.toAlgebra`, so that it applies to a structure the caller already has. -/
theorem finrank_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z) :
    Module.finrank f.fieldRange L = Module.finrank K L := by
  -- transport along `f.equivFieldRange`, the range restriction of `f`, which is the identity
  -- on `L`; both squares commute because `h` says the structure map is `f`
  have hsquare : (algebraMap f.fieldRange L).comp f.equivFieldRange.toRingEquiv.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap K L) := by
    ext z
    exact (_root_.AlgHom.equivFieldRange_apply_coe f z).trans (h z).symm
  exact (Algebra.finrank_eq_of_equiv_equiv f.equivFieldRange.toRingEquiv (RingEquiv.refl L)
    hsquare).symm

/-- **Finiteness above the range of a field embedding transfers to its source.** The range
restriction `f.equivFieldRange` is onto, so `f.fieldRange` is finite over `K`, and the tower
`K → f.fieldRange → L` carries finiteness the rest of the way.

The counterpart of `finrank_fieldRange` for the property rather than the number: a caller who
knows only that `L` is finite over the *range* — which is the form an intermediate field usually
arrives in — gets finiteness over `K` itself, and with it the `Algebra.IsAlgebraic` side condition
the separable and inseparable tower laws take. -/
theorem finiteDimensional_of_fieldRange (f : K →ₐ[F] L) [Algebra K L]
    (h : ∀ z, algebraMap K L z = f z) [FiniteDimensional f.fieldRange L] :
    FiniteDimensional K L :=
  Module.Finite.of_equiv_equiv f.equivFieldRange.toRingEquiv.symm (RingEquiv.refl L) <| by
    ext z
    simpa [h] using (_root_.AlgHom.equivFieldRange_apply_coe f (f.equivFieldRange.symm z)).symm

/-- **The separable degree above the range of a field embedding equals the one above its
source.** The `f.fieldRange` case of `Field.finSepDegree_eq_of_surjective`. -/
theorem finSepDegree_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z) :
    Field.finSepDegree f.fieldRange L = Field.finSepDegree K L := by
  let _ : Algebra K f.fieldRange := (f.equivFieldRange).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K f.fieldRange L :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (h z).trans (_root_.AlgHom.equivFieldRange_apply_coe f z).symm
  exact Field.finSepDegree_eq_of_surjective fun r ↦
    ⟨f.equivFieldRange.symm r, by
      rw [RingHom.algebraMap_toAlgebra]; exact f.equivFieldRange.apply_symm_apply r⟩

/-- **The inseparable degree above the range of a field embedding equals the one above its
source.** The `f.fieldRange` case of `Field.finInsepDegree_eq_of_surjective`. -/
theorem finInsepDegree_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z) :
    Field.finInsepDegree f.fieldRange L = Field.finInsepDegree K L := by
  let _ : Algebra K f.fieldRange := (f.equivFieldRange).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K f.fieldRange L :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (h z).trans (_root_.AlgHom.equivFieldRange_apply_coe f z).symm
  exact Field.finInsepDegree_eq_of_surjective fun r ↦
    ⟨f.equivFieldRange.symm r, by
      rw [RingHom.algebraMap_toAlgebra]; exact f.equivFieldRange.apply_symm_apply r⟩

end TauCeti.AlgHom
