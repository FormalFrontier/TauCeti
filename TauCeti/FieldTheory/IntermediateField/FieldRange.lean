/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

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

end TauCeti.AlgHom
