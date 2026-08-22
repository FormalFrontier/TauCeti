/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Algebra.Lie.Killing.Basic
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# The Killing property under base change

`LieAlgebra.IsKilling R L` says that the Killing form of `L` is nonsingular. This file proves that
for a finite free Lie algebra over an integral domain the property descends along any base change
into a second integral domain, and that an injective base change loses nothing either:

```text
IsKilling A (A ⊗[R] L) → IsKilling R L,  and  IsKilling A (A ⊗[R] L) ↔ IsKilling R L.
```

Both halves are useful. The descent direction transports the Killing property *down* from a
large coefficient ring to a small one, which is what a construction over `ℚ` needs when the
available theorem is stated over an algebraically closed field; it asks nothing of the structure
map, so it also covers reduction `ℤ → 𝔽ₚ`. The ascent direction transports the property *up*,
which is what a base-changed Lie algebra needs before Mathlib's `IsKilling` machinery applies to
it, and there injectivity is genuinely needed.

The mathematical content is entirely in the Gram matrix. Mathlib's `LieModule.traceForm_baseChange`
already says that the Killing form of `A ⊗[R] L` is the base change of the Killing form of `L`, and
`TauCeti.nondegenerate_of_nondegenerate_baseChange` and
`TauCeti.nondegenerate_baseChange_iff` say how a base change of integral domains reflects
and preserves nondegeneracy of a bilinear form on a finite free module. What remains is to read
`IsKilling` as nondegeneracy of the Killing form in both directions;
`TauCeti.isKilling_of_killingForm_nondegenerate` is the direction Mathlib does not already provide.

Nothing here needs the coefficients to be a field, and no characteristic hypothesis appears: the
counterexamples to `HasTrivialRadical → IsKilling` in positive characteristic concern the passage
between semisimplicity and the Killing property, not the base change of the Killing form itself.

## Main declarations

* `TauCeti.isKilling_of_isKilling_baseChange`: the Killing property descends along any base change
  of integral domains, in the form a consumer holding a theorem over a larger coefficient ring
  applies.
* `TauCeti.isKilling_baseChange_iff`: along an injective base change of integral domains the
  descent is an equivalence.

## Roadmap

This is a prerequisite for Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, "**The
Chevalley--Demazure construction.** For each root datum, an explicitly constructed split reductive
group scheme over `ℤ` realizing it, via a Chevalley basis and the Kostant `ℤ`-form of the enveloping
algebra", which is consumed by milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`. The
declaration that will consume it is `TauCeti.IsChevalleySystem`, whose ambient Lie algebra carries
`[LieAlgebra.IsKilling K L]`, applied to `TauCeti.DynkinType.lieAlgebra`. That Lie algebra is
defined over `ℚ`, and
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/LieAlgebra.lean` records that it "is not
asserted to be semisimple: Mathlib derives that from Geck's construction over an algebraically
closed field, and `ℚ` is not one", Mathlib's
`RootPairing.GeckConstruction.instHasTrivialRadical` carrying an `[IsAlgClosed K]` hypothesis. This
file supplies the general half of closing that gap; the remaining half is the identification of
`AlgebraicClosure ℚ ⊗[ℚ] TauCeti.DynkinType.lieAlgebra` with Geck's Lie algebra over
`AlgebraicClosure ℚ`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §5.1, for the Killing
  form and Cartan's criterion.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*, Ch. I, §6, no. 1, for the behaviour of
  the Killing form under extension of scalars.
-/

public section

open TensorProduct

namespace TauCeti

open LieAlgebra LieModule

variable (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L] [Module.Free R L] [Module.Finite R L]
variable [IsDomain A]

/-- **Descent of the Killing property.** A finite free Lie algebra over an integral domain is
Killing as soon as some base change of it into an integral domain is; the structure map is
unrestricted, so this covers reduction of an integral form as well as extension of scalars. -/
theorem isKilling_of_isKilling_baseChange [IsDomain R] [IsKilling A (A ⊗[R] L)] :
    IsKilling R L := by
  rw [isKilling_iff_killingForm_nondegenerate]
  apply nondegenerate_of_nondegenerate_baseChange A _ (Module.Free.chooseBasis R L)
  rw [← traceForm_baseChange R L L A, ← isKilling_iff_killingForm_nondegenerate]
  infer_instance

/-- **The Killing property under an injective base change.** For a finite free Lie algebra over an
integral domain, and an injective structure map into a second integral domain, the base change is
Killing exactly when the original is. -/
@[simp]
theorem isKilling_baseChange_iff [FaithfulSMul R A] :
    IsKilling A (A ⊗[R] L) ↔ IsKilling R L := by
  have : IsDomain R :=
    Function.Injective.isDomain (algebraMap R A) (FaithfulSMul.algebraMap_injective R A)
  -- `killingForm` is Mathlib's reducible abbreviation for the trace form of the adjoint
  -- representation, so `LieModule.traceForm_baseChange` says that the Killing form of `A ⊗[R] L`
  -- is the base change of the Killing form of `L`. `rw` matches up to instances only, so it does
  -- not see the abbreviation; the equation is named here at its `killingForm` spelling.
  have hform : killingForm A (A ⊗[R] L) = (killingForm R L).baseChange A :=
    traceForm_baseChange R L L A
  rw [isKilling_iff_killingForm_nondegenerate, isKilling_iff_killingForm_nondegenerate, hform]
  exact nondegenerate_baseChange_iff _ (Module.Free.chooseBasis R L)

/-! The intended application is a field extension, where every hypothesis above is automatic. -/

example (k K M : Type*) [Field k] [Field K] [Algebra k K] [LieRing M] [LieAlgebra k M]
    [FiniteDimensional k M] [IsKilling K (K ⊗[k] M)] : IsKilling k M :=
  isKilling_of_isKilling_baseChange k K M

end TauCeti
