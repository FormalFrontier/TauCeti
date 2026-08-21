/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Killing
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# The Killing property under base change

`LieAlgebra.IsKilling R L` says that the Killing form of `L` is nonsingular. This file proves that
for a finite free Lie algebra over an integral domain the property neither gains nor loses content
under an injective base change into a second integral domain:

```text
IsKilling A (A ⊗[R] L) ↔ IsKilling R L.
```

Both halves are useful, and the two are proved together because they are the two directions of one
equivalence. The forward direction transports a semisimplicity statement *down* from a large
coefficient ring to a small one, which is what a construction over `ℚ` needs when the available
theorem is stated over an algebraically closed field. The backward direction transports it *up*,
which is what a base-changed Lie algebra needs before Mathlib's `IsKilling` machinery applies to it.

The mathematical content is entirely in the Gram matrix. Mathlib's `LieModule.traceForm_baseChange`
already says that the Killing form of `A ⊗[R] L` is the base change of the Killing form of `L`, and
`TauCeti.nondegenerate_baseChange_iff` says that an injective base change of integral domains
preserves and reflects nondegeneracy of a bilinear form on a finite free module. What remains is to
read `IsKilling` as nondegeneracy of the Killing form in both directions;
`TauCeti.isKilling_of_killingForm_nondegenerate` is the direction Mathlib does not already provide.

Nothing here needs the coefficients to be a field, and no characteristic hypothesis appears: the
counterexamples to `HasTrivialRadical → IsKilling` in positive characteristic concern the passage
between semisimplicity and the Killing property, not the base change of the Killing form itself.

## Main declarations

* `TauCeti.isKilling_of_killingForm_nondegenerate`: a Lie algebra whose Killing form is
  nondegenerate is Killing, the converse of `LieAlgebra.IsKilling.killingForm_nondegenerate`.
* `TauCeti.isKilling_baseChange_iff`: the Killing property transfers in both directions along an
  injective base change of integral domains.
* `TauCeti.isKilling_of_isKilling_baseChange`: the descent direction, in the form a consumer holding
  a theorem over a larger coefficient ring applies.

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
variable [LieRing L] [LieAlgebra R L]

/-- A Lie algebra whose Killing form is nondegenerate is Killing.

This is the converse of `LieAlgebra.IsKilling.killingForm_nondegenerate`, and the two together say
that `LieAlgebra.IsKilling` is exactly nondegeneracy of the Killing form. -/
theorem isKilling_of_killingForm_nondegenerate (h : (killingForm R L).Nondegenerate) :
    IsKilling R L := by
  refine ⟨(LieSubmodule.eq_bot_iff _).mpr fun x hx ↦ h.1 x fun y ↦ ?_⟩
  simp only [LieIdeal.mem_killingCompl, LieSubmodule.mem_top, forall_true_left] at hx
  rw [traceForm_comm R L L x y]
  exact hx y

variable [IsDomain R] [IsDomain A] [FaithfulSMul R A] [Module.Free R L] [Module.Finite R L]

/-- **The Killing property under base change.** For a finite free Lie algebra over an integral
domain, and an injective structure map into a second integral domain, the base change is Killing
exactly when the original is. -/
theorem isKilling_baseChange_iff : IsKilling A (A ⊗[R] L) ↔ IsKilling R L := by
  -- `killingForm` is Mathlib's abbreviation for the trace form of the adjoint representation, so
  -- `LieModule.traceForm_baseChange` states exactly this.
  have hform : killingForm A (A ⊗[R] L) = (killingForm R L).baseChange A :=
    traceForm_baseChange R L L A
  have key : (killingForm A (A ⊗[R] L)).Nondegenerate ↔ (killingForm R L).Nondegenerate := by
    rw [hform]
    exact nondegenerate_baseChange_iff _ (Module.Free.chooseBasis R L)
  exact ⟨fun _ ↦ isKilling_of_killingForm_nondegenerate R L
      (key.mp (IsKilling.killingForm_nondegenerate A (A ⊗[R] L))),
    fun _ ↦ isKilling_of_killingForm_nondegenerate A (A ⊗[R] L)
      (key.mpr (IsKilling.killingForm_nondegenerate R L))⟩

/-- **Descent of the Killing property.** A finite free Lie algebra over an integral domain is
Killing as soon as some injective base change of it into an integral domain is. -/
theorem isKilling_of_isKilling_baseChange [IsKilling A (A ⊗[R] L)] : IsKilling R L :=
  (isKilling_baseChange_iff R A L).mp inferInstance

/-! The intended application is a field extension, where every hypothesis above is automatic. -/

example (k K M : Type*) [Field k] [Field K] [Algebra k K] [LieRing M] [LieAlgebra k M]
    [FiniteDimensional k M] [IsKilling K (K ⊗[k] M)] : IsKilling k M :=
  isKilling_of_isKilling_baseChange k K M

end TauCeti
