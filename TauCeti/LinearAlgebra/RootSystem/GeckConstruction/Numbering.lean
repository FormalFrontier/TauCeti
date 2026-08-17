/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis
import TauCeti.LinearAlgebra.RootSystem.Isomorphism

/-!
# The simple-root numbering in Geck's construction

Mathlib constructs an equivalence between a reduced irreducible root system and the root system
of its Geck matrix Lie algebra. The equivalence is obtained from equality of the two Cartan
matrices. This file identifies its otherwise abstract index equivalence on the chosen simple
roots: the simple root indexed by `i` is carried to the simple weight indexed by `i` in Geck's
distinguished Lie-algebra basis.

This pins the original numbering through the construction. In particular, a downstream pinning
can attach its simple root subgroup to the same index that names the corresponding root in the
input root datum, without choosing a second relabelling.

## Main results

* `TauCeti.geckEquivRootSystem_indexEquiv_apply`: the root-index equivalence preserves the chosen
  simple-root index.
* `TauCeti.geckEquivRootSystem_weightMap_root`: the weight map sends a chosen simple
  root to the corresponding simple weight.
* `TauCeti.geckEquivRootSystem_coweightEquiv_symm_coroot`: the covariant inverse coweight
  equivalence sends the input simple coroot to the corresponding Geck simple coroot.
* `TauCeti.map_geckEquivRootSystem`: transporting the input base along the equivalence gives
  Geck's distinguished base exactly.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§18, 25.

This supplies the numbered Chevalley-basis input to Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. That layer constructs the pinned group schemes whose
numbered simple root subgroups are consumed by milestone L0 of the `CFSGStatement` roadmap.
-/

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling
open _root_.RootPairing.GeckConstruction

noncomputable section

universe u v w

variable {ι : Type u} {K : Type v} {M : Type w} {N : Type*}
  [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [IsAlgClosed K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsReduced] [P.IsCrystallographic]
  [P.IsIrreducible] [P.IsRootSystem] (b : P.Base)

/-- Mathlib's equivalence from the input root system to the root system of Geck's Lie algebra
sends an input simple-root index to the simple-weight index with the same chosen-base label. -/
@[simp] public theorem geckEquivRootSystem_indexEquiv_apply (i : b.support) :
    (equivRootSystem b).indexEquiv i = (basis b).baseSupportEquiv i := by
  simpa only [equivRootSystem] using
    equivOfCartanMatrixEq_indexEquiv_apply b (basis b).base
      (basis b).baseSupportEquiv (by simp [(basis b).cartanMatrix_base_eq]) i

/-- The inverse of Mathlib's root-index equivalence sends the corresponding Geck simple-weight
index back to the input simple-root index. -/
@[simp] public theorem geckEquivRootSystem_indexEquiv_symm_apply (i : b.support) :
    (equivRootSystem b).indexEquiv.symm ((basis b).baseSupportEquiv i) = i := by
  rw [← geckEquivRootSystem_indexEquiv_apply b i]
  exact (equivRootSystem b).indexEquiv.symm_apply_apply i

/-- The weight map underlying Mathlib's Geck root-system equivalence sends each chosen
simple root to the corresponding simple weight of the distinguished Lie-algebra basis. -/
@[simp] public theorem geckEquivRootSystem_weightMap_root (i : b.support) :
    (equivRootSystem b).toHom.weightMap (P.root i) =
      (rootSystem (cartanSubalgebra' b)).root ((basis b).baseSupportEquiv i) := by
  simpa only [equivRootSystem] using
    equivOfCartanMatrixEq_weightMap_root b (basis b).base
      (basis b).baseSupportEquiv (by simp [(basis b).cartanMatrix_base_eq]) i

/-- The covariant inverse of the coweight equivalence sends the input simple coroot to the
corresponding simple coroot of Geck's Lie algebra. -/
@[simp] public theorem geckEquivRootSystem_coweightEquiv_symm_coroot (i : b.support) :
    (_root_.RootPairing.Equiv.coweightEquiv P (rootSystem (cartanSubalgebra' b))
        (equivRootSystem b)).symm (P.coroot i) =
      (rootSystem (cartanSubalgebra' b)).coroot ((basis b).baseSupportEquiv i) := by
  simpa only [equivRootSystem] using
    equivOfCartanMatrixEq_coweightEquiv_symm_coroot b (basis b).base
      (basis b).baseSupportEquiv (by simp [(basis b).cartanMatrix_base_eq]) i

/-- Mathlib's Geck root-system equivalence is an equivalence of based root systems: transporting
the chosen input base along it gives the distinguished base of Geck's Lie-algebra basis. -/
@[simp] public theorem map_geckEquivRootSystem :
    b.map (equivRootSystem b) = (basis b).base := by
  simpa only [equivRootSystem] using
    map_equivOfCartanMatrixEq b (basis b).base (basis b).baseSupportEquiv
      (by simp [(basis b).cartanMatrix_base_eq])

end

end TauCeti
