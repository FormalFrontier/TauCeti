/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations

/-!
# Parametrized points of the full-weight type-C carrier

This file records the explicit root-subgroup and torus parameters on algebra-valued points and
their type-C root-character conjugation formula. The carrier scheme and its bundled matrix-valued
points are publicly imported from `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme`.
-/

public section

open scoped Matrix

universe v

namespace TauCeti.SpStd

open LieAlgebra.Symplectic
open scoped TensorProduct
open scoped CategoryTheory.MonObj

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)


section Carrier

open AlgebraicGeometry CategoryTheory

attribute [local instance high] Algebra.toModule

/-- A parametrized numbered root subgroup on points of a value algebra. -/
noncomputable def rootSubgroupParam (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : CommAlgCat ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice n).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupParam (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
    (isNilpotent_rep_rootGenerator n k) A

/-- The split weight torus on points of a value algebra. -/
noncomputable def torusPoints (A : CommAlgCat ℤ) :
    (Fin (n + 1) → Aˣ) →*
      LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice n).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints (lattice n).toAddSubgroup
    (latticeBasis n) (basisWeight n) A

/-- A torus point conjugates a numbered root element by its type-`C` root character. -/
theorem torusPoints_conj_rootSubgroupParam (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : CommAlgCat ℤ) (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    torusPoints n A s * rootSubgroupParam n k A u * (torusPoints n A s)⁻¹ =
      rootSubgroupParam n k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s (rootGeneratorWeight n k) : A) * Multiplicative.toAdd u)) := by
  unfold torusPoints rootSubgroupParam
  exact TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_conj_kostantRootSubgroupParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n)
    (fun j => lie_cartanGenerator_rootGenerator n k j) _ A s u

end Carrier

end TauCeti.SpStd
