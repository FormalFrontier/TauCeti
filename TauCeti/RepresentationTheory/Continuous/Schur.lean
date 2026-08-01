/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Schur's lemma for continuous self-intertwiners

Over an algebraically closed field, every self-intertwiner of a finite-dimensional irreducible
representation is scalar. This file records that statement for Mathlib's bundled continuous
intertwining maps, which is the form the analytic theory uses.

No topology on the acting monoid and no invariant measure are involved: the proof forgets the
continuity of the intertwiner and applies Mathlib's algebraic Schur lemma
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`.

## Main statements

* `TauCeti.ContRepresentation.exists_eq_smul_one_of_irreducible`: every continuous self-intertwiner
  of an irreducible finite-dimensional representation over an algebraically closed normed field is
  scalar.

The mathematical argument follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

namespace TauCeti

namespace ContRepresentation

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [IsAlgClosed 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable (π : ContRepresentation 𝕜 G V)

/-- Every continuous self-intertwiner of an irreducible finite-dimensional representation over an
algebraically closed normed field is a scalar multiple of the identity. -/
theorem exists_eq_smul_one_of_irreducible (hirr : Representation.IsIrreducible π.toRepresentation)
    (f : ContIntertwiningMap π π) :
    ∃ c : 𝕜, f = c • 1 := by
  letI : Representation.IsIrreducible π.toRepresentation := hirr
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := π.toRepresentation)).2 f.toIntertwiningMap
  refine ⟨c, ContIntertwiningMap.toIntertwiningMap_injective ?_⟩
  -- Forgetting continuity is compatible with scalar multiplication and with the identity, so it
  -- sends the scalar continuous intertwiner `c • 1` to the algebra map's value at `c`.
  have hsmul : (c • (1 : ContIntertwiningMap π π)).toIntertwiningMap
      = c • (1 : ContIntertwiningMap π π).toIntertwiningMap := rfl
  have hone : (1 : ContIntertwiningMap π π).toIntertwiningMap
      = (1 : Representation.IntertwiningMap π.toRepresentation π.toRepresentation) := rfl
  simp only [hsmul, hone]
  rw [← Algebra.algebraMap_eq_smul_one, hc]

end ContRepresentation

end TauCeti
