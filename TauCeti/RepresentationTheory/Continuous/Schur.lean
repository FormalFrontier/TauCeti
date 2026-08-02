/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schur's lemma for continuous intertwiners

Schur's lemma has two halves. Between inequivalent irreducible representations every intertwiner
vanishes; and, over an algebraically closed field, every self-intertwiner of a finite-dimensional
irreducible representation is scalar. This file records both halves for Mathlib's bundled
continuous intertwining maps, which is the form the analytic theory uses.

No topology on the acting monoid and no invariant measure are involved: both proofs forget the
continuity of the intertwiner and apply Mathlib's algebraic Schur lemma, in the form of the
instance `Representation.IsIrreducible.instSubsingletonIntertwiningMap` for the vanishing half and
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed` for the scalar
half.

Forgetting continuity is only sound in the direction "continuous intertwiner ↦ intertwiner"; the
hypothesis of the vanishing half is inequivalence as *continuous* representations, which is the
weaker of the two hypotheses to discharge. `TauCeti.ContRepresentation.nonempty_equiv_iff` is what
closes the gap: in finite dimensions over a complete field the two notions of equivalence agree,
because every linear map out of a finite-dimensional normed space is continuous.

## Main statements

* `TauCeti.ContRepresentation.nonempty_equiv_iff`: two finite-dimensional continuous
  representations are equivalent as continuous representations if and only if they are equivalent
  as abstract representations.
* `TauCeti.ContRepresentation.eq_zero_of_isEmpty_equiv`: every continuous intertwiner between
  inequivalent irreducible finite-dimensional representations is zero.
* `TauCeti.ContRepresentation.exists_eq_smul_one_of_irreducible`: every continuous self-intertwiner
  of an irreducible finite-dimensional representation over an algebraically closed normed field is
  scalar.

The mathematical argument follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

namespace TauCeti

namespace ContRepresentation

section Vanishing

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

variable {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- **Continuity is automatic for finite-dimensional representations.** Two finite-dimensional
continuous representations over a complete field are equivalent as continuous representations
exactly when their underlying abstract representations are equivalent.

The forward direction forgets continuity. The reverse direction is where the finite-dimensionality
is used: a linear equivalence of finite-dimensional normed spaces is a homeomorphism, so an
abstract equivalence carries no extra data. -/
theorem nonempty_equiv_iff :
    Nonempty (_root_.ContRepresentation.Equiv π ρ) ↔
      Nonempty (Representation.Equiv π.toRepresentation ρ.toRepresentation) := by
  constructor
  · rintro ⟨φ⟩
    refine ⟨Representation.Equiv.mk φ.toContinuousLinearEquiv.toLinearEquiv fun g ↦ ?_⟩
    ext v
    exact congr($(φ.isIntertwining g) v)
  · rintro ⟨φ⟩
    refine ⟨_root_.ContRepresentation.Equiv.mk φ.toLinearEquiv.toContinuousLinearEquiv fun g ↦ ?_⟩
    ext v
    exact congr($(φ.isIntertwining' g) v)

/-- **Schur's lemma, vanishing half.** A continuous intertwiner between inequivalent irreducible
finite-dimensional continuous representations is zero.

Inequivalence is asked of the continuous representations, which by `nonempty_equiv_iff` is the same
condition as inequivalence of the underlying abstract representations. No hypothesis on the field
beyond completeness is needed: this half of Schur's lemma does not need eigenvalues, so it does not
need algebraic closedness. -/
theorem eq_zero_of_isEmpty_equiv (hπ : Representation.IsIrreducible π.toRepresentation)
    (hρ : Representation.IsIrreducible ρ.toRepresentation)
    (hne : IsEmpty (_root_.ContRepresentation.Equiv π ρ)) (f : ContIntertwiningMap π ρ) :
    f = 0 := by
  letI : Representation.IsIrreducible π.toRepresentation := hπ
  letI : Representation.IsIrreducible ρ.toRepresentation := hρ
  haveI : IsEmpty (Representation.Equiv π.toRepresentation ρ.toRepresentation) :=
    ⟨fun φ ↦ hne.false (nonempty_equiv_iff.2 ⟨φ⟩).some⟩
  exact ContIntertwiningMap.toIntertwiningMap_injective (Subsingleton.elim _ _)

/-- The underlying continuous linear map of a continuous intertwiner between inequivalent
irreducibles vanishes. This is the form in which the Schur orthogonality relations consume
`eq_zero_of_isEmpty_equiv`. -/
theorem toContinuousLinearMap_eq_zero_of_isEmpty_equiv
    (hπ : Representation.IsIrreducible π.toRepresentation)
    (hρ : Representation.IsIrreducible ρ.toRepresentation)
    (hne : IsEmpty (_root_.ContRepresentation.Equiv π ρ)) (f : ContIntertwiningMap π ρ) :
    f.toContinuousLinearMap = 0 := by
  rw [eq_zero_of_isEmpty_equiv hπ hρ hne f]
  rfl

end Vanishing

section Scalar

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

end Scalar

end ContRepresentation

end TauCeti
