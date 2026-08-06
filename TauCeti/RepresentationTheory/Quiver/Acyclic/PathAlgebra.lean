/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra

/-!
# The path algebra of an acyclic quiver

A finite quiver with finitely many arrows between any two vertices has finitely many paths when it
is acyclic, and the paths are a basis of its path algebra; so the path algebra of such a quiver is
finite-dimensional over a division ring.

This is the only place the generic path algebra of
`TauCeti.RepresentationTheory.Quiver.PathAlgebra` meets acyclicity, which is why it is a module of
its own: the path algebra itself needs nothing from the theory of acyclic quivers.

## Main results

* `TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic`: the path algebra of a finite acyclic
  quiver with finite arrow types is finite-dimensional.
* `TauCeti.vertexIdempotent_mul_mul_vertexIdempotent`: over an acyclic quiver `eᵥ f eᵥ` is the
  coefficient of `f` on the trivial path at `v`, times `eᵥ`, the corner ring `eᵥ kQ eᵥ` being a
  copy of `k`. This is what makes the trivial paths visible to a two-sided ideal.

## References

This file implements the finite-dimensionality half of the path-algebra part of Layer 0 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

/-- The path algebra of a finite acyclic quiver is finite-dimensional. -/
theorem finiteDimensional_pathAlgebra_of_isAcyclic (k : Type w) (Q : Type u) [DivisionRing k]
    [Quiver.{v} Q] [Finite Q] [∀ a b : Q, Finite (a ⟶ b)] (h : Quiver.IsAcyclic Q) :
    FiniteDimensional k (pathAlgebra k Q) :=
  letI := finite_paths_of_isAcyclic h
  module_finite_pathAlgebra k Q

section CornerRing

open PathAlgebra

variable {k : Type w} {Q : Type u} [Semiring k] [Quiver.{v} Q]

/-- **Conjugating by a vertex idempotent reads off a coordinate.** Over an acyclic quiver the only
path from `v` to `v` is the trivial one, so `eᵥ f eᵥ` is the coordinate of `f` on that path, times
`eᵥ`. -/
theorem vertexIdempotent_mul_mul_vertexIdempotent (h : Quiver.IsAcyclic Q) (v : Q)
    (f : pathAlgebra k Q) :
    vertexIdempotent k v * f * vertexIdempotent k v
      = (pathAlgebraBasis k Q).repr f ⟨v, v, Quiver.Path.nil⟩ • vertexIdempotent k v := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [mul_add, add_mul, hf, hg, map_add, Finsupp.add_apply, add_smul]
  | single x c =>
    obtain ⟨a, b, p⟩ := x
    rw [pathAlgebraBasis_repr_single, vertexIdempotent_eq_single, smul_single, mul_one]
    by_cases hb : v = b
    · subst hb
      rw [single_mul_single_of_comp (p := Quiver.Path.nil) (q := p) 1 c, one_mul,
        Quiver.Path.comp_nil]
      by_cases ha : v = a
      · subst ha
        obtain rfl := h.eq_nil p
        rw [single_mul_single_of_comp (p := Quiver.Path.nil) (q := Quiver.Path.nil) c 1, mul_one,
          Quiver.Path.comp_nil, Finsupp.single_eq_same]
      · have hne : (⟨a, v, p⟩ : Quiver.TotalPath Q) ≠ ⟨v, v, Quiver.Path.nil⟩ := by
          intro heq
          have hav : a = v := congrArg (fun z : Quiver.TotalPath Q => z.1) heq
          exact ha hav.symm
        rw [single_mul_single_of_not_composable
          (x := ⟨a, v, p⟩) (y := ⟨v, v, Quiver.Path.nil⟩) ha c 1,
          Finsupp.single_eq_of_ne' hne, single_zero]
    · have hne : (⟨a, b, p⟩ : Quiver.TotalPath Q) ≠ ⟨v, v, Quiver.Path.nil⟩ := by
        intro heq
        have hbv : b = v := congrArg (fun z : Quiver.TotalPath Q => z.2.1) heq
        exact hb hbv.symm
      rw [single_mul_single_of_not_composable
        (x := ⟨v, v, Quiver.Path.nil⟩) (y := ⟨a, b, p⟩) (fun hbv => hb hbv.symm) 1 c, zero_mul,
        Finsupp.single_eq_of_ne' hne, single_zero]

end CornerRing

end TauCeti
