/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Reductive
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Reductive
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Semisimple.Basic

/-!
# Semisimple affine group schemes are reductive

Every semisimple affine group scheme of finite type over a field is reductive. The coordinate
Hopf algebra of a semisimple group has no nontrivial connected normal smooth solvable closed
subgroup after extension to an algebraic closure. In particular it has no nontrivial connected
normal smooth unipotent closed subgroup, because a unipotent group is solvable. This is precisely
the normal-subgroup condition in the definition of reductivity.

The coordinate-Hopf-algebra implication is
`TauCeti.semisimpleCommHopfAlgProperty.reductive`. This file transports it through the affine
Hopf/group-scheme anti-equivalence and packages the resulting fully faithful inclusion from
semisimple affine group schemes to reductive affine group schemes. The inclusion leaves the
underlying finite-type affine group scheme and every morphism unchanged.

## Main declarations

* `TauCeti.semisimpleAffineGroupSchemeProperty.reductive`: a semisimple finite-type affine group
  scheme is reductive.
* `TauCeti.semisimpleToReductiveAffineGroupSchemeFunctor`: the fully faithful inclusion of
  semisimple affine group schemes into reductive affine group schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 21.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.

This is the scheme-side structural implication in Layer 6, "Reductive and semisimple groups", of
the ReductiveGroups roadmap. It synchronizes the coordinate and affine-group-scheme models used
by the simply connected and adjoint form constructions.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

namespace semisimpleAffineGroupSchemeProperty

variable {k : Type u} [Field k]
variable {G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)}

/-- Every semisimple finite-type affine group scheme over a field is reductive. -/
theorem reductive (hG : semisimpleAffineGroupSchemeProperty k G) :
    reductiveAffineGroupSchemeProperty k G := by
  rw [reductiveAffineGroupSchemeProperty_iff]
  exact ((semisimpleAffineGroupSchemeProperty_iff k G).mp hG).reductive

end semisimpleAffineGroupSchemeProperty

/-- Semisimplicity is stronger than reductivity for finite-type affine group schemes. -/
theorem semisimpleAffineGroupSchemeProperty_le_reductiveAffineGroupSchemeProperty
    (k : Type u) [Field k] :
    semisimpleAffineGroupSchemeProperty k ≤ reductiveAffineGroupSchemeProperty k :=
  fun _ hG ↦ hG.reductive

/-- The fully faithful inclusion of semisimple affine group schemes into reductive affine group
schemes. It changes only the proof carried by an object of the full subcategory. -/
noncomputable abbrev semisimpleToReductiveAffineGroupSchemeFunctor
    (k : Type u) [Field k] :
    SemisimpleAffineGroupSchemeCat k ⥤ ReductiveAffineGroupSchemeCat k :=
  ObjectProperty.ιOfLE
    (semisimpleAffineGroupSchemeProperty_le_reductiveAffineGroupSchemeProperty k)

end TauCeti
