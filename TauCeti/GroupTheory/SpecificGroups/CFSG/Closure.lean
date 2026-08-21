/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Algebraic closures for finite groups of Lie type

This file attaches to every valid Lie-type index the algebraically closed field over which its
ambient pinned algebraic group will be evaluated. The field is Mathlib's algebraic closure of the
prime field in the characteristic recorded by the index. Consequently its field, algebraic-closure,
and characteristic structures are the canonical Mathlib instances rather than parallel data.

## Main definition

* `TauCeti.ValidLieTypeIndex.Closure`: the algebraic closure of the index's prime field.

## Roadmap

This is the algebraic-closure part of item I0 in
`TauCetiRoadmap/CFSGStatement/README.md`. Milestone L0 uses this carrier when it base-changes the
pinned Chevalley--Demazure group scheme to the characteristic of a valid Lie-type index and takes
its algebraic-closure-valued points.
-/

public section

namespace TauCeti.ValidLieTypeIndex

/-- The algebraic closure of the prime field in the characteristic attached to a valid Lie-type
index. -/
abbrev Closure (d : ValidLieTypeIndex) : Type :=
  AlgebraicClosure (ZMod d.characteristic)

/-! The instances used by the later ambient-group construction are inherited from Mathlib. -/

noncomputable section

example (d : ValidLieTypeIndex) : Field d.Closure := inferInstance

example (d : ValidLieTypeIndex) : IsAlgClosed d.Closure := inferInstance

example (d : ValidLieTypeIndex) : CharP d.Closure d.characteristic := inferInstance

end

end TauCeti.ValidLieTypeIndex
