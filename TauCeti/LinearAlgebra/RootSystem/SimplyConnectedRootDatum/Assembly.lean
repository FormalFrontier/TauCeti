/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2

public section

/-!
# The pinned simply connected root datum of a Dynkin type

This file assembles the explicit simply connected root data for the nine irreducible
crystallographic Dynkin families into one construction indexed by a valid
`TauCeti.DynkinType`. Both lattices are `Fin t.rank → ℤ`: the character lattice uses the
fundamental-weight basis and the cocharacter lattice uses the simple-coroot basis. Roots are
indexed by `Fin t.numRoots`, with the first `t.rank` indices the Bourbaki-numbered simple roots.

The construction dispatches directly to the coordinate data in the family modules imported
above. It does not choose a root datum from a realization theorem. The branch equations below
make this explicit data available without requiring downstream users to unfold the dispatcher.

## Main definitions

* `TauCeti.DynkinType.simplyConnectedRootDatum`: the pinned datum of a valid Dynkin type.
* `TauCeti.DynkinType.simplyConnectedBase`: its Bourbaki-numbered base.

## Main results

* `TauCeti.DynkinType.hasCartanType_simplyConnectedRootDatum`: the pinned datum realizes its
  indexing Dynkin type.
* `TauCeti.DynkinType.span_coroot_simplyConnectedRootDatum`: its coroots span the cocharacter
  lattice.

## References

The family data and numbering follow N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plates I--IX, and J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*,
Chapter 11. This assembles the target "a named datum per valid type" in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` for its consumer,
`CFSGStatement` milestone L0.
-/

namespace TauCeti.DynkinType

noncomputable section

/-! ## The uniform pinned datum -/

/-- The pinned simply connected root datum attached to a valid Dynkin type.

This is a definition by cases into the nine explicit family data. The validity proof is used only
by the type `D` construction, whose coordinate model requires `4 ≤ n`; the other family models are
defined at every rank, while validity controls which of them enter the classification list. -/
@[expose] def simplyConnectedRootDatum (t : DynkinType) (ht : t.Valid) :
    RootDatum (Fin t.numRoots) (Fin t.rank → ℤ) (Fin t.rank → ℤ) :=
  match t with
  | .A n => typeASimplyConnectedRootDatum n
  | .B n => typeBSimplyConnectedRootDatum n
  | .C n => typeCSimplyConnectedRootDatum n
  | .D n => typeDSimplyConnectedRootDatum n (valid_D.mp ht)
  | .E6 => e6SimplyConnectedRootDatum
  | .E7 => e7SimplyConnectedRootDatum
  | .E8 => e8SimplyConnectedRootDatum
  | .F4 => f4SimplyConnectedRootDatum
  | .G2 => g2SimplyConnectedRootDatum

/-- The Bourbaki-numbered base of `simplyConnectedRootDatum`, supported on its first `t.rank`
root indices. -/
@[expose] def simplyConnectedBase (t : DynkinType) (ht : t.Valid) :
    (t.simplyConnectedRootDatum ht).Base :=
  match t with
  | .A n => typeASimplyConnectedBase n
  | .B n => typeBSimplyConnectedBase n
  | .C n => typeCSimplyConnectedBase n
  | .D n => typeDSimplyConnectedBase n (valid_D.mp ht)
  | .E6 => e6SimplyConnectedBase
  | .E7 => e7SimplyConnectedBase
  | .E8 => e8SimplyConnectedBase
  | .F4 => f4SimplyConnectedBase
  | .G2 => g2SimplyConnectedBase

/-! ## Branch equations -/

@[simp] theorem simplyConnectedRootDatum_A (n : ℕ) (ht : (A n).Valid) :
    (A n).simplyConnectedRootDatum ht = typeASimplyConnectedRootDatum n := (rfl)

@[simp] theorem simplyConnectedRootDatum_B (n : ℕ) (ht : (B n).Valid) :
    (B n).simplyConnectedRootDatum ht = typeBSimplyConnectedRootDatum n := (rfl)

@[simp] theorem simplyConnectedRootDatum_C (n : ℕ) (ht : (C n).Valid) :
    (C n).simplyConnectedRootDatum ht = typeCSimplyConnectedRootDatum n := (rfl)

@[simp] theorem simplyConnectedRootDatum_D (n : ℕ) (ht : (D n).Valid) :
    (D n).simplyConnectedRootDatum ht = typeDSimplyConnectedRootDatum n (valid_D.mp ht) := (rfl)

@[simp] theorem simplyConnectedRootDatum_E6 (ht : E6.Valid) :
    E6.simplyConnectedRootDatum ht = e6SimplyConnectedRootDatum := (rfl)

@[simp] theorem simplyConnectedRootDatum_E7 (ht : E7.Valid) :
    E7.simplyConnectedRootDatum ht = e7SimplyConnectedRootDatum := (rfl)

@[simp] theorem simplyConnectedRootDatum_E8 (ht : E8.Valid) :
    E8.simplyConnectedRootDatum ht = e8SimplyConnectedRootDatum := (rfl)

@[simp] theorem simplyConnectedRootDatum_F4 (ht : F4.Valid) :
    F4.simplyConnectedRootDatum ht = f4SimplyConnectedRootDatum := (rfl)

@[simp] theorem simplyConnectedRootDatum_G2 (ht : G2.Valid) :
    G2.simplyConnectedRootDatum ht = g2SimplyConnectedRootDatum := (rfl)

@[simp] theorem simplyConnectedBase_A (n : ℕ) (ht : (A n).Valid) :
    (A n).simplyConnectedBase ht = typeASimplyConnectedBase n := (rfl)

@[simp] theorem simplyConnectedBase_B (n : ℕ) (ht : (B n).Valid) :
    (B n).simplyConnectedBase ht = typeBSimplyConnectedBase n := (rfl)

@[simp] theorem simplyConnectedBase_C (n : ℕ) (ht : (C n).Valid) :
    (C n).simplyConnectedBase ht = typeCSimplyConnectedBase n := (rfl)

@[simp] theorem simplyConnectedBase_D (n : ℕ) (ht : (D n).Valid) :
    (D n).simplyConnectedBase ht = typeDSimplyConnectedBase n (valid_D.mp ht) := (rfl)

@[simp] theorem simplyConnectedBase_E6 (ht : E6.Valid) :
    E6.simplyConnectedBase ht = e6SimplyConnectedBase := (rfl)

@[simp] theorem simplyConnectedBase_E7 (ht : E7.Valid) :
    E7.simplyConnectedBase ht = e7SimplyConnectedBase := (rfl)

@[simp] theorem simplyConnectedBase_E8 (ht : E8.Valid) :
    E8.simplyConnectedBase ht = e8SimplyConnectedBase := (rfl)

@[simp] theorem simplyConnectedBase_F4 (ht : F4.Valid) :
    F4.simplyConnectedBase ht = f4SimplyConnectedBase := (rfl)

@[simp] theorem simplyConnectedBase_G2 (ht : G2.Valid) :
    G2.simplyConnectedBase ht = g2SimplyConnectedBase := (rfl)

/-! ## Uniform acceptance theorems -/

/-- The pinned simply connected root datum realizes the Dynkin type that indexes it, against the
same Bourbaki numbering. -/
theorem hasCartanType_simplyConnectedRootDatum (t : DynkinType) (ht : t.Valid) :
    ∃ _hcrys : (t.simplyConnectedRootDatum ht).IsCrystallographic,
      HasCartanType (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) t := by
  cases t with
  | A n => exact ⟨inferInstance, hasCartanType_typeASimplyConnectedRootDatum n⟩
  | B n => exact ⟨inferInstance, hasCartanType_typeBSimplyConnectedRootDatum n⟩
  | C n => exact ⟨inferInstance, hasCartanType_typeCSimplyConnectedRootDatum n⟩
  | D n => exact ⟨inferInstance, hasCartanType_typeDSimplyConnectedRootDatum n (valid_D.mp ht)⟩
  | E6 => exact ⟨inferInstance, hasCartanType_e6SimplyConnectedRootDatum⟩
  | E7 => exact ⟨inferInstance, hasCartanType_e7SimplyConnectedRootDatum⟩
  | E8 => exact ⟨inferInstance, hasCartanType_e8SimplyConnectedRootDatum⟩
  | F4 => exact ⟨inferInstance, hasCartanType_f4SimplyConnectedRootDatum⟩
  | G2 => exact ⟨inferInstance, hasCartanType_g2SimplyConnectedRootDatum⟩

/-- The coroots of the pinned datum span the cocharacter lattice. This is the simply connected
lattice condition consumed by the pinned Chevalley--Demazure construction. -/
theorem span_coroot_simplyConnectedRootDatum (t : DynkinType) (ht : t.Valid) :
    Submodule.span ℤ (Set.range (t.simplyConnectedRootDatum ht).coroot) = ⊤ := by
  cases t with
  | A n => exact corootSpan_typeASimplyConnectedRootDatum_eq_top n
  | B n => exact corootSpan_typeBSimplyConnectedRootDatum_eq_top n
  | C n => exact typeCSimplyConnectedRootDatum_corootSpan_eq_top n
  | D n => exact corootSpan_typeDSimplyConnectedRootDatum_eq_top n (valid_D.mp ht)
  | E6 => exact corootSpan_e6SimplyConnectedRootDatum_eq_top
  | E7 => exact corootSpan_e7SimplyConnectedRootDatum_eq_top
  | E8 => exact corootSpan_e8SimplyConnectedRootDatum_eq_top
  | F4 => exact corootSpan_f4SimplyConnectedRootDatum_eq_top
  | G2 => exact corootSpan_g2SimplyConnectedRootDatum_eq_top

end

end TauCeti.DynkinType
