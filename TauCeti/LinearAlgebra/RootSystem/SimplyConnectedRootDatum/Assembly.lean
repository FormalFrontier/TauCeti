/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.Basic
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
* `TauCeti.DynkinType.simpleIndex`: the first `t.rank` root indices in Bourbaki order.

## Main results

* `TauCeti.DynkinType.hasCartanType_simplyConnectedRootDatum`: the pinned datum realizes its
  indexing Dynkin type.
* `TauCeti.DynkinType.span_coroot_simplyConnectedRootDatum`: its coroots span the cocharacter
  lattice.
* `TauCeti.DynkinType.root_simpleIndex`, `coroot_simpleIndex`, and
  `mem_support_simplyConnectedBase`: the entrywise pinning of the simple roots and base.
* `TauCeti.DynkinType.pairing_simpleIndex` and `TauCeti.DynkinType.pairingIn_simpleIndex`: the
  Cartan integers at the simple indices are the entries of the Bourbaki-numbered Cartan matrix.
* `TauCeti.DynkinType.card_support_simplyConnectedBase`: the pinned base has `t.rank` elements.
* `TauCeti.DynkinType.toLinearMap_simplyConnectedRootDatum`: the pinned pairing is the dot
  product, uniformly in the type.

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
def simplyConnectedRootDatum (t : DynkinType) (ht : t.Valid) :
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
def simplyConnectedBase (t : DynkinType) (ht : t.Valid) :
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

-- A base is indexed by its datum, so each base equation explicitly transports along the
-- corresponding datum equation instead of exposing either dispatcher's implementation.
@[simp] theorem simplyConnectedBase_A (n : ℕ) (ht : (A n).Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_A n ht))
      ((A n).simplyConnectedBase ht) = typeASimplyConnectedBase n := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_B (n : ℕ) (ht : (B n).Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_B n ht))
      ((B n).simplyConnectedBase ht) = typeBSimplyConnectedBase n := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_C (n : ℕ) (ht : (C n).Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_C n ht))
      ((C n).simplyConnectedBase ht) = typeCSimplyConnectedBase n := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_D (n : ℕ) (ht : (D n).Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_D n ht))
      ((D n).simplyConnectedBase ht) =
        typeDSimplyConnectedBase n (valid_D.mp ht) := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_E6 (ht : E6.Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_E6 ht))
      (E6.simplyConnectedBase ht) = e6SimplyConnectedBase := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_E7 (ht : E7.Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_E7 ht))
      (E7.simplyConnectedBase ht) = e7SimplyConnectedBase := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_E8 (ht : E8.Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_E8 ht))
      (E8.simplyConnectedBase ht) = e8SimplyConnectedBase := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_F4 (ht : F4.Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_F4 ht))
      (F4.simplyConnectedBase ht) = f4SimplyConnectedBase := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

@[simp] theorem simplyConnectedBase_G2 (ht : G2.Valid) :
    Eq.mp (congrArg (fun P => P.Base) (simplyConnectedRootDatum_G2 ht))
      (G2.simplyConnectedBase ht) = g2SimplyConnectedBase := by
  apply eq_of_heq
  simp only [simplyConnectedBase, simplyConnectedRootDatum]
  exact HEq.rfl

/-! ## The uniform Bourbaki pinning -/

/-- The index of the `i`-th Bourbaki simple root in the pinned root enumeration. -/
def simpleIndex (t : DynkinType) (ht : t.Valid) (i : Fin t.rank) : Fin t.numRoots :=
  Fin.castLE (rank_le_numRoots ht) i

/-- The root enumeration index of a simple root has the same zero-based value as its node. -/
@[simp] theorem simpleIndex_val (t : DynkinType) (ht : t.Valid) (i : Fin t.rank) :
    (t.simpleIndex ht i : ℕ) = i := (rfl)

private theorem simpleIndex_A (n : ℕ) (ht : (A n).Valid) (i : Fin n) :
    (A n).simpleIndex ht i = typeASimpleIndex n i := by
  apply Fin.ext
  rw [typeASimpleIndex_val]
  exact simpleIndex_val (A n) ht i

private theorem simpleIndex_B (n : ℕ) (ht : (B n).Valid) (i : Fin n) :
    (B n).simpleIndex ht i = typeBSimpleIndex n i := by
  apply Fin.ext
  rw [typeBSimpleIndex_val]
  exact simpleIndex_val (B n) ht i

private theorem simpleIndex_C (n : ℕ) (ht : (C n).Valid) (i : Fin n) :
    (C n).simpleIndex ht i = typeCSimpleIndex n i := by
  apply Fin.ext
  rw [typeCSimpleIndex_val]
  exact simpleIndex_val (C n) ht i

private theorem simpleIndex_D (n : ℕ) (ht : (D n).Valid) (i : Fin n) :
    (D n).simpleIndex ht i = typeDSimpleIndex n (valid_D.mp ht) i := by
  apply Fin.ext
  rw [typeDSimpleIndex_val]
  exact simpleIndex_val (D n) ht i

private theorem simpleIndex_E6 (ht : E6.Valid) (i : Fin 6) :
    E6.simpleIndex ht i = e6SimpleIndex i := by
  apply Fin.ext
  rw [e6SimpleIndex_val]
  exact simpleIndex_val E6 ht i

private theorem simpleIndex_E7 (ht : E7.Valid) (i : Fin 7) :
    E7.simpleIndex ht i = e7SimpleIndex i := by
  apply Fin.ext
  rw [e7SimpleIndex_val]
  exact simpleIndex_val E7 ht i

private theorem simpleIndex_E8 (ht : E8.Valid) (i : Fin 8) :
    E8.simpleIndex ht i = e8SimpleIndex i := by
  apply Fin.ext
  rw [e8SimpleIndex_val]
  exact simpleIndex_val E8 ht i

private theorem simpleIndex_F4 (ht : F4.Valid) (i : Fin 4) :
    F4.simpleIndex ht i = Fin.castAdd 44 i := Fin.ext rfl

private theorem simpleIndex_G2 (ht : G2.Valid) (i : Fin 2) :
    G2.simpleIndex ht i = Fin.castAdd 10 i := Fin.ext rfl

/-- The simple coroots of the pinned datum are the standard basis of the cocharacter lattice. -/
@[simp] theorem coroot_simpleIndex (t : DynkinType) (ht : t.Valid) (i : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).coroot (t.simpleIndex ht i) = Pi.single i 1 := by
  -- Case splitting refines `rank`, but Lean retains `i` in the dependent motive. Each first
  -- `change` records the resulting concrete index type; the dispatcher itself is rewritten by its
  -- public branch equation.
  cases t with
  | A n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_A, simpleIndex_A]
    change (typeASimplyConnectedRootDatum n).coroot (typeASimpleIndex n i) = Pi.single i 1
    rw [coroot_typeASimpleIndex]
  | B n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_B, simpleIndex_B]
    change (typeBSimplyConnectedRootDatum n).coroot (typeBSimpleIndex n i) = Pi.single i 1
    rw [coroot_typeBSimpleIndex]
  | C n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_C, simpleIndex_C]
    change (typeCSimplyConnectedRootDatum n).coroot (typeCSimpleIndex n i) = Pi.single i 1
    rw [coroot_typeCSimpleIndex]
  | D n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_D, simpleIndex_D]
    change (typeDSimplyConnectedRootDatum n (valid_D.mp ht)).coroot
      (typeDSimpleIndex n (valid_D.mp ht) i) = Pi.single i 1
    rw [coroot_typeDSimpleIndex]
  | E6 =>
    change Fin 6 at i
    rw [simplyConnectedRootDatum_E6, simpleIndex_E6]
    change e6SimplyConnectedRootDatum.coroot (e6SimpleIndex i) = Pi.single i 1
    rw [e6SimplyConnectedRootDatum_coroot, coroot_e6SimpleIndex]
  | E7 =>
    change Fin 7 at i
    rw [simplyConnectedRootDatum_E7, simpleIndex_E7]
    change e7SimplyConnectedRootDatum.coroot (e7SimpleIndex i) = Pi.single i 1
    rw [e7SimplyConnectedRootDatum_coroot, coroot_e7SimpleIndex]
  | E8 =>
    change Fin 8 at i
    rw [simplyConnectedRootDatum_E8, simpleIndex_E8]
    change e8SimplyConnectedRootDatum.coroot (e8SimpleIndex i) = Pi.single i 1
    rw [e8SimplyConnectedRootDatum_coroot, coroot_e8SimpleIndex]
  | F4 =>
    change Fin 4 at i
    rw [simplyConnectedRootDatum_F4, simpleIndex_F4]
    change f4SimplyConnectedRootDatum.coroot (Fin.castAdd 44 i) = Pi.single i 1
    rw [f4SimplyConnectedRootDatum_coroot, f4Coroot_castAdd]
  | G2 =>
    change Fin 2 at i
    rw [simplyConnectedRootDatum_G2, simpleIndex_G2]
    change g2SimplyConnectedRootDatum.coroot (Fin.castAdd 10 i) = Pi.single i 1
    rw [g2SimplyConnectedRootDatum_coroot, g2Coroot_castAdd]

/-- The simple roots of the pinned datum are the rows of its Bourbaki-numbered Cartan matrix. -/
@[simp] theorem root_simpleIndex (t : DynkinType) (ht : t.Valid) (i : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i) =
      fun k => t.cartanMatrix i k := by
  -- As above, these type annotations expose the concrete rank carried by the dependent motive;
  -- all substantive reductions use named branch and family equations.
  cases t with
  | A n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_A, simpleIndex_A, cartanMatrix_A]
    change (typeASimplyConnectedRootDatum n).root (typeASimpleIndex n i) =
      fun k => CartanMatrix.A n i k
    rw [root_typeASimpleIndex]
  | B n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_B, simpleIndex_B, cartanMatrix_B]
    change (typeBSimplyConnectedRootDatum n).root (typeBSimpleIndex n i) =
      fun k => CartanMatrix.B n i k
    rw [root_typeBSimpleIndex]
  | C n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_C, simpleIndex_C, cartanMatrix_C]
    change (typeCSimplyConnectedRootDatum n).root (typeCSimpleIndex n i) =
      fun k => CartanMatrix.C n i k
    rw [root_typeCSimpleIndex]
  | D n =>
    change Fin n at i
    rw [simplyConnectedRootDatum_D, simpleIndex_D, cartanMatrix_D]
    change (typeDSimplyConnectedRootDatum n (valid_D.mp ht)).root
      (typeDSimpleIndex n (valid_D.mp ht) i) = fun k => CartanMatrix.D n i k
    rw [root_typeDSimpleIndex]
  | E6 =>
    change Fin 6 at i
    rw [simplyConnectedRootDatum_E6, simpleIndex_E6, cartanMatrix_E6]
    change e6SimplyConnectedRootDatum.root (e6SimpleIndex i) = CartanMatrix.E 6 i
    rw [e6SimplyConnectedRootDatum_root, root_e6SimpleIndex]
  | E7 =>
    change Fin 7 at i
    rw [simplyConnectedRootDatum_E7, simpleIndex_E7, cartanMatrix_E7]
    change e7SimplyConnectedRootDatum.root (e7SimpleIndex i) = CartanMatrix.E 7 i
    rw [e7SimplyConnectedRootDatum_root, root_e7SimpleIndex]
  | E8 =>
    change Fin 8 at i
    rw [simplyConnectedRootDatum_E8, simpleIndex_E8, cartanMatrix_E8]
    change e8SimplyConnectedRootDatum.root (e8SimpleIndex i) = CartanMatrix.E 8 i
    rw [e8SimplyConnectedRootDatum_root, root_e8SimpleIndex]
  | F4 =>
    change Fin 4 at i
    rw [simplyConnectedRootDatum_F4, simpleIndex_F4, cartanMatrix_F4]
    change f4SimplyConnectedRootDatum.root (Fin.castAdd 44 i) = CartanMatrix.F₄ i
    rw [f4SimplyConnectedRootDatum_root, f4Root_castAdd]
  | G2 =>
    change Fin 2 at i
    rw [simplyConnectedRootDatum_G2, simpleIndex_G2, cartanMatrix_G2]
    change g2SimplyConnectedRootDatum.root (Fin.castAdd 10 i) =
      fun k => CartanMatrix.G₂.transpose i k
    rw [g2SimplyConnectedRootDatum_root, g2Root_castAdd]

/-- The pinned base is supported exactly on the first `t.rank` root indices. -/
@[simp] theorem mem_support_simplyConnectedBase (t : DynkinType) (ht : t.Valid)
    {k : Fin t.numRoots} :
    k ∈ (t.simplyConnectedBase ht).support ↔ (k : ℕ) < t.rank := by
  cases t with
  | A n => exact mem_typeASimplyConnectedBase_support
  | B n => exact mem_typeBSimplyConnectedBase_support
  | C n => exact mem_support_typeCSimplyConnectedBase
  | D n => exact mem_typeDSimplyConnectedBase_support (valid_D.mp ht)
  | E6 => exact mem_e6SimplyConnectedBase_support
  | E7 => exact mem_support_e7SimplyConnectedBase
  | E8 => exact mem_support_e8SimplyConnectedBase
  | F4 =>
    -- The case split leaves `k` in the dependent motive; expose its concrete index type before
    -- applying the family support equation.
    change Fin 48 at k
    change k ∈ f4SimplyConnectedBase.support ↔ (k : ℕ) < 4
    rw [f4SimplyConnectedBase_support]
    exact mem_f4Support
  | G2 =>
    -- As in the `F4` branch, this only refines the index type retained by the dependent motive.
    change Fin 12 at k
    change k ∈ g2SimplyConnectedBase.support ↔ (k : ℕ) < 2
    rw [g2SimplyConnectedBase_support]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- The Bourbaki numbering identifies the nodes with the support of the pinned integral base. -/
def simpleSupportEquivSimplyConnectedBase (t : DynkinType) (ht : t.Valid) :
    Fin t.rank ≃ (t.simplyConnectedBase ht).support where
  toFun i := ⟨t.simpleIndex ht i, by simp⟩
  invFun k := ⟨(k : Fin t.numRoots), (mem_support_simplyConnectedBase t ht).mp k.2⟩
  left_inv i := Fin.ext (by simp [simpleIndex_val])
  right_inv k := Subtype.ext (Fin.ext (by simp [simpleIndex_val]))

@[simp] theorem coe_simpleSupportEquivSimplyConnectedBase (t : DynkinType) (ht : t.Valid)
    (i : Fin t.rank) :
    ((t.simpleSupportEquivSimplyConnectedBase ht i : Fin t.numRoots)) = t.simpleIndex ht i := by
  simp [simpleSupportEquivSimplyConnectedBase]

/-- The pinned base has one simple root per Bourbaki node. -/
theorem card_support_simplyConnectedBase (t : DynkinType) (ht : t.Valid) :
    (t.simplyConnectedBase ht).support.card = t.rank := by
  classical
  rw [← Fintype.card_coe,
    ← Fintype.card_congr (t.simpleSupportEquivSimplyConnectedBase ht), Fintype.card_fin]

/-- **The pinned pairing is the dot product** of the fundamental-weight and simple-coroot
coordinates, uniformly in the Dynkin type. -/
theorem toLinearMap_simplyConnectedRootDatum (t : DynkinType) (ht : t.Valid)
    (x y : Fin t.rank → ℤ) :
    (t.simplyConnectedRootDatum ht).toLinearMap x y = x ⬝ᵥ y := by
  -- Unlike the entrywise pinning above, no index is retained in a dependent motive here: the case
  -- split refines `t.rank` on a constructor, so `x` and `y` already have the family's index type.
  -- Each branch therefore just rewrites the dispatcher into its family datum and applies that
  -- family's own pairing equation.
  cases t with
  | A n =>
    rw [simplyConnectedRootDatum_A]
    exact toLinearMap_typeASimplyConnectedRootDatum x y
  | B n =>
    rw [simplyConnectedRootDatum_B]
    exact toLinearMap_typeBSimplyConnectedRootDatum x y
  | C n =>
    rw [simplyConnectedRootDatum_C]
    exact toLinearMap_typeCSimplyConnectedRootDatum x y
  | D n =>
    rw [simplyConnectedRootDatum_D]
    exact toLinearMap_typeDSimplyConnectedRootDatum (valid_D.mp ht) x y
  | E6 =>
    rw [simplyConnectedRootDatum_E6]
    exact e6SimplyConnectedRootDatum_toLinearMap x y
  | E7 =>
    rw [simplyConnectedRootDatum_E7]
    exact e7SimplyConnectedRootDatum_toLinearMap_apply x y
  | E8 =>
    rw [simplyConnectedRootDatum_E8]
    exact e8SimplyConnectedRootDatum_toLinearMap_apply x y
  | F4 =>
    rw [simplyConnectedRootDatum_F4]
    exact f4SimplyConnectedRootDatum_toLinearMap_apply_apply x y
  | G2 =>
    rw [simplyConnectedRootDatum_G2]
    exact g2SimplyConnectedRootDatum_toLinearMap x y

/-- **The Cartan integers of the pinned datum at the simple indices are the entries of its
Bourbaki-numbered Cartan matrix.** The simple root is a row of the Cartan matrix and the simple
coroot is a standard basis vector, so the dot product picks out one entry. -/
@[simp] theorem pairing_simpleIndex (t : DynkinType) (ht : t.Valid) (i j : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).pairing (t.simpleIndex ht i) (t.simpleIndex ht j) =
      t.cartanMatrix i j := by
  rw [← RootPairing.root_coroot_eq_pairing, toLinearMap_simplyConnectedRootDatum,
    root_simpleIndex, coroot_simpleIndex, dotProduct_single, mul_one]

/-- The integral form of `TauCeti.DynkinType.pairing_simpleIndex`. -/
@[simp] theorem pairingIn_simpleIndex (t : DynkinType) (ht : t.Valid) (i j : Fin t.rank) :
    (t.simplyConnectedRootDatum ht).pairingIn ℤ (t.simpleIndex ht i) (t.simpleIndex ht j) =
      t.cartanMatrix i j := by
  simpa using (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ (t.simpleIndex ht i)
    (t.simpleIndex ht j) |>.trans (pairing_simpleIndex t ht i j)

/-! ## Uniform acceptance theorems -/

/-- The pinned datum has Cartan type `t`: its base Cartan matrix agrees with the standard one after
a relabelling of the support. The entrywise Bourbaki pinning is given by `root_simpleIndex` and
`coroot_simpleIndex`. -/
theorem hasCartanType_simplyConnectedRootDatum (t : DynkinType) (ht : t.Valid) :
    HasCartanType (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) t := by
  cases t with
  | A n => exact hasCartanType_typeASimplyConnectedRootDatum n
  | B n => exact hasCartanType_typeBSimplyConnectedRootDatum n
  | C n => exact hasCartanType_typeCSimplyConnectedRootDatum n
  | D n => exact hasCartanType_typeDSimplyConnectedRootDatum n (valid_D.mp ht)
  | E6 => exact hasCartanType_e6SimplyConnectedRootDatum
  | E7 => exact hasCartanType_e7SimplyConnectedRootDatum
  | E8 => exact hasCartanType_e8SimplyConnectedRootDatum
  | F4 => exact hasCartanType_f4SimplyConnectedRootDatum
  | G2 => exact hasCartanType_g2SimplyConnectedRootDatum

/-- The coroots of the pinned datum span the cocharacter lattice. This is the simply connected
lattice condition consumed by the pinned Chevalley--Demazure construction. -/
theorem span_coroot_simplyConnectedRootDatum (t : DynkinType) (ht : t.Valid) :
    Submodule.span ℤ (Set.range (t.simplyConnectedRootDatum ht).coroot) = ⊤ := by
  cases t with
  | A n => exact corootSpan_typeASimplyConnectedRootDatum_eq_top n
  | B n => exact corootSpan_typeBSimplyConnectedRootDatum_eq_top n
  | C n => exact corootSpan_typeCSimplyConnectedRootDatum_eq_top n
  | D n => exact corootSpan_typeDSimplyConnectedRootDatum_eq_top n (valid_D.mp ht)
  | E6 => exact corootSpan_e6SimplyConnectedRootDatum_eq_top
  | E7 => exact corootSpan_e7SimplyConnectedRootDatum_eq_top
  | E8 => exact corootSpan_e8SimplyConnectedRootDatum_eq_top
  | F4 =>
    exact simplyConnectedRootDatum_F4 ht ▸
      RootPairing.IsRootSystem.span_coroot_eq_top (P := f4SimplyConnectedRootDatum)
  | G2 =>
    exact simplyConnectedRootDatum_G2 ht ▸
      RootPairing.IsRootSystem.span_coroot_eq_top (P := g2SimplyConnectedRootDatum)

end

end TauCeti.DynkinType
