/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Datum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# A base of the diagonal root datum of the general linear group

For `GL_(n+1)`, the consecutive coordinate differences

```text
α_i = e_i - e_(i+1),  0 ≤ i < n,
```

form a base of the diagonal root datum. Every coordinate root `e_a - e_b` is a sum of these
simple roots or the negative of such a sum, by telescoping. The same statement holds for the
coroots. The simple roots are linearly independent: summing the first `i + 1` coordinates sends
`α_i` to the `i`-th standard basis vector.

The resulting Cartan matrix is `CartanMatrix.A n`. Thus the diagonal root datum already attached
to the standard maximal torus of `GL_(n+1)` carries the expected Bourbaki-numbered base of type
`A_n`, providing the positive-root input for standard Borels and Bruhat theory.

## Main declarations

* `TauCeti.GeneralLinear.diagonalSimpleRootIndex`: the root index of `e_i - e_(i+1)`.
* `TauCeti.GeneralLinear.diagonalRootBase`: the consecutive coordinate roots as a base.
* `TauCeti.GeneralLinear.hasCartanType_diagonalRootDatum`: this base has Cartan type `A_n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 12.1.

The support and telescoping organization follows
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A`, adapted here to the character and
cocharacter lattices of the diagonal torus in `GL_(n+1)`. This advances Layer 7, "Root datum of
`(G, T)`", of the ReductiveGroups roadmap.
-/

public section

open Function Set

namespace TauCeti.GeneralLinear

universe u

noncomputable section

/-- The initial-coordinate-sum map detecting the diagonal simple coroots. -/
private def diagonalInitialSum (n : ℕ) :
    (ULift.{u} (Fin (n + 1)) → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun x i := ∑ j ∈ Finset.Iic i.castSucc, x (ULift.up j)
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r x := by
    ext i
    simp [Finset.mul_sum]

private lemma diagonalInitialSum_coordinateCoroot (n : ℕ) (i : Fin n) :
    diagonalInitialSum n
        (SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ)) =
      Pi.single i 1 := by
  ext j
  classical
  rw [diagonalInitialSum]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, SplitTorus.coordinateCoroot_apply]
  rw [Finset.sum_sub_distrib]
  have hsum (a : Fin (n + 1)) :
      ∑ x ∈ Finset.Iic j.castSucc, (if x = a then (1 : ℤ) else 0) =
        if a ≤ j.castSucc then 1 else 0 := by
    simp
  have hsumVal (a : Fin (n + 1)) :
      ∑ x ∈ Finset.Iic j.castSucc, (if (x : ℕ) = (a : ℕ) then (1 : ℤ) else 0) =
        if a ≤ j.castSucc then 1 else 0 := by
    simpa only [Fin.ext_iff] using hsum a
  simp only [ULift.up_inj, Fin.ext_iff, hsumVal, Pi.single_apply]
  simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

private lemma linearIndependent_diagonalSimpleCoroot (n : ℕ) :
    LinearIndependent ℤ fun i : Fin n =>
      SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ) := by
  apply LinearIndependent.of_comp (diagonalInitialSum n)
  have h : (diagonalInitialSum n ∘ fun i : Fin n =>
      SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ)) =
      fun i => Pi.single i 1 := funext (diagonalInitialSum_coordinateCoroot n)
  rw [h]
  exact Pi.linearIndependent_single_one (Fin n) ℤ

private lemma linearIndependent_diagonalSimpleRoot (n : ℕ) :
    LinearIndependent ℤ fun i : Fin n =>
      SplitTorus.coordinateRoot (ULift.up i.castSucc) (ULift.up i.succ) := by
  apply LinearIndependent.of_comp Finsupp.lcoeFun
  have h : (Finsupp.lcoeFun (R := ℤ) ∘ fun i : Fin n =>
      SplitTorus.coordinateRoot (ULift.up i.castSucc) (ULift.up i.succ)) =
      fun i => SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ) := by
    funext i
    exact SplitTorus.coe_coordinateRoot _ _
  rw [h]
  exact linearIndependent_diagonalSimpleCoroot n

/-- The index of the `i`-th simple root `e_i - e_(i+1)` in the diagonal root datum of
`GL_(n+1)`. -/
def diagonalSimpleRootIndex (n : ℕ) (i : Fin n) : DiagonalRootIndex (n + 1) :=
  ⟨(ULift.up i.castSucc, ULift.up i.succ), by
    intro h
    have := congrArg (fun x : ULift (Fin (n + 1)) => (x.down : ℕ)) h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega⟩

/-- The first coordinate of the `i`-th diagonal simple-root index is `i`. -/
@[simp]
theorem diagonalSimpleRootIndex_fst (n : ℕ) (i : Fin n) :
    (diagonalSimpleRootIndex n i).1.1 = ULift.up i.castSucc := by
  rw [diagonalSimpleRootIndex]

/-- The second coordinate of the `i`-th diagonal simple-root index is `i + 1`. -/
@[simp]
theorem diagonalSimpleRootIndex_snd (n : ℕ) (i : Fin n) :
    (diagonalSimpleRootIndex n i).1.2 = ULift.up i.succ := by
  rw [diagonalSimpleRootIndex]

/-- Distinct nodes give distinct diagonal simple-root indices. -/
theorem diagonalSimpleRootIndex_injective (n : ℕ) : Injective (diagonalSimpleRootIndex n) := by
  intro i j h
  have := congrArg (fun p : DiagonalRootIndex (n + 1) => p.1.1.down) h
  exact Fin.castSucc_injective n this

/-- The periodic coordinate character used to telescope diagonal roots. -/
private noncomputable def diagonalCharacterCoordinate
    (n a : ℕ) : ULift.{u} (Fin (n + 1)) →₀ ℤ :=
  Finsupp.single (ULift.up (Fin.ofNat (n + 1) a)) 1

/-- The periodic coordinate cocharacter used to telescope diagonal coroots. -/
private noncomputable def diagonalCocharacterCoordinate
    (n a : ℕ) : ULift.{u} (Fin (n + 1)) → ℤ :=
  ⇑(diagonalCharacterCoordinate n a)

private lemma diagonalCharacterCoordinate_eq (n : ℕ) (a : Fin (n + 1)) :
    diagonalCharacterCoordinate n a = Finsupp.single (ULift.up a) 1 := by
  rw [diagonalCharacterCoordinate]
  congr 2
  apply Fin.ext
  exact (Fin.coe_ofNat_eq_mod (n + 1) (a : ℕ)).trans (Nat.mod_eq_of_lt a.isLt)

private lemma diagonalCocharacterCoordinate_eq (n : ℕ) (a : Fin (n + 1)) :
    diagonalCocharacterCoordinate n a = fun x => if x = ULift.up a then 1 else 0 := by
  funext x
  rw [diagonalCocharacterCoordinate, diagonalCharacterCoordinate_eq]
  simp [Finsupp.single_apply, eq_comm]

private lemma coordinateRoot_eq_coordinate_sub (n : ℕ) (a b : Fin (n + 1)) :
    SplitTorus.coordinateRoot (ULift.up a) (ULift.up b) =
      diagonalCharacterCoordinate n a - diagonalCharacterCoordinate n b := by
  rw [diagonalCharacterCoordinate_eq, diagonalCharacterCoordinate_eq]
  ext x
  rw [SplitTorus.coordinateRoot_apply]
  simp [Finsupp.single_apply, eq_comm]
  split_ifs <;> rfl

private lemma coordinateCoroot_eq_coordinate_sub (n : ℕ) (a b : Fin (n + 1)) :
    SplitTorus.coordinateCoroot (ULift.up a) (ULift.up b) =
      diagonalCocharacterCoordinate n a - diagonalCocharacterCoordinate n b := by
  funext x
  rw [SplitTorus.coordinateCoroot_apply, diagonalCocharacterCoordinate_eq,
    diagonalCocharacterCoordinate_eq, Pi.sub_apply]
  split_ifs <;> rfl

private lemma diagonalSimpleRoot_eq_coordinate_sub (n : ℕ) (i : Fin n) :
    SplitTorus.coordinateRoot (ULift.up i.castSucc) (ULift.up i.succ) =
      diagonalCharacterCoordinate n (i : ℕ) - diagonalCharacterCoordinate n ((i : ℕ) + 1) := by
  simpa only [Fin.val_castSucc, Fin.val_succ] using
    coordinateRoot_eq_coordinate_sub n i.castSucc i.succ

private lemma diagonalSimpleCoroot_eq_coordinate_sub (n : ℕ) (i : Fin n) :
    SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ) =
      diagonalCocharacterCoordinate n (i : ℕ) -
        diagonalCocharacterCoordinate n ((i : ℕ) + 1) := by
  simpa only [Fin.val_castSucc, Fin.val_succ] using
    coordinateCoroot_eq_coordinate_sub n i.castSucc i.succ

private lemma range_diagonalSimpleRoot (n : ℕ) :
    range (fun i : Fin n =>
      SplitTorus.coordinateRoot (ULift.up i.castSucc) (ULift.up i.succ)) =
      range (fun i : Fin n =>
        diagonalCharacterCoordinate n (i : ℕ) - diagonalCharacterCoordinate n ((i : ℕ) + 1)) :=
  congrArg range (funext (diagonalSimpleRoot_eq_coordinate_sub n))

private lemma range_diagonalSimpleCoroot (n : ℕ) :
    range (fun i : Fin n =>
      SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ)) =
      range (fun i : Fin n =>
        diagonalCocharacterCoordinate n (i : ℕ) -
          diagonalCocharacterCoordinate n ((i : ℕ) + 1)) :=
  congrArg range (funext (diagonalSimpleCoroot_eq_coordinate_sub n))

/-- The root at the `i`-th diagonal simple-root index is the consecutive coordinate root
`e_i - e_(i+1)`. -/
theorem diagonalRootDatum_root_diagonalSimpleRootIndex (n : ℕ) (i : Fin n) :
    (diagonalRootDatum (n + 1)).root (diagonalSimpleRootIndex n i) =
      SplitTorus.coordinateRoot (ULift.up i.castSucc) (ULift.up i.succ) := by
  rw [diagonalRootDatum_root]
  simp only [diagonalSimpleRootIndex_fst, diagonalSimpleRootIndex_snd, ULift.down_up]
  exact diagonalRoot_eq_coordinateRoot i.castSucc i.succ

/-- The coroot at the `i`-th diagonal simple-root index is the consecutive coordinate coroot
`e_i - e_(i+1)`. -/
theorem diagonalRootDatum_coroot_diagonalSimpleRootIndex (n : ℕ) (i : Fin n) :
    (diagonalRootDatum (n + 1)).coroot (diagonalSimpleRootIndex n i) =
      SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ) := by
  rw [diagonalRootDatum_coroot]
  simp only [diagonalSimpleRootIndex_fst, diagonalSimpleRootIndex_snd, ULift.down_up]
  exact diagonalCoroot_eq_coordinateCoroot i.castSucc i.succ

/-- The support consisting of consecutive coordinate-root indices. -/
private abbrev diagonalSimpleSupport (n : ℕ) : Finset (DiagonalRootIndex (n + 1)) :=
  simpleSupport (diagonalSimpleRootIndex_injective n)

private lemma image_root_diagonalSimpleSupport (n : ℕ) :
    (diagonalRootDatum (n + 1)).root ''
        (diagonalSimpleSupport n : Set (DiagonalRootIndex (n + 1))) =
      range fun i : Fin n =>
        SplitTorus.coordinateRoot (ULift.up i.castSucc) (ULift.up i.succ) := by
  rw [diagonalSimpleSupport, image_simpleSupport]
  apply congrArg range
  exact funext (diagonalRootDatum_root_diagonalSimpleRootIndex n)

private lemma image_coroot_diagonalSimpleSupport (n : ℕ) :
    (diagonalRootDatum (n + 1)).coroot ''
        (diagonalSimpleSupport n : Set (DiagonalRootIndex (n + 1))) =
      range fun i : Fin n =>
        SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ) := by
  rw [diagonalSimpleSupport, image_simpleSupport]
  apply congrArg range
  exact funext (diagonalRootDatum_coroot_diagonalSimpleRootIndex n)

/-- The Bourbaki-numbered base of the diagonal root datum of `GL_(n+1)`, supported on the
consecutive coordinate roots `e_i - e_(i+1)`. -/
noncomputable def diagonalRootBase (n : ℕ) : (diagonalRootDatum.{u} (n + 1)).Base where
  support := diagonalSimpleSupport n
  linearIndepOn_root := linearIndepOn_simpleSupport _ _ <| by
    have hroot : (diagonalRootDatum (n + 1)).root ∘ diagonalSimpleRootIndex n =
        fun i : Fin n => SplitTorus.coordinateRoot (ULift.up i.castSucc) (ULift.up i.succ) :=
      funext (diagonalRootDatum_root_diagonalSimpleRootIndex n)
    rw [hroot]
    exact linearIndependent_diagonalSimpleRoot n
  linearIndepOn_coroot := linearIndepOn_simpleSupport _ _ <| by
    have hcoroot : (diagonalRootDatum (n + 1)).coroot ∘ diagonalSimpleRootIndex n =
        fun i : Fin n => SplitTorus.coordinateCoroot (ULift.up i.castSucc) (ULift.up i.succ) :=
      funext (diagonalRootDatum_coroot_diagonalSimpleRootIndex n)
    rw [hcoroot]
    exact linearIndependent_diagonalSimpleCoroot n
  root_mem_or_neg_mem p := by
    rw [image_root_diagonalSimpleSupport, range_diagonalSimpleRoot]
    rcases le_total (p.1.1.down : ℕ) (p.1.2.down : ℕ) with h | h
    · left
      rw [diagonalRootDatum_root]
      rw [diagonalRoot_eq_coordinateRoot p.1.1.down p.1.2.down,
        coordinateRoot_eq_coordinate_sub n p.1.1.down p.1.2.down]
      exact sub_mem_closure_of_le (diagonalCharacterCoordinate n)
        (Nat.lt_succ_iff.mp p.1.2.down.isLt) h
    · right
      rw [diagonalRootDatum_root]
      rw [diagonalRoot_eq_coordinateRoot p.1.1.down p.1.2.down,
        coordinateRoot_eq_coordinate_sub n p.1.1.down p.1.2.down, neg_sub]
      exact sub_mem_closure_of_le (diagonalCharacterCoordinate n)
        (Nat.lt_succ_iff.mp p.1.1.down.isLt) h
  coroot_mem_or_neg_mem p := by
    rw [image_coroot_diagonalSimpleSupport, range_diagonalSimpleCoroot]
    rcases le_total (p.1.1.down : ℕ) (p.1.2.down : ℕ) with h | h
    · left
      rw [diagonalRootDatum_coroot]
      rw [diagonalCoroot_eq_coordinateCoroot p.1.1.down p.1.2.down,
        coordinateCoroot_eq_coordinate_sub n p.1.1.down p.1.2.down]
      exact sub_mem_closure_of_le (diagonalCocharacterCoordinate n)
        (Nat.lt_succ_iff.mp p.1.2.down.isLt) h
    · right
      rw [diagonalRootDatum_coroot]
      rw [diagonalCoroot_eq_coordinateCoroot p.1.1.down p.1.2.down,
        coordinateCoroot_eq_coordinate_sub n p.1.1.down p.1.2.down, neg_sub]
      exact sub_mem_closure_of_le (diagonalCocharacterCoordinate n)
        (Nat.lt_succ_iff.mp p.1.1.down.isLt) h

/-- The support of the diagonal base is the image of the consecutive-root index map. -/
theorem diagonalRootBase_support (n : ℕ) :
    (diagonalRootBase.{u} n).support =
      simpleSupport (diagonalSimpleRootIndex_injective n) :=
  (rfl)

/-- A root index belongs to the diagonal base exactly when it is one of the consecutive-root
indices. -/
@[simp]
theorem mem_diagonalRootBase_support (n : ℕ) (p : DiagonalRootIndex (n + 1)) :
    p ∈ (diagonalRootBase.{u} n).support ↔ ∃ i : Fin n, diagonalSimpleRootIndex n i = p := by
  rw [diagonalRootBase_support, mem_simpleSupport]

/-- The simple-root pairings in the diagonal root datum are the entries of the type-`A` Cartan
matrix. -/
theorem diagonalRootDatum_pairing_diagonalSimpleRootIndex (n : ℕ) (i j : Fin n) :
    (diagonalRootDatum (n + 1)).pairing
        (diagonalSimpleRootIndex n i) (diagonalSimpleRootIndex n j) =
      CartanMatrix.A n i j := by
  simp [diagonalSimpleRootIndex, diagonalRootDatum_pairing_apply, CartanMatrix.A, Matrix.of_apply,
    Fin.ext_iff]
  split_ifs <;> omega

/-- The diagonal root datum of `GL_(n+1)`, with its consecutive-root base, has Cartan type
`A_n`. -/
theorem hasCartanType_diagonalRootDatum (n : ℕ) :
    HasCartanType (diagonalRootDatum.{u} (n + 1)) (diagonalRootBase n) (.A n) :=
  hasCartanType_of_pairing_eq (diagonalSimpleRootIndex_injective n) rfl fun i j => by
    simpa using
      diagonalRootDatum_pairing_diagonalSimpleRootIndex n i j

end

end TauCeti.GeneralLinear
