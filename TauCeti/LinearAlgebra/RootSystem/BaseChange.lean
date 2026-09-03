/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.Matrix.Dual

public section

/-!
# Base change of a root pairing carried by the standard lattices

An integral root datum carries its roots and coroots on the standard lattices `κ → ℤ`, paired by
the dot product. The constructions which build a Lie algebra out of a root system — Serre's
presentation, and Geck's construction — instead want a root system over a field of characteristic
zero. This file moves such a pairing along an injective algebra map, expressed by
`[FaithfulSMul R S]`, applying the structure map entrywise to every root and coroot and keeping the
same reflection permutation.

Only the target pairing is chosen here: it is again the dot product, which is perfect on `κ → S` for
every commutative ring `S` by `TauCeti.dotProductBilin_isPerfPair`. So the construction asks the
source pairing to be the dot product too, and every axiom of `RootPairing` then transports along
`Pi.algebraMap`, entrywise application of `algebraMap R S`.

The properties a downstream Lie-theoretic consumer needs are transported separately, each under its
own hypotheses: being crystallographic, being reduced, spanning, and carrying a base with a
prescribed Cartan matrix. Irreducibility is deliberately absent, because it is *false* over `ℤ`:
the sublattice `2 • (κ → ℤ)` is invariant under every reflection. It has to be proved over the new
base ring rather than transported.

## Main definitions

* `TauCeti.rootPairingBaseChange`: the base change of a dot-product root pairing along an injective
  algebra map `R → S`, expressed by `[FaithfulSMul R S]`.
* `TauCeti.rootPairingBaseChangeBase`: the base of the base change attached to a base of the
  original pairing, supported on the same indices.

## Main results

* `TauCeti.isCrystallographic_rootPairingBaseChange`: base change preserves being crystallographic.
* `TauCeti.isReduced_rootPairingBaseChange`: base change preserves being reduced.
* `TauCeti.span_range_root_rootPairingBaseChange_eq_top` and
  `TauCeti.span_range_coroot_rootPairingBaseChange_eq_top`: a spanning family of roots or coroots
  stays spanning.
* `TauCeti.pairingIn_rootPairingBaseChange`: the integral pairings, hence the Cartan matrix of a
  base, are unchanged.

## References

The construction is the standard passage from a root datum over `ℤ` to the root system over `ℚ`
that it determines; see N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1. It
supplies the root-system input of the Chevalley basis in Layer 9,
"pinned Chevalley--Demazure group schemes over `ℤ`", of `TauCetiRoadmap/ReductiveGroups/README.md`.
-/

namespace TauCeti

open Function Matrix Set
open FaithfulSMul (algebraMap_injective)
open Submodule (span)

/-! ## Entrywise base change of the standard lattice -/

section Entrywise

variable {κ R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Entrywise base change of the standard lattice reads off entrywise. -/
theorem piAlgebraMap_apply (x : κ → R) (j : κ) :
    Pi.algebraMap κ R S x j = algebraMap R S (x j) :=
  rfl

private theorem injective_piAlgebraMap [FaithfulSMul R S] :
    Injective (Pi.algebraMap κ R S) := fun _ _ h =>
  funext fun j => algebraMap_injective R S (congrFun h j)

/-- Entrywise base change carries the additive closure of a family into the additive closure of the
base-changed family. -/
theorem mem_closure_image_piAlgebraMap {ι : Type*} {g : ι → (κ → R)} {s : Set ι} {x : κ → R}
    (hx : x ∈ AddSubmonoid.closure (g '' s)) :
    Pi.algebraMap κ R S x ∈
      AddSubmonoid.closure ((fun i => Pi.algebraMap κ R S (g i)) '' s) := by
  have himage : (fun i => Pi.algebraMap κ R S (g i)) '' s =
      (Pi.algebraMap κ R S : (κ → R) →ₗ[R] (κ → S)) '' (g '' s) := by
    rw [← image_comp]
    rfl
  rw [himage, ← AddMonoidHom.map_mclosure]
  exact AddSubmonoid.mem_map_of_mem _ hx

/-- A family of vectors spanning the standard lattice still spans after entrywise base change. -/
theorem span_range_piAlgebraMap_eq_top [Finite κ] {ι : Type*} {v : ι → (κ → R)}
    (hv : span R (range v) = ⊤) :
    span S (range fun i => Pi.algebraMap κ R S (v i)) = ⊤ := by
  classical
  have _i : Fintype κ := Fintype.ofFinite κ
  set W : Submodule S (κ → S) := span S (range fun i => Pi.algebraMap κ R S (v i))
  have hmem : ∀ x : κ → R, Pi.algebraMap κ R S x ∈ W := by
    intro x
    have hsub : span R (range v) ≤ (W.restrictScalars R).comap (Pi.algebraMap κ R S) := by
      rw [Submodule.span_le]
      rintro - ⟨i, rfl⟩
      exact Submodule.subset_span (mem_range_self i)
    exact hsub (hv ▸ Submodule.mem_top)
  have hsingle : ∀ j : κ, Pi.single j (1 : S) ∈ W := by
    intro j
    have hj : Pi.algebraMap κ R S (Pi.single j (1 : R)) = Pi.single j (1 : S) := by
      funext k
      rw [piAlgebraMap_apply]
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [Pi.single_eq_of_ne hk]
    exact hj ▸ hmem (Pi.single j (1 : R))
  refine top_le_iff.mp fun x _ => ?_
  rw [← Module.Basis.sum_repr (Pi.basisFun S κ) x]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (by simpa using hsingle j)

end Entrywise

/-! ## The base-changed pairing -/

section Defs

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)

private theorem dotProduct_piAlgebraMap (x y : κ → R) :
    Pi.algebraMap κ R S x ⬝ᵥ Pi.algebraMap κ R S y = algebraMap R S (x ⬝ᵥ y) := by
  simp [dotProduct, piAlgebraMap_apply, map_sum]

variable [FaithfulSMul R S]

/-- **Base change of a root pairing on the standard lattices.** The roots and coroots of
`P : RootPairing ι R (κ → R) (κ → R)`, whose pairing is the dot product, are pushed entrywise
along the injective map `algebraMap R S`, with injectivity supplied by `[FaithfulSMul R S]`, and
paired again by the dot product on `κ → S`. -/
def rootPairingBaseChange : RootPairing ι S (κ → S) (κ → S) where
  toLinearMap := dotProductBilin S S
  root := ⟨fun i => Pi.algebraMap κ R S (P.root i),
    (injective_piAlgebraMap S).comp P.root.injective⟩
  coroot := ⟨fun i => Pi.algebraMap κ R S (P.coroot i),
    (injective_piAlgebraMap S).comp P.coroot.injective⟩
  root_coroot_two i := by
    have h : Pi.algebraMap κ R S (P.root i) ⬝ᵥ Pi.algebraMap κ R S (P.coroot i) = (2 : S) := by
      rw [dotProduct_piAlgebraMap, ← hP, P.root_coroot_two i, map_ofNat]
    exact h
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    have h := congrArg (Pi.algebraMap κ R S) (P.reflectionPerm_root i j)
    rw [map_sub, map_smul, hP] at h
    have key : Pi.algebraMap κ R S (P.root j) -
        (Pi.algebraMap κ R S (P.root j) ⬝ᵥ Pi.algebraMap κ R S (P.coroot i)) •
          Pi.algebraMap κ R S (P.root i) =
        Pi.algebraMap κ R S (P.root (P.reflectionPerm i j)) := by
      rw [dotProduct_piAlgebraMap, algebraMap_smul]
      exact h
    exact key
  reflectionPerm_coroot i j := by
    have h := congrArg (Pi.algebraMap κ R S) (P.reflectionPerm_coroot i j)
    rw [map_sub, map_smul, hP] at h
    have key : Pi.algebraMap κ R S (P.coroot j) -
        (Pi.algebraMap κ R S (P.root i) ⬝ᵥ Pi.algebraMap κ R S (P.coroot j)) •
          Pi.algebraMap κ R S (P.coroot i) =
        Pi.algebraMap κ R S (P.coroot (P.reflectionPerm i j)) := by
      rw [dotProduct_piAlgebraMap, algebraMap_smul]
      exact h
    exact key

@[simp] theorem root_rootPairingBaseChange (i : ι) :
    (rootPairingBaseChange S P hP).root i = Pi.algebraMap κ R S (P.root i) :=
  (rfl)

@[simp] theorem coroot_rootPairingBaseChange (i : ι) :
    (rootPairingBaseChange S P hP).coroot i = Pi.algebraMap κ R S (P.coroot i) :=
  (rfl)

@[simp] theorem reflectionPerm_rootPairingBaseChange :
    (rootPairingBaseChange S P hP).reflectionPerm = P.reflectionPerm :=
  (rfl)

@[simp] theorem toLinearMap_rootPairingBaseChange (x y : κ → S) :
    (rootPairingBaseChange S P hP).toLinearMap x y = x ⬝ᵥ y :=
  (rfl)

@[simp] theorem pairing_rootPairingBaseChange (i j : ι) :
    (rootPairingBaseChange S P hP).pairing i j = algebraMap R S (P.pairing i j) := by
  rw [← RootPairing.root_coroot_eq_pairing, ← RootPairing.root_coroot_eq_pairing,
    root_rootPairingBaseChange, coroot_rootPairingBaseChange, toLinearMap_rootPairingBaseChange,
    dotProduct_piAlgebraMap, hP]

end Defs

/-! ## Transport of the axioms a Lie-theoretic consumer needs -/

section Transport

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y) [FaithfulSMul R S]

/-- Base change preserves being crystallographic: a pairing which was an integer stays that same
integer in the new base ring. -/
instance isCrystallographic_rootPairingBaseChange [P.IsCrystallographic] :
    (rootPairingBaseChange S P hP).IsCrystallographic where
  exists_value i j := by
    refine ⟨P.pairingIn ℤ i j, ?_⟩
    rw [pairing_rootPairingBaseChange, ← P.algebraMap_pairingIn ℤ i j]
    simp [algebraMap_int_eq]

/-- The integral pairing of a crystallographic root pairing is unchanged by base change into a
ring of characteristic zero. Hence so is the Cartan matrix of any base. -/
@[simp] theorem pairingIn_rootPairingBaseChange [CharZero S] [P.IsCrystallographic] (i j : ι) :
    (rootPairingBaseChange S P hP).pairingIn ℤ i j = P.pairingIn ℤ i j := by
  refine algebraMap_injective ℤ S ?_
  rw [RootPairing.algebraMap_pairingIn, pairing_rootPairingBaseChange,
    ← P.algebraMap_pairingIn ℤ i j]
  simp [algebraMap_int_eq]

/-- Base change along an injective map into a domain preserves being reduced. -/
theorem isReduced_rootPairingBaseChange [IsDomain S] [P.IsReduced] :
    (rootPairingBaseChange S P hP).IsReduced where
  eq_or_eq_neg i j h := by
    have hv : (fun k => algebraMap R S ∘ ![P.root i, P.root j] k) =
        ![(rootPairingBaseChange S P hP).root i, (rootPairingBaseChange S P hP).root j] := by
      funext k
      fin_cases k <;> rfl
    replace h : ¬ LinearIndependent R ![P.root i, P.root j] := by
      rw [← linearIndependent_algebraMap_comp_iff (S := S), hv]
      exact h
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j h with h | h
    · exact Or.inl <| by rw [root_rootPairingBaseChange, root_rootPairingBaseChange, h]
    · exact Or.inr <| by rw [root_rootPairingBaseChange, root_rootPairingBaseChange, h, map_neg]

/-- Base change preserves spanning by the roots. -/
theorem span_range_root_rootPairingBaseChange_eq_top (h : span R (range P.root) = ⊤) :
    span S (range (rootPairingBaseChange S P hP).root) = ⊤ :=
  span_range_piAlgebraMap_eq_top S h

/-- Base change preserves spanning by the coroots. -/
theorem span_range_coroot_rootPairingBaseChange_eq_top (h : span R (range P.coroot) = ⊤) :
    span S (range (rootPairingBaseChange S P hP).coroot) = ⊤ :=
  span_range_piAlgebraMap_eq_top S h

end Transport

/-! ## Bases -/

section Base

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  (P : RootPairing ι R (κ → R) (κ → R)) (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)
  [FaithfulSMul R S] [IsDomain S] (b : P.Base)

/-- **The base change of a base.** A base of `P` is a base of the base-changed pairing, supported
on the same indices. Linear independence survives because `S` is a domain in which `R` embeds. -/
def rootPairingBaseChangeBase : (rootPairingBaseChange S P hP).Base where
  support := b.support
  linearIndepOn_root :=
    linearIndependent_algebraMap_comp_iff (S := S) |>.mpr b.linearIndepOn_root
  linearIndepOn_coroot :=
    linearIndependent_algebraMap_comp_iff (S := S) |>.mpr b.linearIndepOn_coroot
  root_mem_or_neg_mem i := by
    rcases b.root_mem_or_neg_mem i with h | h
    · exact Or.inl <| mem_closure_image_piAlgebraMap S h
    · refine Or.inr ?_
      have hmem := mem_closure_image_piAlgebraMap (S := S) (g := P.root) (s := b.support) h
      rwa [map_neg] at hmem
  coroot_mem_or_neg_mem i := by
    rcases b.coroot_mem_or_neg_mem i with h | h
    · exact Or.inl <| mem_closure_image_piAlgebraMap S h
    · refine Or.inr ?_
      have hmem := mem_closure_image_piAlgebraMap (S := S) (g := P.coroot) (s := b.support) h
      rwa [map_neg] at hmem

@[simp] theorem support_rootPairingBaseChangeBase :
    (rootPairingBaseChangeBase S P hP b).support = b.support :=
  (rfl)

/-- The supports of a base and of its base change name the same indices. -/
def supportEquivRootPairingBaseChangeBase :
    (rootPairingBaseChangeBase S P hP b).support ≃ b.support :=
  Equiv.subtypeEquivRight fun i => by rw [support_rootPairingBaseChangeBase]

@[simp] theorem coe_supportEquivRootPairingBaseChangeBase
    (i : (rootPairingBaseChangeBase S P hP b).support) :
    (supportEquivRootPairingBaseChangeBase S P hP b i : ι) = i :=
  (rfl)

/-- Base change does not change the Cartan matrix of a base. -/
@[simp] theorem cartanMatrix_rootPairingBaseChangeBase [CharZero S] [P.IsCrystallographic]
    (i j : (rootPairingBaseChangeBase S P hP b).support) :
    (rootPairingBaseChangeBase S P hP b).cartanMatrix i j =
      b.cartanMatrix (supportEquivRootPairingBaseChangeBase S P hP b i)
        (supportEquivRootPairingBaseChangeBase S P hP b j) :=
  pairingIn_rootPairingBaseChange S P hP i j

end Base

/-! ## Root strings -/

section Chain

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S]
  [Algebra R S] (P : RootPairing ι R (κ → R) (κ → R))
  (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)
  [FaithfulSMul R S]

private theorem root_add_nsmul_mem_range_baseChange_iff (i j : ι) (n : ℕ) :
    (rootPairingBaseChange S P hP).root j + n • (rootPairingBaseChange S P hP).root i ∈
        range (rootPairingBaseChange S P hP).root ↔
      P.root j + n • P.root i ∈ range P.root := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, funext fun x ↦ FaithfulSMul.algebraMap_injective R S ?_⟩
    simpa [piAlgebraMap_apply] using congrFun hk x
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa only [root_rootPairingBaseChange, map_add, map_nsmul] using
      congrArg (Pi.algebraMap κ R S) hk

private theorem root_sub_nsmul_mem_range_baseChange_iff (i j : ι) (n : ℕ) :
    (rootPairingBaseChange S P hP).root j - n • (rootPairingBaseChange S P hP).root i ∈
        range (rootPairingBaseChange S P hP).root ↔
      P.root j - n • P.root i ∈ range P.root := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, funext fun x ↦ FaithfulSMul.algebraMap_injective R S ?_⟩
    simpa [piAlgebraMap_apply] using congrFun hk x
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa only [root_rootPairingBaseChange, map_sub, map_nsmul] using
      congrArg (Pi.algebraMap κ R S) hk

variable [Finite ι] [IsDomain S] [CharZero R] [P.IsCrystallographic]

private theorem chainTopCoeff_rootPairingBaseChange_aux [IsDomain R] [hS : CharZero S] (i j : ι) :
    (rootPairingBaseChange S P hP).chainTopCoeff i j = P.chainTopCoeff i j := by
  let P' := rootPairingBaseChange S P hP
  have hv : (fun k ↦ algebraMap R S ∘ ![P.root i, P.root j] k) =
      ![P'.root i, P'.root j] := by
    funext k
    fin_cases k <;> rfl
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent S ![P'.root i, P'.root j] := by
      rw [← hv, linearIndependent_algebraMap_comp_iff]
      exact h
    apply le_antisymm
    · rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h,
        ← root_add_nsmul_mem_range_baseChange_iff S P hP,
        P'.root_add_nsmul_mem_range_iff_le_chainTopCoeff h']
    · rw [← P'.root_add_nsmul_mem_range_iff_le_chainTopCoeff h',
        root_add_nsmul_mem_range_baseChange_iff S P hP,
        P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · have h' : ¬LinearIndependent S ![P'.root i, P'.root j] := by
      rwa [← hv, linearIndependent_algebraMap_comp_iff]
    rw [P.chainTopCoeff_of_not_linearIndependent h,
      P'.chainTopCoeff_of_not_linearIndependent h']

/-- Extending scalars along an injective map preserves the upper root-string coefficient. -/
@[simp]
theorem chainTopCoeff_rootPairingBaseChange (i j : ι) :
    let _ : IsDomain R := IsDomain.of_faithfulSMul R S
    letI : CharZero S := Algebra.charZero_of_charZero R S
    (rootPairingBaseChange S P hP).chainTopCoeff i j = P.chainTopCoeff i j := by
  let _ : IsDomain R := IsDomain.of_faithfulSMul R S
  exact chainTopCoeff_rootPairingBaseChange_aux S P hP
    (hS := Algebra.charZero_of_charZero R S) i j

private theorem chainBotCoeff_rootPairingBaseChange_aux [IsDomain R] [hS : CharZero S] (i j : ι) :
    (rootPairingBaseChange S P hP).chainBotCoeff i j = P.chainBotCoeff i j := by
  let P' := rootPairingBaseChange S P hP
  have hv : (fun k ↦ algebraMap R S ∘ ![P.root i, P.root j] k) =
      ![P'.root i, P'.root j] := by
    funext k
    fin_cases k <;> rfl
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent S ![P'.root i, P'.root j] := by
      rw [← hv, linearIndependent_algebraMap_comp_iff]
      exact h
    apply le_antisymm
    · rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h,
        ← root_sub_nsmul_mem_range_baseChange_iff S P hP,
        P'.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h']
    · rw [← P'.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h',
        root_sub_nsmul_mem_range_baseChange_iff S P hP,
        P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]
  · have h' : ¬LinearIndependent S ![P'.root i, P'.root j] := by
      rwa [← hv, linearIndependent_algebraMap_comp_iff]
    rw [P.chainBotCoeff_of_not_linearIndependent h,
      P'.chainBotCoeff_of_not_linearIndependent h']

/-- Extending scalars along an injective map preserves the lower root-string coefficient. -/
@[simp]
theorem chainBotCoeff_rootPairingBaseChange (i j : ι) :
    let _ : IsDomain R := IsDomain.of_faithfulSMul R S
    letI : CharZero S := Algebra.charZero_of_charZero R S
    (rootPairingBaseChange S P hP).chainBotCoeff i j = P.chainBotCoeff i j := by
  let _ : IsDomain R := IsDomain.of_faithfulSMul R S
  exact chainBotCoeff_rootPairingBaseChange_aux S P hP
    (hS := Algebra.charZero_of_charZero R S) i j

end Chain

end TauCeti
