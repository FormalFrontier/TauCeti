/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Basic

/-!
# Duals of integral lattices

For an integral lattice `L` in a rational vector space with nondegenerate form, its dual carrier
is the submodule

```text
Lᵛ = {x | B(x, y) ∈ ℤ for every y ∈ L}.
```

This file keeps the dual as a submodule of the same rational ambient space.  It is not packaged as
an `IntegralLattice`: the restriction of the form to `Lᵛ` need not be integral.  For example,
the dual of the rank-one lattice of Gram matrix `(2)` has Gram matrix `(1 / 2)`.

Mathlib proves that the dual of the integral span of a rational basis is the integral span of the
bilinear dual basis.  Applying that result to the basis supplied by `Submodule.IsLattice` proves
that `Lᵛ` is again a full lattice.  It also identifies the natural pairing map
`Lᵛ → Module.Dual ℤ L` as an equivalence and proves reflexivity `(Lᵛ)ᵛ = L`.

## Main declarations

* `TauCeti.span_range_extendOfIsLattice`: the chosen basis of a full `ℤ`-submodule spans the
  submodule over `ℤ`.
* `TauCeti.dualSubmoduleToDual_surjective`: surjectivity of `dualSubmoduleToDual` for a full
  `ℤ`-submodule and nondegenerate bilinear form.
* `TauCeti.dualSubmoduleEquivDual`: the perfect linear equivalence
  `B.dualSubmodule N ≃ₗ[ℤ] Module.Dual ℤ N`.
* `TauCeti.dualSubmodule_dualSubmodule_flip`, `TauCeti.dualSubmodule_flip_dualSubmodule`: double
  duality for general full submodules using `B.flip`.
* `TauCeti.IntegralLattice.dualCarrier`: the dual lattice as a submodule of the common ambient
  rational vector space.
* `TauCeti.IntegralLattice.le_dualCarrier`: the inclusion `L.carrier ≤ L.dualCarrier`.
* `TauCeti.IntegralLattice.mem_dualCarrier_iff`: characterization of membership in the dual carrier.
* `TauCeti.IntegralLattice.instIsLatticeDualCarrier`: the dual carrier is a full lattice.
* `TauCeti.IntegralLattice.dualPairingEquiv`: the perfect integral pairing
  `Lᵛ ≃ Module.Dual ℤ L`.
* `TauCeti.IntegralLattice.flip_dualSubmodule_dualCarrier`: double duality with `form.flip`.
* `TauCeti.IntegralLattice.dualCarrier_dualCarrier`: dualizing twice recovers `L`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module

namespace TauCeti

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The integral span of the ambient rational basis obtained from Mathlib's chosen basis of a
lattice is the lattice itself. -/
theorem span_range_extendOfIsLattice (N : Submodule ℤ V) [N.IsLattice ℚ] :
    Submodule.span ℤ (Set.range ((Module.Free.chooseBasis ℤ N).extendOfIsLattice ℚ)) = N := by
  let b := Module.Free.chooseBasis ℤ N
  have hrange : Set.range (b.extendOfIsLattice ℚ) = Set.range (N.subtype ∘ b) := by
    ext x
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (Basis.extendOfIsLattice_apply ℚ b i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, Basis.extendOfIsLattice_apply ℚ b i⟩
  rw [hrange, Set.range_comp, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- The canonical pairing between a dual submodule and the submodule recovers the ambient rational
bilinear form after coercion to `ℚ`. -/
@[simp]
theorem intCast_dualSubmoduleParing {N : Submodule ℤ V} (B : LinearMap.BilinForm ℚ V)
    (x : B.dualSubmodule N) (y : N) :
    ((B.dualSubmoduleParing x y : ℤ) : ℚ) = B (x : V) (y : V) :=
  B.dualSubmoduleParing_spec x y

/-- Surjectivity of Mathlib's canonical pairing `dualSubmoduleToDual` for a full `ℤ`-submodule
and a nondegenerate rational bilinear form. -/
theorem dualSubmoduleToDual_surjective (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (N : Submodule ℤ V) [N.IsLattice ℚ] :
    Function.Surjective (B.dualSubmoduleToDual N) := by
  intro f
  let b := Module.Free.chooseBasis ℤ N
  let b_ext := b.extendOfIsLattice ℚ
  let bd := B.dualBasis hB b_ext
  let x : V := ∑ i, (f (b i) : ℚ) • bd i
  have hx : x ∈ B.dualSubmodule N := by
    rw [← span_range_extendOfIsLattice N, B.dualSubmodule_span_of_basis hB b_ext]
    exact Submodule.sum_mem _ fun i _ => by
      simpa only [Int.cast_smul_eq_zsmul ℚ] using
        Submodule.smul_mem _ (f (b i)) (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨⟨x, hx⟩, ?_⟩
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨i, rfl⟩
  apply Int.cast_injective (α := ℚ)
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    intCast_dualSubmoduleParing]
  have hform (j) : B (bd j) ((b i : N) : V) = if i = j then 1 else 0 := by
    calc
      B (bd j) ((b i : N) : V) = B (bd j) (b_ext i) := by
        rw [Basis.extendOfIsLattice_apply ℚ b i]
      _ = _ := B.apply_dualBasis_left hB b_ext j i
  simp only [x, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [b] at hform ⊢
  rw [Finset.sum_eq_single i]
  · simp [hform]
  · intro j _ hji
    simp [hform, Ne.symm hji]
  · simp

/-- The canonical pairing between the dual submodule of a full `ℤ`-submodule and the submodule
itself is a linear equivalence over `ℤ` whenever the ambient bilinear form is nondegenerate. -/
noncomputable def dualSubmoduleEquivDual (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (N : Submodule ℤ V) [hN : N.IsLattice ℚ] :
    B.dualSubmodule N ≃ₗ[ℤ] Module.Dual ℤ N :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual N)
    ⟨B.dualSubmoduleToDual_injective hB N hN.span_eq_top,
      dualSubmoduleToDual_surjective B hB N⟩

/-- Dualizing by `B.flip` and then by `B` recovers the original full `ℤ`-submodule. -/
theorem dualSubmodule_dualSubmodule_flip (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (N : Submodule ℤ V) [N.IsLattice ℚ] :
    B.dualSubmodule (B.flip.dualSubmodule N) = N := by
  let b := (Module.Free.chooseBasis ℤ N).extendOfIsLattice ℚ
  calc
    B.dualSubmodule (B.flip.dualSubmodule N) =
        B.dualSubmodule (B.flip.dualSubmodule (Submodule.span ℤ (Set.range b))) :=
      congrArg (fun S => B.dualSubmodule (B.flip.dualSubmodule S))
        (span_range_extendOfIsLattice N).symm
    _ = Submodule.span ℤ (Set.range b) :=
      B.dualSubmodule_dualSubmodule_flip_of_basis hB b
    _ = N := span_range_extendOfIsLattice N

/-- Dualizing by `B` and then by `B.flip` recovers the original full `ℤ`-submodule. -/
theorem dualSubmodule_flip_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (N : Submodule ℤ V) [N.IsLattice ℚ] :
    B.flip.dualSubmodule (B.dualSubmodule N) = N := by
  let b := (Module.Free.chooseBasis ℤ N).extendOfIsLattice ℚ
  calc
    B.flip.dualSubmodule (B.dualSubmodule N) =
        B.flip.dualSubmodule (B.dualSubmodule (Submodule.span ℤ (Set.range b))) :=
      congrArg (fun S => B.flip.dualSubmodule (B.dualSubmodule S))
        (span_range_extendOfIsLattice N).symm
    _ = Submodule.span ℤ (Set.range b) :=
      B.dualSubmodule_flip_dualSubmodule_of_basis hB b
    _ = N := span_range_extendOfIsLattice N

namespace IntegralLattice

/-- The dual carrier of an integral lattice:
`x` belongs to it exactly when `L.form x y` is integral for every `y ∈ L`. -/
def dualCarrier (L : IntegralLattice V) : Submodule ℤ V :=
  L.form.dualSubmodule L.carrier

/-- The carrier of an integral lattice is contained in its dual carrier. -/
theorem le_dualCarrier (L : IntegralLattice V) : L.carrier ≤ L.dualCarrier :=
  L.le_dual

/-- Membership in the dual carrier is characterized by integral pairing with every element of the
lattice carrier. -/
@[simp]
theorem mem_dualCarrier_iff (L : IntegralLattice V) (x : V) :
    x ∈ L.dualCarrier ↔ ∀ y ∈ L.carrier, L.form x y ∈ (1 : Submodule ℤ ℚ) :=
  LinearMap.BilinForm.mem_dualSubmodule (B := L.form)

/-- The integral span of the rational basis obtained from Mathlib's chosen basis of `L` is the
carrier itself. -/
theorem span_range_rationalBasis (L : IntegralLattice V) :
    Submodule.span ℤ (Set.range L.rationalBasis) = L.carrier := by
  let b := Module.Free.chooseBasis ℤ L
  have hrange : Set.range L.rationalBasis = Set.range (L.carrier.subtype ∘ b) := by
    ext x
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (L.rationalBasis_apply i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, L.rationalBasis_apply i⟩
  rw [hrange, Set.range_comp, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- The dual carrier is the integral span of the bilinear dual basis to the carrier's rational basis
obtained from Mathlib's chosen basis of `L`. -/
theorem dualCarrier_eq_span_dualBasis (L : IntegralLattice V) [L.IsNondegenerate] :
    L.dualCarrier = Submodule.span ℤ
      (Set.range (L.form.dualBasis L.form_nondegenerate L.rationalBasis)) := by
  calc
    L.dualCarrier = L.form.dualSubmodule
        (Submodule.span ℤ (Set.range L.rationalBasis)) :=
      congrArg L.form.dualSubmodule L.span_range_rationalBasis.symm
    _ = _ := L.form.dualSubmodule_span_of_basis L.form_nondegenerate L.rationalBasis

/-- The dual carrier of a nondegenerate integral lattice is a full lattice in the same rational
ambient space. -/
noncomputable instance instIsLatticeDualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    L.dualCarrier.IsLattice ℚ := by
  rw [L.dualCarrier_eq_span_dualBasis]
  exact isLattice_span_basis (L.form.dualBasis L.form_nondegenerate L.rationalBasis)

/-- The dual carrier has the same rank as the original carrier and the ambient rational space. -/
theorem finrank_dualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    Module.finrank ℤ L.dualCarrier = Module.finrank ℚ V :=
  congr_arg Cardinal.toNat (Submodule.IsLattice.rank' ℚ L.dualCarrier)

/-- The pairing of a dual-lattice vector with a lattice vector, valued in `ℤ`. -/
noncomputable def dualPairing (L : IntegralLattice V) :
    L.dualCarrier →ₗ[ℤ] Module.Dual ℤ L :=
  L.form.dualSubmoduleToDual L.carrier

/-- The integral dual pairing becomes the ambient rational form after casting to `ℚ`. -/
@[simp]
theorem intCast_dualPairing_apply (L : IntegralLattice V) (x : L.dualCarrier) (y : L) :
    (L.dualPairing x y : ℚ) = L.form x y :=
  L.form.dualSubmoduleParing_spec x y

/-- The pairing with the carrier is perfect: every integral functional on `L` is represented by a
unique vector of `Lᵛ`. -/
noncomputable def dualPairingEquiv (L : IntegralLattice V) [L.IsNondegenerate] :
    L.dualCarrier ≃ₗ[ℤ] Module.Dual ℤ L :=
  dualSubmoduleEquivDual L.form L.form_nondegenerate L.carrier

/-- The perfect pairing equivalence agrees with the ambient rational form after casting to `ℚ`. -/
@[simp]
theorem intCast_dualPairingEquiv_apply (L : IntegralLattice V) [L.IsNondegenerate]
    (x : L.dualCarrier) (y : L) :
    (L.dualPairingEquiv x y : ℚ) = L.form x y :=
  L.intCast_dualPairing_apply x y

/-- A vector of the bilinear dual basis, regarded as an element of the dual carrier. -/
noncomputable def dualBasisElem (L : IntegralLattice V) [L.IsNondegenerate]
    (i : Module.Free.ChooseBasisIndex ℤ L) : L.dualCarrier :=
  ⟨L.form.dualBasis L.form_nondegenerate L.rationalBasis i, by
    rw [L.dualCarrier_eq_span_dualBasis]
    exact Submodule.subset_span (Set.mem_range_self i)⟩

/-- The underlying rational vector of `dualBasisElem` is the corresponding vector of the
bilinear dual basis. -/
@[simp]
theorem coe_dualBasisElem (L : IntegralLattice V) [L.IsNondegenerate]
    (i : Module.Free.ChooseBasisIndex ℤ L) :
    (L.dualBasisElem i : V) =
      L.form.dualBasis L.form_nondegenerate L.rationalBasis i :=
  by rw [dualBasisElem]

/-- Under the perfect-pairing equivalence, the bilinear dual basis of the ambient space is sent to
the module-dual basis of the carrier. -/
@[simp]
theorem dualPairingEquiv_dualBasisElem (L : IntegralLattice V) [L.IsNondegenerate]
    (i : Module.Free.ChooseBasisIndex ℤ L) :
    L.dualPairingEquiv (L.dualBasisElem i) =
      (Module.Free.chooseBasis ℤ L).dualBasis i := by
  let b := Module.Free.chooseBasis ℤ L
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  apply Int.cast_injective (α := ℚ)
  rw [L.intCast_dualPairingEquiv_apply, L.coe_dualBasisElem]
  calc
    L.form (L.form.dualBasis L.form_nondegenerate L.rationalBasis i) (b j : V) =
        L.form (L.form.dualBasis L.form_nondegenerate L.rationalBasis i)
          (L.rationalBasis j) := by rw [L.rationalBasis_apply]
    _ = if j = i then 1 else 0 :=
      L.form.apply_dualBasis_left L.form_nondegenerate L.rationalBasis i j
    _ = ((b.dualBasis i (b j) : ℤ) : ℚ) := by
      simp only [Basis.dualBasis_apply, Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp_all

/-- The basis of the dual carrier corresponding to Mathlib's chosen basis of `L`. -/
noncomputable def dualCarrierBasis (L : IntegralLattice V) [L.IsNondegenerate] :
    Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L.dualCarrier :=
  (Module.Free.chooseBasis ℤ L).dualBasis.map L.dualPairingEquiv.symm

/-- The basis of the dual carrier corresponding to Mathlib's chosen basis of `L` consists of the
ambient bilinear dual-basis vectors. -/
@[simp]
theorem dualCarrierBasis_apply (L : IntegralLattice V) [L.IsNondegenerate]
    (i : Module.Free.ChooseBasisIndex ℤ L) :
    L.dualCarrierBasis i = L.dualBasisElem i := by
  apply L.dualPairingEquiv.injective
  rw [dualCarrierBasis, Basis.map_apply, LinearEquiv.apply_symm_apply,
    L.dualPairingEquiv_dualBasisElem]

/-- Taking the flipped dual submodule of the dual carrier recovers the original carrier. -/
theorem flip_dualSubmodule_dualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    L.form.flip.dualSubmodule L.dualCarrier = L.carrier :=
  dualSubmodule_flip_dualSubmodule L.form L.form_nondegenerate L.carrier

/-- Taking the dual submodule twice recovers the original carrier. -/
@[simp]
theorem dualCarrier_dualCarrier (L : IntegralLattice V) [L.IsNondegenerate] :
    L.form.dualSubmodule L.dualCarrier = L.carrier := by
  have hflip : L.form.flip = L.form := by
    ext x y
    exact L.isSymm.eq y x
  rw [← hflip]
  exact L.flip_dualSubmodule_dualCarrier

/-- A vector pairs integrally with every vector of the dual carrier exactly when it belongs to the
original carrier. -/
-- This is deliberately not a simp lemma: `mem_dualCarrier_iff` already expands the quantified
-- domain on the left, so the simp-normal-form linter rejects this statement as a simp rule.
theorem forall_form_mem_one_dualCarrier_iff (L : IntegralLattice V) [L.IsNondegenerate]
    (x : V) :
    (∀ y ∈ L.dualCarrier, L.form x y ∈ (1 : Submodule ℤ ℚ)) ↔ x ∈ L.carrier := by
  rw [← LinearMap.BilinForm.mem_dualSubmodule, L.dualCarrier_dualCarrier]

end IntegralLattice

end TauCeti

