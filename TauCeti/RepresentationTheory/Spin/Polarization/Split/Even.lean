/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The standard split even-dimensional polarization

For a commutative ring `K`, the hyperbolic quadratic space on a finite free module `M` is
`M* × M` with quadratic form `(f, x) ↦ f x`. This file gives the coordinate instance
`M = Fin n → K` its canonical polarization: the two coordinate axes are the isotropic summands,
their polar pairing is evaluation, and the orthogonal remainder is zero.

Unlike the existence construction for a nondegenerate quadratic form over a separably closed
field, this polarization contains no choices. Its named coordinate basis can therefore be fed
directly into the spin representation and Kostant-lattice constructions.

## Main declarations

* `TauCeti.SplitEvenSpace`: the standard hyperbolic quadratic space `M* × M`.
* `TauCeti.splitEvenForm`: its quadratic form `(f, x) ↦ f x`.
* `TauCeti.splitEvenPolarization`: the canonical polarization by the two coordinate axes.
* `TauCeti.splitEvenBasis`: the coordinate basis of the first isotropic summand.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
-/

public section

namespace TauCeti

universe u

/-- The standard split even-dimensional quadratic space on `Fin n → K`: the product of its
dual coordinate module and coordinate module. -/
abbrev SplitEvenSpace (K : Type u) [CommRing K] (n : ℕ) :=
  Module.Dual K (Fin n → K) × (Fin n → K)

/-- The standard split quadratic form on `M* × M`, given by `(f, x) ↦ f x`. -/
def splitEvenForm (K : Type u) [CommRing K] (n : ℕ) :
    QuadraticForm K (SplitEvenSpace K n) :=
  QuadraticForm.dualProd K (Fin n → K)

/-- Evaluation formula for the standard split quadratic form. -/
@[simp]
theorem splitEvenForm_apply (K : Type u) [CommRing K] (n : ℕ)
    (x : SplitEvenSpace K n) : splitEvenForm K n x = x.1 x.2 := by
  simp [splitEvenForm]

/-- Polarization formula for the standard split quadratic form. -/
@[simp]
theorem polar_splitEvenForm (K : Type u) [CommRing K] (n : ℕ)
    (x y : SplitEvenSpace K n) :
    QuadraticMap.polar (splitEvenForm K n) x y = x.1 y.2 + y.1 x.2 := by
  simp [QuadraticMap.polar]
  ring

/-- The coordinate axis in the standard split even-dimensional space. -/
private abbrev splitEvenW (K : Type u) [CommRing K] (n : ℕ) :
    Submodule K (SplitEvenSpace K n) :=
  (⊥ : Submodule K (Module.Dual K (Fin n → K))).prod ⊤

/-- The dual-coordinate axis in the standard split even-dimensional space. -/
private abbrev splitEvenW' (K : Type u) [CommRing K] (n : ℕ) :
    Submodule K (SplitEvenSpace K n) :=
  (⊤ : Submodule K (Module.Dual K (Fin n → K))).prod ⊥

/-- The zero orthogonal remainder in the standard split even-dimensional space. -/
private abbrev splitEvenLine (K : Type u) [CommRing K] (n : ℕ) :
    Submodule K (SplitEvenSpace K n) := ⊥

/-- The first coordinate-axis equivalence used by the standard split polarization. -/
private noncomputable def splitEvenWEquiv (K : Type u) [CommRing K] (n : ℕ) :
    splitEvenW K n ≃ₗ[K] Fin n → K :=
  { toFun := fun x ↦ x.1.2
    invFun := fun x ↦ ⟨(0, x), by simp [splitEvenW]⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      rcases x with ⟨⟨f, x⟩, hx⟩
      simp only [splitEvenW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
        and_true] at hx
      subst f
      rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

/-- The second coordinate-axis equivalence used by the standard split polarization. -/
private noncomputable def splitEvenW'Equiv (K : Type u) [CommRing K] (n : ℕ) :
    splitEvenW' K n ≃ₗ[K] Module.Dual K (Fin n → K) :=
  { toFun := fun x ↦ x.1.1
    invFun := fun f ↦ ⟨(f, 0), by simp [splitEvenW']⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      rcases x with ⟨⟨f, x⟩, hx⟩
      simp only [splitEvenW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
        true_and] at hx
      subst x
      rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

/-- The coordinate decomposition equivalence used by the standard split polarization. -/
private noncomputable def splitEvenDecompositionEquiv
    (K : Type u) [CommRing K] (n : ℕ) :
    ((splitEvenW K n × splitEvenW' K n) × splitEvenLine K n) ≃ₗ[K] SplitEvenSpace K n :=
  { toFun := fun x ↦ (x.1.1 : SplitEvenSpace K n) + x.1.2 + x.2
    invFun := fun x ↦
      ((⟨(0, x.2), by simp [splitEvenW]⟩, ⟨(x.1, 0), by simp [splitEvenW']⟩),
        ⟨0, by simp [splitEvenLine]⟩)
    left_inv := fun x ↦ by
      rcases x with ⟨⟨⟨⟨f, a⟩, ha⟩, ⟨⟨g, b⟩, hb⟩⟩, ⟨⟨h, c⟩, hc⟩⟩
      simp only [splitEvenW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
        and_true] at ha
      simp only [splitEvenW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
        true_and] at hb
      simp only [splitEvenLine, Submodule.mem_bot, Prod.mk_eq_zero] at hc
      rcases hc with ⟨rfl, rfl⟩
      subst f
      subst b
      apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          simp
        · apply Subtype.ext
          simp
      · apply Subtype.ext
        apply Prod.ext <;> rfl
    right_inv := fun x ↦ by
      ext <;> simp
    map_add' := fun x y ↦ by
      ext <;> simp <;> ring
    map_smul' := fun a x ↦ by
      ext <;> simp [smul_add] }

/-- The polar pairing equivalence between the two coordinate axes. -/
private noncomputable def splitEvenPairingEquiv (K : Type u) [CommRing K] (n : ℕ) :
    splitEvenW' K n ≃ₗ[K] Module.Dual K (splitEvenW K n) :=
  (splitEvenW'Equiv K n).trans (splitEvenWEquiv K n).dualMap

private theorem splitEvenPairingEquiv_apply (K : Type u) [CommRing K] (n : ℕ)
    (y : splitEvenW' K n) (x : splitEvenW K n) :
    splitEvenPairingEquiv K n y x = QuadraticMap.polar (splitEvenForm K n) x y := by
  rcases x with ⟨⟨f, x⟩, hx⟩
  rcases y with ⟨⟨g, y⟩, hy⟩
  simp only [splitEvenW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
    and_true] at hx
  simp only [splitEvenW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
    true_and] at hy
  subst f
  subst y
  rw [splitEvenPairingEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
  simp [splitEvenWEquiv, splitEvenW'Equiv, polar_splitEvenForm]

private theorem splitEvenPairing_separatingLeft (K : Type u) [CommRing K] (n : ℕ)
    (x : splitEvenW K n)
    (hx : ∀ y : splitEvenW' K n, QuadraticMap.polar (splitEvenForm K n) x y = 0) :
    x = 0 := by
  rcases x with ⟨⟨g, a⟩, hg⟩
  simp only [splitEvenW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
    and_true] at hg
  subst g
  apply (splitEvenWEquiv K n).injective
  apply (Module.forall_dual_apply_eq_zero_iff K
    (splitEvenWEquiv K n ⟨(0, a), by simp [splitEvenW]⟩)).1
  intro f
  let y : splitEvenW' K n := (splitEvenW'Equiv K n).symm f
  have hy := hx y
  simpa [splitEvenWEquiv, splitEvenW'Equiv, y, polar_splitEvenForm] using hy

/-- The canonical polarization of the standard split quadratic space.

The coordinate axis is the first isotropic summand, the dual-coordinate axis is the second,
and the orthogonal remainder is zero. -/
noncomputable def splitEvenPolarization (K : Type u) [CommRing K] (n : ℕ) :
    SpinPolarizationData (splitEvenForm K n) := by
  refine
    { W := splitEvenW K n
      W' := splitEvenW' K n
      line := splitEvenLine K n
      decompositionEquiv := splitEvenDecompositionEquiv K n
      decompositionEquiv_apply := fun x ↦ rfl
      isotropic_W := ?_
      isotropic_W' := ?_
      pairingEquiv := splitEvenPairingEquiv K n
      pairingEquiv_apply := splitEvenPairingEquiv_apply K n
      pairing_separatingLeft := splitEvenPairing_separatingLeft K n
      lineCoordinate := 0
      lineCoordinate_injective := ?_
      lineCoordinate_sq := ?_
      line_orthogonal_W := ?_
      line_orthogonal_W' := ?_ }
  · rintro ⟨⟨f, x⟩, hx⟩
    simp only [splitEvenW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hx
    subst f
    simp
  · rintro ⟨⟨f, x⟩, hx⟩
    simp only [splitEvenW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
      true_and] at hx
    subst x
    simp
  · intro x y _
    exact Subsingleton.elim x y
  · intro z
    have hz : z = 0 := Subsingleton.elim z 0
    subst z
    simp
  · intro z x
    have hz : z = 0 := Subsingleton.elim z 0
    subst z
    simp
  · intro z y
    have hz : z = 0 := Subsingleton.elim z 0
    subst z
    simp

/-- The first isotropic summand of the standard split polarization is the coordinate axis. -/
@[simp]
theorem splitEvenPolarization_W (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W =
      (⊥ : Submodule K (Module.Dual K (Fin n → K))).prod ⊤ := by
  rw [splitEvenPolarization]

/-- The second isotropic summand of the standard split polarization is the dual-coordinate
axis. -/
@[simp]
theorem splitEvenPolarization_W' (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W' =
      (⊤ : Submodule K (Module.Dual K (Fin n → K))).prod ⊥ := by
  rw [splitEvenPolarization]

/-- The standard split even-dimensional polarization has no orthogonal remainder. -/
@[simp]
theorem splitEvenPolarization_line (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).line = ⊥ := by
  rw [splitEvenPolarization]

/-- The coordinate basis of the first isotropic summand in the standard split polarization. -/
noncomputable def splitEvenBasis (K : Type u) [CommRing K] (n : ℕ) :
    Module.Basis (Fin n) K (splitEvenPolarization K n).W :=
  (Pi.basisFun K (Fin n)).map <|
    (splitEvenWEquiv K n).symm.trans
      (LinearEquiv.ofEq _ _ (splitEvenPolarization_W K n).symm)

/-- A coordinate-basis vector of the first isotropic summand is the corresponding standard
coordinate vector on the second axis of the split space. -/
@[simp]
theorem coe_splitEvenBasis (K : Type u) [CommRing K] (n : ℕ) (i : Fin n) :
    ((splitEvenBasis K n i : (splitEvenPolarization K n).W) : SplitEvenSpace K n) =
      (0, Pi.single i 1) := by
  rw [splitEvenBasis, Module.Basis.map_apply]
  simp [splitEvenWEquiv]

end TauCeti
