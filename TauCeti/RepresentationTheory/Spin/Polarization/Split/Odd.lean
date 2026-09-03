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
# The standard split odd-dimensional polarization

For a commutative ring `K`, the split odd quadratic space of rank `2n + 1` is
`(M* × M) × K`, where `M = Fin n → K`, with quadratic form

```text
  ((f, x), z) ↦ f x + z².
```

This file gives that space its canonical polarization. The two coordinate axes in the
hyperbolic summand are the isotropic subspaces, and the final scalar coordinate is the
orthogonal remainder. The vector with final coordinate one has quadratic norm one, so the
polarization can be used directly by the type-`B` spin representation.

## Main declarations

* `TauCeti.SplitOddSpace`: the standard split quadratic space `(M* × M) × K`.
* `TauCeti.splitOddForm`: its quadratic form `((f, x), z) ↦ f x + z²`.
* `TauCeti.splitOddPolarization`: its canonical polarization.
* `TauCeti.splitOddBasis`: the coordinate basis of the first isotropic summand.
* `TauCeti.splitOddRemainderOne`: the distinguished norm-one remainder vector.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate II.
* `TauCeti.RepresentationTheory.Spin.Polarization.Split.Even`, for the corresponding
  even-dimensional polarization. The odd-dimensional construction adds the scalar coordinate
  and its norm-one remainder.
-/

public section

namespace TauCeti

universe u

/-- The standard split odd-dimensional quadratic space on `Fin n → K`. -/
abbrev SplitOddSpace (K : Type u) [CommRing K] (n : ℕ) :=
  (Module.Dual K (Fin n → K) × (Fin n → K)) × K

/-- The standard split odd quadratic form, given by `((f, x), z) ↦ f x + z²`. -/
def splitOddForm (K : Type u) [CommRing K] (n : ℕ) :
    QuadraticForm K (SplitOddSpace K n) :=
  (QuadraticForm.dualProd K (Fin n → K)).prod (QuadraticMap.sq (R := K))

/-- Evaluation formula for the standard split odd quadratic form. -/
@[simp]
theorem splitOddForm_apply (K : Type u) [CommRing K] (n : ℕ)
    (x : SplitOddSpace K n) : splitOddForm K n x = x.1.1 x.1.2 + x.2 * x.2 := by
  simp [splitOddForm, QuadraticMap.sq]

/-- Polarization formula for the standard split odd quadratic form. -/
@[simp]
theorem polar_splitOddForm (K : Type u) [CommRing K] (n : ℕ)
    (x y : SplitOddSpace K n) :
    QuadraticMap.polar (splitOddForm K n) x y =
      x.1.1 y.1.2 + y.1.1 x.1.2 + 2 * x.2 * y.2 := by
  simp [QuadraticMap.polar]
  ring

/-- The coordinate axis in the hyperbolic summand. -/
private abbrev splitOddW (K : Type u) [CommRing K] (n : ℕ) :
    Submodule K (SplitOddSpace K n) :=
  ((⊥ : Submodule K (Module.Dual K (Fin n → K))).prod ⊤).prod ⊥

/-- The dual-coordinate axis in the hyperbolic summand. -/
private abbrev splitOddW' (K : Type u) [CommRing K] (n : ℕ) :
    Submodule K (SplitOddSpace K n) :=
  ((⊤ : Submodule K (Module.Dual K (Fin n → K))).prod ⊥).prod ⊥

/-- The final scalar coordinate, as the orthogonal remainder. -/
private abbrev splitOddLine (K : Type u) [CommRing K] (n : ℕ) :
    Submodule K (SplitOddSpace K n) :=
  (⊥ : Submodule K (Module.Dual K (Fin n → K) × (Fin n → K))).prod ⊤

/-- Coordinate identification of the first isotropic summand with the standard module. -/
private noncomputable def splitOddWEquiv (K : Type u) [CommRing K] (n : ℕ) :
    splitOddW K n ≃ₗ[K] Fin n → K where
  toFun x := x.1.1.2
  invFun x := ⟨((0, x), 0), by simp [splitOddW]⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨⟨f, x⟩, z⟩, hx⟩
    simp only [splitOddW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hx
    rcases hx with ⟨rfl, rfl⟩
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate identification of the second isotropic summand with the dual module. -/
private noncomputable def splitOddW'Equiv (K : Type u) [CommRing K] (n : ℕ) :
    splitOddW' K n ≃ₗ[K] Module.Dual K (Fin n → K) where
  toFun x := x.1.1.1
  invFun f := ⟨((f, 0), 0), by simp [splitOddW']⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨⟨f, x⟩, z⟩, hx⟩
    simp only [splitOddW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
      true_and] at hx
    rcases hx with ⟨rfl, rfl⟩
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate identification of the orthogonal remainder with the scalar module. -/
private noncomputable def splitOddLineEquiv (K : Type u) [CommRing K] (n : ℕ) :
    splitOddLine K n ≃ₗ[K] K where
  toFun z := z.1.2
  invFun z := ⟨((0, 0), z), by simp [splitOddLine]⟩
  left_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨p, z⟩, hz⟩
    simp only [splitOddLine, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hz
    subst p
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate decomposition of the two isotropic axes and the orthogonal remainder. -/
private noncomputable def splitOddDecompositionEquiv
    (K : Type u) [CommRing K] (n : ℕ) :
    ((splitOddW K n × splitOddW' K n) × splitOddLine K n) ≃ₗ[K] SplitOddSpace K n where
  toFun x := (x.1.1 : SplitOddSpace K n) + x.1.2 + x.2
  invFun x :=
    ((⟨((0, x.1.2), 0), by simp [splitOddW]⟩,
      ⟨((x.1.1, 0), 0), by simp [splitOddW']⟩),
      ⟨((0, 0), x.2), by simp [splitOddLine]⟩)
  left_inv x := by
    rcases x with ⟨⟨⟨⟨⟨f, a⟩, z⟩, ha⟩, ⟨⟨⟨g, b⟩, w⟩, hb⟩⟩,
      ⟨⟨p, c⟩, hc⟩⟩
    simp only [splitOddW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at ha
    simp only [splitOddW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
      true_and] at hb
    simp only [splitOddLine, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hc
    rcases ha with ⟨rfl, rfl⟩
    rcases hb with ⟨rfl, rfl⟩
    subst p
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        simp
      · apply Subtype.ext
        simp
    · apply Subtype.ext
      simp
  right_inv x := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' a x := by
    ext <;> simp [smul_add]

/-- The perfect pairing between the two isotropic coordinate axes. -/
private noncomputable def splitOddPairingEquiv (K : Type u) [CommRing K] (n : ℕ) :
    splitOddW' K n ≃ₗ[K] Module.Dual K (splitOddW K n) :=
  (splitOddW'Equiv K n).trans (splitOddWEquiv K n).dualMap

private theorem splitOddPairingEquiv_apply (K : Type u) [CommRing K] (n : ℕ)
    (y : splitOddW' K n) (x : splitOddW K n) :
    splitOddPairingEquiv K n y x = QuadraticMap.polar (splitOddForm K n) x y := by
  rcases x with ⟨⟨⟨f, x⟩, z⟩, hx⟩
  rcases y with ⟨⟨⟨g, y⟩, w⟩, hy⟩
  simp only [splitOddW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
    and_true] at hx
  simp only [splitOddW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
    true_and] at hy
  rcases hx with ⟨rfl, rfl⟩
  rcases hy with ⟨rfl, rfl⟩
  rw [splitOddPairingEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
  simp [splitOddWEquiv, splitOddW'Equiv]

private theorem splitOddPairing_separatingLeft (K : Type u) [CommRing K] (n : ℕ)
    (x : splitOddW K n)
    (hx : ∀ y : splitOddW' K n, QuadraticMap.polar (splitOddForm K n) x y = 0) :
    x = 0 := by
  apply (splitOddWEquiv K n).injective
  apply (Module.forall_dual_apply_eq_zero_iff K (splitOddWEquiv K n x)).1
  intro f
  let y : splitOddW' K n := (splitOddW'Equiv K n).symm f
  have hy := hx y
  simpa [splitOddWEquiv, splitOddW'Equiv, y] using hy

/-- The canonical polarization of the standard split odd quadratic space. -/
noncomputable def splitOddPolarization (K : Type u) [CommRing K] (n : ℕ) :
    SpinPolarizationData (splitOddForm K n) := by
  refine
    { W := splitOddW K n
      W' := splitOddW' K n
      line := splitOddLine K n
      decompositionEquiv := splitOddDecompositionEquiv K n
      decompositionEquiv_apply := fun x ↦ rfl
      isotropic_W := ?_
      isotropic_W' := ?_
      pairingEquiv := splitOddPairingEquiv K n
      pairingEquiv_apply := splitOddPairingEquiv_apply K n
      pairing_separatingLeft := splitOddPairing_separatingLeft K n
      lineCoordinate := (splitOddLineEquiv K n).toLinearMap
      lineCoordinate_injective := (splitOddLineEquiv K n).injective
      lineCoordinate_sq := ?_
      line_orthogonal_W := ?_
      line_orthogonal_W' := ?_ }
  · rintro ⟨⟨⟨f, x⟩, z⟩, hx⟩
    simp only [splitOddW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hx
    rcases hx with ⟨rfl, rfl⟩
    simp
  · rintro ⟨⟨⟨f, x⟩, z⟩, hx⟩
    simp only [splitOddW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
      true_and] at hx
    rcases hx with ⟨rfl, rfl⟩
    simp
  · rintro ⟨⟨p, z⟩, hz⟩
    simp only [splitOddLine, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hz
    subst p
    simp [splitOddLineEquiv]
  · rintro ⟨⟨p, z⟩, hz⟩ ⟨⟨⟨f, x⟩, w⟩, hw⟩
    simp only [splitOddLine, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hz
    simp only [splitOddW, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hw
    rcases hw with ⟨rfl, rfl⟩
    subst p
    simp
  · rintro ⟨⟨p, z⟩, hz⟩ ⟨⟨⟨f, x⟩, w⟩, hw⟩
    simp only [splitOddLine, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
      and_true] at hz
    simp only [splitOddW', Submodule.mem_prod, Submodule.mem_top, Submodule.mem_bot,
      true_and] at hw
    rcases hw with ⟨rfl, rfl⟩
    subst p
    simp

/-- The first isotropic summand of the split odd polarization is the coordinate axis. -/
@[simp]
theorem splitOddPolarization_W (K : Type u) [CommRing K] (n : ℕ) :
    (splitOddPolarization K n).W =
      ((⊥ : Submodule K (Module.Dual K (Fin n → K))).prod ⊤).prod ⊥ := by
  rw [splitOddPolarization]

/-- The second isotropic summand of the split odd polarization is the dual-coordinate axis. -/
@[simp]
theorem splitOddPolarization_W' (K : Type u) [CommRing K] (n : ℕ) :
    (splitOddPolarization K n).W' =
      ((⊤ : Submodule K (Module.Dual K (Fin n → K))).prod ⊥).prod ⊥ := by
  rw [splitOddPolarization]

/-- The orthogonal remainder of the split odd polarization is the final scalar axis. -/
@[simp]
theorem splitOddPolarization_line (K : Type u) [CommRing K] (n : ℕ) :
    (splitOddPolarization K n).line =
      (⊥ : Submodule K (Module.Dual K (Fin n → K) × (Fin n → K))).prod ⊤ := by
  rw [splitOddPolarization]

/-- The coordinate basis of the first isotropic summand. -/
noncomputable def splitOddBasis (K : Type u) [CommRing K] (n : ℕ) :
    Module.Basis (Fin n) K (splitOddPolarization K n).W :=
  (Pi.basisFun K (Fin n)).map <|
    (splitOddWEquiv K n).symm.trans
      (LinearEquiv.ofEq _ _ (splitOddPolarization_W K n).symm)

/-- A coordinate-basis vector is the corresponding standard vector on the second axis. -/
@[simp]
theorem coe_splitOddBasis (K : Type u) [CommRing K] (n : ℕ) (i : Fin n) :
    ((splitOddBasis K n i : (splitOddPolarization K n).W) : SplitOddSpace K n) =
      ((0, Pi.single i 1), 0) := by
  rw [splitOddBasis, Module.Basis.map_apply]
  simp [splitOddWEquiv]

/-- The distinguished vector of quadratic norm one in the orthogonal remainder. -/
noncomputable def splitOddRemainderOne (K : Type u) [CommRing K] (n : ℕ) :
    (splitOddPolarization K n).line :=
  ⟨((0, 0), 1), by simp [splitOddPolarization_line]⟩

/-- The distinguished remainder vector has the expected ambient coordinates. -/
@[simp]
theorem coe_splitOddRemainderOne (K : Type u) [CommRing K] (n : ℕ) :
    (splitOddRemainderOne K n : SplitOddSpace K n) = ((0, 0), 1) := by
  rw [splitOddRemainderOne]

/-- The distinguished remainder vector has quadratic norm one. -/
theorem splitOddForm_remainderOne (K : Type u) [CommRing K] (n : ℕ) :
    splitOddForm K n (splitOddRemainderOne K n : SplitOddSpace K n) = 1 := by
  simp

end TauCeti
