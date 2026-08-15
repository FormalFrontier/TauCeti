/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.FieldTheory.SquareClassGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Norm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpecialOrthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.CliffordAlgebra.CartanDieudonne
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The spinor norm

The Clifford norm of a Lipschitz element is a square on the kernel of its orthogonal action.
It therefore descends to the orthogonal group modulo square classes. Restricting this homomorphism
to the special orthogonal group gives the spinor norm, whose kernel is exactly the image of the
Spin group.

## Main results

* `TauCeti.CliffordAlgebra.orthogonalSpinorNorm`: the square-class-valued spinor norm on `O(Q)`.
* `TauCeti.CliffordAlgebra.spinorNorm`: its restriction to `SO(Q)`.
* `TauCeti.CliffordAlgebra.range_spinToSpecialOrthogonal_eq_ker_spinorNorm`: the Spin image is
  the kernel of the spinor norm.

## References

See H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

private theorem lipschitzToOrthogonal_surjective_of_invertible
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.Surjective (lipschitzToOrthogonal Q) := by
  have hf : @lipschitzToOrthogonal K V _ _ _ Q (inferInstance : Invertible (2 : K)) =
      @lipschitzToOrthogonal K V _ _ _ Q
        (invertibleOfNonzero (NeZero.ne (2 : K))) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [hf]
  exact lipschitzToOrthogonal_surjective Q hQ

omit [FiniteDimensional K V] in
private theorem inclusion_spinToSpecialOrthogonal_eq_spinToOrthogonal
    (Q : QuadraticForm K V) (x : spinGroup Q) :
    Subgroup.inclusion (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q)
      (spinToSpecialOrthogonal Q x) = spinToOrthogonal Q x := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  -- Imported bundled definitions are opaque here, so compare their public vector equations.
  change (((spinToSpecialOrthogonal Q x : QuadraticMap.specialOrthogonalGroup Q) :
    V ≃ₗ[K] V) v) = (((spinToOrthogonal Q x : QuadraticMap.orthogonalGroup Q) :
      V ≃ₗ[K] V) v)
  rw [coe_spinToSpecialOrthogonal_apply, coe_spinToOrthogonal_apply]

omit [FiniteDimensional K V] in
private theorem pinToOrthogonal_eq_lipschitzToOrthogonal
    (Q : QuadraticForm K V) (p : pinGroup Q) :
    pinToOrthogonal Q p = lipschitzToOrthogonal Q (pinToLipschitz Q p) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp only [coe_pinToOrthogonal_apply, coe_lipschitzToOrthogonal_apply]

/-- The Clifford norm of an element acting trivially on the quadratic space is a square. -/
theorem isSquare_lipschitzNorm_of_mem_ker (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (x : lipschitzGroup Q) (hx : x ∈ MonoidHom.ker (lipschitzToOrthogonal Q)) :
    IsSquare (lipschitzNorm Q x) := by
  let x₀ : CliffordAlgebra Q := ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  have hcomm : ∀ w : V, involute (Q := Q) x₀ * ι Q w = ι Q w * x₀ := by
    intro w
    have haction : lipschitzVectorAction Q x w = w := by
      have h := congrArg (fun g : QuadraticMap.orthogonalGroup Q => ((g : V ≃ₗ[K] V) w))
        (MonoidHom.mem_ker.mp hx)
      rw [coe_lipschitzToOrthogonal_apply] at h
      exact h
    have h := ι_lipschitzVectorAction_apply (Q := Q) x w
    rw [haction] at h
    have h' := congrArg (fun z : CliffordAlgebra Q => z * x₀) h
    simpa [x₀, mul_assoc] using h'.symm
  obtain ⟨r, hr⟩ := exists_eq_algebraMap_of_involute_mul_ι_eq_ι_mul Q hQ x₀ hcomm
  have hr₀ : r ≠ 0 := by
    intro hr₀
    have hx₀ : x₀ = 0 := by simpa [hr₀] using hr
    exact Units.ne_zero (x : (CliffordAlgebra Q)ˣ) hx₀
  let a : Kˣ := Units.mk0 r hr₀
  refine ⟨a, ?_⟩
  apply Units.ext
  apply algebraMap_injective Q
  -- Read the unit equality through the scalar embedding into the Clifford algebra.
  change algebraMap K (CliffordAlgebra Q) (lipschitzNorm Q x : K) =
    algebraMap K (CliffordAlgebra Q) ((a * a : Kˣ) : K)
  rw [← star_mul_self_eq_algebraMap_lipschitzNorm]
  -- Replace the coerced Lipschitz unit by the scalar Clifford element found above.
  change star x₀ * x₀ = _
  rw [hr]
  simp only [star_algebraMap, map_mul, Units.val_mul]
  rfl

private noncomputable def lipschitzSquareClassHom (Q : QuadraticForm K V) :
    lipschitzGroup Q →* Multiplicative (SquareClassGroup K) :=
  squareClassHom.comp (lipschitzNorm Q)

private theorem ker_lipschitzToOrthogonal_le_ker_lipschitzSquareClassHom
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    MonoidHom.ker (lipschitzToOrthogonal Q) ≤ MonoidHom.ker (lipschitzSquareClassHom Q) := by
  intro x hx
  rw [MonoidHom.mem_ker]
  simpa [lipschitzSquareClassHom] using isSquare_lipschitzNorm_of_mem_ker Q hQ x hx

private noncomputable def spinorNormDescentData (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    {g : lipschitzGroup Q →* Multiplicative (SquareClassGroup K) //
      MonoidHom.ker (lipschitzToOrthogonal Q) ≤ MonoidHom.ker g} :=
  ⟨lipschitzSquareClassHom Q,
    ker_lipschitzToOrthogonal_le_ker_lipschitzSquareClassHom Q hQ⟩

/-- The Clifford norm modulo squares, descended through the Lipschitz action to `O(Q)`. -/
noncomputable def orthogonalSpinorNorm (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    QuadraticMap.orthogonalGroup Q →* Multiplicative (SquareClassGroup K) := by
  exact MonoidHom.liftOfSurjective
    (G₃ := Multiplicative (SquareClassGroup K))
    (lipschitzToOrthogonal Q) (lipschitzToOrthogonal_surjective_of_invertible Q hQ)
    (spinorNormDescentData Q hQ)

/-- The descended spinor norm evaluates on a Lipschitz action through its Clifford norm. -/
@[simp]
theorem orthogonalSpinorNorm_lipschitzToOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (x : lipschitzGroup Q) :
    orthogonalSpinorNorm Q hQ (lipschitzToOrthogonal Q x) =
      squareClassHom (lipschitzNorm Q x) := by
  simpa only [orthogonalSpinorNorm, MonoidHom.liftOfSurjective, spinorNormDescentData,
    lipschitzSquareClassHom, MonoidHom.comp_apply] using
    MonoidHom.liftOfRightInverse_comp_apply
      (G₃ := Multiplicative (SquareClassGroup K))
      (lipschitzToOrthogonal Q)
      (Function.surjInv (lipschitzToOrthogonal_surjective_of_invertible Q hQ))
      (Function.rightInverse_surjInv (lipschitzToOrthogonal_surjective_of_invertible Q hQ))
      (spinorNormDescentData Q hQ) x

/-- The spinor norm of an orthogonal reflection is the square class of the negative norm of its
defining vector. -/
@[simp]
theorem orthogonalSpinorNorm_reflection (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (v : V) [Invertible (Q v)] :
    orthogonalSpinorNorm Q hQ (QuadraticMap.reflectionOrthogonal Q v) =
      squareClassHom (-(unitOfInvertible (Q v))) := by
  rw [← lipschitzToOrthogonal_unitι Q v, orthogonalSpinorNorm_lipschitzToOrthogonal,
    lipschitzNorm_unitι]

/-- The spinor norm on `SO(Q)`, obtained by restricting the orthogonal spinor norm. -/
noncomputable def spinorNorm (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    QuadraticMap.specialOrthogonalGroup Q →* Multiplicative (SquareClassGroup K) :=
  (orthogonalSpinorNorm Q hQ).comp
    (Subgroup.inclusion (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q))

/-- The spinor norm is the restriction of the orthogonal spinor norm to `SO(Q)`. -/
@[simp]
theorem spinorNorm_apply (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (g : QuadraticMap.specialOrthogonalGroup Q) :
    spinorNorm Q hQ g = orthogonalSpinorNorm Q hQ
      (Subgroup.inclusion (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q) g) := by
  rw [spinorNorm, MonoidHom.comp_apply]

/-- The Spin action has trivial spinor norm. -/
@[simp high]
theorem spinorNorm_spinToSpecialOrthogonal (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (x : spinGroup Q) : spinorNorm Q hQ (spinToSpecialOrthogonal Q x) = 1 := by
  rw [spinorNorm_apply, inclusion_spinToSpecialOrthogonal_eq_spinToOrthogonal]
  rw [← pinToOrthogonal_spinToPin]
  rw [pinToOrthogonal_eq_lipschitzToOrthogonal,
    orthogonalSpinorNorm_lipschitzToOrthogonal,
    lipschitzNorm_pinToLipschitz, map_one]

omit [FiniteDimensional K V] [Invertible (2 : K)] in
private theorem unitsMap_algebraMap_mem_lipschitzGroup [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (a : Kˣ) :
    Units.map (algebraMap K (CliffordAlgebra Q)) a ∈ lipschitzGroup Q := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ.ne_zero
  have hv' : Q v ≠ 0 := by simpa using hv
  let _ : Invertible (Q v) := invertibleOfNonzero hv'
  have hav : Q ((a : K) • v) ≠ 0 := by
    rw [QuadraticMap.map_smul]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero a) (Units.ne_zero a)) hv'
  let _ : Invertible (Q ((a : K) • v)) := invertibleOfNonzero hav
  let y := unitι Q ((a : K) • v) * (unitι Q v)⁻¹
  have hy : y = Units.map (algebraMap K (CliffordAlgebra Q)) a := by
    have hscale : unitι Q ((a : K) • v) =
        Units.map (algebraMap K (CliffordAlgebra Q)) a * unitι Q v := by
      apply Units.ext
      simp only [coe_unitι, Units.val_mul, Units.coe_map, map_smul, Algebra.smul_def]
      rfl
    dsimp only [y]
    rw [hscale, mul_inv_cancel_right]
  rw [← hy]
  exact mul_mem (unitι_mem_lipschitzGroup _) (inv_mem (unitι_mem_lipschitzGroup _))

omit [FiniteDimensional K V] [Invertible (2 : K)] in
private noncomputable def scalarLipschitz [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (a : Kˣ) : lipschitzGroup Q :=
  ⟨Units.map (algebraMap K (CliffordAlgebra Q)) a,
    unitsMap_algebraMap_mem_lipschitzGroup Q hQ a⟩

omit [FiniteDimensional K V] in
private theorem lipschitzNorm_scalarLipschitz [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (a : Kˣ) :
    lipschitzNorm Q (scalarLipschitz Q hQ a) = a * a := by
  apply Units.ext
  apply algebraMap_injective Q
  rw [← star_mul_self_eq_algebraMap_lipschitzNorm]
  simp only [scalarLipschitz, Units.coe_map, MonoidHom.coe_coe]
  rw [star_algebraMap, ← map_mul]
  rfl

omit [FiniteDimensional K V] in
private theorem scalarLipschitz_mem_ker [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (a : Kˣ) :
    scalarLipschitz Q hQ a ∈ MonoidHom.ker (lipschitzToOrthogonal Q) := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [coe_lipschitzToOrthogonal_apply]
  apply ι_injective Q
  rw [ι_lipschitzVectorAction_apply]
  simp only [scalarLipschitz, Units.coe_map, MonoidHom.coe_coe, AlgHom.commutes,
    Algebra.commutes, Units.coe_map_inv, Units.val_inv_eq_inv_val]
  rw [mul_assoc, ← map_mul]
  simp

private theorem exists_pinToOrthogonal_eq_of_spinorNorm_eq_one [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (g : QuadraticMap.orthogonalGroup Q) (hg : orthogonalSpinorNorm Q hQ g = 1) :
    ∃ p : pinGroup Q, pinToOrthogonal Q p = g := by
  obtain ⟨x, hx⟩ := lipschitzToOrthogonal_surjective_of_invertible Q hQ g
  have hsquare : IsSquare (lipschitzNorm Q x) := by
    have hsquareClass : squareClassHom (lipschitzNorm Q x) = 1 := by
      rw [← orthogonalSpinorNorm_lipschitzToOrthogonal Q hQ, hx, hg]
    simpa using hsquareClass
  obtain ⟨a, ha⟩ := hsquare
  let y : lipschitzGroup Q := scalarLipschitz Q hQ a⁻¹ * x
  have hynorm : lipschitzNorm Q y = 1 := by
    dsimp only [y]
    rw [map_mul, lipschitzNorm_scalarLipschitz, ha]
    simp
  have hyact : lipschitzToOrthogonal Q y = g := by
    dsimp only [y]
    rw [map_mul, MonoidHom.mem_ker.mp (scalarLipschitz_mem_ker Q hQ a⁻¹), hx, one_mul]
  let p : pinGroup Q :=
    ⟨((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      (pinGroup.units_mem_iff).2 ⟨y.2, y.val.isUnit.mem_unitary_of_star_mul_self (by
        rw [star_mul_self_eq_algebraMap_lipschitzNorm Q y, hynorm]
        exact map_one (algebraMap K (CliffordAlgebra Q)))⟩⟩
  refine ⟨p, ?_⟩
  have hpl : pinToLipschitz Q p = y := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_pinToLipschitz_apply]
  rw [pinToOrthogonal_eq_lipschitzToOrthogonal, hpl, hyact]

/-- The image of the Spin action on `SO(Q)` is exactly the kernel of the spinor norm. -/
theorem range_spinToSpecialOrthogonal_eq_ker_spinorNorm
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    MonoidHom.range (spinToSpecialOrthogonal Q) = MonoidHom.ker (spinorNorm Q hQ) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · ext g
    have hg : g = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact hV.elim _ _
    subst g
    simp
  let _ : Nontrivial V := hV
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr (spinorNorm_spinToSpecialOrthogonal Q hQ x)
  · intro g hg
    have hg' : orthogonalSpinorNorm Q hQ
        (Subgroup.inclusion (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q) g) = 1 :=
      MonoidHom.mem_ker.mp hg
    obtain ⟨p, hp⟩ := exists_pinToOrthogonal_eq_of_spinorNorm_eq_one Q hQ _ hg'
    have hpEven : (p : CliffordAlgebra Q) ∈ even Q :=
      mem_even_of_det_pinToOrthogonal_eq_one Q p (by
        rw [hp]
        exact (QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2).2)
    let x : spinGroup Q := ⟨(p : CliffordAlgebra Q), p.2, hpEven⟩
    refine ⟨x, ?_⟩
    have hxp : spinToPin Q x = p := by
      apply Subtype.ext
      rw [coe_spinToPin_apply]
    have horth : spinToOrthogonal Q x =
        Subgroup.inclusion (QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q) g := by
      rw [← pinToOrthogonal_spinToPin, hxp, hp]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [coe_spinToSpecialOrthogonal_apply]
    have hv := congrArg (fun z : QuadraticMap.orthogonalGroup Q => ((z : V ≃ₗ[K] V) v)) horth
    rw [coe_spinToOrthogonal_apply] at hv
    exact hv

end TauCeti.CliffordAlgebra
