/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.LinearAlgebra.BilinearForm.Squares

/-!
# Exterior squares and skew-adjoint endomorphisms

A nondegenerate symmetric bilinear form identifies the second exterior power with its
skew-adjoint endomorphisms.  The construction factors through alternating bilinear forms and the
canonical pairing between the exterior power of the dual and the dual of the exterior power.

## Main definitions

* `TauCeti.exteriorSquareEquivSkewAdjoint`: the linear equivalence from the second exterior power
  to the skew-adjoint endomorphisms.

## Main results

* `TauCeti.exteriorSquareEquivSkewAdjoint_apply_ιMulti_apply`: the action of a decomposable
  bivector.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 3,
  "the Lie algebra `𝔰𝔬(V) ≅ ⋀²V` inside the Clifford algebra".
-/

public section

open LinearMap (BilinForm)

universe u v

namespace TauCeti

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

private def alternatingBilinFormSubmodule : Submodule K (BilinForm K V) where
  carrier := { A | A.IsAlt }
  zero_mem' := LinearMap.BilinForm.isAlt_zero
  add_mem' hA hC := hA.add hC
  smul_mem' c _ hA := hA.smul c

private theorem mem_alternatingBilinFormSubmodule (A : BilinForm K V) :
    A ∈ alternatingBilinFormSubmodule (K := K) (V := V) ↔ A.IsAlt := Iff.rfl

private theorem BilinForm.IsAlt.linearMapIsAlt {B : BilinForm K V} (hB : B.IsAlt) :
    LinearMap.IsAlt B := by
  simpa only [LinearMap.BilinForm.IsAlt] using hB

private noncomputable def exteriorDualEquivAlternatingBilinForm :
    Module.Dual K (⋀[K]^2 V) ≃ₗ[K] alternatingBilinFormSubmodule (K := K) (V := V) where
  toFun ψ := ⟨BilinForm.ofExteriorSquareDual ψ,
    (mem_alternatingBilinFormSubmodule _).mpr (BilinForm.isAlt_ofExteriorSquareDual ψ)⟩
  invFun A := exteriorPower.alternatingMapLinearEquiv
    (LinearMap.IsAlt.toAlternatingMap
      (BilinForm.IsAlt.linearMapIsAlt ((mem_alternatingBilinFormSubmodule _).mp A.property)))
  left_inv ψ := by
    apply BilinForm.ofExteriorSquareDual_injective
    ext x y
    rw [BilinForm.ofExteriorSquareDual_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.IsAlt.toAlternatingMap_apply, BilinForm.ofExteriorSquareDual_apply]
    simp
  right_inv A := by
    apply Subtype.ext
    ext x y
    rw [BilinForm.ofExteriorSquareDual_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.IsAlt.toAlternatingMap_apply]
    simp
  map_add' ψ φ := by
    apply Subtype.ext
    ext x y
    simp
  map_smul' c ψ := by
    apply Subtype.ext
    ext x y
    simp

variable [FiniteDimensional K V]

private noncomputable def symmCompLinear (B : BilinForm K V) (hB : B.Nondegenerate) :
    BilinForm K V →ₗ[K] Module.End K V where
  toFun A := A.symmCompOfNondegenerate B hB
  map_add' A C := by
    apply B.compLeft_injective hB
    ext x y
    simp [LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply]
  map_smul' c A := by
    apply B.compLeft_injective hB
    ext x y
    simp [LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply]

private theorem compLeft_symmComp (B : BilinForm K V) (hB : B.Nondegenerate)
    (A : BilinForm K V) : B.compLeft (A.symmCompOfNondegenerate B hB) = A := by
  ext x y
  exact A.symmCompOfNondegenerate_left_apply hB y x

private theorem symmComp_compLeft (B : BilinForm K V) (hB : B.Nondegenerate)
    (f : Module.End K V) : (B.compLeft f).symmCompOfNondegenerate B hB = f := by
  apply B.compLeft_injective hB
  rw [compLeft_symmComp]

private noncomputable def endEquivBilinForm (B : BilinForm K V) (hB : B.Nondegenerate) :
    Module.End K V ≃ₗ[K] BilinForm K V where
  toLinearMap := LinearMap.llcomp K V V (V →ₗ[K] K) B
  invFun := symmCompLinear B hB
  left_inv := symmComp_compLeft B hB
  right_inv := compLeft_symmComp B hB

omit [FiniteDimensional K V] in
private theorem isAlt_compLeft_of_skewAdjoint (B : BilinForm K V) (hBsymm : B.IsSymm)
    [Invertible (2 : K)] (f : Module.End K V) (hf : f ∈ B.skewAdjointSubmodule) :
    (B.compLeft f).IsAlt := by
  intro x
  have hskew := (LinearMap.mem_skewAdjointSubmodule f).mp hf x x
  have ha : B (f x) x = -B (f x) x := by
    simpa [hBsymm.eq] using hskew
  calc
    B (f x) x = ⅟(2 : K) * (2 * B (f x) x) := by
      rw [← mul_assoc, invOf_mul_self, one_mul]
    _ = 0 := by rw [two_mul, add_eq_zero_iff_eq_neg.mpr ha, mul_zero]

omit [FiniteDimensional K V] in
private theorem skewAdjoint_of_isAlt_compLeft (B : BilinForm K V) (hBsymm : B.IsSymm)
    (f : Module.End K V) (hf : (B.compLeft f).IsAlt) : f ∈ B.skewAdjointSubmodule := by
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  have hxy := congrArg Neg.neg (hf.neg_eq x y)
  calc
    B (f x) y = -B (f y) x := by simpa using hxy
    _ = -B x (f y) := by rw [hBsymm.eq]
    _ = B x ((-f) y) := by simp

private noncomputable def skewAdjointEquivAlternatingBilinForm
    (B : BilinForm K V) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    [Invertible (2 : K)] :
    skewAdjointLieSubalgebra B ≃ₗ[K] alternatingBilinFormSubmodule (K := K) (V := V) :=
  LinearEquiv.ofSubmodules (endEquivBilinForm B hB)
    B.skewAdjointSubmodule (alternatingBilinFormSubmodule (K := K) (V := V)) <| by
      ext A
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact isAlt_compLeft_of_skewAdjoint B hBsymm f hf
      · intro hA
        refine ⟨A.symmCompOfNondegenerate B hB,
          skewAdjoint_of_isAlt_compLeft B hBsymm _ ?_, ?_⟩
        · rwa [compLeft_symmComp]
        · exact compLeft_symmComp B hB A

private noncomputable def skewAdjointEquivExteriorDual
    (B : BilinForm K V) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    [Invertible (2 : K)] :
    skewAdjointLieSubalgebra B ≃ₗ[K] Module.Dual K (⋀[K]^2 V) :=
  (skewAdjointEquivAlternatingBilinForm B hB hBsymm).trans
    exteriorDualEquivAlternatingBilinForm.symm

private theorem skewAdjointEquivExteriorDual_apply_ιMulti
    (B : BilinForm K V) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    [Invertible (2 : K)] (f : skewAdjointLieSubalgebra B) (x y : V) :
    skewAdjointEquivExteriorDual B hB hBsymm f
      (exteriorPower.ιMulti K 2 ![x, y]) = B ((f : Module.End K V) x) y := by
  -- Expose the composite equivalence as evaluation of its alternating-map representative.
  change exteriorPower.alternatingMapLinearEquiv
    (LinearMap.IsAlt.toAlternatingMap
      (BilinForm.IsAlt.linearMapIsAlt (isAlt_compLeft_of_skewAdjoint B hBsymm f f.property)))
      (exteriorPower.ιMulti K 2 ![x, y]) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [LinearMap.IsAlt.toAlternatingMap_apply]
  simp

private theorem pairingDual_bijective (n : ℕ) :
    Function.Bijective (exteriorPower.pairingDual K V n) := by
  classical
  let b := Module.Free.chooseBasis K V
  let : LinearOrder (Module.Free.ChooseBasisIndex K V) := linearOrderOfSTO WellOrderingRel
  let sourceBasis := b.dualBasis.exteriorPower n
  let targetBasis := (b.exteriorPower n).dualBasis
  have hmap : exteriorPower.pairingDual K V n =
      (sourceBasis.equiv targetBasis (Equiv.refl _)).toLinearMap := by
    apply sourceBasis.ext
    intro s
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply]
    dsimp [sourceBasis, targetBasis]
    rw [exteriorPower.basis_apply]
    -- Identify the chosen dual-basis vector with the corresponding coordinate functional.
    rw [show (b.exteriorPower n).dualBasis s = (b.exteriorPower n).coord s by
      exact congrFun (Module.Basis.coe_dualBasis (b.exteriorPower n)) s]
    -- Express the basis vector through the exterior product used by `pairingDual`.
    change exteriorPower.pairingDual K V n
      (exteriorPower.ιMulti_family K n b.dualBasis s) = (b.exteriorPower n).coord s
    -- Replace the dual-basis family by the definitionally equal coordinate family.
    rw [show exteriorPower.ιMulti_family K n b.dualBasis s =
      exteriorPower.ιMulti_family K n b.coord s by
        congr 1
        ext i x
        rw [Module.Basis.coe_dualBasis]]
    -- Fold the pairing into Mathlib's named dual exterior-basis functional.
    change exteriorPower.ιMultiDual K n b s = _
    exact (exteriorPower.basis_coord K n b s).symm
  rw [hmap]
  exact (sourceBasis.equiv targetBasis (Equiv.refl _)).bijective

private noncomputable def exteriorBilinDualEquiv (B : BilinForm K V) (hB : B.Nondegenerate)
    (n : ℕ) : ⋀[K]^n V ≃ₗ[K] Module.Dual K (⋀[K]^n V) :=
  LinearEquiv.ofBijective
    ((exteriorPower.pairingDual K V n).comp (exteriorPower.map n (B.toDual hB))) (by
      constructor
      · intro x y hxy
        exact exteriorPower.map_injective_field (B.toDual hB).injective
          ((pairingDual_bijective n).injective hxy)
      · intro y
        obtain ⟨z, rfl⟩ := (pairingDual_bijective n).surjective y
        obtain ⟨x, rfl⟩ := exteriorPower.map_surjective (B.toDual hB).surjective z
        exact ⟨x, rfl⟩)

/-- A nondegenerate symmetric bilinear form identifies the second exterior power with its
skew-adjoint endomorphisms.  The sign is chosen to agree with the normalized Clifford bivector
action. -/
noncomputable def exteriorSquareEquivSkewAdjoint
    (B : BilinForm K V) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    [Invertible (2 : K)] : ⋀[K]^2 V ≃ₗ[K] skewAdjointLieSubalgebra B :=
  (LinearEquiv.neg K).trans <|
    (exteriorBilinDualEquiv B hB 2).trans
      (skewAdjointEquivExteriorDual B hB hBsymm).symm

/-- A decomposable bivector acts by the standard skew-adjoint rank-two endomorphism. -/
@[simp]
theorem exteriorSquareEquivSkewAdjoint_apply_ιMulti_apply
    (B : BilinForm K V) (hB : B.Nondegenerate) (hBsymm : B.IsSymm)
    [Invertible (2 : K)] (u v x : V) :
    ((exteriorSquareEquivSkewAdjoint B hB hBsymm
      (exteriorPower.ιMulti K 2 ![u, v]) : skewAdjointLieSubalgebra B) : Module.End K V) x =
      B v x • u - B u x • v := by
  apply (B.toDual hB).injective
  ext y
  rw [B.toDual_def hB, B.toDual_def hB,
    ← skewAdjointEquivExteriorDual_apply_ιMulti B hB hBsymm]
  -- Cancel the outer equivalences and expose the induced exterior-power pairing.
  rw [show skewAdjointEquivExteriorDual B hB hBsymm
      (exteriorSquareEquivSkewAdjoint B hB hBsymm
        (exteriorPower.ιMulti K 2 ![u, v])) =
      exteriorBilinDualEquiv B hB 2
        (-exteriorPower.ιMulti K 2 ![u, v]) by
    simp [exteriorSquareEquivSkewAdjoint]]
  unfold exteriorBilinDualEquiv
  rw [map_neg]
  -- Normalize the composite linear map to the scalar pairing evaluated on decomposable inputs.
  change -((exteriorPower.pairingDual K V 2)
      ((exteriorPower.map 2 (B.toDual hB))
        (exteriorPower.ιMulti K 2 ![u, v])))
      (exteriorPower.ιMulti K 2 ![x, y]) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  simp [Matrix.det_fin_two, B.toDual_def hB]

end TauCeti
