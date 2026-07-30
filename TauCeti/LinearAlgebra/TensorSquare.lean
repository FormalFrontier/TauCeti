/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import TauCeti.LinearAlgebra.SymmetricPower

/-!
# Decomposing a tensor square

When `2` is invertible, the tensor square of a module is the direct sum of its symmetric and
alternating parts. This file constructs the natural equivalence

`⨂[R]^2 M ≃ₗ[R] Sym[R]^2 M × ⋀[R]^2 M`

using the half-symmetrizer and half-antisymmetrizer. No freeness or finite-generation hypothesis
is needed.

## Main definitions

* `SymmetricPower.toTensorSquare` embeds a symmetric square by averaging the two orders.
* `exteriorPower.toTensorSquare` embeds an exterior square by alternating the two orders.
* `TauCeti.tensorSquareEquivSymmetricExterior` is the resulting direct-sum decomposition.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 6.
* Mathlib's `SymmetricPower` quotient API, by Kenny Lau.
* Mathlib's `exteriorPower` universal-property API, by Sophie Morel and Joël Riou.
-/

public section

open scoped TensorProduct

universe v

variable (R : Type) (M : Type v)
variable [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

namespace TauCeti

private theorem perm_fin_two_eq (e : Equiv.Perm (Fin 2)) :
    e = 1 ∨ e = Equiv.swap 0 1 := by
  by_cases h0 : e 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · apply Fin.eq_one_of_ne_zero
      intro h1
      exact one_ne_zero (e.injective (h1.trans h0.symm))
  · right
    have h0' : e 0 = 1 := Fin.eq_one_of_ne_zero _ h0
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using h0'
    · have h1 : e 1 = 0 := by
        by_contra h
        have h1' : e 1 = 1 := Fin.eq_one_of_ne_zero _ h
        exact one_ne_zero (e.injective (h1'.trans h0'.symm))
      simpa using h1

private noncomputable def tensorSwap :
    (⨂[R]^2 M) ≃ₗ[R] ⨂[R]^2 M :=
  PiTensorProduct.reindex R (fun _ : Fin 2 ↦ M) (Equiv.swap 0 1)

private noncomputable def symmetricProjection :
    (⨂[R]^2 M) →ₗ[R] ⨂[R]^2 M :=
  (⅟ (2 : R)) • (LinearMap.id + (tensorSwap R M).toLinearMap)

private theorem symmetricProjection_rel :
    addConGen (SymmetricPower.Rel R (Fin 2) M) ≤
      AddCon.ker (symmetricProjection R M).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e f =>
      apply (AddCon.ker_rel _).2
      rcases perm_fin_two_eq e with rfl | rfl
      · rfl
      · change symmetricProjection R M (PiTensorProduct.tprod R f) =
          symmetricProjection R M
            (PiTensorProduct.tprod R fun i ↦ f (Equiv.swap 0 1 i))
        -- Unfold the quotient relation to the corresponding equality of pure tensor powers.
        simp [symmetricProjection, tensorSwap, Equiv.symm_swap, add_comm]

end TauCeti

namespace SymmetricPower

/-- The embedding of the symmetric square in the tensor square, given on a pure symmetric
tensor by `x ⊗ₛ y ↦ ⅟2 • (x ⊗ₜ y + y ⊗ₜ x)`. -/
noncomputable def toTensorSquare : Sym[R]^2 M →ₗ[R] ⨂[R]^2 M where
  toFun :=
    (addConGen (Rel R (Fin 2) M)).lift
      (TauCeti.symmetricProjection R M).toAddMonoidHom
      (TauCeti.symmetricProjection_rel R M)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x ↦ by
    exact (TauCeti.symmetricProjection R M).map_smul r x

/-- The symmetric-square embedding is the half-sum of the two orders on pure tensors. -/
@[simp]
theorem toTensorSquare_tprod (f : Fin 2 → M) :
    toTensorSquare R M (⨂ₛ[R] i, f i) =
      (⅟ (2 : R)) •
        (PiTensorProduct.tprod R f +
          PiTensorProduct.tprod R (fun i ↦ f (Equiv.swap 0 1 i))) := by
  simp only [toTensorSquare, tprod, LinearMap.compMultilinearMap_apply, mk,
    LinearMap.coe_mk, AddHom.coe_mk, AddMonoidHom.toFun_eq_coe,
    TauCeti.symmetricProjection]
  rw [AddCon.lift_mk']
  simp [TauCeti.tensorSwap]

end SymmetricPower

namespace exteriorPower

private noncomputable def tensorSquareAlternating :
    M [⋀^Fin 2]→ₗ[R] (⨂[R]^2 M) where
  toMultilinearMap :=
    (⅟ (2 : R)) •
      (PiTensorProduct.tprod R -
        (PiTensorProduct.tprod R).domDomCongr (Equiv.swap 0 1))
  map_eq_zero_of_eq' f i j hij hne := by
    have hswap : (fun k ↦ f (Equiv.swap 0 1 k)) = f := by
      funext k
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    simp [MultilinearMap.domDomCongr_apply, hswap]

/-- The embedding of the exterior square in the tensor square, given on a pure wedge by
`x ∧ y ↦ ⅟2 • (x ⊗ₜ y - y ⊗ₜ x)`. -/
noncomputable def toTensorSquare : ⋀[R]^2 M →ₗ[R] ⨂[R]^2 M :=
  alternatingMapLinearEquiv (tensorSquareAlternating R M)

/-- The exterior-square embedding is the half-difference of the two orders on pure wedges. -/
@[simp]
theorem toTensorSquare_ιMulti (f : Fin 2 → M) :
    toTensorSquare R M (ιMulti R 2 f) =
      (⅟ (2 : R)) •
        (PiTensorProduct.tprod R f -
          PiTensorProduct.tprod R (fun i ↦ f (Equiv.swap 0 1 i))) := by
  simp [toTensorSquare, tensorSquareAlternating, MultilinearMap.domDomCongr_apply]

end exteriorPower

namespace TauCeti

private noncomputable def tensorSquareToSymmetricExterior :
    (⨂[R]^2 M) →ₗ[R] (Sym[R]^2 M) × (⋀[R]^2 M) :=
  (SymmetricPower.mk R (Fin 2) M).prod
    (PiTensorProduct.lift
      (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap)

private noncomputable def symmetricExteriorToTensorSquare :
    (Sym[R]^2 M) × (⋀[R]^2 M) →ₗ[R] ⨂[R]^2 M :=
  (SymmetricPower.toTensorSquare R M).coprod
    (exteriorPower.toTensorSquare R M)

end TauCeti

namespace SymmetricPower

/-- The symmetric quotient composed with the symmetric-square embedding is the identity. -/
theorem mk_comp_toTensorSquare :
    (SymmetricPower.mk R (Fin 2) M).comp
        (SymmetricPower.toTensorSquare R M) = LinearMap.id := by
  apply LinearMap.ext_on
    (SymmetricPower.span_tprod_eq_top (R := R) (ι := Fin 2) (M := M))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, SymmetricPower.toTensorSquare_tprod, map_smul, map_add]
  -- `SymmetricPower.mk` sends each tensor-power generator to its symmetric class.
  change (⅟ (2 : R)) • (⨂ₛ[R] i, f i) +
    (⅟ (2 : R)) • (⨂ₛ[R] i, f (Equiv.swap 0 1 i)) = ⨂ₛ[R] i, f i
  rw [SymmetricPower.tprod_equiv (Equiv.swap 0 1) f, ← add_smul,
    invOf_two_add_invOf_two, one_smul]

/-- Projecting the symmetric-square embedding back to the symmetric square is the identity. -/
@[simp]
theorem mk_toTensorSquare (x : Sym[R]^2M) :
    mk R (Fin 2) M (toTensorSquare R M x) = x :=
  DFunLike.congr_fun (mk_comp_toTensorSquare R M) x

/-- The map from the symmetric square to the tensor square is injective. -/
theorem toTensorSquare_injective :
    Function.Injective (toTensorSquare R M) := by
  intro x y h
  rw [← mk_toTensorSquare R M x, ← mk_toTensorSquare R M y, h]

end SymmetricPower

namespace exteriorPower

/-- The exterior projection vanishes on the symmetric-square embedding. -/
theorem lift_ιMulti_comp_symmetricPower_toTensorSquare :
    (PiTensorProduct.lift
      (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap).comp
        (SymmetricPower.toTensorSquare R M) = 0 := by
  apply LinearMap.ext_on
    (SymmetricPower.span_tprod_eq_top (R := R) (ι := Fin 2) (M := M))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.comp_apply, SymmetricPower.toTensorSquare_tprod, map_smul,
    map_add, PiTensorProduct.lift.tprod, LinearMap.zero_apply]
  -- The lifted wedge projection evaluates on pure tensors as `exteriorPower.ιMulti`.
  change (⅟ (2 : R)) •
    ((exteriorPower.ιMulti R 2) f +
      (exteriorPower.ιMulti R 2) (f ∘ Equiv.swap 0 1)) = 0
  rw [(exteriorPower.ιMulti R 2).map_swap f (by decide)]
  simp

/-- The exterior projection of an element embedded from the symmetric square vanishes. -/
@[simp]
theorem lift_ιMulti_symmetricPower_toTensorSquare (x : Sym[R]^2M) :
    PiTensorProduct.lift (ιMulti R 2 (M := M)).toMultilinearMap
        (SymmetricPower.toTensorSquare R M x) = 0 :=
  DFunLike.congr_fun (lift_ιMulti_comp_symmetricPower_toTensorSquare R M) x

end exteriorPower

namespace SymmetricPower

/-- The symmetric projection vanishes on the exterior-square embedding. -/
theorem mk_comp_exteriorPower_toTensorSquare :
    (SymmetricPower.mk R (Fin 2) M).comp
        (exteriorPower.toTensorSquare R M) = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.toTensorSquare_ιMulti, map_smul, map_sub, LinearMap.zero_apply]
  -- `SymmetricPower.mk` sends each tensor-power generator to its symmetric class.
  change (⅟ (2 : R)) •
    ((⨂ₛ[R] i, f i) - (⨂ₛ[R] i, f (Equiv.swap 0 1 i))) = 0
  rw [SymmetricPower.tprod_equiv (Equiv.swap 0 1) f]
  simp

/-- The symmetric projection of an element embedded from the exterior square vanishes. -/
@[simp]
theorem mk_exteriorPower_toTensorSquare (x : ⋀[R]^2 M) :
    mk R (Fin 2) M (exteriorPower.toTensorSquare R M x) = 0 :=
  DFunLike.congr_fun (mk_comp_exteriorPower_toTensorSquare R M) x

end SymmetricPower

namespace exteriorPower

/-- The exterior projection composed with the exterior-square embedding is the identity. -/
theorem lift_ιMulti_comp_toTensorSquare :
    (PiTensorProduct.lift
      (exteriorPower.ιMulti R 2 (M := M)).toMultilinearMap).comp
        (exteriorPower.toTensorSquare R M) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.toTensorSquare_ιMulti, map_smul, map_sub,
    PiTensorProduct.lift.tprod, LinearMap.id_apply]
  -- Expose the swapped family as precomposition so `AlternatingMap.map_swap` applies.
  rw [show (fun i ↦ f (Equiv.swap 0 1 i)) = f ∘ Equiv.swap 0 1 by rfl]
  have hswap :
      (exteriorPower.ιMulti R 2).toMultilinearMap
          (f ∘ Equiv.swap (0 : Fin 2) 1) =
        -(exteriorPower.ιMulti R 2).toMultilinearMap f :=
    (exteriorPower.ιMulti R 2).map_swap f (by decide)
  rw [hswap]
  simp

/-- Projecting the exterior-square embedding back to the exterior square is the identity. -/
@[simp]
theorem lift_ιMulti_toTensorSquare (x : ⋀[R]^2 M) :
    PiTensorProduct.lift (ιMulti R 2 (M := M)).toMultilinearMap
        (toTensorSquare R M x) = x :=
  DFunLike.congr_fun (lift_ιMulti_comp_toTensorSquare R M) x

/-- The map from the exterior square to the tensor square is injective. -/
theorem toTensorSquare_injective :
    Function.Injective (toTensorSquare R M) := by
  intro x y h
  rw [← lift_ιMulti_toTensorSquare R M x, ← lift_ιMulti_toTensorSquare R M y, h]

end exteriorPower

namespace TauCeti

private theorem symmetricExteriorToTensorSquare_comp :
    (symmetricExteriorToTensorSquare R M).comp
        (tensorSquareToSymmetricExterior R M) = LinearMap.id := by
  rw [symmetricExteriorToTensorSquare, tensorSquareToSymmetricExterior,
    LinearMap.coprod_comp_prod]
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := R))
  rintro _ ⟨f, rfl⟩
  simp only [LinearMap.add_apply, LinearMap.comp_apply, PiTensorProduct.lift.tprod,
    LinearMap.id_apply]
  -- The two components of the product map reduce to the symmetric class and wedge.
  change SymmetricPower.toTensorSquare R M (⨂ₛ[R] i, f i) +
      exteriorPower.toTensorSquare R M ((exteriorPower.ιMulti R 2) f) =
    PiTensorProduct.tprod R f
  rw [SymmetricPower.toTensorSquare_tprod, exteriorPower.toTensorSquare_ιMulti]
  rw [smul_add, smul_sub]
  abel_nf
  rw [two_smul, ← add_smul, invOf_two_add_invOf_two, one_smul]

private theorem tensorSquareToSymmetricExterior_comp :
    (tensorSquareToSymmetricExterior R M).comp
        (symmetricExteriorToTensorSquare R M) = LinearMap.id := by
  rw [tensorSquareToSymmetricExterior, symmetricExteriorToTensorSquare,
    LinearMap.prod_comp, LinearMap.comp_coprod, LinearMap.comp_coprod,
    SymmetricPower.mk_comp_toTensorSquare,
    exteriorPower.lift_ιMulti_comp_symmetricPower_toTensorSquare,
    SymmetricPower.mk_comp_exteriorPower_toTensorSquare,
    exteriorPower.lift_ιMulti_comp_toTensorSquare]
  rw [← LinearMap.fst_eq_coprod, ← LinearMap.snd_eq_coprod,
    LinearMap.pair_fst_snd]

/-- The tensor square is naturally the direct sum of its symmetric and exterior squares when
`2` is invertible. The forward map sends a tensor to its symmetric quotient and exterior
product. -/
noncomputable def tensorSquareEquivSymmetricExterior :
    (⨂[R]^2 M) ≃ₗ[R] (Sym[R]^2 M) × (⋀[R]^2 M) :=
  LinearEquiv.mk
    (tensorSquareToSymmetricExterior R M)
    (symmetricExteriorToTensorSquare R M)
    (fun x ↦ DFunLike.congr_fun (symmetricExteriorToTensorSquare_comp R M) x)
    (fun x ↦ DFunLike.congr_fun (tensorSquareToSymmetricExterior_comp R M) x)

/-- The tensor-square decomposition sends a pure tensor to its symmetric and exterior
classes. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_tprod (f : Fin 2 → M) :
    tensorSquareEquivSymmetricExterior R M (PiTensorProduct.tprod R f) =
      (⨂ₛ[R] i, f i, exteriorPower.ιMulti R 2 f) := by
  simp [tensorSquareEquivSymmetricExterior, tensorSquareToSymmetricExterior]
  rfl

/-- The inverse tensor-square decomposition is the sum of the symmetric and exterior
embeddings. -/
@[simp]
theorem tensorSquareEquivSymmetricExterior_symm_apply
    (x : (Sym[R]^2M) × (⋀[R]^2 M)) :
    (tensorSquareEquivSymmetricExterior R M).symm x =
      SymmetricPower.toTensorSquare R M x.1 + exteriorPower.toTensorSquare R M x.2 := by
  rfl

end TauCeti
