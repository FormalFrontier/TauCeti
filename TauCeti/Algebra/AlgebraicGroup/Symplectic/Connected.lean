/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

/-!
# Geometric connectedness of the symplectic group

The coordinate Hopf algebra of the standard symplectic group `Sp_{2m}` is geometrically connected
over every field. The proof uses idempotents and algebraically closed points, avoiding an explicit
presentation of the coordinate algebra as an integral domain.

The formal proof architecture is adapted from
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected`.

Over an algebraically closed extension, an idempotent in a finite-type coordinate algebra is
constant once right translation by every rational point fixes it. Every standard symplectic root
subgroup is connected to the identity by its parameter over the polynomial ring. The root-subgroup
generation theorem for `Sp_{2m}` therefore makes every rational-point translation fix every
idempotent. This argument includes rank zero, where the family of roots is empty and the
generation theorem still applies.

## Main declaration

* `TauCeti.Symplectic.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  `Sp_{2m}` is geometrically connected.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §5.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.Symplectic

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local instance : IsScalarTower k K (Polynomial K) :=
  IsScalarTower.of_algebraMap_eq (by simp)

/-- Base-changed symplectic points identified with symplectic matrices. -/
private def baseChangeSymplecticPointsMulEquiv
    (m : ℕ) (A : Type u) [CommRing A] [Algebra k A] [Algebra K A]
    [IsScalarTower k K A] :
    WithConv (K ⊗[k] coordinateHopfAlgebra k m →ₐ[K] A) ≃*
      GLSymplecticFin m A :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
    (A := coordinateHopfAlgebra k m) (R := A)).symm.trans
      (pointsMulEquiv (R := k) (A := A) m)

private theorem baseChangeSymplecticPointsMulEquiv_mapValue
    (m : ℕ) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    [Algebra k B] [Algebra K B] [IsScalarTower k K B]
    (f : WithConv (K ⊗[k] coordinateHopfAlgebra k m →ₐ[K] A))
    (phi : A →ₐ[K] B) :
    baseChangeSymplecticPointsMulEquiv m B
        (AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k m) phi f) =
      GLSymplecticFin.map m A phi.toRingHom
        (baseChangeSymplecticPointsMulEquiv m A f) := by
  rw [baseChangeSymplecticPointsMulEquiv, MulEquiv.trans_apply,
    AlgHom.baseChangePointsMulEquiv_symm_mapValue,
    baseChangeSymplecticPointsMulEquiv, MulEquiv.trans_apply]
  exact pointsMulEquiv_mapValue (R := k) (A := A) (B := B) m
    (phi.restrictScalars k) _

/-- The polynomial path through a standard symplectic root subgroup. -/
private def rootPath (m : ℕ) (root : GLSymplecticFin.RootSubgroupIndex m) :
    WithConv (K ⊗[k] coordinateHopfAlgebra k m →ₐ[K] Polynomial K) :=
  (baseChangeSymplecticPointsMulEquiv (k := k) (K := K) m (Polynomial K)).symm
    (root.hom (Multiplicative.ofAdd Polynomial.X))

private theorem mapValue_rootPath
    (m : ℕ) (root : GLSymplecticFin.RootSubgroupIndex m) (c : K) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k m)
        (Polynomial.aevalTower (AlgHom.id K K) c) (rootPath (k := k) (K := K) m root) =
      (baseChangeSymplecticPointsMulEquiv (k := k) (K := K) m K).symm
        (root.hom (Multiplicative.ofAdd c)) := by
  apply (baseChangeSymplecticPointsMulEquiv (k := k) (K := K) m K).injective
  rw [baseChangeSymplecticPointsMulEquiv_mapValue (k := k) (K := K)]
  simp [rootPath]

private theorem mapValue_rootPath_zero
    (m : ℕ) (root : GLSymplecticFin.RootSubgroupIndex m) :
    AlgHom.mapValue (H := K ⊗[k] coordinateHopfAlgebra k m)
        (Polynomial.aevalTower (AlgHom.id K K) 0) (rootPath (k := k) (K := K) m root) = 1 := by
  simpa using mapValue_rootPath (k := k) (K := K) m root 0

private theorem rightTranslationAlgHom_eq_self_of_root
    (m : ℕ) [IsAlgClosed K] (e : K ⊗[k] coordinateHopfAlgebra k m)
    (he : IsIdempotentElem e) (root : GLSymplecticFin.RootSubgroupIndex m) (c : K) :
    HopfAlgebra.rightTranslationAlgHom
        ((baseChangeSymplecticPointsMulEquiv (k := k) (K := K) m K).symm
          (root.hom (Multiplicative.ofAdd c))) e = e := by
  let eval (a : K) : Polynomial K →ₐ[K] K :=
    Polynomial.aevalTower (AlgHom.id K K) a
  apply HopfAlgebra.rightTranslationAlgHom_eq_self_of_path e he _
    (rootPath (k := k) (K := K) m root) (eval c) (eval 0)
  · exact mapValue_rootPath (k := k) (K := K) m root c
  · exact mapValue_rootPath_zero (k := k) (K := K) m root

private theorem rightTranslationAlgHom_eq_self
    (m : ℕ) [IsAlgClosed K] (e : K ⊗[k] coordinateHopfAlgebra k m)
    (he : IsIdempotentElem e)
    (g : WithConv (K ⊗[k] coordinateHopfAlgebra k m →ₐ[K] K)) :
    HopfAlgebra.rightTranslationAlgHom g e = e := by
  let E := baseChangeSymplecticPointsMulEquiv (k := k) (K := K) m K
  let fixes (x : GLSymplecticFin m K) : Prop :=
    HopfAlgebra.rightTranslationAlgHom (E.symm x) e = e
  have fixes_one : fixes 1 := by
    dsimp only [fixes]
    rw [map_one, HopfAlgebra.rightTranslationAlgHom_one, AlgHom.id_apply]
  have fixes_mul {x y : GLSymplecticFin m K} (hx : fixes x) (hy : fixes y) :
      fixes (x * y) := by
    dsimp only [fixes] at hx hy ⊢
    rw [map_mul, HopfAlgebra.rightTranslationAlgHom_mul, AlgHom.comp_apply, hy, hx]
  have fixes_inv {x : GLSymplecticFin m K} (hx : fixes x) : fixes x⁻¹ := by
    dsimp only [fixes] at hx ⊢
    have h := DFunLike.congr_fun
      (HopfAlgebra.rightTranslationAlgHom_mul (E.symm x⁻¹) (E.symm x)) e
    rw [← map_mul E.symm, inv_mul_cancel x, map_one,
      HopfAlgebra.rightTranslationAlgHom_one,
      AlgHom.id_apply, AlgHom.comp_apply, hx] at h
    exact h.symm
  let P : Subgroup (GLSymplecticFin m K) :=
    { carrier := fixes
      one_mem' := fixes_one
      mul_mem' := fixes_mul
      inv_mem' := fixes_inv }
  have mem_P (x : GLSymplecticFin m K) : x ∈ P ↔ fixes x := Iff.rfl
  have hP : P = ⊤ := by
    apply GLSymplecticFin.eq_top_of_root_subgroups P
    intro root c
    exact (mem_P _).mpr
      (rightTranslationAlgHom_eq_self_of_root (k := k) (K := K) m e he root c.toAdd)
  have hg : E g ∈ P := by rw [hP]; exact Subgroup.mem_top _
  simpa only [fixes, MulEquiv.symm_apply_apply] using (mem_P _).mp hg

/-- The coordinate Hopf algebra of `Sp_{2m}` is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] (m : ℕ) :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k m) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_of_isAlgClosed]
  intro K _ _ _
  let H := coordinateHopfAlgebra k m
  let _ : Nontrivial H := Bialgebra.nontrivial (A := H) k
  let _ : Nontrivial (K ⊗[k] H) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k K H
      (RingHom.injective (algebraMap k H))
  have hconnected : ConnectedSpace (PrimeSpectrum (K ⊗[k] H)) :=
    HopfAlgebra.connectedSpace_primeSpectrum_of_forall_rightTranslationAlgHom_eq_self
      fun e he g ↦ rightTranslationAlgHom_eq_self (k := k) (K := K) m e he g
  let e : (H : Type u) ⊗[k] K ≃+* K ⊗[k] H :=
    (Algebra.TensorProduct.comm k H K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr hconnected

end

end TauCeti.Symplectic
