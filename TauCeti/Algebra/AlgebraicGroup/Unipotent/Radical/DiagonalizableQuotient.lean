/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced

/-!
# Unipotent radicals from diagonalizable quotients

Let `H` represent a finite-type affine group and let a morphism from a diagonalizable coordinate
algebra to `H` represent a homomorphism from that group to a diagonalizable group. If its kernel
is connected, normal, smooth, and unipotent, then that kernel is the unipotent radical.

Indeed, the kernel is contained in the radical by maximality. In the other direction, the image
of the smooth unipotent radical in the diagonalizable target is reduced and unipotent, hence
trivial. This forces the radical to lie in the kernel.

## Main declaration

* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_diagonalizable`:
  a unipotent kernel with diagonalizable target is the unipotent radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 12.40 and §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.

This is the quotient criterion used to identify concrete unipotent radicals in Layer 5 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A connected normal smooth unipotent kernel of a homomorphism to a diagonalizable group is
the unipotent radical. -/
theorem unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_diagonalizable
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (G : FGCommGrpCat.{u})
    (f : (DiagonalizableGroup.coordinateRing k G).obj ⟶ H.obj)
    (hf : HopfIdeal.IsUnipotentRadicalCandidate H
      (CommHopfAlgCat.kernelHopfIdeal f)) :
    unipotentRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f := by
  apply le_antisymm
  · exact unipotentRadicalDefiningIdeal_le H _ hf
  · rw [CommHopfAlgCat.kernelHopfIdeal_le_iff]
    let J := unipotentRadicalDefiningIdeal H
    let Q := quotient H J
    let q : H.obj ⟶ Q.obj := CommHopfAlgCat.mkQuotient H.obj J
    let g : (DiagonalizableGroup.coordinateRing k G).obj ⟶ Q.obj := f ≫ q
    have hQ := smoothUnipotent_unipotentRadical H
    have hQ' := (smoothUnipotentCommHopfAlgProperty_iff k Q).mp hQ
    let _ : Algebra.Smooth k Q := hQ'.1
    let _ : IsReduced Q := isReduced_of_smooth_of_field k Q
    have hQunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k Q.obj := by
      rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
      exact hQ'.2
    let _ : IsReduced (CommHopfAlgCat.image g) :=
      isReduced_of_injective (CommHopfAlgCat.imageι g).hom
        (CommHopfAlgCat.imageι_injective g)
    have himage : geometricallyUnipotentPointsCommHopfAlgProperty k
        (CommHopfAlgCat.image g) :=
      geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced g hQunipotent
    have hker : HopfIdeal.ker g.hom =
        HopfIdeal.augmentation k (DiagonalizableGroup.coordinateRing k G) :=
      DiagonalizableGroup.eq_augmentation_of_geometricallyUnipotent k G
        (HopfIdeal.ker g.hom) himage
    have hg : g = _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom k Q.obj).comp
          (Bialgebra.counitBialgHom k (DiagonalizableGroup.coordinateRing k G))) := by
      apply _root_.CommHopfAlgCat.hom_ext
      apply BialgHom.coe_fn_injective
      funext x
      have hx : x - algebraMap k (DiagonalizableGroup.coordinateRing k G)
          (Coalgebra.counit (R := k) x) ∈
          HopfIdeal.augmentation k (DiagonalizableGroup.coordinateRing k G) := by
        rw [HopfIdeal.mem_augmentation]
        simp
      rw [← hker, HopfIdeal.mem_ker] at hx
      change g.hom x = algebraMap k Q.obj (Coalgebra.counit (R := k) x)
      rw [← sub_eq_zero]
      simpa only [map_sub, AlgHomClass.commutes] using hx
    exact hg

end FiniteTypeCommHopfAlgCat

end

end TauCeti
