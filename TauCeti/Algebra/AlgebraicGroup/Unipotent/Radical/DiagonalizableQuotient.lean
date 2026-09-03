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
# Unipotent radicals from geometrically semisimple quotients

Let `H` represent a finite-type affine group and let a morphism from a coordinate algebra with
geometrically semisimple points to `H` represent a quotient homomorphism from that group. If its
kernel is connected, normal, smooth, and unipotent, then that kernel is the unipotent radical.

Indeed, the kernel is contained in the radical by maximality. In the other direction, the image
of the smooth unipotent radical in the geometrically semisimple target is reduced and unipotent,
hence trivial. This forces the radical to lie in the kernel.

## Main declaration

* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_geometricallySemisimple`:
  a unipotent kernel with geometrically semisimple target is the unipotent radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 12.40 and §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A connected normal smooth unipotent kernel of a homomorphism to a group with geometrically
semisimple points is the unipotent radical. -/
theorem unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_geometricallySemisimple
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : geometricallySemisimplePointsCommHopfAlgProperty k D.obj)
    (f : D.obj ⟶ H.obj)
    (hf : HopfIdeal.IsUnipotentRadicalCandidate H
      (CommHopfAlgCat.kernelHopfIdeal f)) :
    unipotentRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f := by
  apply le_antisymm
  · exact unipotentRadicalDefiningIdeal_le H _ hf
  · rw [CommHopfAlgCat.kernelHopfIdeal_le_iff]
    let J := unipotentRadicalDefiningIdeal H
    let Q := quotient H J
    let q : H.obj ⟶ Q.obj := CommHopfAlgCat.mkQuotient H.obj J
    let g : D.obj ⟶ Q.obj := f ≫ q
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
    have hker : HopfIdeal.ker g.hom = HopfIdeal.augmentation k D :=
      eq_augmentation_of_geometricallySemisimple_of_geometricallyUnipotent
        D (HopfIdeal.ker g.hom)
        (geometricallySemisimplePointsCommHopfAlgProperty_of_surjective k
          (mkQuotient D (HopfIdeal.ker g.hom)).hom
          (Ideal.Quotient.mkₐ_surjective k (HopfIdeal.ker g.hom).toIdeal) hD)
        himage
    have hg : g = _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom k Q.obj).comp
          (Bialgebra.counitBialgHom k D)) := by
      rw [← Category.id_comp g]
      apply (CommHopfAlgCat.comp_eq_unit_comp_counit_iff (𝟙 D.obj) g).mpr
      rw [CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective
          (𝟙 D.obj) Function.surjective_id,
        ← hker, HopfIdeal.ker_toIdeal]
      exact fun _ hx ↦ hx
    exact hg

end FiniteTypeCommHopfAlgCat

end

end TauCeti
