/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# Normal Hopf ideals in quotient Hopf algebras

If `I ≤ J` are Hopf ideals of a commutative Hopf algebra `H`, the ideal defining `J`
after passage to `H ⧸ I` is the image of `J` under the quotient morphism. This file
shows that pulling that image back recovers `J`, and identifies it with the kernel of
the induced map `H ⧸ I ⟶ H ⧸ J`.

When `J` is normal, its image in `H ⧸ I` is normal by `HopfIdeal.IsNormal.map`.  Thus the
construction supplies the normal Hopf ideal needed to form successive affine-group quotients.

## Main declarations

* `TauCeti.HopfIdeal.comapOfSurjective_map_mkQuotient`: pulling the image of `J` back from
  `H ⧸ I` recovers `J`, provided `I ≤ J`.
* `TauCeti.CommHopfAlgCat.ker_quotientMapOfLe`: the Hopf ideal `J/I` is the kernel of the
  induced quotient map when the base is a field.

## References

This is part of the Hopf-algebra form of the third isomorphism theorem. It supplies Layer 3
normality-and-quotients infrastructure required by the unipotent-radical construction in Layer 5
of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u v

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H : _root_.CommHopfAlgCat.{v} R}

/-- Pulling the image of `J` in `H ⧸ I` back along the quotient morphism recovers `J`
when `I ≤ J`. -/
@[simp]
theorem comapOfSurjective_map_mkQuotient {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    (J.map (CommHopfAlgCat.mkQuotient H I).hom).comapOfSurjective
        (CommHopfAlgCat.mkQuotient H I).hom
        (CommHopfAlgCat.mkQuotient_surjective H I) = J := by
  rw [comapOfSurjective_map]
  have hker : kerOfSurjective (CommHopfAlgCat.mkQuotient H I).hom
      (CommHopfAlgCat.mkQuotient_surjective H I) = I := by
    simpa only [CommHopfAlgCat.hom_mkQuotient] using
      kerOfSurjective_mkBialgHom I
  rw [hker, sup_eq_left]
  exact hIJ

end HopfIdeal

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

variable {k : Type u} [Field k]
variable {H : _root_.CommHopfAlgCat.{v} k}

/-- The kernel Hopf ideal of the induced map `H ⧸ I ⟶ H ⧸ J` is the image of `J`
in `H ⧸ I`. -/
@[simp]
theorem ker_quotientMapOfLe {I J : HopfIdeal k H} (hIJ : I ≤ J) :
    HopfIdeal.ker (quotientMapOfLe H hIJ).hom = J.map (mkQuotient H I).hom := by
  apply HopfIdeal.ext
  intro q
  rw [HopfIdeal.mem_ker]
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := mkQuotient_surjective H I q
    rw [mkQuotient_apply] at hq ⊢
    rw [quotientMapOfLe_mk] at hq
    exact HopfIdeal.mem_map_of_mem (mkQuotient H I).hom
      ((HopfIdeal.mem_toIdeal (I := J)).mp ((mkQuotient_eq_zero_iff H J x).mp hq))
  · intro hq
    rw [HopfIdeal.mem_map_iff_of_surjective (mkQuotient_surjective H I)] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    rw [mkQuotient_apply]
    rw [quotientMapOfLe_mk]
    exact (mkQuotient_eq_zero_iff H J x).mpr
      ((HopfIdeal.mem_toIdeal (I := J)).mpr hx)

end CommHopfAlgCat

end TauCeti
