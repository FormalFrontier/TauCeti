/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation

/-!
# Central closed subgroup schemes

A closed subgroup of the affine group scheme `Spec H` is cut out by a Hopf ideal `I`, and it is
**central** when conjugating by its points does nothing. This file states that condition on `I`,
in the same coordinate style as normality: the coordinate morphism of conjugation agrees with the
second projection modulo `I ⊗ H`, the ideal of `V(I) × G`.

The condition is proved equivalent to the functorial one, that every point of `V(I)` is a central
point of `G` in the sense of `TauCeti.HopfAlgebra.IsCentralPoint`. As for normality, one value
algebra suffices to detect it, namely `(H ⧸ I) ⊗[R] H`, which carries the tautological point of
the subgroup together with the tautological point of the ambient group.

Two immediate consequences record that the notion behaves as expected. A central Hopf ideal is
normal, and the zero Hopf ideal — the one cutting out the whole group — is central exactly when
`H` is cocommutative, that is, exactly when `G` is commutative.

Centrality is *upward* closed in the lattice of Hopf ideals, since a larger Hopf ideal cuts out a
smaller closed subgroup. It is not closed downwards, so this file does not construct a smallest
central Hopf ideal; the centre `Z(G)` as a closed subgroup scheme needs the extra work of
producing a Hopf ideal from the cocommutativity defect of `H`.

## Main declarations

* `TauCeti.HopfIdeal.IsCentral`: centrality of a Hopf ideal, that is, of the closed subgroup
  scheme it cuts out.

## Main results

* `TauCeti.CommHopfAlgCat.isCentral_iff_forall_isCentralPoint`: **a Hopf ideal is central exactly
  when the points it cuts out are central points over every value algebra.**
* `TauCeti.HopfIdeal.IsCentral.isNormal`: a central Hopf ideal is normal.
* `TauCeti.HopfIdeal.isCentral_bot_iff_isCocomm`: the whole group is central exactly when the
  coordinate Hopf algebra is cocommutative.
* `TauCeti.CommHopfAlgCat.isCentral_augmentation`: the trivial subgroup is central.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.k and §2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

The coordinate condition is the conjugation-triviality criterion for a central closed subgroup,
and mirrors the normality criterion of `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal`. This is
a prerequisite for the centre `Z(G)` in Layer 6, "Reductive and semisimple groups", of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

open TensorProduct WithConv

namespace TauCeti

universe u v

namespace HopfIdeal

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H] [_root_.HopfAlgebra R H]

/-- A Hopf ideal is **central** when the coordinate morphism of conjugation agrees with the
inclusion of the acted-on variable modulo `I ⊗ H`.

The first tensor factor of `TauCeti.HopfAlgebra.conjugationAlgHom` is the conjugating variable,
so the left tensor ideal is the ideal of `V(I) × G`: the condition says that conjugating an
arbitrary point of `G` by a point of the closed subgroup `V(I)` leaves it unchanged. -/
def IsCentral (I : HopfIdeal R H) : Prop :=
  ∀ x : H, HopfAlgebra.conjugationAlgHom (R := R) (H := H) x -
      Algebra.TensorProduct.includeRight x ∈ leftTensorIdeal (R := R) (H := H) I.toIdeal

/-- Centrality restated as the defining ideal membership. -/
theorem isCentral_def (I : HopfIdeal R H) :
    I.IsCentral ↔
      ∀ x : H, HopfAlgebra.conjugationAlgHom (R := R) (H := H) x -
        Algebra.TensorProduct.includeRight x ∈ leftTensorIdeal (R := R) (H := H) I.toIdeal :=
  Iff.rfl

/-- Centrality passes to larger Hopf ideals, which cut out smaller closed subgroups. -/
theorem IsCentral.mono {I J : HopfIdeal R H} (hI : I.IsCentral) (hIJ : I ≤ J) : J.IsCentral :=
  fun x ↦ leftTensorIdeal_mono R H (toIdeal_le_toIdeal.mpr hIJ) (hI x)

/-- A supremum of Hopf ideals is central as soon as one of them is; the closed subgroup it cuts
out is contained in the central one. -/
theorem isCentral_iSup_of_isCentral {ι : Sort*} {I : ι → HopfIdeal R H} {j : ι}
    (hj : (I j).IsCentral) : (⨆ i, I i).IsCentral :=
  hj.mono (le_sSup (Set.mem_range_self j))

/-- The coordinate morphism of conjugation, as a point, written with the underlying algebra maps
of the two tensor-factor inclusions. -/
private theorem toConv_conjugationAlgHom' :
    toConv (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) =
      toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)) *
          toConv (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)) *
        (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)))⁻¹ := by
  simpa using HopfAlgebra.toConv_conjugationAlgHom (R := R) (H := H)

/-- **The whole group is central exactly when its coordinate Hopf algebra is cocommutative.**
The zero Hopf ideal cuts out all of `Spec H`, so its centrality says that conjugation is trivial,
which for the convolution group of points is commutativity. -/
theorem isCentral_bot_iff_isCocomm :
    (⊥ : HopfIdeal R H).IsCentral ↔ _root_.Coalgebra.IsCocomm R H := by
  rw [isCentral_def, ← HopfAlgebra.commute_includeLeft_includeRight_iff_isCocomm R H,
    commute_iff_eq]
  have hzero : leftTensorIdeal (R := R) (H := H) (⊥ : HopfIdeal R H).toIdeal = ⊥ := by
    rw [bot_toIdeal, leftTensorIdeal_def, Ideal.map_bot]
  have hiff : (∀ x : H, HopfAlgebra.conjugationAlgHom (R := R) (H := H) x -
        Algebra.TensorProduct.includeRight x ∈
          leftTensorIdeal (R := R) (H := H) (⊥ : HopfIdeal R H).toIdeal) ↔
      HopfAlgebra.conjugationAlgHom (R := R) (H := H) =
        Algebra.TensorProduct.includeRight := by
    rw [hzero]
    refine ⟨fun hx ↦ AlgHom.ext fun x ↦ sub_eq_zero.mp (Ideal.mem_bot.mp (hx x)),
      fun he x ↦ ?_⟩
    rw [he]
    simp
  rw [hiff]
  constructor
  · intro he
    refine mul_inv_eq_iff_eq_mul.mp ?_
    rw [← toConv_conjugationAlgHom', he]
  · intro hc
    exact WithConv.toConv_injective
      ((toConv_conjugationAlgHom').trans (mul_inv_eq_iff_eq_mul.mpr hc))

end HopfIdeal

namespace CommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- Every point cut out by a central Hopf ideal is a central point of the ambient group, over
every value algebra. -/
theorem isCentralPoint_of_mem_quotientPointsSubgroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsCentral) (A : CommAlgCat.{v} R)
    {g : HopfAlgebra.points (R := R) (H := H) A} (hg : g ∈ quotientPointsSubgroup H I A) :
    HopfAlgebra.IsCentralPoint g := by
  rw [HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ h
  set g' : WithConv (↥H →ₐ[R] B) := AlgHom.mapValue φ g with hg'
  have hker : HopfIdeal.leftTensorIdeal (R := R) (H := ↥H) I.toIdeal ≤
      RingHom.ker (Algebra.TensorProduct.productMap g'.ofConv h.ofConv).toRingHom := by
    rw [HopfIdeal.leftTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hzero : g.ofConv y = 0 :=
      (mem_quotientPointsSubgroup_iff H I A g).mp hg y (HopfIdeal.mem_toIdeal.mp hy)
    simp [hg', hzero]
  have hconj : ∀ x : ↥H, (g' * h * g'⁻¹).ofConv x = h.ofConv x := by
    intro x
    have heval := AlgHom.congr_fun
      (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := ↥H) g' h) x
    have hsub : Algebra.TensorProduct.productMap g'.ofConv h.ofConv
        (HopfAlgebra.conjugationAlgHom (R := R) (H := ↥H) x -
          Algebra.TensorProduct.includeRight x) = 0 :=
      RingHom.mem_ker.mp (hker (hI x))
    rw [map_sub, sub_eq_zero] at hsub
    rw [← heval, AlgHom.comp_apply, hsub, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.productMap_right_apply]
  have : g' * h * g'⁻¹ = h :=
    WithConv.ofConv_injective (AlgHom.ext hconj)
  exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp this)

/-- If the points cut out by a Hopf ideal are central over the value algebra `(H ⧸ I) ⊗ H`, the
Hopf ideal is central. That single test algebra suffices: it carries the tautological point of
the closed subgroup together with the tautological point of the ambient group. -/
private theorem isCentral_of_isCentralPoint (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H)
    (hcentral : ∀ g ∈ quotientPointsSubgroup H I
        (CommAlgCat.of R (TensorProduct R (↥H ⧸ I.toIdeal) ↥H)),
      HopfAlgebra.IsCentralPoint g) :
    I.IsCentral := by
  intro x
  set Q := ↥H ⧸ I.toIdeal
  set A : CommAlgCat.{v} R := CommAlgCat.of R (TensorProduct R Q ↥H)
  set g : HopfAlgebra.points (R := R) (H := ↥H) A :=
    quotientPointsHom H I A (toConv (Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := Q) (B := ↥H)))
  set h : HopfAlgebra.points (R := R) (H := ↥H) A :=
    toConv (Algebra.TensorProduct.includeRight (R := R) (A := Q) (B := ↥H)) with hhdef
  have hgmem : g ∈ quotientPointsSubgroup H I A :=
    quotientPointsHom_mem_quotientPointsSubgroup H I A _
  have hcomm : g * h * g⁻¹ = h := by
    have hgh := ((hcentral g hgmem).commute h).eq
    rw [hgh, mul_assoc, mul_inv_cancel, mul_one]
  have hgof : g.ofConv =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := Q) (B := ↥H)).comp
        (Ideal.Quotient.mkₐ R I.toIdeal) :=
    AlgHom.ext fun y ↦ quotientPointsHom_apply_apply H I A _ y
  have hhof : h.ofConv =
      (Algebra.TensorProduct.includeRight (R := R) (A := Q) (B := ↥H)) := by
    rw [hhdef, ofConv_toConv]
  have hproduct : Algebra.TensorProduct.productMap g.ofConv h.ofConv =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal) (AlgHom.id R ↥H) := by
    rw [hgof, hhof]
    refine Algebra.TensorProduct.ext ?_ ?_
    · exact (Algebra.TensorProduct.productMap_left _ _).trans
        (Algebra.TensorProduct.map_comp_includeLeft _ _).symm
    · exact (Algebra.TensorProduct.productMap_right _ _).trans
        (((Algebra.TensorProduct.map_comp_includeRight _ _).trans (AlgHom.comp_id _)).symm)
  have heval := AlgHom.congr_fun
    (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := ↥H) g h) x
  have hmem : HopfAlgebra.conjugationAlgHom (R := R) (H := ↥H) x -
      Algebra.TensorProduct.includeRight x ∈
      RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I.toIdeal)
        (AlgHom.id R ↥H)) := by
    rw [← hproduct, RingHom.mem_ker, map_sub, sub_eq_zero,
      Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.productMap_right_apply, ← AlgHom.comp_apply, heval, hcomm]
  rwa [HopfIdeal.ker_tensorProduct_map_quotient_id I.toIdeal] at hmem

/-- **A Hopf ideal is central exactly when it cuts out central points over every value
algebra.** -/
theorem isCentral_iff_forall_isCentralPoint (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) :
    I.IsCentral ↔
      ∀ (A : CommAlgCat.{v} R), ∀ g ∈ quotientPointsSubgroup H I A,
        HopfAlgebra.IsCentralPoint g :=
  ⟨fun hI A _ hg ↦ isCentralPoint_of_mem_quotientPointsSubgroup H I hI A hg,
    fun hcentral ↦ isCentral_of_isCentralPoint H I (hcentral _)⟩

/-- The points cut out by a central Hopf ideal lie in the centre of the functor of points. -/
theorem quotientPointsSubgroup_le_centre (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsCentral) (A : CommAlgCat.{v} R) :
    quotientPointsSubgroup H I A ≤ HopfAlgebra.centre R ↥H ↥A :=
  fun _ hg ↦ isCentralPoint_of_mem_quotientPointsSubgroup H I hI A hg

/-- A point killing the augmentation ideal is the identity point: the trivial subgroup has only
the identity over every value algebra. -/
theorem eq_one_of_mem_quotientPointsSubgroup_augmentation (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{v} R) {g : HopfAlgebra.points (R := R) (H := H) A}
    (hg : g ∈ quotientPointsSubgroup H (HopfIdeal.augmentation R ↥H) A) : g = 1 := by
  refine WithConv.ofConv_injective (AlgHom.ext fun x ↦ ?_)
  have hx : x - algebraMap R ↥H (Coalgebra.counit (R := R) x) ∈
      HopfIdeal.augmentation R ↥H := by
    rw [HopfIdeal.mem_augmentation]
    simp
  have hzero := (mem_quotientPointsSubgroup_iff H _ A g).mp hg _ hx
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, AlgHom.commutes]
  exact (AlgHom.convOne_apply x).symm

/-- **The trivial subgroup is central.** -/
theorem isCentral_augmentation (H : _root_.CommHopfAlgCat.{v} R) :
    (HopfIdeal.augmentation R ↥H).IsCentral := by
  rw [isCentral_iff_forall_isCentralPoint]
  intro A g hg
  rw [eq_one_of_mem_quotientPointsSubgroup_augmentation H A hg]
  exact HopfAlgebra.isCentralPoint_one

end CommHopfAlgCat

namespace HopfIdeal

variable {R : Type u} [CommRing R]

/-- **A central Hopf ideal is normal.** Its points commute with every point of the ambient group
over the same value algebra, so they form a normal subgroup there, and normality of a Hopf ideal
is detected pointwise. -/
theorem IsCentral.isNormal {H : _root_.CommHopfAlgCat.{v} R} {I : HopfIdeal R H}
    (hI : I.IsCentral) : I.IsNormal := by
  rw [CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal]
  intro A
  refine ⟨fun n hn g ↦ ?_⟩
  have hcom :=
    (CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup H I hI A hn).commute g
  have : g * n * g⁻¹ = n := by
    rw [← hcom.eq, mul_assoc, mul_inv_cancel, mul_one]
  rwa [this]

end HopfIdeal

end TauCeti
