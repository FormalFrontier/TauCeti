/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Comap

/-!
# Normal Hopf ideals

A Hopf ideal `I` in a commutative Hopf algebra `H` defines a closed subgroup of the affine
group represented by `H`. This file defines normality of that closed subgroup in Hopf-algebra
coordinates: the ideal is stable under the coordinate morphism of conjugation,

`c♯ : H → H ⊗[R] H`,

with the first tensor factor carrying the conjugating variable. Thus `I` is normal when
`c♯(I) ⊆ H ⊗ I`. It also verifies the pointwise meaning of this condition: over every
commutative value algebra, the subgroup cut out by a normal Hopf ideal is a normal subgroup of
the ambient group of points.

Normal Hopf ideals are closed under arbitrary suprema. Every Hopf ideal has a normal core: the
largest normal Hopf ideal below it. This normal-core API is the Hopf-ideal analogue of Mathlib's
`Subgroup.normalCore`.

## Main declarations

* `TauCeti.HopfIdeal.IsNormal`: stability under the coordinate conjugation action.
* `TauCeti.HopfIdeal.isNormal_bot`: the zero Hopf ideal is normal.
* `TauCeti.HopfIdeal.isNormal_iSup`: arbitrary suprema of normal Hopf ideals are normal.
* `TauCeti.HopfIdeal.normalCore`: the largest normal Hopf ideal below a given Hopf ideal.
* `TauCeti.HopfIdeal.IsNormal.comap_of_bijective`: normality is preserved by pullback along a
  bijective bialgebra morphism.
* `TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal`: a normal Hopf ideal cuts out a normal
  subgroup on points over every commutative value algebra.

## References

The coordinate criterion is the usual adjoint-coaction characterization of a normal closed
subgroup; see J. S. Milne, *Algebraic Groups* (2017), §3.5 and §10.20. This is the normality
prerequisite in Layer 3, “Normality and quotients”, of the ReductiveGroups roadmap.
-/

public section

open WithConv

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {R : Type u} {H : Type v}
variable [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]

/-- A Hopf ideal is normal when the coordinate morphism of conjugation carries it into
`H ⊗ I`. The first tensor factor of `HopfAlgebra.conjugationAlgHom` is the conjugating
variable, so the right tensor ideal is the ideal of `G × V(I)`. -/
def IsNormal (I : HopfIdeal R H) : Prop :=
  Ideal.map (HopfAlgebra.conjugationAlgHom (R := R) (H := H)).toRingHom I.toIdeal ≤
    rightTensorIdeal (R := R) (H := H) I.toIdeal

/-- Normality restated as the defining ideal inclusion. -/
theorem isNormal_def (I : HopfIdeal R H) :
    I.IsNormal ↔
      Ideal.map (HopfAlgebra.conjugationAlgHom (R := R) (H := H)).toRingHom I.toIdeal ≤
        rightTensorIdeal (R := R) (H := H) I.toIdeal :=
  Iff.rfl

/-- A Hopf ideal is normal exactly when the coordinate conjugation of each of its elements
belongs to `H ⊗ I`. -/
theorem isNormal_iff_conjugation_mem (I : HopfIdeal R H) :
    I.IsNormal ↔ ∀ ⦃x : H⦄, x ∈ I →
      HopfAlgebra.conjugationAlgHom (R := R) (H := H) x ∈
        rightTensorIdeal (R := R) (H := H) I.toIdeal := by
  rw [isNormal_def, Ideal.map_le_iff_le_comap]
  rfl

/-- The coordinate conjugation of an element of a normal Hopf ideal belongs to `H ⊗ I`. -/
theorem IsNormal.conjugation_mem {I : HopfIdeal R H} (hI : I.IsNormal) {x : H} (hx : x ∈ I) :
    HopfAlgebra.conjugationAlgHom (R := R) (H := H) x ∈
      rightTensorIdeal (R := R) (H := H) I.toIdeal :=
  (isNormal_iff_conjugation_mem I).mp hI hx

/-- The zero Hopf ideal cuts out the whole affine group, hence is normal. -/
@[simp]
theorem isNormal_bot : (⊥ : HopfIdeal R H).IsNormal := by
  rw [isNormal_def, bot_toIdeal, Ideal.map_bot]
  exact bot_le

/-- An arbitrary supremum of normal Hopf ideals is normal. -/
theorem isNormal_iSup {i : Sort*} {I : i → HopfIdeal R H} (hI : ∀ j, (I j).IsNormal) :
    (⨆ j, I j).IsNormal := by
  rw [isNormal_def, iSup_toIdeal, Ideal.map_iSup, rightTensorIdeal_iSup]
  exact iSup_le fun j ↦ le_iSup_of_le j (hI j)

/-- The supremum of a set of normal Hopf ideals is normal. -/
theorem isNormal_sSup {s : Set (HopfIdeal R H)} (hs : ∀ I ∈ s, I.IsNormal) :
    (sSup s).IsNormal := by
  rw [sSup_eq_iSup']
  exact isNormal_iSup fun I ↦ hs I I.property

/-- The largest normal Hopf ideal contained in `J`. -/
noncomputable def normalCore (J : HopfIdeal R H) : HopfIdeal R H :=
  sSup {I | I.IsNormal ∧ I ≤ J}

/-- The normal core is normal. -/
@[simp]
theorem isNormal_normalCore (J : HopfIdeal R H) : J.normalCore.IsNormal :=
  isNormal_sSup fun _ hI ↦ hI.1

/-- The normal core of a Hopf ideal is contained in that ideal. -/
theorem normalCore_le (J : HopfIdeal R H) : J.normalCore ≤ J := by
  rw [normalCore]
  exact sSup_le fun I hI ↦ hI.2

/-- Every normal Hopf ideal below `J` lies below the normal core of `J`. -/
theorem le_normalCore (I J : HopfIdeal R H) (hI : I.IsNormal) (hIJ : I ≤ J) :
    I ≤ J.normalCore := by
  rw [normalCore]
  exact le_sSup ⟨hI, hIJ⟩

/-- A normal Hopf ideal lies below the normal core of `J` exactly when it lies below `J`. -/
theorem le_normalCore_iff_of_isNormal (I J : HopfIdeal R H) (hI : I.IsNormal) :
    I ≤ J.normalCore ↔ I ≤ J :=
  ⟨fun h ↦ h.trans J.normalCore_le, le_normalCore I J hI⟩

/-- The normal-core operator is monotone. -/
theorem normalCore_mono {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    I.normalCore ≤ J.normalCore :=
  le_normalCore I.normalCore J (isNormal_normalCore I) (I.normalCore_le.trans hIJ)

/-- A normal Hopf ideal equals its normal core. -/
theorem normalCore_eq_self_of_isNormal (J : HopfIdeal R H) (hJ : J.IsNormal) :
    J.normalCore = J :=
  le_antisymm J.normalCore_le (le_normalCore J J hJ le_rfl)

/-- Taking the normal core twice has the same effect as taking it once. -/
@[simp]
theorem normalCore_idempotent (J : HopfIdeal R H) : J.normalCore.normalCore = J.normalCore :=
  normalCore_eq_self_of_isNormal J.normalCore (isNormal_normalCore J)

/-- A Hopf ideal equals its normal core exactly when it is normal. -/
theorem normalCore_eq_self_iff (J : HopfIdeal R H) : J.normalCore = J ↔ J.IsNormal :=
  ⟨fun h ↦ h ▸ isNormal_normalCore J, normalCore_eq_self_of_isNormal J⟩

end HopfIdeal

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- A normal Hopf ideal cuts out a normal subgroup of points over every commutative
`R`-algebra. -/
theorem quotientPointsSubgroup_normal (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) :
    (quotientPointsSubgroup H I A).Normal := by
  refine ⟨fun n hn g ↦ ?_⟩
  rw [mem_quotientPointsSubgroup_iff] at hn ⊢
  intro x hx
  rw [← HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H) g n]
  have hker :
      HopfIdeal.rightTensorIdeal (R := R) (H := H) I.toIdeal ≤
        RingHom.ker (Algebra.TensorProduct.productMap g.ofConv n.ofConv).toRingHom := by
    rw [HopfIdeal.rightTensorIdeal_le_iff]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa using hn y ((HopfIdeal.mem_toIdeal (I := I)).mp hy)
  exact RingHom.mem_ker.mp (hker (hI.conjugation_mem hx))

/-- If a Hopf ideal cuts out a normal subgroup over the value algebra `H ⊗ (H ⧸ I)`, then it is
normal. That single test algebra suffices: it carries the two points whose conjugate detects
membership in the ideal. -/
private theorem isNormal_of_quotientPointsSubgroup_normal
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H)
    (hnormal : (quotientPointsSubgroup H I
      (CommAlgCat.of R (TensorProduct R H (H ⧸ I.toIdeal)))).Normal) :
    I.IsNormal := by
  rw [HopfIdeal.isNormal_iff_conjugation_mem]
  intro x hx
  let Q := H ⧸ I.toIdeal
  let A : CommAlgCat R := CommAlgCat.of R (TensorProduct R H Q)
  let g : HopfAlgebra.points (R := R) (H := H) A :=
    toConv Algebra.TensorProduct.includeLeft
  let n : HopfAlgebra.points (R := R) (H := H) A :=
    quotientPointsHom H I A (toConv Algebra.TensorProduct.includeRight)
  have hn : n ∈ quotientPointsSubgroup H I A :=
    quotientPointsHom_mem_quotientPointsSubgroup H I A _
  have hgof : g.ofConv = (Algebra.TensorProduct.includeLeft : H →ₐ[R] TensorProduct R H Q) :=
    ofConv_toConv _
  have hnof : n.ofConv =
      (Algebra.TensorProduct.includeRight : Q →ₐ[R] TensorProduct R H Q).comp
        (Ideal.Quotient.mkₐ R I.toIdeal) :=
    AlgHom.ext fun h => quotientPointsHom_apply_apply H I A _ h
  have hconj := hnormal.conj_mem n hn g
  rw [mem_quotientPointsSubgroup_iff] at hconj
  have hzero := hconj x hx
  have heval :
      (Algebra.TensorProduct.productMap g.ofConv n.ofConv)
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H) x) = 0 :=
    (AlgHom.congr_fun
      (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H) g n) x).trans hzero
  have hproduct :
      Algebra.TensorProduct.productMap g.ofConv n.ofConv =
        Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R I.toIdeal) := by
    rw [hgof, hnof]
    refine Algebra.TensorProduct.ext ?_ ?_
    · rw [Algebra.TensorProduct.productMap_left,
        Algebra.TensorProduct.map_comp_includeLeft, AlgHom.comp_id]
    · exact (Algebra.TensorProduct.productMap_right _ _).trans
        (Algebra.TensorProduct.map_comp_includeRight _ _).symm
  rw [hproduct] at heval
  have hmem := RingHom.mem_ker.mpr heval
  rw [HopfIdeal.ker_tensorProduct_map_id_quotient I.toIdeal] at hmem
  exact hmem

/-- A Hopf ideal is normal if and only if it cuts out a normal subgroup over every
commutative value algebra. -/
theorem isNormal_iff_quotientPointsSubgroup_normal
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    I.IsNormal ↔ ∀ A : CommAlgCat.{v} R, (quotientPointsSubgroup H I A).Normal :=
  ⟨fun hI A => quotientPointsSubgroup_normal H I hI A,
    fun hnormal => isNormal_of_quotientPointsSubgroup_normal H I (hnormal _)⟩

end CommHopfAlgCat

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H K : Type v} [CommRing H] [CommRing K]
variable [HopfAlgebra R H] [HopfAlgebra R K]

/-- Pulling a normal Hopf ideal back along a bijective bialgebra morphism preserves normality. -/
theorem IsNormal.comap_of_bijective {I : HopfIdeal R K} (hI : I.IsNormal) (f : H →ₐc[R] K)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    (I.comap f hsurj).IsNormal := by
  apply (CommHopfAlgCat.isNormal_iff_quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R H) (I.comap f hsurj)).mpr
  intro A
  let e := BialgEquiv.ofBijective f ⟨hinj, hsurj⟩
  let E := AlgHom.mapDomainMulEquiv (A := A) e
  have hmem (g : HopfAlgebra.points (R := R) (H := K) A) :
      E g ∈ CommHopfAlgCat.quotientPointsSubgroup
          (_root_.CommHopfAlgCat.of R H) (I.comap f hsurj) A ↔
        g ∈ CommHopfAlgCat.quotientPointsSubgroup
          (_root_.CommHopfAlgCat.of R K) I A := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    constructor
    · intro hg y hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact hg x (mem_comap.mpr hy)
    · intro hg x hx
      exact hg (f x) (mem_comap.mp hx)
  constructor
  intro n hn g
  have hn' : E.symm n ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of R K) I A := by
    rw [← hmem]
    simpa using hn
  have hconj := (CommHopfAlgCat.quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R K) I hI A).conj_mem (E.symm n) hn' (E.symm g)
  rw [← hmem] at hconj
  simpa using hconj

end HopfIdeal

end TauCeti
