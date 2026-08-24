/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Representation.NormalInvariants
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation

/-!
# The general linear group is reductive

The coordinate Hopf algebra of `GL_n` is reductive over every field and in every natural rank.
The proof uses the geometric definition, so it works in arbitrary characteristic.

First, the determinant localization defining `O(GL_n)` is smooth and geometrically connected.
For the normal-subgroup condition, work over an algebraically closed field and let `I` cut out a
normal smooth unipotent closed subgroup. Its fixed vectors in the standard representation are
stable under the ambient group. Geometric point separation promotes this fixed subspace to a
subcomodule. Kolchin's fixed-vector theorem makes it nonzero, while simplicity of the standard
`GL_n`-comodule makes it the whole representation. The subgroup therefore acts trivially, and
faithfulness of the standard representation identifies `I` with the augmentation ideal.

The final theorem transports this argument across the canonical identification

`AlgebraicClosure k ⊗[k] O(GL_n) ≃ O(GL_n, AlgebraicClosure k)`.

## Main declarations

* `TauCeti.GeneralLinear.smooth_coordinateHopfAlgebra`: `O(GL_n)` is smooth.
* `TauCeti.GeneralLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  `GL_n` is geometrically connected.
* `TauCeti.GeneralLinear.eq_augmentation_of_isNormal_of_smoothUnipotent`: a normal smooth
  unipotent closed subgroup of `GL_n` over an algebraically closed field is trivial.
* `TauCeti.GeneralLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  **`GL_n` is reductive.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a, 5, and 12.45.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2 and 2.4.

This completes the `GL_n` worked example requested alongside Layer 6, "Reductive and semisimple
groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v

noncomputable section

/-- The coordinate Hopf algebra of `GL_n` is smooth over its base ring. -/
theorem smooth_coordinateHopfAlgebra (R : Type u) [CommRing R] (n : Nat) :
    Algebra.Smooth R (coordinateHopfAlgebra R n) := by
  let _ : Algebra.Smooth R (MatrixMonoid.CoordinateRing R n) :=
    ⟨inferInstance, inferInstance⟩
  let _ : Algebra.Smooth (MatrixMonoid.CoordinateRing R n) (CoordinateRing R n) :=
    Algebra.Smooth.of_isLocalization_Away
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
  let _ : Algebra.Smooth R (CoordinateRing R n) :=
    Algebra.Smooth.comp R (MatrixMonoid.CoordinateRing R n) (CoordinateRing R n)
  exact Algebra.Smooth.of_equiv (coordinateHopfAlgebraAlgEquiv R n)

/-- Over a field, the coordinate Hopf algebra of `GL_n` is an integral domain. -/
theorem isDomain_coordinateHopfAlgebra (k : Type u) [Field k] (n : Nat) :
    IsDomain (coordinateHopfAlgebra k n) := by
  let _ : IsDomain (CoordinateRing k n) :=
    Localization.Away.isDomain (Matrix.det_mvPolynomialX_ne_zero (Fin n) k)
  exact (coordinateHopfAlgebraAlgEquiv k n).toRingEquiv.isDomain_iff.mp inferInstance

/-- The coordinate Hopf algebra of `GL_n` is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] (n : Nat) :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  let e : coordinateHopfAlgebra k n ⊗[k] K ≃+* coordinateHopfAlgebra K n :=
    (Algebra.TensorProduct.comm k (coordinateHopfAlgebra k n) K).toRingEquiv.trans
      (coordinateHopfAlgebraBaseChangeBialgEquiv k K n).toAlgEquiv.toRingEquiv
  let _ : IsDomain (coordinateHopfAlgebra K n) := isDomain_coordinateHopfAlgebra K n
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr inferInstance

/-- The finite-type coordinate Hopf algebra of `GL_n` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso
    (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K] (n : Nat) :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R n) ≅
      finiteTypeCoordinateHopfAlgebra K n :=
  ObjectProperty.isoMk _ <|
    eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
      (finiteTypeCoordinateHopfAlgebra_obj R n)) ≪≫
    coordinateHopfAlgebraBaseChangeIso R K n ≪≫
    eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n).symm

/-- The coordinate Hopf algebra and the underlying object of its finite-type package are
canonically identical. -/
private noncomputable def coordinateHopfAlgebraFiniteTypeObjIso
    (R : Type u) [CommRing R] (n : Nat) :
    coordinateHopfAlgebra R n ≅ (finiteTypeCoordinateHopfAlgebra R n).obj :=
  eqToIso (finiteTypeCoordinateHopfAlgebra_obj R n).symm

private theorem eq_augmentation_of_isNormal_of_smooth_of_geometricallyUnipotent_of_neZero
    (k : Type u) [Field k] [IsAlgClosed k] (n : Nat) [NeZero n]
    (I : HopfIdeal k (coordinateHopfAlgebra k n)) (hI : I.IsNormal)
    (hSmooth : Algebra.Smooth k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I))
    (hU : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)) :
    I = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) := by
  let Q := CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I
  let q : coordinateHopfAlgebra k n →ₐc[k] Q :=
    (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k n) I).hom
  let _ : IsDomain (coordinateHopfAlgebra k n) := isDomain_coordinateHopfAlgebra k n
  let _ : IsReduced (coordinateHopfAlgebra k n) := inferInstance
  let _ : Algebra.Smooth k Q := hSmooth
  let _ : IsReduced Q := isReduced_of_smooth_of_field k Q
  let _ : Comodule k (coordinateHopfAlgebra k n) (Fin n → k) := standardComodule k n
  -- Geometric unipotence also detects the base-valued points because the base is algebraically
  -- closed and unipotence is reflected by an injective extension of the value field.
  have hu : ∀ g : WithConv (Q →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g := by
    intro g
    let φ : k →ₐ[k] AlgebraicClosure k := Algebra.ofId k (AlgebraicClosure k)
    exact (HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective g φ φ.injective).mp
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k Q).mp hU
        (AlgHom.mapValue (H := Q) φ g))
  -- Normality makes the subgroup-fixed vectors pointwise stable under the ambient group; reduced
  -- finite-type point separation upgrades that stability to an ambient subcomodule.
  let hstable : ∀ (g : coordinateHopfAlgebra k n →ₐ[k] k) {m : Fin n → k},
      m ∈ I.basePointFixedSubmodule (Fin n → k) →
        Comodule.endOfPoint (Fin n → k) g (1 ⊗ₜ[k] m) ∈
          (I.basePointFixedSubmodule (Fin n → k)).baseChange k := fun g _ hm ↦ by
    simpa only [WithConv.ofConv_toConv] using
      hI.endOfPoint_one_tmul_mem_basePointFixedSubmodule_baseChange
        (WithConv.toConv g) hm
  let S : Subcomodule k (coordinateHopfAlgebra k n) (Fin n → k) :=
    Subcomodule.ofEndOfPointStable (I.basePointFixedSubmodule (Fin n → k)) hstable
  have hSto : S.toSubmodule = I.basePointFixedSubmodule (Fin n → k) :=
    Subcomodule.ofEndOfPointStable_toSubmodule _ hstable
  -- Kolchin supplies a nonzero subgroup-fixed vector in the standard representation.
  let _ : Comodule k Q (Fin n → k) := Comodule.Corestrict q.toCoalgHom
  obtain ⟨v, hv, hvcoact⟩ :=
    (Comodule.hasNonzeroFixedVector_iff (k := k) (H := Q) (M := Fin n → k)).mp
      (Comodule.hasNonzeroFixedVector_of_forall_isUnipotentPoint (M := Fin n → k) hu)
  have hvfixed : v ∈ I.basePointFixedSubmodule (Fin n → k) :=
    HopfIdeal.mem_basePointFixedSubmodule_of_quotient_coact_eq_tmul_one I v <| by
      simpa only [Comodule.corestrict_coact_apply] using hvcoact
  have hvS : v ∈ S := by
    -- Expose the underlying submodule so the construction's characteristic equality rewrites.
    change v ∈ S.toSubmodule
    rw [hSto]
    exact hvfixed
  -- Simplicity of the standard ambient representation makes its nonzero fixed subcomodule all.
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with hbot | htop
    · exfalso
      rw [hbot, Subcomodule.mem_bot] at hvS
      exact hv hvS
    · exact htop
  -- The whole standard representation is now subgroup-fixed, and its faithfulness eliminates the
  -- subgroup scheme rather than merely its rational points.
  apply Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one I
    (isFaithful_standardComodule k n)
  intro m
  apply (HopfIdeal.mem_basePointFixedSubmodule_iff_quotient_coact_eq_tmul_one I m).mp
  have hmS : m ∈ S := by
    rw [hS]
    exact Subcomodule.mem_top m
  -- Expose the fixed submodule to transfer membership back from the bundled subcomodule.
  change m ∈ I.basePointFixedSubmodule (Fin n → k)
  rw [← hSto]
  exact hmS

/-- A normal smooth unipotent closed subgroup of `GL_n` over an algebraically closed field is
trivial.

For positive rank the proof uses a nonzero fixed vector in the simple standard representation;
in rank zero the faithful standard representation is already trivial. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    (k : Type u) [Field k] [IsAlgClosed k] (n : Nat)
    (I : HopfIdeal k (finiteTypeCoordinateHopfAlgebra k n)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I)) :
    I = HopfIdeal.augmentation k (finiteTypeCoordinateHopfAlgebra k n) := by
  let e := coordinateHopfAlgebraFiniteTypeObjIso k n
  let f : coordinateHopfAlgebra k n →ₐc[k] (finiteTypeCoordinateHopfAlgebra k n) :=
    CommHopfAlgCat.ofIso e
  have hf : Function.Bijective f := ConcreteCategory.bijective_of_isIso e.hom
  let J : HopfIdeal k (coordinateHopfAlgebra k n) := I.comap f hf.2
  have hJnormal : J.IsNormal := hI.comap_of_bijective f hf.1 hf.2
  let qIso : CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J ≅
      CommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n).obj I :=
    CommHopfAlgCat.quotientIsoOfIso e I
  have hU' := (smoothUnipotentCommHopfAlgProperty_iff k
    (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k n) I)).mp hU
  have hJsmooth : Algebra.Smooth k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso qIso.symm
        ((smoothCommHopfAlgProperty_iff _).mpr hU'.1)
  have hJunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) J) :=
    (geometricallyUnipotentPointsCommHopfAlgProperty k).prop_of_iso qIso.symm
      ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hU'.2)
  have hJ : J = HopfIdeal.augmentation k (coordinateHopfAlgebra k n) := by
    cases n with
    | zero =>
        let _ : Comodule k (coordinateHopfAlgebra k 0) (Fin 0 → k) := standardComodule k 0
        apply Comodule.eq_augmentation_of_isFaithful_of_quotient_coact_eq_tmul_one J
          (isFaithful_standardComodule k 0)
        intro m
        have hm : m = 0 := Subsingleton.elim _ _
        rw [hm]
        simp only [map_zero, TensorProduct.zero_tmul]
    | succ n =>
        let _ : NeZero n.succ := ⟨Nat.succ_ne_zero n⟩
        exact eq_augmentation_of_isNormal_of_smooth_of_geometricallyUnipotent_of_neZero
          k n.succ J hJnormal hJsmooth hJunipotent
  rw [← HopfIdeal.comap_eq_comap_iff_of_surjective f hf.2,
    HopfIdeal.comap_augmentation]
  exact hJ

/-- **The general linear group is reductive over every field.** -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (n : Nat) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k n) := by
  rw [reductiveCommHopfAlgProperty_iff]
  let e := coordinateHopfAlgebraFiniteTypeObjIso k n
  refine ⟨(smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e
        ((smoothCommHopfAlgProperty_iff _).mpr (smooth_coordinateHopfAlgebra k n)),
    (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n), ?_⟩
  intro I hI _ hU
  let K := AlgebraicClosure k
  let Hbar := FiniteTypeCommHopfAlgCat.baseChange (K := K)
    (finiteTypeCoordinateHopfAlgebra k n)
  let Gbar := finiteTypeCoordinateHopfAlgebra K n
  let e : Hbar ≅ Gbar := finiteTypeCoordinateHopfAlgebraBaseChangeIso k K n
  let f : Gbar →ₐc[K] Hbar := FiniteTypeCommHopfAlgCat.toBialgHom e.inv
  have hf : Function.Bijective f := ConcreteCategory.bijective_of_isIso e.inv
  let J : HopfIdeal K Gbar := I.comap f hf.2
  have hJnormal : J.IsNormal := hI.comap_of_bijective f hf.1 hf.2
  let qIso : FiniteTypeCommHopfAlgCat.quotient Gbar J ≅
      FiniteTypeCommHopfAlgCat.quotient Hbar I :=
    FiniteTypeCommHopfAlgCat.quotientIsoOfIso e.symm I
  have hJU : smoothUnipotentCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient Gbar J) :=
    (smoothUnipotentCommHopfAlgProperty K).prop_of_iso qIso.symm hU
  have hJ : J = HopfIdeal.augmentation K Gbar :=
    eq_augmentation_of_isNormal_of_smoothUnipotent K n J hJnormal hJU
  rw [← HopfIdeal.comap_eq_comap_iff_of_surjective f hf.2,
    HopfIdeal.comap_augmentation]
  exact hJ

end

end TauCeti.GeneralLinear
