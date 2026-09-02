/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Maximality of the diagonal torus in the general linear group

Over any field, the diagonal torus of `GL_n` is a maximal torus. Over an algebraically closed
field, it is moreover maximal among reduced commutative closed subgroup schemes. In Hopf
coordinates, its defining ideal is the kernel of the surjective restriction morphism from
`O(GL_n)` to the Laurent coordinate ring of the split torus.

The proof compares algebraically closed points. A reduced commutative closed subgroup containing
the diagonal torus gives a commutative matrix subgroup containing all invertible diagonal
matrices. The point-level centralizer calculation says that this subgroup is exactly the diagonal
torus. Reduced finite-type point separation then upgrades equality of point subgroups to equality
of their defining Hopf ideals.

This statement is stronger than maximality among tori: every torus is reduced and commutative,
whereas the competing subgroup below need not itself be a torus or connected.

## Main declarations

* `TauCeti.GeneralLinear.diagonalTorusDefiningIdeal`: the Hopf ideal cutting out the diagonal
  torus in `GL_n`.
* `TauCeti.GeneralLinear.diagonalTorusCoordinateIso`: its coordinate quotient is the standard
  Laurent Hopf algebra.
* `TauCeti.GeneralLinear.splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal`:
  its quotient coordinate Hopf algebra is a split torus.
* `TauCeti.GeneralLinear.quotientPointsSubgroup_diagonalTorusDefiningIdeal`: its points are the
  range of the diagonal-torus point morphism.
* `TauCeti.GeneralLinear.eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm`: no larger reduced
  commutative closed subgroup contains the diagonal torus.
* `TauCeti.GeneralLinear.isMaximalTorus_diagonalTorusDefiningIdeal`: the diagonal torus is a
  maximal torus in the Hopf-ideal API.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 12.6 and Section 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 15.3 and 16.1.

This completes the standard `GL_n` maximal-torus example required by Layer 7, "Borel subgroups,
maximal tori", of the ReductiveGroups roadmap. Together with the existing adjoint root spaces and
normalizer quotient, it validates the torus used by the packaged `GL_n` root datum and Weyl group.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (k : Type u) [Field k] (n : ℕ)

/-- The Hopf ideal defining the diagonal torus inside the coordinate Hopf algebra of `GL_n`.

It is the ordinary kernel of the surjective restriction morphism to the split-torus coordinate
ring, packaged as a Hopf ideal. -/
noncomputable def diagonalTorusDefiningIdeal :
    HopfIdeal k (coordinateHopfAlgebra k n) :=
  HopfIdeal.kerOfSurjective (diagonalTorusCoordinateMap (R := k) (N := n)).hom
    (diagonalTorusCoordinateMap_surjective k n)

private theorem comapOfSurjective_bot_diagonalTorusCoordinateMap :
    (⊥ : HopfIdeal k _).comapOfSurjective
        (diagonalTorusCoordinateMap (R := k) (N := n)).hom
        (diagonalTorusCoordinateMap_surjective k n) =
      diagonalTorusDefiningIdeal k n := by
  rw [diagonalTorusDefiningIdeal]
  exact HopfIdeal.comapOfSurjective_bot _ _

/-- The quotient by the diagonal-torus defining ideal is its Laurent coordinate Hopf algebra. -/
noncomputable def diagonalTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n,
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal k n) ≅
      DiagonalizableGroup.coordinateRing k
        (SplitTorus.characterGroup (ULift.{u} (Fin n))) :=
  ObjectProperty.isoMk _ <|
    eqToIso (congrArg (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n))
      (comapOfSurjective_bot_diagonalTorusCoordinateMap k n).symm) ≪≫
    CommHopfAlgCat.quotientIsoOfSurjective
      (diagonalTorusCoordinateMap (R := k) (N := n))
      (diagonalTorusCoordinateMap_surjective k n) ⊥ ≪≫
    CommHopfAlgCat.quotientBotIso _

/-- The diagonal-torus quotient isomorphism identifies the quotient morphism with the canonical
restriction to diagonal coordinates. -/
@[simp]
theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient
          ⟨coordinateHopfAlgebra k n,
            (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          (diagonalTorusDefiningIdeal k n) ≫
        (diagonalTorusCoordinateIso k n).hom =
      ObjectProperty.homMk (diagonalTorusCoordinateMap (R := k) (N := n)) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, diagonalTorusCoordinateIso,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom, Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_eqToHom
      (comapOfSurjective_bot_diagonalTorusCoordinateMap k n),
    ← Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientIsoOfSurjective_hom,
    ← CommHopfAlgCat.quotientBotIso_inv]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat :
    CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k n) (diagonalTorusDefiningIdeal k n) ≫
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (_root_.CommHopfAlgCat.{u} k)).mapIso (diagonalTorusCoordinateIso k n)).hom =
      diagonalTorusCoordinateMap (R := k) (N := n) := by
  have h := congrArg
    (fun f ↦ (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
      (_root_.CommHopfAlgCat.{u} k)).map f)
    (mkQuotient_comp_diagonalTorusCoordinateIso_hom k n)
  rw [Functor.map_comp] at h
  -- A morphism in an `ObjectProperty.FullSubcategory` is definitionally its underlying
  -- morphism, so applying the forgetful functor changes only the wrapper. There is no
  -- propositional rewrite lemma for this reducible coercion.
  change CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n) ≫
        ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (_root_.CommHopfAlgCat.{u} k)).mapIso (diagonalTorusCoordinateIso k n)).hom =
      diagonalTorusCoordinateMap (R := k) (N := n) at h
  exact h

private theorem map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal
    (K : Type u) [Field K] [Algebra k K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal k n)).map
        (coordinateHopfAlgebraBaseChangeIso k K n).hom.hom =
      diagonalTorusDefiningIdeal K n := by
  let H := coordinateHopfAlgebra k n
  let D := diagonalTorusDefiningIdeal k n
  let e := coordinateHopfAlgebraBaseChangeIso k K n
  let q := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (_root_.CommHopfAlgCat.{u} k)).mapIso (diagonalTorusCoordinateIso k n)
  let t := DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso k K
    (SplitTorus.characterGroup (ULift.{u} (Fin n)))
  let r := CommHopfAlgCat.baseChangeMap (K := K) q.hom ≫ t.hom
  have he : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hq : CommHopfAlgCat.mkQuotient H D ≫ q.hom =
      diagonalTorusCoordinateMap (R := k) (N := n) :=
    mkQuotient_comp_diagonalTorusCoordinateIso_hom_commHopfAlgCat k n
  have hqK :
      CommHopfAlgCat.baseChangeMap (K := K) (CommHopfAlgCat.mkQuotient H D) ≫
          CommHopfAlgCat.baseChangeMap (K := K) q.hom =
        CommHopfAlgCat.baseChangeMap (K := K)
          (diagonalTorusCoordinateMap (R := k) (N := n)) := by
    rw [← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp]
    exact congrArg (CommHopfAlgCat.baseChangeMap (K := K)) hq
  have hdiag := diagonalTorusCoordinateMap_baseChange (N := n) k K
  -- The local names `e` and `t` abbreviate exactly the isomorphisms in the preceding theorem;
  -- exposing them is a definitional conversion, with no propositional equality to rewrite.
  change e.inv ≫
      CommHopfAlgCat.baseChangeMap (K := K)
        (diagonalTorusCoordinateMap (R := k) (N := n)) ≫ t.hom =
    diagonalTorusCoordinateMap (R := K) (N := n) at hdiag
  have hcomm :
      CommHopfAlgCat.baseChangeMap (K := K) (CommHopfAlgCat.mkQuotient H D) ≫ r =
        e.hom ≫ diagonalTorusCoordinateMap (R := K) (N := n) := by
    dsimp only [r]
    rw [← Category.assoc, hqK, ← hdiag]
    simp
  have hr : Function.Injective r.hom := by
    dsimp only [r]
    exact (ConcreteCategory.bijective_of_isIso
      ((CommHopfAlgCat.baseChangeFunctor (K := K)).mapIso q ≪≫ t).hom).1
  have hzero (y : CommHopfAlgCat.baseChange (K := K) H) :
      (CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient H D)).hom y = 0 ↔
        (diagonalTorusCoordinateMap (R := K) (N := n)).hom (e.hom.hom y) = 0 := by
    have hy := congrArg (fun f ↦ f.hom y) hcomm
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at hy
    rw [← hy]
    exact ⟨fun hy0 ↦ by rw [hy0, map_zero], fun hy0 ↦ hr (by simpa using hy0)⟩
  ext x
  rw [HopfIdeal.mem_map_iff_of_surjective he.2]
  have hmemx : x ∈ diagonalTorusDefiningIdeal K n ↔
      (diagonalTorusCoordinateMap (R := K) (N := n)).hom x = 0 := by
    rw [diagonalTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]
  rw [hmemx]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hzero y).mp ((CommHopfAlgCat.mem_baseChangeHopfIdeal_iff D y).mp hy)
  · intro hx
    refine ⟨e.inv.hom x, ?_, _root_.CommHopfAlgCat.hom_inv_apply e x⟩
    rw [CommHopfAlgCat.mem_baseChangeHopfIdeal_iff]
    apply (hzero _).mpr
    rwa [_root_.CommHopfAlgCat.hom_inv_apply]

/-- The quotient coordinate Hopf algebra of the diagonal torus is a split torus of rank `n`. -/
theorem splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n,
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal k n)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  exact ⟨n, ⟨(diagonalTorusCoordinateIso k n).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal k n

/-- The quotient coordinate Hopf algebra of the diagonal torus is a torus. -/
theorem torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal :
    torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient
        ⟨coordinateHopfAlgebra k n,
          (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
        (diagonalTorusDefiningIdeal k n)) :=
  (splitTorusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n).torus k _

grind_pattern torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal =>
  diagonalTorusDefiningIdeal k n

/-- The points cut out by `diagonalTorusDefiningIdeal` are exactly the diagonal-torus points. -/
theorem quotientPointsSubgroup_diagonalTorusDefiningIdeal (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra k n)
        (diagonalTorusDefiningIdeal k n) A =
      ((CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := k) (N := n))).app A).hom.range := by
  rw [diagonalTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range]
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro q
  rw [AlgHom.mapDomain_apply]
  exact (CommHopfAlgCat.mapPointsFunctor_app_apply
    (diagonalTorusCoordinateMap (R := k) (N := n)) A q).symm

variable [IsAlgClosed k]

private instance instNontrivialUnitsOfInfiniteField {F : Type*} [Field F] [Infinite F] :
    Nontrivial Fˣ := by
  let U := {x : F // x ∈ ({0} : Set F)ᶜ}
  let _ : Infinite U := (Set.toFinite ({0} : Set F)).infinite_compl.to_subtype
  obtain ⟨x, y, hxy⟩ := exists_pair_ne U
  refine ⟨Units.mk0 x (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property),
    Units.mk0 y (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.property), ?_⟩
  intro h
  apply hxy
  apply Subtype.ext
  exact congrArg Units.val h

omit [IsAlgClosed k] in
private theorem isReduced_quotient_diagonalTorusDefiningIdeal :
    IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n)) := by
  let f := (diagonalTorusCoordinateMap (R := k) (N := n)).hom
  let hf : Function.Surjective f := diagonalTorusCoordinateMap_surjective k n
  let e := HopfIdeal.kerLiftBialgEquiv f hf
  exact isReduced_of_injective e.toAlgEquiv.toRingEquiv.toRingHom e.injective

omit [IsAlgClosed k] in
private theorem pointsMulEquiv_diagonalTorusPoints_symm (t : Fin n → kˣ) :
    pointsMulEquiv (R := k) (A := k) n
        (diagonalTorusPoints
          ((SplitTorus.pointsMulEquiv (R := k) (A := k)).symm
            (fun i : ULift.{u} (Fin n) ↦ t i.down))) =
      diagGL t := by
  rw [pointsMulEquiv_diagonalTorusPoints]
  congr 1
  funext i
  rw [diagonalTorusCoordinates_apply]
  exact congrFun
    ((SplitTorus.pointsMulEquiv (R := k) (A := k)).apply_symm_apply
      (fun j : ULift.{u} (Fin n) ↦ t j.down)) (ULift.up i)

/-- **The diagonal torus of `GL_n` is maximal among reduced commutative closed subgroup
schemes over an algebraically closed field.**

If `I` cuts out a reduced commutative closed subgroup containing the diagonal torus, then `I` is
the diagonal-torus defining ideal. Containment is written contravariantly as
`I ≤ diagonalTorusDefiningIdeal k n`; commutativity is the cocommutativity of the quotient
coordinate Hopf algebra. -/
theorem eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm
    (I : HopfIdeal k (coordinateHopfAlgebra k n))
    [IsReduced (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    [Coalgebra.IsCocomm k (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I)]
    (hI : I ≤ diagonalTorusDefiningIdeal k n) :
    I = diagonalTorusDefiningIdeal k n := by
  let H := coordinateHopfAlgebra k n
  let D := diagonalTorusDefiningIdeal k n
  let A := CommAlgCat.of k k
  let GI := CommHopfAlgCat.quotientPointsSubgroup H I A
  let GD := CommHopfAlgCat.quotientPointsSubgroup H D A
  let e := pointsMulEquiv (R := k) (A := k) n
  let P : Subgroup (GL (Fin n) k) := GI.map e.toMonoidHom
  let _ : IsMulCommutative GI :=
    CommHopfAlgCat.instIsMulCommutativeQuotientPointsSubgroup
      (coordinateHopfAlgebra k n) I (CommAlgCat.of k k)
  let _ : IsMulCommutative P := Subgroup.map_isMulCommutative GI e.toMonoidHom
  have hDG : GD ≤ GI :=
    CommHopfAlgCat.quotientPointsSubgroup_le_of_le H hI A
  have hdiagonalP : TauCeti.diagonalTorus k n ≤ P := by
    intro m hm
    obtain ⟨t, rfl⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hm
    let s : ULift.{u} (Fin n) → kˣ := fun i ↦ t i.down
    let q : WithConv
        (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] k) :=
      (SplitTorus.pointsMulEquiv (R := k) (A := k)).symm s
    let d := diagonalTorusPoints (R := k) (N := n) (A := k) q
    have hdD : d ∈ GD := by
      dsimp only [GD, D]
      rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
      refine ⟨q, ?_⟩
      exact mapPointsFunctor_diagonalTorusCoordinateMap_app A q
    refine ⟨d, hDG hdD, ?_⟩
    -- Unfold the `e.toMonoidHom` coercion introduced by `Subgroup.map` to the coercion of `e`.
    change e d = diagGL t
    simpa only [e, d, q, s] using pointsMulEquiv_diagonalTorusPoints_symm k n t
  have hP : P = TauCeti.diagonalTorus k n :=
    eq_diagonalTorus_of_le_of_isMulCommutative P hdiagonalP
  have hpoints : GI = GD := by
    apply le_antisymm
    · intro g hg
      have hegP : e g ∈ P := ⟨g, hg, rfl⟩
      have hegD : e g ∈ TauCeti.diagonalTorus k n := hP ▸ hegP
      obtain ⟨t, ht⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hegD
      let s : ULift.{u} (Fin n) → kˣ := fun i ↦ t i.down
      let q : WithConv
          (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] k) :=
        (SplitTorus.pointsMulEquiv (R := k) (A := k)).symm s
      have hdiag : e (diagonalTorusPoints (R := k) (N := n) (A := k) q) = diagGL t := by
        simpa only [e, q, s] using pointsMulEquiv_diagonalTorusPoints_symm k n t
      dsimp only [GD, D]
      rw [quotientPointsSubgroup_diagonalTorusDefiningIdeal]
      refine ⟨q, ?_⟩
      apply e.injective
      rw [mapPointsFunctor_diagonalTorusCoordinateMap_app]
      exact hdiag.trans ht
    · exact hDG
  let _ : IsReduced (CommHopfAlgCat.quotient H D) :=
    isReduced_quotient_diagonalTorusDefiningIdeal k n
  exact HopfIdeal.eq_of_quotientPointsSubgroup_eq hpoints

/-- **The diagonal torus of `GL_n` is a maximal torus.** This packages the stronger result that
no reduced commutative closed subgroup properly containing it exists into the general
Hopf-ideal maximal-torus predicate. -/
private theorem isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n, ?_⟩
  intro I hI hID
  let _ : IsReduced
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I) :=
    hI.geometricallyReduced.isReduced
  let _ : Coalgebra.IsCocomm k
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n) I) :=
    hI.isCocomm k _
  have hEq := eq_diagonalTorusDefiningIdeal_of_le_of_isCocomm k n I hID
  subst I
  exact le_rfl

omit [IsAlgClosed k] in
/-- **The diagonal torus of `GL_n` is a maximal torus over every field.** Maximality is checked
after base change to an algebraic closure, where the stronger pointwise maximality theorem
applies, and then descended using faithful flatness. -/
@[grind =>]
theorem isMaximalTorus_diagonalTorusDefiningIdeal :
    HopfIdeal.IsMaximalTorus k (coordinateHopfAlgebra k n)
      (diagonalTorusDefiningIdeal k n) := by
  rw [HopfIdeal.isMaximalTorus_iff]
  refine ⟨torusCommHopfAlgProperty_quotient_diagonalTorusDefiningIdeal k n, ?_⟩
  intro I hI hID
  let K := AlgebraicClosure k
  let H := coordinateHopfAlgebra k n
  let HK := coordinateHopfAlgebra K n
  let Hft : FiniteTypeCommHopfAlgCat k :=
    ⟨H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let HKft : FiniteTypeCommHopfAlgCat K :=
    ⟨HK, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let e := coordinateHopfAlgebraBaseChangeIso k K n
  let IK := (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).map e.hom.hom
  have hmapI :
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I).map e.hom.hom = IK := rfl
  let qIso : FiniteTypeCommHopfAlgCat.baseChange (K := K)
        (FiniteTypeCommHopfAlgCat.quotient Hft I) ≅
      FiniteTypeCommHopfAlgCat.quotient HKft IK :=
    ObjectProperty.isoMk _
      (CommHopfAlgCat.quotientBaseChangeIsoOfMapEq I IK e hmapI)
  have hsplit : splitTorusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.baseChange (K := K)
        (FiniteTypeCommHopfAlgCat.quotient Hft I)) := by
    rw [splitTorusCommHopfAlgProperty_iff]
    rw [torusCommHopfAlgProperty_iff] at hI
    simpa only [Hft] using hI
  have hIK : torusCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient HKft IK) :=
    ((splitTorusCommHopfAlgProperty K).prop_of_iso qIso hsplit).torus K _
  have hIKD : IK ≤ diagonalTorusDefiningIdeal K n := by
    rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal k n K]
    exact HopfIdeal.map_mono e.hom.hom
      (CommHopfAlgCat.baseChangeHopfIdeal_mono hID)
  have hmaxK := isMaximalTorus_diagonalTorusDefiningIdeal_of_isAlgClosed K n
  rw [HopfIdeal.isMaximalTorus_iff] at hmaxK
  have hDIK : diagonalTorusDefiningIdeal K n ≤ IK := hmaxK.2 IK hIK hIKD
  have he : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hbase :
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (diagonalTorusDefiningIdeal k n) ≤
        CommHopfAlgCat.baseChangeHopfIdeal (K := K) I := by
    have hcomap := HopfIdeal.comapOfSurjective_mono e.hom.hom he.2 hDIK
    rw [← map_baseChangeHopfIdeal_diagonalTorusDefiningIdeal k n K,
      HopfIdeal.comapOfSurjective_map_of_bijective _ _ he,
      HopfIdeal.comapOfSurjective_map_of_bijective _ _ he] at hcomap
    exact hcomap
  exact (CommHopfAlgCat.baseChangeHopfIdeal_le_iff
    (algebraMap k K).injective).mp hbase

end

end TauCeti.GeneralLinear
