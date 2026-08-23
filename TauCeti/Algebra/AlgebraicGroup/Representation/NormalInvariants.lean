/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

/-!
# Invariants of normal closed subgroups

Let `H` be a commutative Hopf algebra and `M` an `H`-comodule. A point of the affine group
represented by `H` acts naturally on `M` itself when its value algebra is the base ring. For a
Hopf ideal `I`, this file defines the submodule fixed by the base-valued points of the closed
subgroup cut out by `I`.

When `I` is normal, its point subgroup is normal over every value algebra. The standard theorem
that the invariants of a normal subgroup form a subrepresentation therefore shows that this
fixed submodule is preserved by every ambient point. This is the pointwise algebraic-group input
to the direct proof that `GLₙ` is reductive: the fixed vectors of a normal unipotent subgroup in
the standard representation form an ambient subrepresentation.

The definition deliberately says `basePointFixedSubmodule`: without a point-separation
hypothesis, base-valued points need not detect scheme-theoretic invariants. The normality and
stability results require no reducedness, finite-type, or field hypotheses.

The group-representation step is Mathlib's `Representation.toInvariants`; this file adds the
Hopf-ideal and comodule interface around it rather than repeating the normal-subgroup conjugation
argument.

## Main declarations

* `TauCeti.HopfIdeal.basePointFixedSubmodule`: the vectors fixed by the base-valued points cut out
  by a Hopf ideal.
* `TauCeti.HopfIdeal.mem_basePointFixedSubmodule_iff_quotient_coact_eq_tmul_one`: geometric-point
  detection identifies the pointwise and scheme-theoretic fixed-vector conditions.
* `TauCeti.HopfIdeal.IsNormal.basePointFixedSubrepresentation`: Mathlib's representation on the
  invariants of the point subgroup cut out by a normal Hopf ideal.
* `TauCeti.HopfIdeal.IsNormal.basePointsRepresentation_mem_basePointFixedSubmodule`: the ambient
  base-point action preserves the base-point-fixed submodule.
* `TauCeti.HopfIdeal.IsNormal.endOfPoint_one_tmul_mem_basePointFixedSubmodule_baseChange`:
  pointwise
  stability in the scalar-extension form used to detect subcomodules.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

open CategoryTheory WithConv

universe u v w x

noncomputable section

namespace HopfIdeal

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

variable (M) in
/-- The submodule fixed by all base-valued points of the closed subgroup cut out by `I`. -/
def basePointFixedSubmodule (I : HopfIdeal R H) : Submodule R M :=
  Representation.invariants
    ((Comodule.basePointsRepresentation (R := R) (H := H) M).comp
      (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
        (CommAlgCat.of R R)).subtype)

/-- The base-point-fixed submodule as Mathlib's invariant submodule for the quotient point
subgroup. -/
theorem basePointFixedSubmodule_def (I : HopfIdeal R H) :
    I.basePointFixedSubmodule M =
      Representation.invariants
        ((Comodule.basePointsRepresentation (R := R) (H := H) M).comp
          (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
            (CommAlgCat.of R R)).subtype) := by
  rfl

/-- Membership in the base-point-fixed submodule means being fixed by every base-valued point cut
out by the Hopf ideal. -/
@[simp]
theorem mem_basePointFixedSubmodule (I : HopfIdeal R H) (m : M) :
    m ∈ I.basePointFixedSubmodule M ↔
      ∀ n : CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
          (CommAlgCat.of R R),
        Comodule.basePointsRepresentation (R := R) (H := H) M
          (n : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) m = m := by
  rfl

/-- A vector fixed by the quotient coaction is fixed by every base-valued point of the closed
subgroup cut out by `I`. This direction requires no point-separation hypotheses. -/
theorem mem_basePointFixedSubmodule_of_quotient_coact_eq_tmul_one
    (I : HopfIdeal R H) (m : M)
    (hm : TensorProduct.map LinearMap.id
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H) I).hom.toLinearMap
        (Comodule.coact (R := R) (C := H) m) =
      m ⊗ₜ[R] (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) I)) :
    m ∈ I.basePointFixedSubmodule M := by
  let A := _root_.CommHopfAlgCat.of R H
  let Q := CommHopfAlgCat.quotient A I
  let q : H →ₐc[R] Q := (CommHopfAlgCat.mkQuotient A I).hom
  let _ : Comodule R Q M := Comodule.Corestrict q.toCoalgHom
  have hm' : Comodule.coact (R := R) (C := Q) m = m ⊗ₜ[R] (1 : Q) := by
    simpa only [Comodule.corestrict_coact_apply] using hm
  rw [mem_basePointFixedSubmodule]
  intro n
  obtain ⟨g, hg⟩ := n.2
  have hfixed := Comodule.basePointsRepresentation_eq_of_coact_eq_tmul_one m hm' g
  have hinclude : AlgHom.mapDomain q g =
      CommHopfAlgCat.quotientPointsHom A I (CommAlgCat.of R R) g := by
    rw [CommHopfAlgCat.quotientPointsHom_apply, AlgHom.mapDomain_apply]
  have hq : AlgHom.mapDomain q g = n.1 := by
    exact hinclude.trans hg
  rw [Comodule.basePointsRepresentation_corestrict q g, hq] at hfixed
  exact hfixed

section GeometricDetection

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [CommRing A] [HopfAlgebra k A]
variable [AddCommGroup M] [Module k M] [Comodule k A M] [IsAlgClosed k]

/-- Over an algebraically closed field, if the quotient coordinate ring is reduced and of finite
type, base-point-fixed vectors are exactly the vectors fixed by the restricted coaction of the
closed subgroup scheme. -/
theorem mem_basePointFixedSubmodule_iff_quotient_coact_eq_tmul_one
    (I : HopfIdeal k A)
    [Algebra.FiniteType k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I)]
    [IsReduced (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I)]
    (m : M) :
    m ∈ I.basePointFixedSubmodule M ↔
      TensorProduct.map LinearMap.id
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k A) I).hom.toLinearMap
          (Comodule.coact (R := k) (C := A) m) =
        m ⊗ₜ[k]
          (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I) := by
  let H := _root_.CommHopfAlgCat.of k A
  let Q := CommHopfAlgCat.quotient H I
  let q : A →ₐc[k] Q := (CommHopfAlgCat.mkQuotient H I).hom
  let _ : Comodule k Q M := Comodule.Corestrict q.toCoalgHom
  have hinclude (g : HopfAlgebra.points (R := k) (H := Q) (CommAlgCat.of k k)) :
      AlgHom.mapDomain q g =
        CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) g := by
    rw [CommHopfAlgCat.quotientPointsHom_apply, AlgHom.mapDomain_apply]
  constructor
  · intro hm
    have hfixed : ∀ g : HopfAlgebra.points (R := k) (H := Q) (CommAlgCat.of k k),
        Comodule.basePointsRepresentation (R := k) (H := Q) M g m = m := by
      intro g
      let n := CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) g
      have hn := (mem_basePointFixedSubmodule I m).mp hm
        ⟨n, CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H I
          (CommAlgCat.of k k) g⟩
      rw [Comodule.basePointsRepresentation_corestrict q g, hinclude]
      exact hn
    have hcoact :=
      (Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq m).2 hfixed
    simpa only [Comodule.corestrict_coact_apply] using hcoact
  · exact mem_basePointFixedSubmodule_of_quotient_coact_eq_tmul_one I m

end GeometricDetection

namespace IsNormal

variable {I : HopfIdeal R H}

/-- Every ambient base-valued point sends a base-point-fixed vector to another base-point-fixed
vector. -/
theorem basePointsRepresentation_mem_basePointFixedSubmodule (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {m : M} (hm : m ∈ I.basePointFixedSubmodule M) :
    Comodule.basePointsRepresentation (R := R) (H := H) M g m ∈
      I.basePointFixedSubmodule M := by
  let N := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
    (CommAlgCat.of R R)
  let _ : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R H) I hI (CommAlgCat.of R R)
  have hm' : m ∈ Representation.invariants
      ((Comodule.basePointsRepresentation (R := R) (H := H) M).comp N.subtype) := by
    simpa only [basePointFixedSubmodule_def] using hm
  have hstable := Representation.le_comap_invariants
    (Comodule.basePointsRepresentation (R := R) (H := H) M) N g hm'
  simpa only [Submodule.mem_comap, basePointFixedSubmodule_def] using hstable

variable (M) in
/-- The representation of the full group of base-valued points on the vectors fixed by the point
subgroup cut out by the normal Hopf ideal `I`. Normality makes this submodule ambient-stable. -/
noncomputable abbrev basePointFixedSubrepresentation (hI : I.IsNormal) :
    Representation R
      (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
      (I.basePointFixedSubmodule M) := by
  rw [basePointFixedSubmodule_def]
  let N := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
    (CommAlgCat.of R R)
  let _ : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R H) I hI (CommAlgCat.of R R)
  exact Representation.toInvariants
    (Comodule.basePointsRepresentation (R := R) (H := H) M)
    N

/-- The scalar extension of the base-point-fixed submodule is stable under every ambient point
endomorphism. -/
theorem endOfPoint_le_comap_basePointFixedSubmodule_baseChange (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.basePointFixedSubmodule M).baseChange R ≤
      ((I.basePointFixedSubmodule M).baseChange R).comap (Comodule.endOfPoint M g.ofConv) := by
  rw [Submodule.baseChange_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply]
  rw [Comodule.endOfPoint_tmul, one_smul,
    Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
  exact Submodule.subset_span
    ⟨_, basePointsRepresentation_mem_basePointFixedSubmodule hI g hm, rfl⟩

/-- Scalar-extension form of the stability of normal-subgroup fixed vectors. This is the shape
needed by geometric point-separation criteria for promoting a submodule to a subcomodule. -/
theorem endOfPoint_one_tmul_mem_basePointFixedSubmodule_baseChange (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {m : M} (hm : m ∈ I.basePointFixedSubmodule M) :
    Comodule.endOfPoint M g.ofConv (1 ⊗ₜ[R] m) ∈
      (I.basePointFixedSubmodule M).baseChange R :=
  endOfPoint_le_comap_basePointFixedSubmodule_baseChange hI g
    (Submodule.tmul_mem_baseChange_of_mem _ hm)

end IsNormal

end HopfIdeal

end

end TauCeti
