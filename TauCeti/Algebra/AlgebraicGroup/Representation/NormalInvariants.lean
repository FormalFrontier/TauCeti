/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
import TauCeti.Algebra.Coalgebra.Comodule.PointAction

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

The definition deliberately says `pointFixedSubmodule`: without a point-separation hypothesis,
base-valued points need not detect scheme-theoretic invariants. The normality and stability
results require no reducedness, finite-type, or field hypotheses.

The group-representation step is Mathlib's `Representation.le_comap_invariants`; this file adds
the Hopf-ideal and comodule interface around it rather than repeating its conjugation argument.

## Main declarations

* `TauCeti.HopfIdeal.pointFixedSubmodule`: the vectors fixed by the points cut out by a Hopf
  ideal.
* `TauCeti.HopfIdeal.mem_pointFixedSubmodule_iff_quotient_coact_eq_tmul_one`: geometric-point
  detection identifies the pointwise and scheme-theoretic fixed-vector conditions.
* `TauCeti.HopfIdeal.IsNormal.pointFixedSubrepresentation`: the ambient representation on those
  fixed vectors when the Hopf ideal is normal.
* `TauCeti.HopfIdeal.IsNormal.endOfPoint_tmul_mem_pointFixedSubmodule_baseChange`: pointwise
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

/-- The submodule fixed by all base-valued points of the closed subgroup cut out by `I`. -/
def pointFixedSubmodule (I : HopfIdeal R H) : Submodule R M :=
  let N := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
    (CommAlgCat.of R R)
  Representation.invariants
    ((Comodule.basePointsRepresentation (R := R) (H := H) M).comp N.subtype :
      Representation R N M)

/-- Membership in the point-fixed submodule means being fixed by every base-valued point cut out
by the Hopf ideal. -/
@[simp]
theorem mem_pointFixedSubmodule (I : HopfIdeal R H) (m : M) :
    m ∈ I.pointFixedSubmodule (M := M) ↔
      ∀ n : CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
          (CommAlgCat.of R R),
        Comodule.basePointsRepresentation (R := R) (H := H) M
          (n : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) m = m := by
  rfl

section GeometricDetection

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [CommRing A] [HopfAlgebra k A]
variable [AddCommGroup M] [Module k M] [Comodule k A M] [IsAlgClosed k]

/-- Over an algebraically closed field, if the quotient coordinate ring is reduced and of finite
type, point-fixed vectors are exactly the vectors fixed by the restricted coaction of the closed
subgroup scheme. -/
theorem mem_pointFixedSubmodule_iff_quotient_coact_eq_tmul_one
    (I : HopfIdeal k A)
    [Algebra.FiniteType k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I)]
    [IsReduced (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I)]
    (m : M) :
    m ∈ I.pointFixedSubmodule (M := M) ↔
      TensorProduct.map LinearMap.id
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k A) I).hom.toLinearMap
          (Comodule.coact (R := k) (C := A) m) =
        m ⊗ₜ[k]
          (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I) := by
  let H := _root_.CommHopfAlgCat.of k A
  let Q := CommHopfAlgCat.quotient H I
  let q : A →ₐc[k] Q := (CommHopfAlgCat.mkQuotient H I).hom
  let _ : Comodule k Q M := Comodule.Corestrict q.toCoalgHom
  -- The displayed tensor map is definitionally the coaction corestricted along `q`.
  change m ∈ I.pointFixedSubmodule (M := M) ↔
    Comodule.coact (R := k) (C := Q) m = m ⊗ₜ[k] (1 : Q)
  rw [Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq]
  have hinclude (g : HopfAlgebra.points (R := k) (H := Q) (CommAlgCat.of k k)) :
      AlgHom.mapDomain q g =
        CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) g := by
    rw [CommHopfAlgCat.quotientPointsHom_apply, AlgHom.mapDomain_apply]
  constructor
  · intro hm g
    let n := CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) g
    have hfixed := (mem_pointFixedSubmodule I m).mp hm
      ⟨n, CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H I
        (CommAlgCat.of k k) g⟩
    rw [Comodule.basePointsRepresentation_corestrict q g]
    rw [hinclude]
    exact hfixed
  · intro hm
    rw [mem_pointFixedSubmodule]
    intro n
    have hn : n.1 ∈ Set.range
        (CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k)) :=
      (CommHopfAlgCat.mem_range_quotientPointsHom_iff H I (CommAlgCat.of k k) n.1).2 <|
        (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H I (CommAlgCat.of k k) n.1).1 n.2
    obtain ⟨g, hg⟩ := hn
    have hq : AlgHom.mapDomain q g = n.1 := (hinclude g).trans hg
    have hfixed := hm g
    rw [Comodule.basePointsRepresentation_corestrict q g, hq] at hfixed
    exact hfixed

end GeometricDetection

namespace IsNormal

variable {I : HopfIdeal R H}

/-- The point-fixed submodule of a normal closed subgroup is preserved by every base-valued
ambient point. -/
theorem pointFixedSubmodule_le_comap (hI : I.IsNormal) (g : HopfAlgebra.points
    (R := R) (H := H) (CommAlgCat.of R R)) :
    I.pointFixedSubmodule (M := M) ≤
      (I.pointFixedSubmodule (M := M)).comap
        (Comodule.basePointsRepresentation (R := R) (H := H) M g) := by
  let N := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
    (CommAlgCat.of R R)
  let hN : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R H) I hI (CommAlgCat.of R R)
  let ρ : Representation R
      (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) M :=
    Comodule.basePointsRepresentation (R := R) (H := H) M
  exact @Representation.le_comap_invariants R _ _ _ M _ _ ρ N hN g

/-- The ambient base-point representation restricted to the vectors fixed by a normal closed
subgroup. -/
def pointFixedSubrepresentation (hI : I.IsNormal) :
    Representation R
      (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
      (I.pointFixedSubmodule (M := M)) :=
  (Comodule.basePointsRepresentation (R := R) (H := H) M).subrepresentation
    (I.pointFixedSubmodule (M := M)) (pointFixedSubmodule_le_comap hI)

/-- The restricted point action agrees with the ambient base-point action after coercion. -/
@[simp]
theorem pointFixedSubrepresentation_apply (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (m : I.pointFixedSubmodule (M := M)) :
    ((hI.pointFixedSubrepresentation g m : I.pointFixedSubmodule (M := M)) : M) =
      Comodule.basePointsRepresentation (R := R) (H := H) M g m := by
  rfl

/-- Every ambient base-valued point sends a point-fixed vector to another point-fixed vector. -/
theorem basePointsRepresentation_mem_pointFixedSubmodule (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {m : M} (hm : m ∈ I.pointFixedSubmodule (M := M)) :
    Comodule.basePointsRepresentation (R := R) (H := H) M g m ∈
      I.pointFixedSubmodule (M := M) :=
  pointFixedSubmodule_le_comap hI g hm

/-- Scalar-extension form of the stability of normal-subgroup fixed vectors. This is the shape
needed by geometric point-separation criteria for promoting a submodule to a subcomodule. -/
theorem endOfPoint_tmul_mem_pointFixedSubmodule_baseChange (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {m : M} (hm : m ∈ I.pointFixedSubmodule (M := M)) :
    Comodule.endOfPoint M g.ofConv (1 ⊗ₜ[R] m) ∈
      (I.pointFixedSubmodule (M := M)).baseChange R := by
  rw [Comodule.endOfPoint_one_tmul_eq_tmul_basePointsRepresentation]
  exact Submodule.tmul_mem_baseChange_of_mem _
    (basePointsRepresentation_mem_pointFixedSubmodule hI g hm)

end IsNormal

end HopfIdeal

end

end TauCeti
