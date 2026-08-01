/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map

/-!
# Evaluation of the group-like monoid algebra

Every bialgebra `H` over a commutative semiring `R` receives a canonical bialgebra morphism from
the monoid algebra on its group-like elements. It sends each standard basis element to its
underlying group-like element. Its linear range is exactly the span of the group-like elements,
and its subcoalgebra image is the subcoalgebra spanned by all group-like elements. The morphism is
injective exactly when the underlying group-like elements are linearly independent, and it is a
bialgebra equivalence when they are also spanning. Over a commutative domain, linear independence
is automatic when the carrier of `H` is torsion-free.

## Main declarations

* `TauCeti.GroupLike.evaluationBialgHom`: the canonical bialgebra morphism
  `R[GroupLike R H] →ₐc[R] H`.
* `TauCeti.GroupLike.range_evaluationBialgHom`: its linear range is the span of the group-like
  elements.
* `TauCeti.GroupLike.map_top_evaluationBialgHom`: its subcoalgebra image is the subcoalgebra
  spanned by all group-like elements.
* `TauCeti.GroupLike.evaluationBialgHom_injective_iff_linearIndependent`: injectivity is equivalent
  to linear independence of the group-like elements.
* `TauCeti.GroupLike.evaluationBialgEquivOfLinearIndependent`: the equivalence obtained from linear
  independence and spanning.
* `TauCeti.GroupLike.evaluationBialgHom_injective`: injectivity over a domain for a torsion-free
  carrier.
* `TauCeti.GroupLike.evaluationBialgEquiv`: the specialized equivalence over a domain when the
  group-like elements span a torsion-free carrier.

## References

The automatic linear independence used in the domain and torsion-free specialization is the
domain-valued form of Milne, *Algebraic Groups*, Proposition 4.23. The reconstruction in the
spanning case is the bialgebra form underlying Definition 12.7 and Theorem 12.8 of the same
reference.
-/

public section

namespace TauCeti

universe u v

namespace GroupLike

variable (R : Type u) (H : Type v)

section Semiring

variable [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- The canonical bialgebra morphism from the monoid algebra on the group-like elements of `H`
to `H`, sending each standard basis element to its underlying group-like element. -/
noncomputable def evaluationBialgHom :
    MonoidAlgebra R (_root_.GroupLike R H) →ₐc[R] H :=
  BialgHom.ofAlgHom
    (MonoidAlgebra.lift R H (_root_.GroupLike R H) (_root_.GroupLike.valMonoidHom R H))
    (by ext; simp)
    (by ext; simp)

/-- The algebra homomorphism underlying evaluation is the defining monoid-algebra lift. -/
private theorem evaluationBialgHom_toAlgHom :
    (evaluationBialgHom R H :
      MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H) =
      MonoidAlgebra.lift R H (_root_.GroupLike R H)
        (_root_.GroupLike.valMonoidHom R H) :=
  rfl

/-- Evaluation on a scalar multiple of a standard basis element. -/
@[simp]
theorem evaluationBialgHom_single (g : _root_.GroupLike R H) (r : R) :
    evaluationBialgHom R H (MonoidAlgebra.single g r) = r • (g : H) := by
  calc
    evaluationBialgHom R H (MonoidAlgebra.single g r) =
        (evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H)
            (MonoidAlgebra.single g r) := by
      simp only [BialgHom.coe_toAlgHom]
    _ = MonoidAlgebra.lift R H (_root_.GroupLike R H)
          (_root_.GroupLike.valMonoidHom R H) (MonoidAlgebra.single g r) := by
      rw [evaluationBialgHom_toAlgHom]
    _ = r • (g : H) := by
      rw [MonoidAlgebra.lift_single, _root_.GroupLike.valMonoidHom_apply]

/-- Evaluation of a monoid-algebra element is the finite linear combination of its group-like
indices with its coefficients. -/
theorem evaluationBialgHom_apply (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    evaluationBialgHom R H x = x.coeff.sum fun g r => r • (g : H) := by
  calc
    evaluationBialgHom R H x =
        (evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H) x := by
      simp only [BialgHom.coe_toAlgHom]
    _ = MonoidAlgebra.lift R H (_root_.GroupLike R H)
          (_root_.GroupLike.valMonoidHom R H) x := by
      rw [evaluationBialgHom_toAlgHom]
    _ = x.coeff.sum fun g r => r • (g : H) := by
      rw [MonoidAlgebra.lift_apply]
      simp only [_root_.GroupLike.valMonoidHom_apply]

/-- Evaluation is finite linear combination of the underlying group-like elements after passing
to the coefficient representation of the monoid algebra. -/
theorem evaluationBialgHom_toLinearMap :
    (evaluationBialgHom R H : MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
      (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))).comp
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
  calc
    (evaluationBialgHom R H :
        MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
        ((evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H) :
            MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) :=
      (BialgHom.toAlgHom_toLinearMap (evaluationBialgHom R H)).symm
    _ = (MonoidAlgebra.lift R H (_root_.GroupLike R H)
          (_root_.GroupLike.valMonoidHom R H)).toLinearMap :=
      congrArg (fun f : MonoidAlgebra R (_root_.GroupLike R H) →ₐ[R] H =>
        f.toLinearMap) (evaluationBialgHom_toAlgHom R H)
    _ = (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))).comp
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
      apply LinearMap.ext
      intro x
      rw [AlgHom.toLinearMap_apply, MonoidAlgebra.lift_apply,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination_apply]
      simp only [_root_.GroupLike.valMonoidHom_apply]

/-- The linear range of evaluation is the span of the underlying group-like elements. -/
theorem range_evaluationBialgHom :
    LinearMap.range
        (evaluationBialgHom R H : MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
      Submodule.span R
        (Set.range (_root_.GroupLike.val (R := R) (A := H))) := by
  rw [evaluationBialgHom_toLinearMap]
  calc
    LinearMap.range
        ((Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))).comp
            (MonoidAlgebra.coeffLinearEquiv R).toLinearMap) =
        LinearMap.range (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))) :=
      LinearMap.range_comp_of_range_eq_top _
        (LinearEquiv.range (MonoidAlgebra.coeffLinearEquiv R))
    _ = Submodule.span R
        (Set.range (_root_.GroupLike.val (R := R) (A := H))) :=
      Finsupp.range_linearCombination (R := R)
        (v := _root_.GroupLike.val (R := R) (A := H))

/-- The linear range of evaluation is the underlying submodule of the subcoalgebra spanned by all
group-like elements. -/
theorem range_evaluationBialgHom_eq_groupLikeSetSpan_toSubmodule :
    LinearMap.range
        (evaluationBialgHom R H : MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
      (Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ).toSubmodule := by
  rw [range_evaluationBialgHom, Subcoalgebra.groupLikeSetSpan_toSubmodule]
  congr 1
  simp only [Set.image_univ]

/-- The image of the full source subcoalgebra under evaluation is the subcoalgebra spanned by all
group-like elements. -/
theorem map_top_evaluationBialgHom :
    (Subcoalgebra.map
        (evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
        (⊤ : Subcoalgebra R (MonoidAlgebra R (_root_.GroupLike R H)))) =
      Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ := by
  apply Subcoalgebra.ext
  intro h
  have hmap :
      (Subcoalgebra.map
        (evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
        (⊤ : Subcoalgebra R (MonoidAlgebra R (_root_.GroupLike R H)))).toSubmodule =
        LinearMap.range
          (evaluationBialgHom R H :
            MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) :=
    Subcoalgebra.map_top_toSubmodule _
  calc
    h ∈ Subcoalgebra.map
        (evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
        (⊤ : Subcoalgebra R (MonoidAlgebra R (_root_.GroupLike R H))) ↔
        h ∈ (Subcoalgebra.map
          (evaluationBialgHom R H :
            MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
          (⊤ : Subcoalgebra R
            (MonoidAlgebra R (_root_.GroupLike R H)))).toSubmodule :=
      Subcoalgebra.mem_toSubmodule.symm
    _ ↔ h ∈ LinearMap.range
        (evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) := by
      rw [hmap]
    _ ↔ h ∈
        (Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ).toSubmodule := by
      rw [range_evaluationBialgHom_eq_groupLikeSetSpan_toSubmodule]
    _ ↔ h ∈ Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ :=
      Subcoalgebra.mem_toSubmodule

/-- Evaluation is surjective exactly when the group-like elements span the whole bialgebra. -/
theorem evaluationBialgHom_surjective_iff_span_eq_top :
    Function.Surjective (evaluationBialgHom R H) ↔
      Submodule.span R
          (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤ := by
  constructor
  · intro h
    rw [← range_evaluationBialgHom R H]
    apply LinearMap.range_eq_top.2
    simpa only [BialgHom.coe_toLinearMap] using h
  · intro h
    have hsurjective : Function.Surjective
        (evaluationBialgHom R H :
          MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) := by
      apply LinearMap.range_eq_top.1
      rw [range_evaluationBialgHom R H]
      exact h
    simpa only [BialgHom.coe_toLinearMap] using hsurjective

/-- Evaluation is surjective exactly when the subcoalgebra spanned by all group-like elements is
the full subcoalgebra. -/
theorem evaluationBialgHom_surjective_iff_groupLikeSetSpan_eq_top :
    Function.Surjective (evaluationBialgHom R H) ↔
      Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ = ⊤ := by
  rw [evaluationBialgHom_surjective_iff_span_eq_top]
  constructor
  · intro h
    apply Subcoalgebra.ext
    intro x
    rw [Subcoalgebra.mem_groupLikeSetSpan]
    simp [h]
  · intro h
    have hsubmodule := congrArg Subcoalgebra.toSubmodule h
    simpa only [Subcoalgebra.groupLikeSetSpan_toSubmodule,
      Subcoalgebra.top_toSubmodule, Set.image_univ] using hsubmodule

/-- Evaluation is injective exactly when the underlying group-like elements are linearly
independent. -/
theorem evaluationBialgHom_injective_iff_linearIndependent :
    Function.Injective (evaluationBialgHom R H) ↔
      LinearIndependent R (_root_.GroupLike.val (R := R) (A := H)) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  have hevaluation :
      (evaluationBialgHom R H :
        MonoidAlgebra R (_root_.GroupLike R H) → H) =
        (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))) ∘
          (MonoidAlgebra.coeffLinearEquiv R) := by
    simpa only [BialgHom.coe_toLinearMap, LinearMap.coe_comp,
      LinearEquiv.coe_toLinearMap] using
      congrArg
        (fun f : MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H =>
          (f : MonoidAlgebra R (_root_.GroupLike R H) → H))
        (evaluationBialgHom_toLinearMap R H)
  rw [hevaluation]
  exact Function.Injective.of_comp_iff'
    (Finsupp.linearCombination R
      (_root_.GroupLike.val (R := R) (A := H)))
    (MonoidAlgebra.coeffLinearEquiv R).bijective

/-- If the underlying group-like elements are linearly independent and span the bialgebra,
evaluation is a bialgebra equivalence. -/
noncomputable def evaluationBialgEquivOfLinearIndependent
    (hlinear : LinearIndependent R
      (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    MonoidAlgebra R (_root_.GroupLike R H) ≃ₐc[R] H :=
  BialgEquiv.ofBijective (evaluationBialgHom R H)
    ⟨(evaluationBialgHom_injective_iff_linearIndependent R H).2 hlinear,
      (evaluationBialgHom_surjective_iff_span_eq_top R H).2 hspan⟩

/-- The general bialgebra equivalence obtained from linear independence and spanning applies as
evaluation. -/
@[simp]
theorem evaluationBialgEquivOfLinearIndependent_apply
    (hlinear : LinearIndependent R
      (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤)
    (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    evaluationBialgEquivOfLinearIndependent R H hlinear hspan x =
      evaluationBialgHom R H x := by
  rw [evaluationBialgEquivOfLinearIndependent]
  exact congrFun (BialgEquiv.coe_ofBijective (evaluationBialgHom R H) _) x

/-- The bialgebra morphism underlying the general equivalence from linear independence and
spanning is evaluation. -/
@[simp]
theorem evaluationBialgEquivOfLinearIndependent_toBialgHom
    (hlinear : LinearIndependent R
      (_root_.GroupLike.val (R := R) (A := H)))
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    (evaluationBialgEquivOfLinearIndependent R H hlinear hspan :
      MonoidAlgebra R (_root_.GroupLike R H) →ₐc[R] H) = evaluationBialgHom R H := by
  apply BialgHom.ext
  exact evaluationBialgEquivOfLinearIndependent_apply R H hlinear hspan

end Semiring

section Domain

variable (R : Type u) (H : Type v)
variable [CommRing R] [IsDomain R] [Ring H] [Bialgebra R H]
variable [Module.IsTorsionFree R H]

/-- Over a commutative domain, evaluation is injective when the carrier is torsion-free. -/
theorem evaluationBialgHom_injective :
    Function.Injective (evaluationBialgHom R H) := by
  exact (evaluationBialgHom_injective_iff_linearIndependent R H).2
    (linearIndep_groupLikeVal (R := R) (A := H))

/-- If the group-like elements span a torsion-free bialgebra over a commutative domain, evaluation
is a bialgebra equivalence. -/
noncomputable def evaluationBialgEquiv
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    MonoidAlgebra R (_root_.GroupLike R H) ≃ₐc[R] H :=
  evaluationBialgEquivOfLinearIndependent R H
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan

/-- The bialgebra equivalence obtained from spanning applies as evaluation. -/
@[simp]
theorem evaluationBialgEquiv_apply
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤)
    (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    evaluationBialgEquiv R H hspan x = evaluationBialgHom R H x :=
  evaluationBialgEquivOfLinearIndependent_apply R H
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan x

/-- The bialgebra morphism underlying the spanning equivalence is evaluation. -/
@[simp]
theorem evaluationBialgEquiv_toBialgHom
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    (evaluationBialgEquiv R H hspan :
      MonoidAlgebra R (_root_.GroupLike R H) →ₐc[R] H) = evaluationBialgHom R H :=
  evaluationBialgEquivOfLinearIndependent_toBialgHom R H
    (linearIndep_groupLikeVal (R := R) (A := H)) hspan

end Domain

end GroupLike

end TauCeti
