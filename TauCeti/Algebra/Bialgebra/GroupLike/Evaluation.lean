/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Map

/-!
# Evaluation of the group-like monoid algebra

Every bialgebra `H` over a commutative semiring `R` receives a canonical bialgebra morphism from
the monoid algebra on its group-like elements. It sends each standard basis element to its
underlying group-like element. Its linear range is exactly the span of the group-like elements,
and its subcoalgebra image is the subcoalgebra spanned by all group-like elements.

Over a commutative domain, when the carrier of `H` is torsion-free, linear independence of
group-like elements makes this canonical morphism injective. It is therefore a bialgebra
equivalence whenever the group-like elements span `H`. For a Hopf algebra the indexing monoid is
automatically a group, and it is a commutative group when the Hopf algebra is commutative.

## Main declarations

* `TauCeti.GroupLike.evaluationBialgHom`: the canonical bialgebra morphism
  `R[GroupLike R H] →ₐc[R] H`.
* `TauCeti.GroupLike.range_evaluationBialgHom`: its linear range is the span of the group-like
  elements.
* `TauCeti.GroupLike.map_top_evaluationBialgHom`: its subcoalgebra image is the subcoalgebra
  spanned by all group-like elements.
* `TauCeti.GroupLike.evaluationBialgHom_injective`: injectivity over a domain for a torsion-free
  carrier.
* `TauCeti.GroupLike.evaluationBialgEquiv`: the resulting equivalence when the group-like
  elements span.

## References

The linear-independence input is the domain-valued form of Milne, *Algebraic Groups*, Proposition
4.23. The reconstruction in the spanning case is the bialgebra form underlying Definition 12.7
and Theorem 12.8 of the same reference.
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
@[expose] noncomputable def evaluationBialgHom :
    MonoidAlgebra R (_root_.GroupLike R H) →ₐc[R] H :=
  BialgHom.ofAlgHom
    (MonoidAlgebra.lift R H (_root_.GroupLike R H) (_root_.GroupLike.valMonoidHom R H))
    (by ext; simp)
    (by ext; simp)

/-- Evaluation on a scalar multiple of a standard basis element. -/
@[simp]
theorem evaluationBialgHom_single (g : _root_.GroupLike R H) (r : R) :
    evaluationBialgHom R H (MonoidAlgebra.single g r) = r • (g : H) := by
  exact MonoidAlgebra.lift_single (_root_.GroupLike.valMonoidHom R H) g r

/-- Evaluation of a monoid-algebra element is the finite linear combination of its group-like
indices with its coefficients. -/
theorem evaluationBialgHom_apply (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    evaluationBialgHom R H x = x.coeff.sum fun g r => r • (g : H) := by
  change
    MonoidAlgebra.lift R H (_root_.GroupLike R H)
        (_root_.GroupLike.valMonoidHom R H) x = _
  rw [MonoidAlgebra.lift_apply]
  simp only [_root_.GroupLike.valMonoidHom_apply]

/-- Evaluation is finite linear combination of the underlying group-like elements after passing
to the coefficient representation of the monoid algebra. -/
theorem evaluationBialgHom_toLinearMap :
    (evaluationBialgHom R H : MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) =
      (Finsupp.linearCombination R
          (_root_.GroupLike.val (R := R) (A := H))).comp
        (MonoidAlgebra.coeffLinearEquiv R).toLinearMap := by
  apply LinearMap.ext
  intro x
  change
    MonoidAlgebra.lift R H (_root_.GroupLike R H)
        (_root_.GroupLike.valMonoidHom R H) x =
      Finsupp.linearCombination R
        (_root_.GroupLike.val (R := R) (A := H)) x.coeff
  rw [MonoidAlgebra.lift_apply, Finsupp.linearCombination_apply]
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
  change
    h ∈ (Subcoalgebra.map
      (evaluationBialgHom R H :
        MonoidAlgebra R (_root_.GroupLike R H) →ₗc[R] H)
      (⊤ : Subcoalgebra R (MonoidAlgebra R (_root_.GroupLike R H)))).toSubmodule ↔
    h ∈ (Subcoalgebra.groupLikeSetSpan (R := R) (C := H) Set.univ).toSubmodule
  rw [hmap, range_evaluationBialgHom_eq_groupLikeSetSpan_toSubmodule]

/-- Evaluation is surjective exactly when the group-like elements span the whole bialgebra. -/
theorem evaluationBialgHom_surjective_iff_span_eq_top :
    Function.Surjective (evaluationBialgHom R H) ↔
      Submodule.span R
          (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤ := by
  change Function.Surjective
      (evaluationBialgHom R H :
        MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) ↔ _
  constructor
  · intro h
    rw [← range_evaluationBialgHom R H]
    exact LinearMap.range_eq_top.2 h
  · intro h
    apply LinearMap.range_eq_top.1
    rw [range_evaluationBialgHom R H]
    exact h

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

end Semiring

section Domain

variable (R : Type u) (H : Type v)
variable [CommRing R] [IsDomain R] [Ring H] [Bialgebra R H]
variable [Module.IsTorsionFree R H]

/-- Over a commutative domain, evaluation is injective when the carrier is torsion-free. -/
theorem evaluationBialgHom_injective :
    Function.Injective (evaluationBialgHom R H) := by
  intro x y hxy
  change
    (evaluationBialgHom R H :
        MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) x =
      (evaluationBialgHom R H :
        MonoidAlgebra R (_root_.GroupLike R H) →ₗ[R] H) y at hxy
  rw [evaluationBialgHom_toLinearMap] at hxy
  apply (MonoidAlgebra.coeffLinearEquiv R).injective
  exact (linearIndep_groupLikeVal (R := R) (A := H)) hxy

/-- If the group-like elements span a torsion-free bialgebra over a commutative domain, evaluation
is a bialgebra equivalence. -/
@[expose] noncomputable def evaluationBialgEquiv
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    MonoidAlgebra R (_root_.GroupLike R H) ≃ₐc[R] H :=
  BialgEquiv.ofBijective (evaluationBialgHom R H)
    ⟨evaluationBialgHom_injective R H,
      (evaluationBialgHom_surjective_iff_span_eq_top R H).2 hspan⟩

/-- The bialgebra equivalence obtained from spanning applies as evaluation. -/
@[simp]
theorem evaluationBialgEquiv_apply
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤)
    (x : MonoidAlgebra R (_root_.GroupLike R H)) :
    evaluationBialgEquiv R H hspan x = evaluationBialgHom R H x :=
  rfl

/-- The bialgebra morphism underlying the spanning equivalence is evaluation. -/
@[simp]
theorem evaluationBialgEquiv_toBialgHom
    (hspan : Submodule.span R
      (Set.range (_root_.GroupLike.val (R := R) (A := H))) = ⊤) :
    (evaluationBialgEquiv R H hspan :
      MonoidAlgebra R (_root_.GroupLike R H) →ₐc[R] H) = evaluationBialgHom R H :=
  rfl

end Domain

end GroupLike

end TauCeti
