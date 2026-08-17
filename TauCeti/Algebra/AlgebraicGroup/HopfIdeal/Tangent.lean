/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic

/-!
# The Lie algebra of a closed affine subgroup

A Hopf ideal `I` in a commutative Hopf algebra `H` presents the closed affine subgroup
`Spec (H ⧸ I) ↪ Spec H`. The differential of this inclusion is contravariantly induced by the
quotient bialgebra morphism `H → H ⧸ I`. This file identifies that differential as an injective
Lie algebra morphism and characterizes its image: it consists exactly of the counit-valued
derivations of `H` which vanish on `I`.

Thus the Lie algebra of the closed subgroup is canonically a Lie subalgebra of the Lie algebra of
the ambient group. This is the coordinate-Hopf-algebra form of the ReductiveGroups roadmap's
Layer 2 target "the Lie algebra of a closed subgroup".

## Main declarations

* `TauCeti.HopfIdeal.quotientLieHom`: the coefficient-linear differential of the closed-subgroup
  inclusion.
* `TauCeti.HopfIdeal.lieSubalgebra`: its image in the ambient Lie algebra.
* `TauCeti.HopfIdeal.mem_lieSubalgebra_iff`,
  `TauCeti.HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span`: membership means vanishing on the
  Hopf ideal, or just on a chosen set of ideal generators.
* `TauCeti.HopfIdeal.quotientLieEquiv`: the closed subgroup's Lie algebra is Lie-equivalent to
  that image.

## References

This is the affine coordinate-ring description in J. S. Milne, *Algebraic Groups* (2017),
§10.a: the tangent space of a closed subgroup is the subspace of tangent derivations annihilating
its defining ideal. The Lie bracket and differential use Tau Ceti's convolution-derivation API;
the quotient Hopf algebra itself is Mathlib's `Bialgebra.Quotient` construction.
-/

public section

namespace TauCeti

open _root_.Coalgebra

universe u v w

namespace HopfIdeal

variable {R : Type u} {H : Type v} {B : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [CommRing B] [Algebra R B]

/-- The differential of the closed-subgroup inclusion presented by a Hopf ideal `I`.

On coordinate rings the inclusion is represented by the quotient bialgebra morphism
`H → H ⧸ I`; the differential therefore sends a derivation of the quotient to its
precomposition with the quotient map. -/
noncomputable def quotientLieHom (I : HopfIdeal R H) :
    Derivation R (H ⧸ I.toIdeal)
        (Bialgebra.CounitAlgebra R (H ⧸ I.toIdeal) B) →ₗ⁅B⁆
      Derivation R H (Bialgebra.CounitAlgebra R H B) :=
  derivationCompLieHom (B := B) (Bialgebra.Quotient.mkBialgHom I.toIdeal)

/-- The closed-subgroup differential acts by precomposition with the quotient map. -/
@[simp]
lemma quotientLieHom_apply_apply (I : HopfIdeal R H)
    (d : Derivation R (H ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (H ⧸ I.toIdeal) B)) (x : H) :
    quotientLieHom I d x =
      Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
        (d (Ideal.Quotient.mkₐ R I.toIdeal x)) := by
  simp [quotientLieHom]
  rfl

/-- The differential of a closed-subgroup inclusion is injective. -/
theorem quotientLieHom_injective (I : HopfIdeal R H) :
    Function.Injective (quotientLieHom (B := B) I) := by
  intro d e hde
  apply Derivation.ext
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q
  apply (Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B).injective
  have hx := congrArg
    (fun f => Bialgebra.CounitAlgebra.algEquivSelf R H B (f x)) hde
  simp only [quotientLieHom_apply_apply] at hx
  rw [Bialgebra.CounitAlgebra.algEquivSelf_apply R H B
      (Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
        (d (Ideal.Quotient.mkₐ R I.toIdeal x))),
    Bialgebra.CounitAlgebra.algEquivSelf_apply R H B
      (Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
        (e (Ideal.Quotient.mkₐ R I.toIdeal x)))] at hx
  exact hx

/-- The Lie subalgebra of the ambient tangent Lie algebra cut out by a Hopf ideal.

It is defined intrinsically as the range of the closed-subgroup differential; membership is
characterized without reference to this range by `mem_lieSubalgebra_iff`. -/
noncomputable def lieSubalgebra (I : HopfIdeal R H) :
    LieSubalgebra B (Derivation R H (Bialgebra.CounitAlgebra R H B)) :=
  (quotientLieHom (B := B) I).range

/-- The `R`-linear identification between the two copies of the coefficient ring used by the
ambient Hopf algebra and its quotient. -/
private noncomputable def coefficientLinearEquiv (I : HopfIdeal R H) :
    Bialgebra.CounitAlgebra R H B ≃ₗ[R]
      Bialgebra.CounitAlgebra R (H ⧸ I.toIdeal) B :=
  (Bialgebra.CounitAlgebra.algEquivSelf R H B).toLinearEquiv.trans
    (Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B).symm.toLinearEquiv

/-- The coefficient identification is the identity after forgetting the indexing Hopf algebra. -/
@[simp]
private lemma coefficientLinearEquiv_apply (I : HopfIdeal R H)
    (b : Bialgebra.CounitAlgebra R H B) :
    Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
        (coefficientLinearEquiv I b) =
      Bialgebra.CounitAlgebra.algEquivSelf R H B b := by
  -- The composition is definitionally `old copy → B → new copy`; the public inverse law of the
  -- second equivalence is the stable way to discharge the synonym transport.
  change Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
      ((Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B).symm
        (Bialgebra.CounitAlgebra.algEquivSelf R H B b)) =
    Bialgebra.CounitAlgebra.algEquivSelf R H B b
  exact (Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B).apply_symm_apply _

/-- The coefficient identification intertwines the scalar actions through the quotient map. -/
private lemma coefficientLinearEquiv_smul (I : HopfIdeal R H) (x : H)
    (b : Bialgebra.CounitAlgebra R H B) :
    coefficientLinearEquiv I (x • b) =
      Ideal.Quotient.mkₐ R I.toIdeal x • coefficientLinearEquiv I b := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B).injective
  calc
    Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
          (coefficientLinearEquiv I (x • b)) =
        Bialgebra.CounitAlgebra.algEquivSelf R H B (x • b) :=
      coefficientLinearEquiv_apply I (x • b)
    _ = algebraMap R B (counit (R := R) x) *
          Bialgebra.CounitAlgebra.algEquivSelf R H B b := by
      rw [Algebra.smul_def, map_mul, Bialgebra.CounitAlgebra.algebraMap_apply]
      rw [Bialgebra.CounitAlgebra.algEquivSelf_apply R H B
        (algebraMap R B (counit (R := R) x))]
    _ = algebraMap R B
          (counit (R := R) (Ideal.Quotient.mkₐ R I.toIdeal x)) *
            Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
              (coefficientLinearEquiv I b) := by
      rw [coefficientLinearEquiv_apply]
      congr 1
    _ = Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
          (Ideal.Quotient.mkₐ R I.toIdeal x • coefficientLinearEquiv I b) := by
      rw [Algebra.smul_def, map_mul, Bialgebra.CounitAlgebra.algebraMap_apply]
      rw [Bialgebra.CounitAlgebra.algEquivSelf_apply R (H ⧸ I.toIdeal) B
        (algebraMap R B (counit (R := R) (Ideal.Quotient.mkₐ R I.toIdeal x)))]

/-- A derivation which vanishes on `I` descends to the quotient `H ⧸ I`.

This is the linear quotient universal property together with the Leibniz rule on representatives.
It is an implementation of the reverse implication in `mem_lieSubalgebra_iff`; the canonical
public inverse is packaged by `quotientLieEquiv`. -/
private noncomputable def descendDerivation (I : HopfIdeal R H)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (hd : ∀ x ∈ I.toIdeal, d x = 0) :
    Derivation R (H ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (H ⧸ I.toIdeal) B) :=
  Derivation.mk'
    ((I.toIdeal.restrictScalars R).liftQ
      ((coefficientLinearEquiv I).toLinearMap.comp d.toLinearMap) fun x hx => by
      rw [LinearMap.mem_ker]
      exact (coefficientLinearEquiv I).map_eq_zero_iff.mpr (hd x hx))
    fun q₁ q₂ => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q₁
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I.toIdeal q₂
      -- The quotient lift computes on representatives, but its application is hidden behind
      -- `Derivation.mk'`; restate that stable pointwise formula before using the public API.
      change coefficientLinearEquiv I (d (x * y)) =
        Ideal.Quotient.mkₐ R I.toIdeal x • coefficientLinearEquiv I (d y) +
          Ideal.Quotient.mkₐ R I.toIdeal y • coefficientLinearEquiv I (d x)
      rw [d.leibniz, map_add]
      rw [coefficientLinearEquiv_smul, coefficientLinearEquiv_smul]

/-- The descended derivation evaluates on a quotient class as the original derivation. -/
@[simp]
private lemma descendDerivation_mk (I : HopfIdeal R H)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B))
    (hd : ∀ x ∈ I.toIdeal, d x = 0) (x : H) :
    Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
        (descendDerivation I d hd (Ideal.Quotient.mkₐ R I.toIdeal x)) =
      Bialgebra.CounitAlgebra.algEquivSelf R H B (d x) := by
  -- As above, this is the quotient-lift computation hidden behind `Derivation.mk'`.
  change Bialgebra.CounitAlgebra.algEquivSelf R (H ⧸ I.toIdeal) B
      (coefficientLinearEquiv I (d x)) =
    Bialgebra.CounitAlgebra.algEquivSelf R H B (d x)
  exact coefficientLinearEquiv_apply I (d x)

/-- A tangent derivation belongs to the Lie algebra of the closed subgroup defined by `I`
exactly when it vanishes on the defining Hopf ideal. -/
@[simp]
theorem mem_lieSubalgebra_iff (I : HopfIdeal R H)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ lieSubalgebra (B := B) I ↔ ∀ x ∈ I.toIdeal, d x = 0 := by
  constructor
  · rw [lieSubalgebra, LieHom.mem_range]
    rintro ⟨e, rfl⟩ x hx
    rw [quotientLieHom_apply_apply]
    have hqx : Ideal.Quotient.mkₐ R I.toIdeal x = 0 := by
      simpa only [Ideal.Quotient.mkₐ_eq_mk] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
    rw [hqx, map_zero]
    exact Bialgebra.CounitAlgebra.algEquivSelf_apply R (H ⧸ I.toIdeal) B 0
  · intro hd
    rw [lieSubalgebra, LieHom.mem_range]
    refine ⟨descendDerivation I d hd, Derivation.ext fun x => ?_⟩
    rw [quotientLieHom_apply_apply]
    exact (descendDerivation_mk I d hd x).trans
      (Bialgebra.CounitAlgebra.algEquivSelf_apply R H B (d x))

/-- When a Hopf ideal is generated by `S`, membership in its tangent Lie subalgebra is equivalent
to vanishing of the derivation on the generators in `S`. -/
theorem mem_lieSubalgebra_iff_of_toIdeal_eq_span (I : HopfIdeal R H) {S : Set H}
    (hI : I.toIdeal = Ideal.span S)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ lieSubalgebra (B := B) I ↔ ∀ x ∈ S, d x = 0 := by
  rw [mem_lieSubalgebra_iff]
  constructor
  · intro hd x hx
    apply hd x
    rw [hI]
    exact Ideal.subset_span hx
  · intro hd x hx
    apply TauCeti.Derivation.apply_eq_zero_of_mem_span d (hd := hd) (hx := hI ▸ hx)
    intro y hy
    apply I.counit_eq_zero
    apply HopfIdeal.mem_toIdeal.mp
    rw [hI]
    exact Ideal.subset_span hy

/-- The Lie algebra of the quotient Hopf algebra is canonically Lie-equivalent to its image in
the ambient tangent Lie algebra. -/
noncomputable def quotientLieEquiv (I : HopfIdeal R H) :
    Derivation R (H ⧸ I.toIdeal)
        (Bialgebra.CounitAlgebra R (H ⧸ I.toIdeal) B) ≃ₗ⁅B⁆
      lieSubalgebra (B := B) I :=
  (quotientLieHom (B := B) I).equivRangeOfInjective (quotientLieHom_injective I)

/-- The canonical Lie equivalence sends a quotient derivation to its precomposition with the
quotient map. -/
@[simp]
theorem quotientLieEquiv_apply_coe (I : HopfIdeal R H)
    (d : Derivation R (H ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (H ⧸ I.toIdeal) B)) :
    (quotientLieEquiv (B := B) I d :
      Derivation R H (Bialgebra.CounitAlgebra R H B)) = quotientLieHom I d :=
  congrArg Subtype.val
    (LieHom.equivRangeOfInjective_apply (quotientLieHom (B := B) I)
      (quotientLieHom_injective I) d)

/-- The inverse of the canonical Lie equivalence descends an ambient derivation by evaluating
on representatives of the quotient. -/
@[simp]
theorem quotientLieEquiv_symm_apply_mk (I : HopfIdeal R H)
    (d : lieSubalgebra (B := B) I) (x : H) :
    (quotientLieEquiv (B := B) I).symm d (Ideal.Quotient.mk I.toIdeal x) =
      (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) x := by
  have h : quotientLieHom I ((quotientLieEquiv (B := B) I).symm d) =
      (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :=
    (quotientLieEquiv_apply_coe I ((quotientLieEquiv (B := B) I).symm d)).symm.trans
      (congrArg Subtype.val ((quotientLieEquiv (B := B) I).apply_symm_apply d))
  have hx := congrArg (fun e : Derivation R H (Bialgebra.CounitAlgebra R H B) => e x) h
  rw [quotientLieHom_apply_apply] at hx
  rw [← Ideal.Quotient.mkₐ_eq_mk (R₁ := R)]
  exact (Bialgebra.CounitAlgebra.algEquivSelf_apply R (H ⧸ I.toIdeal) B _).symm.trans hx

end HopfIdeal

end TauCeti
