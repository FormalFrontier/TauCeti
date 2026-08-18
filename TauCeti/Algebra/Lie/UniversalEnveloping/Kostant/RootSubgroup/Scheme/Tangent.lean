/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic

/-!
# The tangent vector of a Kostant root subgroup

A pinning of a split reductive group scheme is the data `(G, T, B, {X_α})` of a split maximal
torus, a Borel containing it, and a root vector `X_α` in the Lie algebra for each simple root.
What ties that data to the root subgroup maps `x_α : 𝔾ₐ → G` is a pair of equations: the
differential of `x_α` at the identity is `X_α`, and the torus acts on `X_α` through the root `α`.
This file proves the first, so that the Kostant root vectors are read off the morphisms already
built rather than posited alongside them; the second is
`kostantTorusPoints_conj_kostantRootOperator`, an algebraic statement about points that needs no
scheme theory and lives beside the torus it is about.

The integral operator `X_α` is `kostantRootOperator`, the restriction to the lattice `M` of the
designated root vector `ρ(eᵢ)`. It is the first restricted divided power, so it is exactly the
linear coefficient of the divided-power exponential

```text
xᵢ(t) = ∑ₖ e⁽ᵏ⁾ tᵏ.
```

The coordinate morphism of `x_α` therefore sends a generic matrix entry to a polynomial in the
coordinate `t` of `𝔾ₐ` whose linear coefficient is the corresponding entry of `X_α`. A tangent
vector at the identity is a counit-valued derivation, and the coordinate `t` is primitive, so
such a derivation annihilates every power of `t` other than the first
(`AdditiveGroup.tangent_ι_pow_eq_zero`). Differentiating the coordinate morphism therefore reads
off precisely that linear coefficient, which is
`tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap`. Together with the torus equation
both directions of the pinning are available in the form a consumer states its conventions in.

## Main results

* `tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap`, in the namespace
  `TauCeti.UniversalEnvelopingAlgebra`: **the differential of the root subgroup is the root
  vector.** The matrix of the tangent vector obtained by differentiating `x_α : 𝔾ₐ → GLₙ` along a
  tangent vector of `𝔾ₐ` is that tangent vector's value times the matrix of `X_α`. The entrywise
  form is `..._apply`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10, 21.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

section Differential

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (i : I)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable {B : Type*} [CommRing B] [Algebra ℤ B]

/-- The linear term of the divided-power expansion is the root operator. -/
private theorem integralDividedPower_one_eq_kostantRootOperator
    (hv : ∀ v ∈ M, Associative.dividedPower 1
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) • v ∈ M) (v : M) :
    integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 1 hv v =
      kostantRootOperator e h ρ M hM i v :=
  Subtype.ext <| by
    rw [coe_integralDividedPower_apply, coe_kostantRootOperator_apply,
      Associative.dividedPower_one, Module.End.smul_def]

/-- A root vector acting nilpotently with nilpotency class at most one acts as zero, so the
degenerate branch of the divided-power expansion carries no linear term. -/
private theorem kostantRootOperator_eq_zero_of_pow_eq_zero
    (hz : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^ 1 = 0) :
    kostantRootOperator e h ρ M hM i = 0 :=
  LinearMap.ext fun v => Subtype.ext <| by
    rw [coe_kostantRootOperator_apply, ← pow_one (ρ _), hz]
    simp

/-- The coordinate polynomial of the root subgroup: the `(r, s)` entry of the coefficient matrix
of the divided-power comodule is `∑ₖ ⟨b_r, e⁽ᵏ⁾ b_s⟩ tᵏ`. -/
private theorem coefficientMatrix_kostantRootSubgroupComodule (r s : Fin n) :
    letI : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
      kostantRootSubgroupComodule e h ρ M hM i hnil
    Comodule.coefficientMatrix (C := SymmetricAlgebra ℤ ℤ) b r s =
      ∑ k ∈ Finset.range
          (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
        b.repr
            (integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M k
              (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i k hv)
              (b s)) r •
          SymmetricAlgebra.ι ℤ ℤ 1 ^ k := by
  let : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  rw [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    kostantRootSubgroupComodule_coact]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    TensorProduct.lid_tmul, Module.Basis.coord_apply]

/-- Only the linear coefficient of a coordinate polynomial survives differentiation at the
identity, so the derivation reads off the entry of the root operator. -/
private theorem derivation_coefficientMatrix
    (d : Derivation ℤ (SymmetricAlgebra ℤ ℤ)
      (Bialgebra.CounitAlgebra ℤ (SymmetricAlgebra ℤ ℤ) B)) (r s : Fin n) :
    letI : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
      kostantRootSubgroupComodule e h ρ M hM i hnil
    d (Comodule.coefficientMatrix (C := SymmetricAlgebra ℤ ℤ) b r s) =
      b.repr (kostantRootOperator e h ρ M hM i (b s)) r •
        d (SymmetricAlgebra.ι ℤ ℤ 1) := by
  let : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  rw [coefficientMatrix_kostantRootSubgroupComodule e h ρ M hM i hnil b r s, map_sum]
  by_cases hlt : 1 < nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  · refine Finset.sum_eq_single_of_mem 1 (Finset.mem_range.2 hlt) ?_ |>.trans ?_
    · intro k _ hk
      rw [map_zsmul, AdditiveGroup.tangent_ι_pow_eq_zero d 1 hk]
      simp
    · rw [map_zsmul, pow_one,
        integralDividedPower_one_eq_kostantRootOperator e h ρ M hM i _ (b s)]
  · -- Below nilpotency class two the root vector already acts as zero, and no linear term
    -- occurs in the expansion.
    have hz : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^ 1 = 0 :=
      pow_eq_zero_of_le (by omega) (pow_nilpotencyClass hnil)
    rw [kostantRootOperator_eq_zero_of_pow_eq_zero e h ρ M hM i hz]
    rw [Finset.sum_eq_zero, LinearMap.zero_apply, map_zero, Finsupp.coe_zero,
      Pi.zero_apply, zero_smul]
    intro k hk
    rw [map_zsmul, AdditiveGroup.tangent_ι_pow_eq_zero d 1 (by
      have := Finset.mem_range.1 hk
      omega)]
    simp

/-- **The differential of a Kostant root subgroup is the root vector.**

Differentiating the coordinate morphism of `x_α : 𝔾ₐ → GLₙ` at the identity carries a tangent
vector of `𝔾ₐ`, that is a scalar of the coefficient algebra, to that scalar times the matrix of
the integral root operator `X_α`. This is the equation pinning the root subgroup map against the
root vector of the pinning. This is the entrywise form;
`tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap` is the matrix it computes. -/
theorem tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap_apply
    (d : Derivation ℤ (SymmetricAlgebra ℤ ℤ)
      (Bialgebra.CounitAlgebra ℤ (SymmetricAlgebra ℤ ℤ) B)) (r s : Fin n) :
    GeneralLinear.tangentMatrix (R := ℤ) (B := B) n
        (derivationComp (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom d) r s =
      b.repr (kostantRootOperator e h ρ M hM i (b s)) r •
        AdditiveGroup.gaTangentLinearEquiv d := by
  let : Comodule ℤ (SymmetricAlgebra ℤ ℤ) M :=
    kostantRootSubgroupComodule e h ρ M hM i hnil
  -- The differential applies the coordinate morphism through its algebra-hom coercion, while
  -- its computation rule is stated for the bialgebra morphism itself; the two agree
  -- definitionally.
  have hX : (((kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom :
        (GeneralLinear.coordinateHopfAlgebra ℤ n : Type) →ₐ[ℤ] _)
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
        (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (r, s))))) =
      Comodule.coefficientMatrix (C := SymmetricAlgebra ℤ ℤ) b r s :=
    kostantRootSubgroupCoordinateMap_X e h ρ M hM i hnil b r s
  rw [GeneralLinear.tangentMatrix_apply, derivationComp_apply, hX,
    derivation_coefficientMatrix e h ρ M hM i hnil b d r s,
    AdditiveGroup.gaTangentLinearEquiv_apply]
  -- Both coefficient synonyms carry `B` itself, and their identifications with it are the
  -- identity map, so the two scalar multiplications agree.
  simp only [Bialgebra.CounitAlgebra.algEquivSelf_apply]
  exact Bialgebra.CounitAlgebra.algEquivSelf_apply ℤ _ B _

/-- **The differential of a Kostant root subgroup is the root vector**, as a matrix.

Along the tangent vector of `𝔾ₐ` with value `t`, the differential of `x_α : 𝔾ₐ → GLₙ` at the
identity is `t X_α`, with `X_α` the integral root operator written in the lattice basis. This is
the equation pinning the root subgroup map against the root vector of the pinning; it determines
`X_α` from `x_α`, since a matrix is determined by its entries. -/
theorem tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap
    (d : Derivation ℤ (SymmetricAlgebra ℤ ℤ)
      (Bialgebra.CounitAlgebra ℤ (SymmetricAlgebra ℤ ℤ) B)) :
    GeneralLinear.tangentMatrix (R := ℤ) (B := B) n
        (derivationComp (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom d) =
      AdditiveGroup.gaTangentLinearEquiv d •
        (LinearMap.toMatrix b b (kostantRootOperator e h ρ M hM i)).map
          (algebraMap ℤ B) := by
  ext r s
  rw [tangentMatrix_derivationComp_kostantRootSubgroupCoordinateMap_apply
      e h ρ M hM i hnil b d r s,
    Matrix.smul_apply, Matrix.map_apply, LinearMap.toMatrix_apply, zsmul_eq_mul,
    smul_eq_mul, mul_comm]
  simp

end Differential

end TauCeti.UniversalEnvelopingAlgebra
