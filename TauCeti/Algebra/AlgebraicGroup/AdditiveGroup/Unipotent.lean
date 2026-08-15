/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic

/-!
# The additive group is unipotent

Let `R` be a commutative ring and let `R[x] = SymmetricAlgebra R R` be the coordinate Hopf
algebra of the additive group `𝔾ₐ`, with primitive generator `x = ι(1)`. This file proves that
**every point of `𝔾ₐ` is unipotent**: for every commutative `R`-algebra `A`, every point
`g : R[x] →ₐ[R] A` acts on the scalar extension of every finitely generated comodule by an
automorphism whose difference from the identity is nilpotent. Over a field this says that `𝔾ₐ`
acts unipotently in every finite-dimensional representation, which is the geometric definition of
a unipotent group; together with the smoothness of `R[x]` it exhibits `𝔾ₐ` as the basic example
of the Layer 5 predicates of the reductive-groups roadmap.

The proof is the classical divided-power argument. The monomials `xⁿ` form a basis of `R[x]`
(`monomialBasis`), so the coaction of a comodule `V` can be written `ρ v = ∑ₙ Nₙ v ⊗ xⁿ` for a
family of endomorphisms `Nₙ` of `V` (`coactComponent`), only finitely many of which are nonzero
on any given vector. The counit axiom says `N₀ = id`, and coassociativity, combined with the
binomial expansion `Δ(xⁿ) = ∑ₖ (n choose k) xᵏ ⊗ xⁿ⁻ᵏ` of the primitive generator, says that
`Nᵢ ∘ Nⱼ = (i + j choose i) Nᵢ₊ⱼ`. A point `g` then acts by `a ⊗ v ↦ ∑ᵢ a (g x)ⁱ ⊗ Nᵢ v`, so its
difference from the identity involves only the components of positive index. Filtering `V` by the
submodules `Vₚ` on which every `Nᵢ` with `i > p` vanishes (`coactFiltration`), that difference
carries `Vₚ` into `Vₚ₋₁` and annihilates `V₀`; since a finitely generated comodule is `V_d` for
some `d`, the `(d + 1)`-st power of the difference vanishes.

## Main definitions

* `TauCeti.AdditiveGroup.monomialBasis`: the monomials `xⁿ` as a basis of `R[x]`, with
  `TauCeti.AdditiveGroup.coeff` its coordinate functionals.
* `TauCeti.AdditiveGroup.coactComponent`: the `n`-th divided-power component `Nₙ` of the coaction
  of an `R[x]`-comodule, and `TauCeti.AdditiveGroup.coactDecomposition` the family of all of them.
* `TauCeti.AdditiveGroup.coactFiltration`: the divided-power filtration of an `R[x]`-comodule.

## Main results

* `TauCeti.AdditiveGroup.coactComponent_coactComponent`: the divided-power components compose by
  the binomial rule `Nᵢ ∘ Nⱼ = (i + j choose i) Nᵢ₊ⱼ`.
* `TauCeti.AdditiveGroup.exists_coactFiltration_eq_top`: the filtration of a finitely generated
  comodule is exhausted at a finite stage.
* `TauCeti.AdditiveGroup.isNilpotent_endOfPoint_sub_one` and
  `TauCeti.AdditiveGroup.isUnipotentPoint`: **every point of `𝔾ₐ` is unipotent.**
* `TauCeti.AdditiveGroup.smoothUnipotentCommHopfAlgProperty_coordinateHopfAlgebra`: **`𝔾ₐ` over a
  field is a smooth unipotent affine group**, together with the geometric-point form
  `TauCeti.AdditiveGroup.geometricallyUnipotentPointsCommHopfAlgProperty_coordinateHopfAlgebra`.

## Implementation notes

The shape of the argument parallels the weight decomposition of a comodule over a monoid algebra
in `TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra`, which also expands a coaction along a basis
of the coalgebra using `TensorProduct.equivFinsuppOfBasisRight`. The two cannot share more than
that tool: there the basis consists of group-like elements, so the components are orthogonal
idempotents and the comodule splits, whereas here the generator is primitive, so the components
compose by the binomial rule and the comodule is only filtered.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.8.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §8.3.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the first worked example of Layer 5, "Unipotent groups", of the ReductiveGroups
roadmap: the smooth unipotence predicates defined in
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic` are shown to be non-vacuous, on the group out of
which the upper-triangular unipotent groups `Uₙ` and the root subgroups of a reductive group are
built.
-/

public section

open Module SymmetricAlgebra
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w

section MonomialBasis

variable (R : Type u) [CommRing R]

/-- Exponent vectors on a singleton are natural numbers. -/
private noncomputable def unitFinsuppEquivNat : (Unit →₀ ℕ) ≃ ℕ where
  toFun f := f ()
  invFun n := Finsupp.single () n
  left_inv f := by
    refine Finsupp.ext fun u => ?_
    cases u
    simp
  right_inv n := by simp

/-- **The monomials `xⁿ` in the coordinate `x = ι(1)` form a basis of the coordinate algebra
`R[x] = SymmetricAlgebra R R` of the additive group.** -/
noncomputable def monomialBasis : Basis ℕ R (SymmetricAlgebra R R) :=
  (Basis.symmetricAlgebra (Basis.singleton Unit R)).reindex unitFinsuppEquivNat

@[simp]
theorem monomialBasis_apply (n : ℕ) :
    monomialBasis R n = (ι R R 1 : SymmetricAlgebra R R) ^ n := by
  rw [monomialBasis, Basis.reindex_apply]
  change (Basis.symmetricAlgebra (Basis.singleton Unit R)) (Finsupp.single () n) = _
  rw [Basis.symmetricAlgebra, Basis.map_apply]
  simp only [MvPolynomial.coe_basisMonomials, AlgEquiv.toLinearEquiv_apply,
    ← MvPolynomial.X_pow_eq_monomial, map_pow, SymmetricAlgebra.equivMvPolynomial_symm_X,
    Basis.singleton_apply]

/-- The `n`-th coefficient functional of the coordinate algebra of `𝔾ₐ`: the coefficient of the
monomial `xⁿ`. -/
noncomputable def coeff (n : ℕ) : SymmetricAlgebra R R →ₗ[R] R :=
  (monomialBasis R).coord n

@[simp]
theorem coeff_pow (m n : ℕ) :
    coeff R n ((ι R R 1 : SymmetricAlgebra R R) ^ m) = if m = n then 1 else 0 := by
  rw [coeff, ← monomialBasis_apply R m, Basis.coord_apply, Basis.repr_self_apply]

/-- The coefficient of `x⁰` is the counit. -/
theorem coeff_zero_eq_counit :
    coeff R 0 = Coalgebra.counit (R := R) (A := SymmetricAlgebra R R) := by
  refine (monomialBasis R).ext fun n => ?_
  rw [monomialBasis_apply, coeff_pow]
  rw [show (Coalgebra.counit (R := R) ((ι R R 1 : SymmetricAlgebra R R) ^ n)) =
      Bialgebra.counitAlgHom R (SymmetricAlgebra R R) ((ι R R 1) ^ n) from rfl, map_pow]
  simp only [Bialgebra.counitAlgHom_apply, SymmetricAlgebra.counit_ι]
  cases n <;> simp

/-- **The binomial expansion of the comultiplication on monomials.** The coordinate `x` is
primitive, so `Δ(xⁿ) = ∑ₖ (n choose k) xᵏ ⊗ xⁿ⁻ᵏ`. -/
theorem comul_pow (n : ℕ) :
    Coalgebra.comul (R := R) ((ι R R 1 : SymmetricAlgebra R R) ^ n) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k) •
        (((ι R R 1 : SymmetricAlgebra R R) ^ k) ⊗ₜ[R]
          ((ι R R 1 : SymmetricAlgebra R R) ^ (n - k))) := by
  rw [show (Coalgebra.comul (R := R) ((ι R R 1 : SymmetricAlgebra R R) ^ n)) =
      Bialgebra.comulAlgHom R (SymmetricAlgebra R R) ((ι R R 1) ^ n) from rfl, map_pow]
  simp only [Bialgebra.comulAlgHom_apply, SymmetricAlgebra.comul_ι]
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, nsmul_eq_mul, mul_comm]

/-- The pairing of two coefficient functionals on a tensor square of the coordinate algebra. -/
noncomputable def coeffPair (i j : ℕ) :
    SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R →ₗ[R] R :=
  (TensorProduct.rid R R).toLinearMap ∘ₗ TensorProduct.map (coeff R i) (coeff R j)

@[simp]
theorem coeffPair_tmul (i j : ℕ) (a b : SymmetricAlgebra R R) :
    coeffPair R i j (a ⊗ₜ[R] b) = coeff R i a * coeff R j b := by
  simp [coeffPair, smul_eq_mul, mul_comm]

/-- **The coefficient functionals are a divided-power system.** Pairing the `i`-th and `j`-th
coefficients across the comultiplication returns `(i + j choose i)` times the `(i + j)`-th
coefficient. -/
theorem coeffPair_comp_comul (i j : ℕ) :
    coeffPair R i j ∘ₗ (Coalgebra.comul (R := R) (A := SymmetricAlgebra R R)) =
      ((i + j).choose i) • coeff R (i + j) := by
  refine (monomialBasis R).ext fun n => ?_
  rw [monomialBasis_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, coeff_pow,
    comul_pow, map_sum, map_nsmul, coeffPair_tmul, coeff_pow]
  rcases eq_or_ne n (i + j) with rfl | hn
  · rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hi
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_add_right i j))) hi
  · rw [ite_eq_right hn, smul_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rcases eq_or_ne k i with rfl | hki
    · have : n - k ≠ j := fun h => hn (by omega)
      simp [this]
    · simp [hki]

end MonomialBasis

section Component

variable (R : Type u) [CommRing R] (V : Type v) [AddCommMonoid V] [Module R V]

/-- The `n`-th coefficient map of `V ⊗[R] R[x]`, reading off the coefficient of the monomial
`xⁿ` in the second factor. -/
noncomputable def tensorComponent (n : ℕ) : V ⊗[R] SymmetricAlgebra R R →ₗ[R] V :=
  (TensorProduct.rid R V).toLinearMap ∘ₗ (coeff R n).lTensor V

@[simp]
theorem tensorComponent_tmul (n : ℕ) (v : V) (h : SymmetricAlgebra R R) :
    tensorComponent R V n (v ⊗ₜ[R] h) = coeff R n h • v := by
  simp [tensorComponent]

/-- The `(i, j)`-th coefficient map of `V ⊗[R] (R[x] ⊗[R] R[x])`. -/
noncomputable def tensorPairComponent (i j : ℕ) :
    V ⊗[R] (SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R) →ₗ[R] V :=
  (TensorProduct.rid R V).toLinearMap ∘ₗ (coeffPair R i j).lTensor V

@[simp]
theorem tensorPairComponent_tmul (i j : ℕ) (v : V)
    (h : SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R) :
    tensorPairComponent R V i j (v ⊗ₜ[R] h) = coeffPair R i j h • v := by
  simp [tensorPairComponent]

/-- Reading off a coefficient of a tensor is compatible with the associator. -/
theorem tensorComponent_comp_tensorComponent (i j : ℕ) :
    tensorComponent R V i ∘ₗ tensorComponent R (V ⊗[R] SymmetricAlgebra R R) j =
      tensorPairComponent R V i j ∘ₗ
        (TensorProduct.assoc R V (SymmetricAlgebra R R) (SymmetricAlgebra R R)).toLinearMap := by
  refine TensorProduct.ext' fun z h₂ => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v h₁ => simp [smul_smul, mul_comm]
  | add z w hz hw => simp only [TensorProduct.add_tmul, map_add, hz, hw]

/-- Pairing the `i`-th and `j`-th coefficients across the comultiplication picks out
`(i + j choose i)` times the `(i + j)`-th coefficient. -/
theorem tensorPairComponent_comp_lTensor_comul (i j : ℕ) :
    tensorPairComponent R V i j ∘ₗ
        (Coalgebra.comul (R := R) (A := SymmetricAlgebra R R)).lTensor V =
      ((i + j).choose i) • tensorComponent R V (i + j) := by
  refine TensorProduct.ext' fun v h => ?_
  have hc := congr($(coeffPair_comp_comul R i j) h)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply] at hc
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    tensorPairComponent_tmul, hc, LinearMap.smul_apply, tensorComponent_tmul,
    ← Nat.cast_smul_eq_nsmul R, smul_smul, smul_eq_mul]

end Component

section CoactComponent

variable (R : Type u) [CommRing R] (V : Type v) [AddCommMonoid V] [Module R V]
variable [Comodule R (SymmetricAlgebra R R) V]

/-- **The `n`-th divided-power component of the coaction** of a comodule over the coordinate
algebra of `𝔾ₐ`: writing the coaction as `ρ v = ∑ₙ Nₙ v ⊗ xⁿ`, this is `Nₙ`. -/
@[expose] noncomputable def coactComponent (n : ℕ) : V →ₗ[R] V :=
  tensorComponent R V n ∘ₗ Comodule.coact (R := R) (C := SymmetricAlgebra R R)

theorem coactComponent_apply (n : ℕ) (v : V) :
    coactComponent R V n v =
      tensorComponent R V n (Comodule.coact (R := R) (C := SymmetricAlgebra R R) v) :=
  rfl

/-- The zeroth divided-power component is the identity: this is the counit axiom. -/
@[simp]
theorem coactComponent_zero : coactComponent R V 0 = LinearMap.id := by
  ext v
  rw [coactComponent_apply, tensorComponent, LinearMap.coe_comp, Function.comp_apply,
    coeff_zero_eq_counit, Comodule.lTensor_counit_coact]
  simp

/-- Reading off a coefficient of the coaction commutes with the coaction itself. -/
theorem coact_comp_tensorComponent (n : ℕ) :
    Comodule.coact (R := R) (C := SymmetricAlgebra R R) ∘ₗ tensorComponent R V n =
      tensorComponent R (V ⊗[R] SymmetricAlgebra R R) n ∘ₗ
        (Comodule.coact (R := R) (C := SymmetricAlgebra R R) (M := V)).rTensor
          (SymmetricAlgebra R R) := by
  refine TensorProduct.ext' fun v h => ?_
  simp

/-- **The divided-power components compose by the binomial rule** `Nᵢ ∘ Nⱼ = (i + j choose i)
Nᵢ₊ⱼ`. This is coassociativity of the coaction, read off in the monomial basis. -/
theorem coactComponent_coactComponent (i j : ℕ) (v : V) :
    coactComponent R V i (coactComponent R V j v) =
      ((i + j).choose i) • coactComponent R V (i + j) v := by
  have hcoact := congr($(coact_comp_tensorComponent R V j)
    (Comodule.coact (R := R) (C := SymmetricAlgebra R R) v))
  simp only [LinearMap.coe_comp, Function.comp_apply] at hcoact
  have hpair := congr($(tensorComponent_comp_tensorComponent R V i j)
    ((Comodule.coact (R := R) (C := SymmetricAlgebra R R) (M := V)).rTensor (SymmetricAlgebra R R)
      (Comodule.coact (R := R) (C := SymmetricAlgebra R R) v)))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hpair
  have hfinal := congr($(tensorPairComponent_comp_lTensor_comul R V i j)
    (Comodule.coact (R := R) (C := SymmetricAlgebra R R) v))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply] at hfinal
  rw [coactComponent_apply, coactComponent_apply, hcoact, hpair,
    Comodule.coassoc_apply, hfinal, coactComponent_apply]

end CoactComponent

section Decomposition

variable (R : Type u) [CommRing R] (V : Type v) [AddCommMonoid V] [Module R V]

/-- Reading off the `n`-th coefficient of a tensor is the `n`-th coordinate of its expansion in
the monomial basis. -/
theorem equivFinsuppOfBasisRight_monomialBasis_apply (z : V ⊗[R] SymmetricAlgebra R R) (n : ℕ) :
    TensorProduct.equivFinsuppOfBasisRight (monomialBasis R) z n = tensorComponent R V n z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v h =>
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, tensorComponent_tmul, coeff,
      Basis.coord_apply]
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]

variable [Comodule R (SymmetricAlgebra R R) V]

/-- **The divided-power decomposition of the coaction**, as a finitely supported family: writing
`ρ v = ∑ₙ Nₙ v ⊗ xⁿ`, this collects the vectors `Nₙ v`, only finitely many of which are
nonzero. -/
noncomputable def coactDecomposition : V →ₗ[R] (ℕ →₀ V) :=
  (TensorProduct.equivFinsuppOfBasisRight (monomialBasis R)).toLinearMap ∘ₗ
    Comodule.coact (R := R) (C := SymmetricAlgebra R R)

@[simp]
theorem coactDecomposition_apply (v : V) (n : ℕ) :
    coactDecomposition R V v n = coactComponent R V n v :=
  equivFinsuppOfBasisRight_monomialBasis_apply R V _ n

/-- The coaction is recovered from its divided-power components: `ρ v = ∑ₙ Nₙ v ⊗ xⁿ`. -/
theorem coact_eq_sum (v : V) :
    Comodule.coact (R := R) (C := SymmetricAlgebra R R) v =
      (coactDecomposition R V v).sum fun i w =>
        w ⊗ₜ[R] ((ι R R 1 : SymmetricAlgebra R R) ^ i) := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight
    (monomialBasis R)).symm_apply_apply (Comodule.coact (R := R) (C := SymmetricAlgebra R R) v)]
  rw [show TensorProduct.equivFinsuppOfBasisRight (monomialBasis R)
      (Comodule.coact (R := R) (C := SymmetricAlgebra R R) v) = coactDecomposition R V v from rfl,
    TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  exact Finsupp.sum_congr fun i _ => by rw [monomialBasis_apply]

end Decomposition

section Filtration

variable (R : Type u) [CommRing R] (V : Type v) [AddCommMonoid V] [Module R V]
variable [Comodule R (SymmetricAlgebra R R) V]

/-- **The divided-power filtration of a `𝔾ₐ`-comodule**: the `p`-th step consists of the vectors
whose divided-power components above `p` all vanish. Equivalently, it is the preimage under the
coaction of `V ⊗ (R ⊕ Rx ⊕ ⋯ ⊕ Rxᵖ)`. -/
noncomputable def coactFiltration (p : ℕ) : Submodule R V :=
  ⨅ i ∈ Set.Ioi p, LinearMap.ker (coactComponent R V i)

variable {V}

theorem mem_coactFiltration {p : ℕ} {v : V} :
    v ∈ coactFiltration R V p ↔ ∀ i, p < i → coactComponent R V i v = 0 := by
  simp [coactFiltration]

variable (V)

/-- The filtration is monotone. -/
theorem coactFiltration_mono {p q : ℕ} (h : p ≤ q) :
    coactFiltration R V p ≤ coactFiltration R V q := fun _v hv =>
  (mem_coactFiltration R).2 fun i hi => (mem_coactFiltration R).1 hv i (lt_of_le_of_lt h hi)

/-- **The divided-power filtration of a finitely generated comodule is exhaustive.** Each vector
has only finitely many nonzero divided-power components, and finitely many generators bound them
all at once. -/
theorem exists_coactFiltration_eq_top [Module.Finite R V] :
    ∃ d : ℕ, coactFiltration R V d = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := V)
  refine ⟨s.sup fun v => (coactDecomposition R V v).support.sup id, ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro v hv
  rw [SetLike.mem_coe, mem_coactFiltration]
  intro i hi
  rw [← coactDecomposition_apply]
  refine Finsupp.notMem_support_iff.1 fun hmem => absurd (Finset.le_sup (f := id) hmem) ?_
  exact not_le.2 (lt_of_le_of_lt (Finset.le_sup (f := fun v =>
    (coactDecomposition R V v).support.sup id) hv) hi)

end Filtration

section Nilpotent

variable (R : Type u) [CommRing R] (V : Type v) [AddCommMonoid V] [Module R V]
variable [Comodule R (SymmetricAlgebra R R) V]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- **A point of `𝔾ₐ` acts through the divided-power components of the coaction.** A point with
parameter `g x` sends `a ⊗ v` to `∑ᵢ a (g x)ⁱ ⊗ Nᵢ v`. -/
theorem endOfPoint_tmul_eq_sum (g : SymmetricAlgebra R R →ₐ[R] A) (a : A) (v : V) :
    Comodule.endOfPoint V g (a ⊗ₜ[R] v) =
      (coactDecomposition R V v).sum fun i w =>
        (a * g (ι R R 1) ^ i) ⊗ₜ[R] w := by
  rw [Comodule.endOfPoint_tmul, coact_eq_sum, map_finsuppSum, map_finsuppSum, Finsupp.smul_sum]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_pow, TensorProduct.comm_tmul,
    TensorProduct.smul_tmul', smul_eq_mul]

/-- The action of a point, minus the identity, involves only the positive divided-power
components. -/
theorem endOfPoint_sub_one_tmul (g : SymmetricAlgebra R R →ₐ[R] A) (a : A) (v : V) :
    (Comodule.endOfPoint V g - 1) (a ⊗ₜ[R] v) =
      ∑ i ∈ (coactDecomposition R V v).support.erase 0,
        (a * g (ι R R 1) ^ i) ⊗ₜ[R] coactComponent R V i v := by
  have hsum : (coactDecomposition R V v).sum
      (fun i w => (a * g (ι R R 1) ^ i) ⊗ₜ[R] w) =
      ∑ i ∈ insert 0 (coactDecomposition R V v).support,
        (a * g (ι R R 1) ^ i) ⊗ₜ[R] coactDecomposition R V v i :=
    Finsupp.sum_of_support_subset _ (Finset.subset_insert _ _) _ fun i _ =>
      TensorProduct.tmul_zero _ _
  rw [LinearMap.sub_apply, Module.End.one_apply, endOfPoint_tmul_eq_sum, hsum,
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 _), Finset.erase_insert_eq_erase]
  simp only [coactDecomposition_apply, coactComponent_zero, LinearMap.id_coe, id_eq, pow_zero,
    mul_one, add_sub_cancel_left]

/-- The positive divided-power components lower the filtration by one step. -/
theorem coactComponent_mem_coactFiltration {p i : ℕ} (hi : 0 < i) {v : V}
    (hv : v ∈ coactFiltration R V (p + 1)) :
    coactComponent R V i v ∈ coactFiltration R V p := by
  rw [mem_coactFiltration]
  intro j hj
  rw [coactComponent_coactComponent, (mem_coactFiltration R).1 hv (j + i) (by omega), smul_zero]

/-- A point acts as the identity on the bottom step of the filtration. -/
theorem endOfPoint_sub_one_tmul_eq_zero (g : SymmetricAlgebra R R →ₐ[R] A) (a : A) {v : V}
    (hv : v ∈ coactFiltration R V 0) :
    (Comodule.endOfPoint V g - 1) (a ⊗ₜ[R] v) = 0 := by
  rw [endOfPoint_sub_one_tmul]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [(mem_coactFiltration R).1 hv i (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)),
    TensorProduct.tmul_zero]

/-- A point moves the base change of one step of the filtration into the base change of the
previous step. -/
theorem endOfPoint_sub_one_tmul_mem (g : SymmetricAlgebra R R →ₐ[R] A) (a : A) {p : ℕ} {v : V}
    (hv : v ∈ coactFiltration R V (p + 1)) :
    (Comodule.endOfPoint V g - 1) (a ⊗ₜ[R] v) ∈ (coactFiltration R V p).baseChange A := by
  rw [endOfPoint_sub_one_tmul]
  refine Submodule.sum_mem _ fun i hi => ?_
  exact Submodule.tmul_mem_baseChange_of_mem _
    (coactComponent_mem_coactFiltration R V (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)) hv)

/-- **The action of a point is unipotent on each step of the filtration**: on the base change of
the `p`-th step, the `(p + 1)`-st power of the action minus the identity vanishes. -/
theorem pow_endOfPoint_sub_one_apply_eq_zero (g : SymmetricAlgebra R R →ₐ[R] A) (p : ℕ)
    {z : A ⊗[R] V} (hz : z ∈ (coactFiltration R V p).baseChange A) :
    ((Comodule.endOfPoint V g - 1) ^ (p + 1)) z = 0 := by
  induction p generalizing z with
  | zero =>
    have h : (coactFiltration R V 0).baseChange A ≤
        LinearMap.ker (Comodule.endOfPoint V g - 1) := by
      rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact endOfPoint_sub_one_tmul_eq_zero R V g 1 hv
    rw [pow_one]
    exact h hz
  | succ p ih =>
    have h : (coactFiltration R V (p + 1)).baseChange A ≤
        Submodule.comap (Comodule.endOfPoint V g - 1)
          ((coactFiltration R V p).baseChange A) := by
      rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact endOfPoint_sub_one_tmul_mem R V g 1 hv
    rw [pow_succ, Module.End.mul_apply]
    exact ih (h hz)

/-- **Every point of `𝔾ₐ` acts unipotently on every finitely generated comodule.** -/
theorem isNilpotent_endOfPoint_sub_one [Module.Finite R V]
    (g : SymmetricAlgebra R R →ₐ[R] A) :
    IsNilpotent (Comodule.endOfPoint V g - 1) := by
  obtain ⟨d, hd⟩ := exists_coactFiltration_eq_top R V
  refine ⟨d + 1, LinearMap.ext fun z => ?_⟩
  rw [LinearMap.zero_apply]
  refine pow_endOfPoint_sub_one_apply_eq_zero R V g d ?_
  rw [hd, Submodule.baseChange_top]
  trivial

end Nilpotent

section AffineGroup

variable (R : Type u) [CommRing R]

/-- The coordinate algebra of `𝔾ₐ` is of finite type: it is the polynomial algebra on the single
generator `x`. -/
instance instFiniteTypeSymmetricAlgebra : Algebra.FiniteType R (SymmetricAlgebra R R) :=
  Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType R (MvPolynomial Unit R)))
    (SymmetricAlgebra.equivMvPolynomial (Basis.singleton Unit R)).symm

/-- The coordinate algebra of `𝔾ₐ` is smooth: it is the polynomial algebra on the single
generator `x`. -/
instance instSmoothSymmetricAlgebra : Algebra.Smooth R (SymmetricAlgebra R R) :=
  letI : Algebra.Smooth R (MvPolynomial Unit R) := ⟨inferInstance, inferInstance⟩
  Algebra.Smooth.of_equiv
    (SymmetricAlgebra.equivMvPolynomial (Basis.singleton Unit R)).symm

/-- **Every point of the additive group is unipotent.** A point of `𝔾ₐ` valued in a commutative
`R`-algebra acts on every finitely generated comodule, over a field on every finite-dimensional
representation, by a unipotent automorphism. -/
theorem isUnipotentPoint {A : Type w} [CommRing A] [Algebra R A]
    (g : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    HopfAlgebra.IsUnipotentPoint g := by
  rw [HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  exact fun M => isNilpotent_endOfPoint_sub_one R M g.ofConv

/-- **The additive group has only unipotent geometric points.** -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallyUnipotentPointsCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
  exact fun g => isUnipotentPoint k g

/-- **The additive group `𝔾ₐ` is a smooth unipotent affine group.** This is the basic worked
example of the Layer 5 definition, and the one from which the unipotent upper-triangular groups
are built. -/
theorem smoothUnipotentCommHopfAlgProperty_coordinateHopfAlgebra (k : Type u) [Field k] :
    smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (SymmetricAlgebra k k)) := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  exact ⟨inferInstance, fun g => isUnipotentPoint k g⟩

end AffineGroup

end AdditiveGroup

end TauCeti
