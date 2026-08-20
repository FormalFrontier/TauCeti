/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.CartanDualBasis
public import TauCeti.Algebra.Lie.Killing.DualBasis
public import TauCeti.Algebra.Lie.Weights.Sl2System

/-!
# A basis adapted to the root space decomposition, and its Killing-dual basis

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero and let `H` be a splitting Cartan subalgebra. The root space decomposition
`L = H ⊕ ⨁_{α ∈ Φ} Lα` turns a basis `bH` of `H` and a normalised family `x` of root vectors
(`TauCeti.IsSl2System`) into a basis of `L` indexed by `ιH ⊕ H.root`. This file builds that basis
together with a candidate for its Killing-dual family, which is dual when `x` satisfies
`TauCeti.IsSl2System`: the Cartan part is dual inside `H`, and the vector paired with `x α` is a
multiple of `x (-α)`.

Everything rests on one biorthogonality computation
(`TauCeti.IsSl2System.killingForm_cartanRootFamily_cartanRootDualFamily_self` and its companion
for distinct indices): the root space orthogonality `κ(Lα, Lβ) = 0` for `α + β ≠ 0`, together with
the non-vanishing of `κ(x α, x (-α))`. Biorthogonality already forces the two families to be dual
bases, through `Module.DualBases`, so no separate linear independence argument is needed; only the
spanning of the dual family has to be checked, and that is the root space decomposition again.

The point of the construction is that the Casimir element `∑ᵢ xᵢ yᵢ` of
`TauCeti/Algebra/Lie/UniversalEnveloping/Casimir.lean` may be evaluated against *any* basis
(`TauCeti.casimirElement_eq_sum`); against this one the sum splits into a Cartan part and one term
for each root, which is what computes the Casimir scalar of a highest weight vector.

## Main definitions

* `TauCeti.cartanRootFamily`: a basis of `H` followed by the root vectors `x α`.
* `TauCeti.cartanRootDualFamily`: the candidate dual family, whose value at the root `α` is
  `κ(x α, x (-α))⁻¹ • x (-α)`; it is dual when `x` satisfies `TauCeti.IsSl2System`.
* `TauCeti.IsSl2System.cartanRootBasis`: the first family, as a basis of `L`.

## Main results

* `TauCeti.IsSl2System.killingForm_cartanRootFamily_cartanRootDualFamily_self` and
  `TauCeti.IsSl2System.killingForm_cartanRootFamily_cartanRootDualFamily_of_ne`: the two families
  are biorthogonal for the Killing form.
* `TauCeti.IsSl2System.coe_cartanRootBasis` and
  `TauCeti.IsSl2System.coe_killingDualBasis_cartanRootBasis`: the basis is the first family and its
  Killing-dual basis is the second.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §8.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L}

/-! ### Recognising a vector by its Killing pairings -/

/-- A vector paired to zero by the Killing form against a spanning set is zero. -/
private theorem eq_zero_of_forall_mem_killingForm_eq_zero [IsKilling K L] {S : Set L}
    (hS : Submodule.span K S = ⊤) {z : L} (h : ∀ w ∈ S, killingForm K L w z = 0) : z = 0 := by
  have hflip : (killingForm K L).flip z = 0 :=
    LinearMap.ext_on hS fun w hw ↦ by simpa using h w hw
  have hker : killingForm K L z = 0 := by
    ext w
    simpa [LieModule.traceForm_comm K L L z w] using LinearMap.congr_fun hflip w
  have hmem : z ∈ LinearMap.ker (killingForm K L) := LinearMap.mem_ker.mpr hker
  rwa [ker_killingForm_eq_bot, Submodule.mem_bot] at hmem

variable [IsKilling K L] [FiniteDimensional K L] [H.IsCartanSubalgebra]
  {ιH : Type w} [Finite ιH] [DecidableEq ιH]

/-! ### The adapted families -/

variable [CharZero K] [IsTriangularizable K H L]

variable (bH : Basis ιH K H) (x : Weight K H L → L)

/-- The family of vectors of `L` indexed by `ιH ⊕ H.root` given by a basis of the Cartan
subalgebra together with a family of root vectors. -/
noncomputable def cartanRootFamily : ιH ⊕ H.root → L :=
  Sum.elim (fun i ↦ (bH i : L)) fun α ↦ x α

/-- The candidate family dual to `TauCeti.cartanRootFamily` under the Killing form: the Cartan
part is `TauCeti.cartanKillingDualBasis`, and the candidate dual to the root vector `x α` is the
normalised opposite root vector `κ(x α, x (-α))⁻¹ • x (-α)`. It is dual when `x` satisfies
`TauCeti.IsSl2System`. -/
noncomputable def cartanRootDualFamily : ιH ⊕ H.root → L :=
  Sum.elim (fun i ↦ (cartanKillingDualBasis bH i : L))
    fun α ↦ (killingForm K L (x (α : Weight K H L)) (x (-(α : Weight K H L))))⁻¹ •
      x (-(α : Weight K H L))

omit [IsKilling K L] [Finite ιH] [DecidableEq ιH] [CharZero K] [IsTriangularizable K H L] in
/-- On the Cartan block, the adapted family is the chosen basis of `H`. -/
@[simp]
theorem cartanRootFamily_inl (i : ιH) : cartanRootFamily bH x (Sum.inl i) = (bH i : L) := (rfl)

omit [IsKilling K L] [Finite ιH] [DecidableEq ιH] [CharZero K] [IsTriangularizable K H L] in
/-- On the root block, the adapted family is the given family of root vectors. -/
@[simp]
theorem cartanRootFamily_inr (α : H.root) :
    cartanRootFamily bH x (Sum.inr α) = x (α : Weight K H L) := (rfl)

omit [CharZero K] in
/-- On the Cartan block, the dual family is the Killing-dual basis of `H`. -/
@[simp]
theorem cartanRootDualFamily_inl (i : ιH) :
    cartanRootDualFamily bH x (Sum.inl i) = (cartanKillingDualBasis bH i : L) := (rfl)

omit [CharZero K] in
/-- On the root block, the dual family is the normalised opposite root vector. -/
@[simp]
theorem cartanRootDualFamily_inr (α : H.root) :
    cartanRootDualFamily bH x (Sum.inr α) =
      (killingForm K L (x (α : Weight K H L)) (x (-(α : Weight K H L))))⁻¹ •
        x (-(α : Weight K H L)) := (rfl)

namespace IsSl2System

variable {x} (hx : IsSl2System x)

include hx

/-- The Killing form pairs each member of the adapted family with its own dual to `1`. -/
theorem killingForm_cartanRootFamily_cartanRootDualFamily_self (i : ιH ⊕ H.root) :
    killingForm K L (cartanRootFamily bH x i) (cartanRootDualFamily bH x i) = 1 := by
  rcases i with i | α
  · rw [cartanRootFamily_inl, cartanRootDualFamily_inl, killingForm_cartanKillingDualBasis]
    simp
  · rw [cartanRootFamily_inr, cartanRootDualFamily_inr, map_smul, smul_eq_mul,
      inv_mul_cancel₀
        (hx.killingForm_root_neg_ne_zero (α : Weight K H L)
          (LieSubalgebra.isNonZero_coe_root α))]

omit [CharZero K] in
/-- **The two adapted families are biorthogonal for the Killing form.** The mixed Cartan-root
blocks vanish because `H` is the zero root space, and a root block vanishes unless the two roots
agree, root spaces at `α` and `β` being Killing-orthogonal unless `α + β = 0`. -/
theorem killingForm_cartanRootFamily_cartanRootDualFamily_of_ne {i j : ιH ⊕ H.root}
    (hij : i ≠ j) :
    killingForm K L (cartanRootFamily bH x i) (cartanRootDualFamily bH x j) = 0 := by
  have hzero : ∀ u : H, (u : L) ∈ rootSpace H (0 : H → K) := fun u ↦ by
    rw [rootSpace_zero_eq K L H, LieSubalgebra.mem_toLieSubmodule]
    exact u.2
  rcases i with i | α <;> rcases j with j | β
  · have hne : i ≠ j := fun h ↦ hij (by rw [h])
    rw [cartanRootFamily_inl, cartanRootDualFamily_inl, killingForm_cartanKillingDualBasis]
    simp [hne]
  · have hne : (0 : H → K) + ((-(β : Weight K H L) : Weight K H L) : H → K) ≠ 0 := by
      rw [Weight.coe_neg, zero_add, ne_eq, neg_eq_zero]
      exact LieSubalgebra.isNonZero_coe_root β
    have h0 : killingForm K L (bH i : L) (x (-(β : Weight K H L))) = 0 :=
      killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H (hzero (bH i))
        (hx.mem_rootSpace _) hne
    rw [cartanRootFamily_inl, cartanRootDualFamily_inr, map_smul, h0, smul_zero]
  · have hne : ((α : Weight K H L) : H → K) + (0 : H → K) ≠ 0 := by
      rw [add_zero]
      exact LieSubalgebra.isNonZero_coe_root α
    rw [cartanRootFamily_inr, cartanRootDualFamily_inl]
    exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H (hx.mem_rootSpace _)
      (hzero (cartanKillingDualBasis bH j)) hne
  · have hαβ : α ≠ β := fun h ↦ hij (by rw [h])
    have hne : ((α : Weight K H L) : H → K) +
        ((-(β : Weight K H L) : Weight K H L) : H → K) ≠ 0 := by
      rw [Weight.coe_neg, ← sub_eq_add_neg, sub_ne_zero]
      exact fun h ↦ hαβ (Subtype.ext (Weight.ext fun z ↦ congrFun h z))
    have h0 : killingForm K L (x (α : Weight K H L)) (x (-(β : Weight K H L))) = 0 :=
      killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H (hx.mem_rootSpace _)
        (hx.mem_rootSpace _) hne
    rw [cartanRootFamily_inr, cartanRootDualFamily_inr, map_smul, h0, smul_zero]

/-- **The dual family spans `L`**: the root space decomposition again, the Cartan part being
spanned by a basis of `H` and each root space by the opposite normalised root vector. -/
private theorem span_range_cartanRootDualFamily_eq_top :
    Submodule.span K (Set.range (cartanRootDualFamily bH x)) = ⊤ := by
  set S := Submodule.span K (Set.range (cartanRootDualFamily bH x)) with hS
  have hcartan : (H : Submodule K L) ≤ S := by
    have hspan : (H : Submodule K L) =
        Submodule.span K (Set.range fun i ↦ ((cartanKillingDualBasis bH i : H) : L)) := by
      conv_lhs => rw [← Submodule.map_subtype_top (H : Submodule K L),
        ← (cartanKillingDualBasis bH).span_eq]
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  rw [← top_le_iff, ← hx.span_range_sup_toSubmodule_eq_top]
  refine sup_le (Submodule.span_le.mpr ?_) hcartan
  rintro _ ⟨χ, rfl⟩
  by_cases hχ : χ.IsNonZero
  · have hmem : (-χ) ∈ H.root := by simpa [LieSubalgebra.root] using hχ.neg
    have hmemS : cartanRootDualFamily bH x (Sum.inr ⟨-χ, hmem⟩) ∈ S :=
      Submodule.subset_span ⟨_, rfl⟩
    rw [cartanRootDualFamily_inr] at hmemS
    simp only [neg_neg] at hmemS
    have hne := hx.killingForm_root_neg_ne_zero (-χ) hχ.neg
    have hx0 : x χ ∈ S := by
      have hmul := S.smul_mem (killingForm K L (x (-χ)) (x χ)) hmemS
      rwa [smul_smul, mul_inv_cancel₀ (by simpa using hne), one_smul] at hmul
    exact hx0
  · rw [hx.eq_zero_of_isZero χ (not_not.mp hχ)]
    exact S.zero_mem

/-- The two adapted families are a pair of dual bases for the Killing form. -/
private theorem dualBases_cartanRootFamily :
    Module.DualBases (cartanRootFamily bH x)
      fun i ↦ killingForm K L (cartanRootDualFamily bH x i) where
  eval_same i :=
    (LieModule.traceForm_comm K L L _ _).trans
      (hx.killingForm_cartanRootFamily_cartanRootDualFamily_self bH i)
  eval_of_ne i j hij :=
    (LieModule.traceForm_comm K L L _ _).trans
      (hx.killingForm_cartanRootFamily_cartanRootDualFamily_of_ne bH (Ne.symm hij))
  total {z₁ z₂} h := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mem_killingForm_eq_zero
      (hx.span_range_cartanRootDualFamily_eq_top bH) ?_
    rintro _ ⟨i, rfl⟩
    rw [map_sub, sub_eq_zero]
    exact h i

/-- **The basis of `L` adapted to the root space decomposition**: a basis of the Cartan subalgebra
followed by the root vectors of a normalised family. -/
noncomputable def cartanRootBasis : Basis (ιH ⊕ H.root) K L :=
  (hx.dualBases_cartanRootFamily bH).basis

/-- **The adapted basis is the adapted family**: coercing
`TauCeti.IsSl2System.cartanRootBasis` back to a family of vectors of `L` returns
`TauCeti.cartanRootFamily`, the basis of `H` followed by the root vectors. -/
@[simp]
theorem coe_cartanRootBasis : ⇑(hx.cartanRootBasis bH) = cartanRootFamily bH x :=
  (hx.dualBases_cartanRootFamily bH).coe_basis

/-- **The Killing-dual basis of the adapted basis is the dual family.** Both are characterised by
biorthogonality against the adapted basis, and the Killing form is non-degenerate. -/
@[simp]
theorem coe_killingDualBasis_cartanRootBasis [DecidableEq H.root] :
    ⇑(killingDualBasis (hx.cartanRootBasis bH)) = cartanRootDualFamily bH x := by
  classical
  apply (LinearMap.BilinForm.dualBasis_eq_iff
    (LieAlgebra.IsKilling.killingForm_nondegenerate K L) _ _).mpr
  intro i j
  rw [LieModule.traceForm_comm K L L, hx.coe_cartanRootBasis]
  rcases eq_or_ne j i with rfl | hji
  · rw [hx.killingForm_cartanRootFamily_cartanRootDualFamily_self bH]
    simp
  · rw [hx.killingForm_cartanRootFamily_cartanRootDualFamily_of_ne bH hji]
    simp [hji]

end IsSl2System

end TauCeti
