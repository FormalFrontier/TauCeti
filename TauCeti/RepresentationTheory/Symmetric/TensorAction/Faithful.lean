/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic

/-!
# How faithfully the symmetric group acts on a tensor power

The symmetric group `S_d` acts on `(Rⁿ)^{⊗d}` by permuting tensor factors, and that action
extends to an algebra map `R[S_d] → End((Rⁿ)^{⊗d})`.  This file measures how much of `R[S_d]`
survives: the algebra map is injective **exactly** when `d ≤ n`.

Above the threshold the tensor power is too small to separate permutations linearly.  For `n < d`
every monomial basis vector of `(Rⁿ)^{⊗d}` repeats one of its factors, so the full antisymmetrizer
`∑_σ sgn(σ) σ` is a nonzero element of `R[S_d]` acting as `0`.  This is why Schur--Weyl duality is
stated for the *image* of `R[S_d]` in `End((Rⁿ)^{⊗d})` rather than for `R[S_d]` itself.

The group-level question has a different, coarser answer, recorded here as well: the permutation
representation itself is faithful as soon as `Rⁿ` has two independent coordinate directions with
which to tell tensor slots apart, that is, exactly when `2 ≤ n` or `d ≤ 1`.

Both answers are read off the monomial basis `tensorPowerBasis` of `(Rⁿ)^{⊗d}`, indexed by the
functions `Fin d → Fin n`, on which a permutation acts by precomposition with its inverse.

## Main definitions

* `TauCeti.tensorPowerBasis` is the monomial basis of `(Rⁿ)^{⊗d}`.

## Main results

* `TauCeti.permTensorAction_tensorPowerBasis`: a permutation acts on the monomial basis by
  precomposition with its inverse.
* `TauCeti.permTensorActionAlgHom_injective_iff`: the algebra map `R[S_d] → End((Rⁿ)^{⊗d})` is
  injective if and only if `d ≤ n`.
* `TauCeti.permTensorAction_injective_iff`: the permutation representation itself is faithful if
  and only if `2 ≤ n` or `d ≤ 1`.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8, “The double centralizer (image-level)”: the faithfulness refinement recording that the
  symmetric-group image is faithful once the dimension is at least the tensor degree, and that the
  group algebra maps on as a proper quotient otherwise.
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti

variable (R : Type u) (n d : ℕ) [CommRing R]

/-- The monomial basis of `(Rⁿ)^{⊗d}`: the basis vector at `f : Fin d → Fin n` is the pure tensor
whose `i`-th factor is the `f i`-th standard basis vector of `Rⁿ`. -/
noncomputable def tensorPowerBasis :
    Module.Basis (Fin d → Fin n) R (⨂[R] _ : Fin d, Fin n → R) :=
  Basis.piTensorProduct fun _ => Pi.basisFun R (Fin n)

@[simp]
theorem tensorPowerBasis_apply (f : Fin d → Fin n) :
    tensorPowerBasis R n d f = PiTensorProduct.tprod R fun i => Pi.single (f i) (1 : R) := by
  classical
  rw [tensorPowerBasis, Basis.piTensorProduct_apply]
  simp

/-- A permutation acts on the monomial basis of `(Rⁿ)^{⊗d}` by precomposing the index function
with its inverse. -/
theorem permTensorAction_tensorPowerBasis (σ : Equiv.Perm (Fin d)) (f : Fin d → Fin n) :
    permTensorAction R n d σ (tensorPowerBasis R n d f) =
      tensorPowerBasis R n d fun i => f (σ.symm i) := by
  simp

/-- A group-algebra basis element acts on a monomial basis vector by precomposition and
scaling. -/
theorem permTensorActionAlgHom_single_tensorPowerBasis (ρ : Equiv.Perm (Fin d)) (r : R)
    (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d (MonoidAlgebra.single ρ r) (tensorPowerBasis R n d f) =
      r • tensorPowerBasis R n d fun i => f (ρ.symm i) := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_single, LinearMap.smul_apply,
    permTensorAction_tensorPowerBasis]

/-- The group-algebra action on a monomial basis vector is the coefficient-weighted sum of the
precomposed monomial basis vectors. -/
theorem permTensorActionAlgHom_apply_tensorPowerBasis
    (a : MonoidAlgebra R (Equiv.Perm (Fin d))) (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d a (tensorPowerBasis R n d f) =
      ∑ σ ∈ a.coeff.support,
        a.coeff σ • tensorPowerBasis R n d fun i => f (σ.symm i) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single a]
  rw [Finsupp.sum, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun σ _ =>
    permTensorActionAlgHom_single_tensorPowerBasis R n d σ (a.coeff σ) f

variable {R n d}

/-- Precomposing an injective function with the inverses of the permutations of its domain
separates those permutations. -/
theorem injective_comp_perm_symm {ι κ : Type*} {f : ι → κ} (hf : Function.Injective f) :
    Function.Injective fun σ : Equiv.Perm ι => fun i => f (σ.symm i) := by
  intro σ τ h
  have hsymm : σ.symm = τ.symm := Equiv.ext fun i => hf (congrFun h i)
  simpa using congrArg Equiv.symm hsymm

/-- An injective index function makes the monomial basis read the coefficients of a group-algebra
element off the image of its basis vector: this is the mechanism behind faithfulness. -/
theorem repr_permTensorActionAlgHom_apply_tensorPowerBasis
    (a : MonoidAlgebra R (Equiv.Perm (Fin d))) {f : Fin d → Fin n} (hf : Function.Injective f)
    (ρ : Equiv.Perm (Fin d)) :
    (tensorPowerBasis R n d).repr
        (permTensorActionAlgHom R n d a (tensorPowerBasis R n d f))
        (fun i => f (ρ.symm i)) = a.coeff ρ := by
  classical
  rw [permTensorActionAlgHom_apply_tensorPowerBasis, map_sum, Finset.sum_apply']
  have hterm : ∀ σ ∈ a.coeff.support,
      ((tensorPowerBasis R n d).repr
          (a.coeff σ • tensorPowerBasis R n d fun i => f (σ.symm i))) (fun i => f (ρ.symm i)) =
        if σ = ρ then a.coeff σ else 0 := by
    intro σ _
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]
    exact if_congr ⟨fun hc => injective_comp_perm_symm hf hc, fun hc => by rw [hc]⟩ rfl rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' a.coeff.support ρ]
  by_cases hρ : ρ ∈ a.coeff.support
  · rw [if_pos hρ]
  · rw [if_neg hρ, Finsupp.notMem_support_iff.mp hρ]

/-- **Faithfulness of the symmetric-group image.**  If the tensor degree does not exceed the
dimension, the algebra map `R[S_d] → End((Rⁿ)^{⊗d})` is injective. -/
theorem permTensorActionAlgHom_injective_of_le (h : d ≤ n) :
    Function.Injective (permTensorActionAlgHom R n d) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
  rw [← MonoidAlgebra.coeff_inj, MonoidAlgebra.coeff_zero]
  ext ρ
  rw [← repr_permTensorActionAlgHom_apply_tensorPowerBasis a (Fin.castLE_injective h) ρ, ha]
  simp

/-- **The antisymmetrizer dies below the threshold.**  If the dimension is smaller than the tensor
degree, then every monomial basis vector of `(Rⁿ)^{⊗d}` repeats a factor, and the full
antisymmetrizer `∑_σ sgn(σ) σ` annihilates the whole tensor power. -/
theorem permTensorActionAlgHom_sum_sign_eq_zero (h : n < d) :
    permTensorActionAlgHom R n d
        (∑ σ : Equiv.Perm (Fin d), MonoidAlgebra.single σ ((Equiv.Perm.sign σ : ℤ) : R)) = 0 := by
  classical
  refine (tensorPowerBasis R n d).ext fun f => ?_
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using h)
  set τ : Equiv.Perm (Fin d) := Equiv.swap i j with hτ
  have hsign : Equiv.Perm.sign τ = -1 := by rw [hτ, Equiv.Perm.sign_swap hij]
  have hτ_ne_one : τ ≠ 1 := by
    intro hc
    rw [hc, map_one] at hsign
    exact absurd hsign (by decide)
  have hτ_sq : τ * τ = 1 := by rw [hτ, Equiv.swap_mul_self]
  have hfτ : ∀ x, f (τ x) = f x := by
    intro x
    rcases eq_or_ne x i with rfl | hxi
    · rw [hτ, Equiv.swap_apply_left, hfij]
    rcases eq_or_ne x j with rfl | hxj
    · rw [hτ, Equiv.swap_apply_right, hfij]
    · rw [hτ, Equiv.swap_apply_of_ne_of_ne hxi hxj]
  rw [map_sum, LinearMap.sum_apply, LinearMap.zero_apply]
  refine Finset.sum_ninvolution (fun σ => σ * τ) (fun σ => ?_) (fun σ _ hc => ?_)
    (fun _ => Finset.mem_univ _) (fun σ => by rw [mul_assoc, hτ_sq, mul_one])
  · have hcomp : (fun x => f ((σ * τ).symm x)) = fun x => f (σ.symm x) := by
      funext x
      have hmul : (σ * τ).symm x = τ.symm (σ.symm x) := rfl
      rw [hmul, hτ, Equiv.symm_swap, ← hτ, hfτ]
    have hscalar : (((Equiv.Perm.sign (σ * τ) : ℤ)) : R) = -(((Equiv.Perm.sign σ : ℤ)) : R) := by
      rw [Equiv.Perm.sign_mul, hsign]
      simp
    rw [permTensorActionAlgHom_single_tensorPowerBasis,
      permTensorActionAlgHom_single_tensorPowerBasis, hcomp, hscalar, ← add_smul, add_neg_cancel,
      zero_smul]
  · exact hτ_ne_one (mul_eq_left.mp hc)

/-- **Non-faithfulness above the threshold.**  If the dimension is smaller than the tensor degree,
the algebra map `R[S_d] → End((Rⁿ)^{⊗d})` has a nonzero kernel, so the symmetric-group image is a
proper quotient of the group algebra. -/
theorem permTensorActionAlgHom_not_injective_of_lt [Nontrivial R] (h : n < d) :
    ¬Function.Injective (permTensorActionAlgHom R n d) := by
  classical
  intro hinj
  have hzero : (∑ σ : Equiv.Perm (Fin d), MonoidAlgebra.single σ ((Equiv.Perm.sign σ : ℤ) : R))
      = 0 := by
    refine hinj ?_
    rw [permTensorActionAlgHom_sum_sign_eq_zero h, map_zero]
  have hone := congrArg (fun x : MonoidAlgebra R (Equiv.Perm (Fin d)) => x.coeff 1) hzero
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply] at hone

/-- **The faithfulness threshold.**  The algebra map `R[S_d] → End((Rⁿ)^{⊗d})` is injective
exactly when the tensor degree does not exceed the dimension. -/
theorem permTensorActionAlgHom_injective_iff [Nontrivial R] :
    Function.Injective (permTensorActionAlgHom R n d) ↔ d ≤ n :=
  ⟨fun hinj => not_lt.mp fun h => permTensorActionAlgHom_not_injective_of_lt h hinj,
    permTensorActionAlgHom_injective_of_le⟩

/-- With at most one coordinate direction the tensor slots cannot be told apart, and the
permutation action on `(Rⁿ)^{⊗d}` is trivial. -/
theorem permTensorAction_eq_one_of_le_one (h : n ≤ 1) (σ : Equiv.Perm (Fin d)) :
    permTensorAction R n d σ = 1 := by
  haveI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr h
  refine (tensorPowerBasis R n d).ext fun f => ?_
  rw [permTensorAction_tensorPowerBasis, Module.End.one_apply]
  exact congrArg _ (funext fun i => Subsingleton.elim _ _)

/-- With at least two coordinate directions the permutation action on `(Rⁿ)^{⊗d}` is faithful:
the monomial basis vector marking a single tensor slot already detects the permutation. -/
theorem permTensorAction_injective_of_two_le [Nontrivial R] (h : 2 ≤ n) :
    Function.Injective (permTensorAction R n d) := by
  classical
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr h
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Fin n)
  intro σ τ hστ
  have hsymm : σ.symm = τ.symm := by
    refine Equiv.ext fun x => ?_
    have himg : permTensorAction R n d σ
          (tensorPowerBasis R n d fun y => if y = σ.symm x then a else b) =
        permTensorAction R n d τ
          (tensorPowerBasis R n d fun y => if y = σ.symm x then a else b) := by
      rw [hστ]
    rw [permTensorAction_tensorPowerBasis, permTensorAction_tensorPowerBasis] at himg
    have hfun := congrFun ((tensorPowerBasis R n d).injective himg) x
    rw [if_pos rfl] at hfun
    by_contra hne
    rw [if_neg fun hc => hne hc.symm] at hfun
    exact hab hfun
  simpa using congrArg Equiv.symm hsymm

/-- **When the permutation representation itself is faithful.**  Unlike the group-algebra image,
the representation of `S_d` on `(Rⁿ)^{⊗d}` is faithful for every tensor degree once `2 ≤ n`; it
fails only when the dimension collapses the action while there is more than one slot to permute. -/
theorem permTensorAction_injective_iff [Nontrivial R] :
    Function.Injective (permTensorAction R n d) ↔ 2 ≤ n ∨ d ≤ 1 := by
  refine ⟨fun hinj => ?_, ?_⟩
  · rcases le_or_gt 2 n with h2 | h2
    · exact Or.inl h2
    refine Or.inr ?_
    by_contra hd
    haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Fin d)
    have hswap : Equiv.swap a b = 1 :=
      hinj (by rw [permTensorAction_eq_one_of_le_one (by omega), map_one])
    rw [Equiv.Perm.one_def, Equiv.swap_eq_refl_iff] at hswap
    exact hab hswap
  · rintro (h | h)
    · exact permTensorAction_injective_of_two_le h
    · haveI : Subsingleton (Fin d) := Fin.subsingleton_iff_le_one.mpr h
      exact fun σ τ _ => Equiv.ext fun x => Subsingleton.elim _ _

end TauCeti
