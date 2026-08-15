/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction

/-!
# Root subgroup actions on base changes of Kostant-stable additive subgroups

Let `L` be a Lie algebra over `ℚ`, and let `U_ℤ = kostantForm e h` be the Kostant integral form in
`UniversalEnvelopingAlgebra ℚ L`. When a representation `ρ` preserves an additive subgroup
`M ≤ V`, every divided power of `ρ(eᵢ)` also preserves `M`.

Combining this with the generic base-change exponential from
`TauCeti/RingTheory/Nilpotent/BaseChangeAction.lean`, we obtain the additive one-parameter
action of an arbitrary commutative ring `R` on `R ⊗[ℤ] M` attached to each root vector `eᵢ`.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.dividedPower_apply_mem_of_kostantForm_apply_mem`: divided
  powers of root vectors preserve any Kostant-stable additive subgroup.
* `TauCeti.UniversalEnvelopingAlgebra.baseChangeKostantExpHom`: the root-vector one-parameter
  subgroup on an arbitrary base change of a Kostant-stable additive subgroup.
* `TauCeti.UniversalEnvelopingAlgebra.baseChangeKostantExpHom_toLinearMap`: its underlying linear
  map is the base-changed exponential.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

namespace TauCeti

open Finset IsNilpotent TensorProduct

namespace UniversalEnvelopingAlgebra

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {R : Type v} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}

/-- Every designated root vector's divided powers preserve an additive subgroup stable under the
whole Kostant form. -/
theorem dividedPower_apply_mem_of_kostantForm_apply_mem (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) {M : AddSubgroup V}
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) (i : ι) (n : ℕ)
    {v : V} (hv : v ∈ M) :
    Associative.dividedPower n
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) v ∈ M := by
  rw [← Associative.map_dividedPower ρ n]
  exact hM _ (dividedPower_mem_kostantForm e h i n) v hv

/-- The root-vector one-parameter subgroup on an arbitrary base change of a Kostant-stable
additive subgroup.

For each commutative ring `R`, the parameter `t : R` acts on `R ⊗[ℤ] M` through the integral
divided-power polynomial of `ρ(eᵢ)`. This is the ring-valued action that underlies the root
subgroup map attached to `eᵢ` in the Chevalley--Demazure construction. -/
noncomputable def baseChangeKostantExpHom (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) (i : ι)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))) :
    Multiplicative R →* (R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M) :=
  baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv) hnil

/-- The underlying linear map of the base-changed Kostant root subgroup is the integral
divided-power exponential. -/
@[simp]
theorem baseChangeKostantExpHom_toLinearMap (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) (i : ι)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (t : Multiplicative R) :
    (baseChangeKostantExpHom e h ρ M hM i hnil t).toLinearMap =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
        (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv) hnil
        (Multiplicative.toAdd t) :=
  baseChangeExpHom_toLinearMap _ _ _ _ _

end UniversalEnvelopingAlgebra

end TauCeti
