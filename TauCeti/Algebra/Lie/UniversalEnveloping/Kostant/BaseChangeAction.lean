/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Exponential
public import TauCeti.RingTheory.Nilpotent.BaseChangeAction

/-!
# Root subgroup actions on base changes of Kostant-stable additive subgroups

Let `L` be a Lie algebra over `ℚ`, and let `U_ℤ = kostantForm e h` be the Kostant integral form in
`UniversalEnvelopingAlgebra ℚ L`. When `M ≤ V` is stable under `ρ(U_ℤ)`, every divided power of
`ρ(eᵢ)` preserves `M`, since those divided powers lie in `U_ℤ`.

Combining this with the generic base-change exponential from
`TauCeti/RingTheory/Nilpotent/BaseChangeAction.lean`, we obtain the additive one-parameter
action of an arbitrary commutative ring `R` on `R ⊗[ℤ] M` attached to each root vector `eᵢ` whose
image `ρ(eᵢ)` is nilpotent.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.baseChangeKostantExpHom`: the root-vector one-parameter
  subgroup on an arbitrary base change of a Kostant-stable additive subgroup for each root vector
  whose image is nilpotent.
* `TauCeti.UniversalEnvelopingAlgebra.baseChangeKostantExpHom_toLinearMap`: its underlying linear
  map is the base-changed exponential.
* `TauCeti.UniversalEnvelopingAlgebra.coe_baseChangeKostantExpHom`: coercing the base-changed
  Kostant root subgroup to a function yields the base-changed exponential.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

namespace TauCeti

open TensorProduct

namespace UniversalEnvelopingAlgebra

universe u v w

-- Match tensor products to the explicit `ℤ`-algebra instance supplied by a value-ring object.
attribute [local instance high] Algebra.toModule

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {R : Type v} [CommRing R] [Algebra ℤ R]
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}

/-- The root-vector one-parameter subgroup on an arbitrary base change of a Kostant-stable
additive subgroup, for a root vector whose image is nilpotent.

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
        (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
        (Multiplicative.toAdd t) :=
  baseChangeExpHom_toLinearMap _ _ _ _ _

/-- Coercing the base-changed Kostant root subgroup to a function yields the base-changed
exponential. -/
@[simp]
theorem coe_baseChangeKostantExpHom (e : ι → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) (i : ι)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (t : Multiplicative R) :
    ⇑(baseChangeKostantExpHom e h ρ M hM i hnil t) =
      ⇑(baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
        (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
        (Multiplicative.toAdd t)) :=
  coe_baseChangeExpHom _ _ _ _ _

end UniversalEnvelopingAlgebra

end TauCeti
