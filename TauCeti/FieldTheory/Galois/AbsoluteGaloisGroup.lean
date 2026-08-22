/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The absolute Galois group of a field, taken at its separable closure

For a normal extension `E/F` an automorphism of `E` is determined by, and determined on, the
separable closure of `F` in `E`: restriction

```
Gal(E/F) → Gal(separableClosure F E / F)
```

is an isomorphism of topological groups, `TauCeti.separableClosureRestrictEquiv`. Specialised to
`E = AlgebraicClosure F` this identifies Mathlib's `Field.absoluteGaloisGroup F`, defined through
the algebraic closure, with `TauCeti.AbsoluteGaloisGroup F = Gal(SeparableClosure F / F)`, which is
the carrier every Galois-cohomological statement is written against.

Which of the two closures is used is not a matter of taste.
`TauCeti.mem_perfectClosure_iff_fixed` says
that the elements of a normal `E/F` fixed by every `F`-automorphism are exactly the elements purely
inseparable over `F`. So for an imperfect `F` the fixed field of `Field.absoluteGaloisGroup F` is
the purely inseparable closure of `F` and not `F` itself, while over the separable closure
`InfiniteGalois.mem_range_algebraMap_iff_fixed` gives the fixed field `F` that a Galois descent
argument needs. The two groups are nonetheless the same topological group, which is what makes it
legitimate to state a theorem for one and use it for the other.

## Main definitions and results

* `TauCeti.AbsoluteGaloisGroup K`: the automorphisms of a separable closure of `K`.
* `TauCeti.separableClosureRestrictEquiv`: restriction to the separable closure is an isomorphism
  of topological groups, for any normal extension.
* `TauCeti.absoluteGaloisGroupRestrictEquiv`: its specialisation comparing
  `Field.absoluteGaloisGroup K` with `TauCeti.AbsoluteGaloisGroup K`.
* `TauCeti.mem_perfectClosure_iff_fixed`: the fixed field of `Gal(E/F)` for a normal
  extension `E/F` is the relative perfect closure of `F` in `E`.

This is the "the group, fixed once" milestone of Layer 9 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`; that layer's warning about the algebraic closure is
`mem_perfectClosure_iff_fixed` here.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. VI §1, for the
  convention that the absolute Galois group of a field is taken at its separable closure.
-/

public section

noncomputable section

namespace TauCeti

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

section Auxiliary

variable {F E}

/-- The preimage of a finite intermediate field `M` of `E/F` under an `F`-algebra map `g` into `E`
is finite over `F`: it is `F`-isomorphic to its image under `g`, which is contained in `M`. -/
private theorem finiteDimensional_comap {L : Type*} [Field L] [Algebra F L] (g : L →ₐ[F] E)
    (M : IntermediateField F E) [FiniteDimensional F M] : FiniteDimensional F (M.comap g) :=
  have hle : (M.comap g).map g ≤ M := (IntermediateField.map_comap_eq g M).le.trans inf_le_left
  Module.Finite.of_injective
    (((IntermediateField.inclusion hle).comp
      (IntermediateField.equivMap (M.comap g) g).toAlgHom).toLinearMap)
    ((IntermediateField.inclusion_injective hle).comp
      (IntermediateField.equivMap (M.comap g) g).injective)

end Auxiliary

section Normal

variable [Normal F E]

/-! ### Restriction to the separable closure -/

namespace AlgEquiv

/-- An `F`-automorphism of a normal extension `E/F` that is the identity on the separable closure
of `F` in `E` is the identity: what is left of the extension is purely inseparable. -/
theorem restrictNormalHom_separableClosure_injective :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (separableClosure F E)) := by
  rw [← MonoidHom.ker_eq_bot_iff, IntermediateField.restrictNormalHom_ker]
  have h : Subsingleton Gal(E/(separableClosure F E)) :=
    AlgEquiv.coe_toAlgHom_injective.subsingleton
  have h' : Subsingleton (separableClosure F E).fixingSubgroup :=
    (IntermediateField.fixingSubgroupEquiv _).toEquiv.subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

end AlgEquiv

variable {F E}

/-- A homomorphism into `Gal(E/F)` lifting the automorphisms of the separable closure is
continuous.

This is the criterion the inverse of `separableClosureRestrictEquiv` is checked against, and it is
where the topologies are compared: the fixing subgroup of a finite subextension `M` of `E` is
pulled back to the fixing subgroup of `M ∩ separableClosure F E`, because for every `x ∈ M` the
power `x ^ q ^ n` lies in that intersection for some `n`, where `q` is the exponential
characteristic. -/
private theorem continuous_of_algebraMap_comm (s : Gal(separableClosure F E/F) → Gal(E/F))
    (hmul : ∀ a b, s (a * b) = s a * s b)
    (hs : ∀ (τ : Gal(separableClosure F E/F)) (y : separableClosure F E),
      s τ (algebraMap (separableClosure F E) E y) =
        algebraMap (separableClosure F E) E (τ y)) :
    Continuous s := by
  have hSq : ExpChar (separableClosure F E) (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective _
  refine continuous_of_continuousAt_one (MonoidHom.mk' s hmul)
    (continuousAt_def.mpr fun N hN ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨M, hM, hMN⟩ := hN
  have : FiniteDimensional F M := hM
  rw [krullTopology_mem_nhds_one_iff]
  -- `M.comap g` is `M ∩ separableClosure F E`.
  set g : separableClosure F E →ₐ[F] E := IsScalarTower.toAlgHom F _ E with hg
  refine ⟨M.comap g, finiteDimensional_comap g M, fun τ hτ ↦ hMN ?_⟩
  -- Each `x ∈ M` has `x ^ q ^ n` in that intersection, hence fixed, hence `x` itself is fixed.
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure F E) (ringExpChar F) x
  -- `M.comap g` is by definition the set of `y` with `g y ∈ M`.
  have hyM : g y ∈ M := by
    rw [hg, IsScalarTower.toAlgHom_apply, hy]
    exact pow_mem hx _
  have hτy : τ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ y hyM
  have hpow : (s τ x) ^ ringExpChar F ^ n = x ^ ringExpChar F ^ n := by
    rw [← hy, ← map_pow, ← hy, hs τ y, hτy]
  have hE : ExpChar E (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F E).injective _
  exact iterateFrobenius_inj E (ringExpChar F) n hpow

variable (F E)

/-- Restriction to the separable closure as a group isomorphism, for a normal extension `E/F`.

This is the underlying multiplicative equivalence of `separableClosureRestrictEquiv`, named so
that the structure field and the inverse-continuity proof below refer to one and the same term
rather than to two separately built copies identified by definitional unfolding. -/
private def separableClosureRestrictMulEquiv : Gal(E/F) ≃* Gal(separableClosure F E/F) :=
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (separableClosure F E))
    ⟨AlgEquiv.restrictNormalHom_separableClosure_injective F E,
      AlgEquiv.restrictNormalHom_surjective E⟩

/-- **Restriction to the separable closure is an isomorphism of topological groups**
`Gal(E/F) ≃ₜ* Gal(separableClosure F E / F)`, for a normal extension `E/F`. -/
def separableClosureRestrictEquiv : Gal(E/F) ≃ₜ* Gal(separableClosure F E/F) where
  __ := separableClosureRestrictMulEquiv F E
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous _
  continuous_invFun :=
    continuous_of_algebraMap_comm (separableClosureRestrictMulEquiv F E).symm
      (map_mul _) fun τ y ↦ by
        conv_rhs => rw [← (separableClosureRestrictMulEquiv F E).apply_symm_apply τ]
        exact (AlgEquiv.restrictNormal_commutes _ _ y).symm

variable {F E}

/-- The isomorphism `separableClosureRestrictEquiv` is the restriction map
`AlgEquiv.restrictNormalHom`, which is what identifies it with the map Mathlib's API is about. -/
theorem separableClosureRestrictEquiv_apply (σ : Gal(E/F)) :
    separableClosureRestrictEquiv F E σ = AlgEquiv.restrictNormalHom (separableClosure F E) σ :=
  (rfl)

/-- Restricting `σ : Gal(E/F)` to the separable closure does not move elements: the image of
`x ∈ separableClosure F E` under `separableClosureRestrictEquiv F E σ` is `σ x`, computed in `E`. -/
@[simp]
theorem coe_separableClosureRestrictEquiv_apply (σ : Gal(E/F)) (x : separableClosure F E) :
    (separableClosureRestrictEquiv F E σ x : E) = σ x :=
  AlgEquiv.restrictNormal_commutes _ _ x

/-- The automorphism of `E` extending `τ : Gal(separableClosure F E/F)` agrees with `τ` on the
separable closure. -/
@[simp]
theorem separableClosureRestrictEquiv_symm_apply_coe (τ : Gal(separableClosure F E/F))
    (x : separableClosure F E) :
    (separableClosureRestrictEquiv F E).symm τ (x : E) = (τ x : E) := by
  conv_rhs => rw [← (separableClosureRestrictEquiv F E).apply_symm_apply τ]
  exact (coe_separableClosureRestrictEquiv_apply _ x).symm

/-! ### The fixed field of a normal extension -/

/-- **The fixed field of `Gal(E/F)` for a normal extension `E/F` is the relative perfect closure**
of `F` in `E`, and not `F`. The two agree exactly when `E/F` has no nontrivial purely inseparable
part, so for `E` an algebraic closure they agree exactly when `F` is perfect. -/
theorem mem_perfectClosure_iff_fixed {x : E} :
    x ∈ perfectClosure F E ↔ ∀ σ : Gal(E/F), σ x = x := by
  have hSq : ExpChar (separableClosure F E) (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective _
  refine ⟨fun hx σ ↦ ?_, fun hx ↦ ?_⟩
  · -- `perfectClosure F E` is purely inseparable over `F`, so `σ` and the inclusion are the same
    -- `F`-algebra map on it.
    exact AlgHom.congr_fun
      (Subsingleton.elim (σ.toAlgHom.comp (perfectClosure F E).val) (perfectClosure F E).val)
      ⟨x, hx⟩
  · -- Push `x` into the separable closure by a `q`-th power, where the fixed field is `F`.
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure F E) (ringExpChar F) x
    have hfix : ∀ τ : Gal(separableClosure F E/F), τ y = y := fun τ ↦ by
      have h2 : (separableClosureRestrictEquiv F E).symm τ
          (algebraMap (separableClosure F E) E y) = algebraMap (separableClosure F E) E y := by
        rw [hy, map_pow, hx]
      rw [IntermediateField.algebraMap_apply, separableClosureRestrictEquiv_symm_apply_coe] at h2
      exact Subtype.ext h2
    obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr hfix
    exact (mem_perfectClosure_iff_pow_mem (F := F) (E := E) (ringExpChar F)).mpr
      ⟨n, b, by rw [IsScalarTower.algebraMap_apply F (separableClosure F E) E, hb, hy]⟩

end Normal

/-! ### The absolute Galois group -/

variable (K : Type*) [Field K]

/-- The absolute Galois group of `K`: the group of automorphisms of a separable closure of `K`.

This, rather than Mathlib's `Field.absoluteGaloisGroup`, is the group Galois cohomology is stated
at, because it is `Kˢ` and not an algebraic closure whose invariants are `K` for every `K`. It is
an abbreviation so that the Krull topology, the profinite structure and the action on `Kˢ` are the
ones Mathlib already provides for `Gal(E/F)`; `absoluteGaloisGroupRestrictEquiv` compares it with
`Field.absoluteGaloisGroup`. -/
abbrev AbsoluteGaloisGroup := Gal(SeparableClosure K/K)

/-- **Mathlib's absolute Galois group and `AbsoluteGaloisGroup` are the same topological group**:
restricting an automorphism of an algebraic closure of `K` to the separable closure is an
isomorphism `Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K`.

Its forward map is restriction, `absoluteGaloisGroupRestrictEquiv_apply`, and both directions are
computed on elements of `SeparableClosure K` by `coe_absoluteGaloisGroupRestrictEquiv_apply` and
`absoluteGaloisGroupRestrictEquiv_symm_apply_coe`. Those lemmas are stated on applications rather
than on the isomorphisms themselves, because `Field.absoluteGaloisGroup K` carries its own derived
group and topology instances, so an equation between the isomorphisms is not usable by `rw`. -/
def absoluteGaloisGroupRestrictEquiv :
    Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K :=
  separableClosureRestrictEquiv K (AlgebraicClosure K)

/-- The comparison isomorphism is the restriction map `AlgEquiv.restrictNormalHom`, which is what
identifies it with the map Mathlib's API is about. -/
theorem absoluteGaloisGroupRestrictEquiv_apply (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisGroupRestrictEquiv K σ =
      AlgEquiv.restrictNormalHom (separableClosure K (AlgebraicClosure K)) σ :=
  (rfl)

/-- An automorphism of an algebraic closure of `K` and its image in `AbsoluteGaloisGroup K` take
the same value on an element of `SeparableClosure K`, computed in the algebraic closure. -/
@[simp]
theorem coe_absoluteGaloisGroupRestrictEquiv_apply (σ : Gal(AlgebraicClosure K/K))
    (x : SeparableClosure K) :
    (absoluteGaloisGroupRestrictEquiv K σ x : AlgebraicClosure K) = σ x :=
  coe_separableClosureRestrictEquiv_apply _ x

/-- The automorphism of `AlgebraicClosure K` extending `τ : AbsoluteGaloisGroup K` agrees with `τ`
on `SeparableClosure K`; this is what computes the inverse of the comparison isomorphism.

The coercion to a function carries its type argument explicitly because
`Field.absoluteGaloisGroup K` is a plain definition, so elaboration does not see an element of it
as a function on `AlgebraicClosure K` on its own. -/
@[simp]
theorem absoluteGaloisGroupRestrictEquiv_symm_apply_coe (τ : AbsoluteGaloisGroup K)
    (x : SeparableClosure K) :
    DFunLike.coe (F := Gal(AlgebraicClosure K/K)) ((absoluteGaloisGroupRestrictEquiv K).symm τ)
        (x : AlgebraicClosure K) = (τ x : AlgebraicClosure K) :=
  separableClosureRestrictEquiv_symm_apply_coe _ x

/-- The absolute Galois group of a separably closed field is trivial. -/
instance [IsSepClosed K] : Subsingleton (AbsoluteGaloisGroup K) := by
  have hbot : separableClosure K (AlgebraicClosure K) = ⊥ :=
    (IsSepClosed.separableClosure_eq_bot_iff K (AlgebraicClosure K)).mpr ‹_›
  refine ⟨fun σ τ ↦ AlgEquiv.ext fun x ↦ ?_⟩
  have hxb : (x : AlgebraicClosure K) ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    rw [← hbot]; exact x.2
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hxb
  have hx : x = algebraMap K _ y := Subtype.ext hy.symm
  rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]

end TauCeti
