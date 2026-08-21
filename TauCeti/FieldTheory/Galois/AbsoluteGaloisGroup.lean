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
`TauCeti.mem_perfectClosure_iff_forall_fixed` says
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
* `TauCeti.mem_perfectClosure_iff_forall_fixed`: the fixed field of `Gal(E/F)` for a normal
  extension `E/F` is the relative perfect closure of `F` in `E`.

This is the "the group, fixed once" milestone of Layer 9 of the human-authored roadmap at
`TauCetiRoadmap/ProfiniteCohomology/README.md`; that layer's warning about the algebraic closure is
`mem_perfectClosure_iff_forall_fixed` here.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §2 and
  Ch. IV, for the convention that the absolute Galois group is taken at the separable closure.
-/

public section

noncomputable section

namespace TauCeti

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

section Normal

variable [Normal F E]

/-! ### Restriction to the separable closure -/

/-- An `F`-automorphism of a normal extension `E/F` that is the identity on the separable closure
of `F` in `E` is the identity: what is left of the extension is purely inseparable. -/
theorem restrictNormalHom_separableClosure_injective :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (separableClosure F E)) := by
  rw [← MonoidHom.ker_eq_bot_iff, IntermediateField.restrictNormalHom_ker]
  have h : Subsingleton Gal(E/(separableClosure F E)) :=
    ⟨fun a b ↦ AlgEquiv.ext fun x ↦
      AlgHom.congr_fun (Subsingleton.elim a.toAlgHom b.toAlgHom) x⟩
  have h' : Subsingleton (separableClosure F E).fixingSubgroup :=
    (IntermediateField.fixingSubgroupEquiv _).toEquiv.subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

/-- Restriction to the separable closure is bijective on the automorphism group of a normal
extension. -/
theorem restrictNormalHom_separableClosure_bijective :
    Function.Bijective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (separableClosure F E)) :=
  ⟨restrictNormalHom_separableClosure_injective F E,
    AlgEquiv.restrictNormalHom_surjective E⟩

variable {F E}

/-- A homomorphism into `Gal(E/F)` lifting the automorphisms of the separable closure is
continuous.

This is the criterion the inverse of `separableClosureRestrictEquiv` is checked against, and it is
where the topologies are compared: the fixing subgroup of a finite subextension `M` of `E` is
pulled back to the fixing subgroup of the trace of `M` on `separableClosure F E`, because every
element of `M` has a `q`-th power root of itself inside that trace. -/
private theorem continuous_of_algebraMap_comm (s : Gal(separableClosure F E/F) → Gal(E/F))
    (hmul : ∀ a b, s (a * b) = s a * s b)
    (hs : ∀ (τ : Gal(separableClosure F E/F)) (y : separableClosure F E),
      s τ (algebraMap (separableClosure F E) E y) =
        algebraMap (separableClosure F E) E (τ y)) :
    Continuous s := by
  have hEq : ExpChar E (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F E).injective _
  have hSq : ExpChar (separableClosure F E) (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective _
  refine continuous_of_continuousAt_one (MonoidHom.mk' s hmul)
    (continuousAt_def.mpr fun N hN ↦ ?_)
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨M, hM, hMN⟩ := hN
  rw [krullTopology_mem_nhds_one_iff]
  -- `M.comap g` is the trace of `M` on the separable closure.
  set g : separableClosure F E →ₐ[F] E := IsScalarTower.toAlgHom F _ E
  refine ⟨M.comap g, ?_, fun τ hτ ↦ hMN ?_⟩
  · -- It is finite over `F` because it embeds `F`-linearly into `M`.
    have : Module.Finite F M := hM
    exact Module.Finite.of_injective
      ({ toFun := fun x : M.comap g ↦ (⟨g x, x.2⟩ : M)
         map_add' := fun _ _ ↦ Subtype.ext (map_add g _ _)
         map_smul' := fun _ _ ↦ Subtype.ext (map_smul g _ _) } : M.comap g →ₗ[F] M)
      fun a b h ↦ by
        have hab : g a = g b := congrArg (fun z : M ↦ (z : E)) h
        exact Subtype.ext (g.injective hab)
  · -- Each `x ∈ M` has `x ^ q ^ n` in the trace, hence fixed, hence `x` itself is fixed.
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure F E) (ringExpChar F) x
    -- `M.comap g` is by definition the set of `y` with `g y ∈ M`.
    have hyM : g y ∈ M := by
      have hgy : g y = x ^ ringExpChar F ^ n := hy
      rw [hgy]
      exact pow_mem hx _
    have hτy : τ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ y hyM
    have hpow : (s τ x) ^ ringExpChar F ^ n = x ^ ringExpChar F ^ n := by
      rw [← hy, ← map_pow, ← hy, hs τ y, hτy]
    simpa [iterateFrobenius_def] using (iterateFrobenius E (ringExpChar F) n).injective hpow

variable (F E)

/-- **Restriction to the separable closure is an isomorphism of topological groups**
`Gal(E/F) ≃ₜ* Gal(separableClosure F E / F)`, for a normal extension `E/F`. -/
def separableClosureRestrictEquiv : Gal(E/F) ≃ₜ* Gal(separableClosure F E/F) where
  __ := MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (separableClosure F E))
    (restrictNormalHom_separableClosure_bijective F E)
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous _
  continuous_invFun := by
    set e := MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (separableClosure F E))
      (restrictNormalHom_separableClosure_bijective F E)
    refine continuous_of_algebraMap_comm e.symm (map_mul e.symm) fun τ y ↦ ?_
    conv_rhs => rw [← e.apply_symm_apply τ]
    exact (AlgEquiv.restrictNormal_commutes _ _ y).symm

variable {F E}

@[simp]
theorem separableClosureRestrictEquiv_apply (σ : Gal(E/F)) :
    separableClosureRestrictEquiv F E σ = AlgEquiv.restrictNormalHom (separableClosure F E) σ :=
  (rfl)

theorem coe_separableClosureRestrictEquiv_apply (σ : Gal(E/F)) (x : separableClosure F E) :
    (separableClosureRestrictEquiv F E σ x : E) = σ x :=
  AlgEquiv.restrictNormal_commutes _ _ x

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
theorem mem_perfectClosure_iff_forall_fixed {x : E} :
    x ∈ perfectClosure F E ↔ ∀ σ : Gal(E/F), σ x = x := by
  have hEq : ExpChar E (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F E).injective _
  have hSq : ExpChar (separableClosure F E) (ringExpChar F) :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective _
  refine ⟨fun hx σ ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨n, a, ha⟩ := (mem_perfectClosure_iff_pow_mem (F := F) (E := E) (ringExpChar F)).mp hx
    have hpow : (σ x) ^ ringExpChar F ^ n = x ^ ringExpChar F ^ n := by
      rw [← map_pow, ← ha, AlgEquiv.commutes]
    simpa [iterateFrobenius_def] using (iterateFrobenius E (ringExpChar F) n).injective hpow
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
isomorphism `Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K`. -/
def absoluteGaloisGroupRestrictEquiv :
    Field.absoluteGaloisGroup K ≃ₜ* AbsoluteGaloisGroup K :=
  separableClosureRestrictEquiv K (AlgebraicClosure K)

@[simp]
theorem coe_absoluteGaloisGroupRestrictEquiv_apply (σ : Gal(AlgebraicClosure K/K))
    (x : SeparableClosure K) :
    (absoluteGaloisGroupRestrictEquiv K σ x : AlgebraicClosure K) = σ x :=
  coe_separableClosureRestrictEquiv_apply _ x

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
