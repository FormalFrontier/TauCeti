/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Unipotent
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RingTheory.Semisimple.DoubleCentralizer
public import TauCeti.RingTheory.Semisimple.Schur

/-!
# Kolchin's common fixed vector theorem

This file proves the linear-algebraic core of Kolchin's theorem: a group acting by unipotent
automorphisms on a nonzero finite-dimensional vector space over an algebraically closed field has
a common nonzero fixed vector. No commutativity or finiteness assumption is made on the group.

The proof first chooses a minimal nonzero invariant subspace. Burnside density identifies the
group algebra on this irreducible subspace with the full endomorphism algebra. For each group
element `g`, unipotence makes the trace of `(g - 1)h` vanish for every group element `h`, hence for
every endomorphism. Nondegeneracy of the trace pairing forces `g - 1 = 0` on the irreducible
subspace, so every nonzero vector in it is fixed.

## Main results

* `TauCeti.Representation.asAlgebraHom_surjective_of_isIrreducible`: Burnside density for a
  finite-dimensional irreducible representation over an algebraically closed field.
* `TauCeti.exists_common_fixed_vector_of_forall_isUnipotent`: Kolchin's common fixed vector
  theorem.
* `TauCeti.exists_fixed_submodule_finrank_eq_one_of_forall_isUnipotent`: the equivalent fixed-line
  form.

## References

* A. Borel, *Linear Algebraic Groups*, Proposition 4.8.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.
-/

public section

namespace TauCeti

open scoped MonoidAlgebra

universe u v w

noncomputable section

namespace LinearMap

variable {K : Type u} {V : Type v}
variable [CommRing K] [AddCommGroup V] [Module K V]

/-- The trace pairing on the endomorphisms of a finite-dimensional vector space is nondegenerate:
an endomorphism whose product with every endomorphism has zero trace is zero. -/
theorem eq_zero_of_trace_mul_eq_zero [Module.Free K V] [Module.Finite K V]
    (f : Module.End K V)
    (h : ∀ g : Module.End K V, _root_.LinearMap.trace K V (f * g) = 0) : f = 0 := by
  let b := Module.Free.chooseBasis K V
  apply (_root_.LinearMap.toMatrixAlgEquiv b).injective
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  have hY := h ((_root_.LinearMap.toMatrixAlgEquiv b).symm Y)
  rw [_root_.LinearMap.trace_eq_matrix_trace K b] at hY
  change (((_root_.LinearMap.toMatrixAlgEquiv b)
    (f * (_root_.LinearMap.toMatrixAlgEquiv b).symm Y)).trace = 0) at hY
  simpa only [map_mul, AlgEquiv.apply_symm_apply, map_zero, zero_mul, Matrix.trace_zero] using hY

end LinearMap

namespace GeneralLinearGroup

variable {K : Type u} {V : Type v}
variable [CommRing K] [IsReduced K] [AddCommGroup V] [Module K V]

/-- A unipotent automorphism has trace equal to the dimension of its space. -/
theorem IsUnipotent.trace_eq_finrank [Module.Free K V] [Module.Finite K V]
    {g : _root_.LinearMap.GeneralLinearGroup K V}
    (hg : _root_.LinearMap.GeneralLinearGroup.IsUnipotent g) :
    _root_.LinearMap.trace K V (g : Module.End K V) = (Module.finrank K V : K) := by
  have hnil := _root_.LinearMap.isNilpotent_trace_of_isNilpotent
    ((_root_.LinearMap.GeneralLinearGroup.isUnipotent_def g).mp hg)
  rw [map_sub, _root_.LinearMap.trace_one] at hnil
  exact sub_eq_zero.mp hnil.eq_zero

end GeneralLinearGroup

namespace Representation

variable {K : Type u} {G : Type w} {V : Type v}
variable [Field K] [IsAlgClosed K] [Monoid G] [AddCommGroup V] [Module K V]

/-- **Burnside density theorem.** The monoid algebra of a finite-dimensional irreducible
representation over an algebraically closed field exhausts the full endomorphism algebra.

Jacobson density gives all endomorphisms linear over the representation's commuting endomorphism
ring. Schur's lemma identifies that ring with the base field, so these are exactly the
`K`-linear endomorphisms. -/
theorem asAlgebraHom_surjective_of_isIrreducible [FiniteDimensional K V]
    (ρ : Representation K G V) (hρ : ρ.IsIrreducible) :
    Function.Surjective ρ.asAlgebraHom := by
  have : ρ.IsIrreducible := hρ
  have : IsSimpleModule K[G] ρ.asModule := inferInstance
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial K[G] ρ.asModule
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  have : Module.Finite (Module.End K[G] ρ.asModule) ρ.asModule :=
    finite_end_of_smulCommClass (R := K[G]) (M := ρ.asModule) K
  intro T
  let T' : Module.End (Module.End K[G] ρ.asModule) ρ.asModule :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f x ↦ by
        change T (f x) = f (T x)
        rw [← endAlgEquivSelfOfIsSimpleModule_smul (k := K) (A := K[G]) f x,
          ← endAlgEquivSelfOfIsSimpleModule_smul (k := K) (A := K[G]) f (T x)]
        exact T.map_smul _ _ }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := ρ.asModule) T'
  refine ⟨a, LinearMap.ext fun x ↦ ?_⟩
  have hx := LinearMap.congr_fun ha (ρ.asModuleEquiv.symm x)
  -- `asModule` is a type synonym, and its comparison with `V` is the identity equivalence.
  dsimp [Representation.asModuleEquiv, T'] at hx
  exact hx

end Representation

namespace GeneralLinearGroup

variable {K : Type u} {G : Type w} {V : Type v}
variable [CommRing K] [Group G] [AddCommGroup V] [Module K V]

/-- Unipotence is inherited by the restriction of a group representation to an invariant
subspace. -/
theorem IsUnipotent.subrepresentation {ρ : Representation K G V} (S : Subrepresentation ρ)
    (g : G) (hg : _root_.LinearMap.GeneralLinearGroup.IsUnipotent (ρ.asGroupHom g)) :
    _root_.LinearMap.GeneralLinearGroup.IsUnipotent (S.toRepresentation.asGroupHom g) := by
  rw [_root_.LinearMap.GeneralLinearGroup.isUnipotent_def] at hg ⊢
  rw [Representation.asGroupHom_apply] at hg
  let hmap : Set.MapsTo ((ρ g : Module.End K V) - (1 : Module.End K V))
      S.toSubmodule S.toSubmodule := by
    intro x hx
    exact S.toSubmodule.sub_mem (S.apply_mem_toSubmodule g hx) hx
  have hrestrict := Module.End.isNilpotent.restrict hmap hg
  convert hrestrict using 1
  ext x
  -- Restriction to a subrepresentation uses the original action on underlying vectors.
  rfl

end GeneralLinearGroup

variable {K : Type u} {G : Type w} {V : Type v}
variable [Field K] [IsAlgClosed K] [Group G] [AddCommGroup V] [Module K V]

/-- **Kolchin's common fixed vector theorem.** If every element of a group acts unipotently on a
nonzero finite-dimensional vector space over an algebraically closed field, then the group fixes a
nonzero vector. -/
theorem exists_common_fixed_vector_of_forall_isUnipotent [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K G V)
    (hunipotent : ∀ g, LinearMap.GeneralLinearGroup.IsUnipotent (ρ.asGroupHom g)) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  obtain ⟨S, hS, hSirr⟩ := Representation.exists_isIrreducible_subrepresentation ρ
  have hSne : S.toSubmodule ≠ ⊥ := fun h ↦
    hS (Subrepresentation.toSubmodule_injective
      (h.trans Subrepresentation.toSubmodule_bot.symm))
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hSne
  have hsurjective :=
    Representation.asAlgebraHom_surjective_of_isIrreducible S.toRepresentation hSirr
  have hSUnipotent (g : G) :
      LinearMap.GeneralLinearGroup.IsUnipotent (S.toRepresentation.asGroupHom g) :=
    TauCeti.GeneralLinearGroup.IsUnipotent.subrepresentation S g (hunipotent g)
  have htrivial (g : G) : S.toRepresentation g = 1 := by
    apply sub_eq_zero.mp
    apply LinearMap.eq_zero_of_trace_mul_eq_zero
    intro T
    obtain ⟨a, rfl⟩ := hsurjective T
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simpa [mul_add, map_add] using congrArg₂ (fun x y ↦ x + y) ha hb
    | single h r =>
        rw [Representation.asAlgebraHom_single, mul_smul_comm, map_smul, smul_eq_mul]
        rw [sub_mul, one_mul, ← map_mul, map_sub]
        have hgh := TauCeti.GeneralLinearGroup.IsUnipotent.trace_eq_finrank
          (hSUnipotent (g * h))
        have hh := TauCeti.GeneralLinearGroup.IsUnipotent.trace_eq_finrank (hSUnipotent h)
        rw [Representation.asGroupHom_apply] at hgh hh
        rw [hgh, hh, sub_self, mul_zero]
  obtain ⟨x, hx⟩ := exists_ne (0 : S.toSubmodule)
  refine ⟨x, fun h ↦ hx (Subtype.ext h), fun g ↦ ?_⟩
  have hfixed := LinearMap.congr_fun (htrivial g) x
  exact congrArg Subtype.val hfixed

/-- Under Kolchin's hypotheses, the common fixed vectors contain a one-dimensional subspace. -/
theorem exists_fixed_submodule_finrank_eq_one_of_forall_isUnipotent
    [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V)
    (hunipotent : ∀ g, LinearMap.GeneralLinearGroup.IsUnipotent (ρ.asGroupHom g)) :
    ∃ p : Submodule K V, Module.finrank K p = 1 ∧ ∀ g, ∀ x ∈ p, ρ g x = x := by
  obtain ⟨v, hv, hfixed⟩ :=
    exists_common_fixed_vector_of_forall_isUnipotent ρ hunipotent
  refine ⟨K ∙ v, finrank_span_singleton hv, fun g x hx ↦ ?_⟩
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  simp [hfixed]

end

end TauCeti
