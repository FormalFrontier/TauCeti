/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.OrthonormalContraction
public import TauCeti.LinearAlgebra.Dimension.Sup
public import TauCeti.RepresentationTheory.Continuous.Conjugate
public import TauCeti.RepresentationTheory.Continuous.Schur
public import TauCeti.RepresentationTheory.Continuous.Square.Basic

/-!
# The invariant tensors of an irreducible unitary representation are at most a line

For an irreducible unitary representation `π` of a monoid on a finite-dimensional inner product
space over an algebraically closed field, the invariants of the **tensor square** are at most
one-dimensional, and consequently so are the invariants of the symmetric and of the exterior
square **together**:

`dim (Sym²V)ᴳ + dim (Λ²V)ᴳ ≤ 1`.

That inequality is the whole content of the Frobenius-Schur trichotomy: the indicator is the
difference of those two dimensions
(`ContRepresentation.frobeniusSchurIndicator_eq_sub_finrank_invariants`), so an inequality on their
sum pins the difference to `1`, `0` or `-1`.

The argument is Schur's lemma applied through a contraction. An orthonormal basis `e` carries the
bilinear form `B(v, w) = ⟪J v, w⟫` and the contraction
`TauCeti.tensorSquareEquivEnd e : V ⊗[𝕜] V ≃ₗ[𝕜] (V →ₗ[𝕜] V)`; unitarity of `π` makes `B` invariant
for the pair `(π, {}^J π)`, where `{}^J π = TauCeti.ContRepresentation.conjugate e π` is the
conjugate representation, so an **invariant** tensor contracts to an intertwiner `{}^J π ⟶ π`.
Schur's lemma makes a nonzero such intertwiner surjective, hence bijective, and then every other
one is a scalar multiple of it, because the two composed through the inverse commute with `π`.
Pulling that back along the contraction, which is injective, says the invariant tensors are a line.

Only the **target** `π` of those intertwiners has to be irreducible, which is why the conjugate
representation is never itself shown irreducible: surjectivity of a nonzero intertwiner needs
irreducibility of the target only, and injectivity then comes from finite-dimensionality.

The symmetric and the antisymmetric tensors are invariant submodules that meet in `0`
(`TauCeti.isCompl_symmetricTensors_antisymmetricTensors`), so their invariants sit inside the
invariants of the tensor square as two submodules in direct sum, and the bound on the sum follows
from the bound on the tensor square.

## Main statements

* `ContRepresentation.finrank_invariants_tprod_self_le_one`: **the invariant tensors of an
  irreducible unitary representation are at most a line.**
* `ContRepresentation.finrank_invariants_squares_le_one`: the two invariant counts that the
  Frobenius-Schur indicator subtracts add up to at most `1`.
* `ContRepresentation.tensorSquareEquivEnd_conjCLM_of_mem_invariants`: the contraction of an
  invariant tensor intertwines the conjugate representation with `π`.

## Implementation notes

All declarations sit in the **root** `ContRepresentation` namespace, so that dot notation on
Mathlib's `ContRepresentation` elaborates and `scripts/lint-dot-notation.py` is satisfied; the
ambient `TauCeti` names are brought in by `open`, following
`TauCeti/RepresentationTheory/Continuous/Square/Basic.lean`.

The statements that do not name a contraction take no orthonormal basis: a finite-dimensional
inner product space has `stdOrthonormalBasis`, and the bounds do not depend on which basis is
used. The conjugate representation appears only through `TauCeti.conjCLM`, never through a
statement about its irreducibility or its character.

## References

This is the linear-algebra half of the Frobenius-Schur reality trichotomy of Layer 6b of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md);
the trichotomy itself is in
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/Trichotomy.lean`. The mathematical development
follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck,
*Representations of Compact Lie Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open Module TauCeti TauCeti.ContRepresentation

open scoped InnerProductSpace TensorProduct

namespace ContRepresentation

section Contraction

variable {𝕜 ι G V : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [Monoid G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  (e : OrthonormalBasis ι 𝕜 V) (π : ContRepresentation 𝕜 G V)

omit [DecidableEq ι] in
/-- **The bilinear form of an orthonormal basis is invariant for `π` against its conjugate.** The
two conjugations cancel against the unitarity of `π`, which is the identity that makes the
contraction of an invariant tensor an intertwiner. -/
theorem inner_conjugation_apply_conjCLM (hπ : IsUnitary π) (g : G) (v u : V) :
    ⟪conjugation e (π g v), conjCLM e (π g) u⟫_𝕜 = ⟪conjugation e v, u⟫_𝕜 := by
  rw [conjCLM_apply, inner_conjugation_conjugation, hπ.inner_map_map]
  conv_rhs => rw [← conjugation_conjugation e u]
  rw [inner_conjugation_conjugation]

/-- Contracting the tensor square commutes with the action, up to conjugating the argument: the
contraction of `(π g ⊗ π g) t` at `{}^J(π g) u` is `π g` of the contraction of `t` at `u`. -/
theorem tensorSquareEquivEnd_tprod_apply (hπ : IsUnitary π) (g : G) (t : V ⊗[𝕜] V) (u : V) :
    tensorSquareEquivEnd e (tprod π π g t) (conjCLM e (π g) u)
      = π g (tensorSquareEquivEnd e t u) := by
  induction t with
  | zero => simp
  | tmul v w =>
      rw [ContRepresentation.tprod_apply, TensorProduct.mapL_apply, TensorProduct.map_tmul]
      simp only [ContinuousLinearMap.coe_coe, tensorSquareEquivEnd_tmul_apply]
      rw [inner_conjugation_apply_conjCLM e π hπ, map_smul]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- **The contraction of an invariant tensor intertwines** the conjugate representation with `π`. -/
theorem tensorSquareEquivEnd_conjCLM_of_mem_invariants (hπ : IsUnitary π) {t : V ⊗[𝕜] V}
    (ht : t ∈ (tprod π π).invariants) (g : G) (u : V) :
    tensorSquareEquivEnd e t (conjCLM e (π g) u) = π g (tensorSquareEquivEnd e t u) := by
  conv_lhs => rw [← (mem_invariants t).mp ht g]
  exact tensorSquareEquivEnd_tprod_apply e π hπ g t u

/-- The intertwiner `{}^J π ⟶ π` that an invariant tensor contracts to. -/
noncomputable def invariantTensorIntertwiner (hπ : IsUnitary π) {t : V ⊗[𝕜] V}
    (ht : t ∈ (tprod π π).invariants) :
    Representation.IntertwiningMap (conjugate e π).toRepresentation π.toRepresentation :=
  (tensorSquareEquivEnd e t).intertwiningMap_of_isIntertwiningMap
    (conjugate e π).toRepresentation π.toRepresentation fun g u ↦ by
      have h := tensorSquareEquivEnd_conjCLM_of_mem_invariants e π hπ ht g u
      rw [← conjugate_apply e π g] at h
      exact h

@[simp]
theorem invariantTensorIntertwiner_apply (hπ : IsUnitary π) {t : V ⊗[𝕜] V}
    (ht : t ∈ (tprod π π).invariants) (u : V) :
    invariantTensorIntertwiner e π hπ ht u = tensorSquareEquivEnd e t u := (rfl)

end Contraction

section Irreducible

variable {𝕜 ι G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Fintype ι] [DecidableEq ι] [Monoid G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  (e : OrthonormalBasis ι 𝕜 V) (π : ContRepresentation 𝕜 G V)

omit [IsAlgClosed 𝕜] in
/-- A nonzero invariant tensor contracts to a **bijection**: its contraction is a nonzero
intertwiner into the irreducible `π`, hence surjective, and in finite dimensions surjective is
bijective. -/
theorem tensorSquareEquivEnd_bijective_of_mem_invariants (hπ : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) {t : V ⊗[𝕜] V}
    (ht : t ∈ (tprod π π).invariants) (ht0 : t ≠ 0) :
    Function.Bijective (tensorSquareEquivEnd e t) := by
  let _ : Representation.IsIrreducible π.toRepresentation := hirr
  have hne : invariantTensorIntertwiner e π hπ ht ≠ 0 := by
    intro h
    refine ht0 ((tensorSquareEquivEnd e).map_eq_zero_iff.mp (LinearMap.ext fun u ↦ ?_))
    have hu : invariantTensorIntertwiner e π hπ ht u
        = (0 : Representation.IntertwiningMap (conjugate e π).toRepresentation
            π.toRepresentation) u := by rw [h]
    simpa using hu
  have hsurj : Function.Surjective (tensorSquareEquivEnd e t) :=
    (Representation.IsIrreducible.surjective_or_eq_zero
      (invariantTensorIntertwiner e π hπ ht)).resolve_right hne
  exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

variable {π}

/-- **Any two invariant tensors of an irreducible unitary representation are proportional**, once
one of them is nonzero: composing the contraction of the second with the inverse of the contraction
of the first gives a self-intertwiner of `π`, which Schur's lemma makes a scalar. -/
theorem exists_smul_eq_of_mem_invariants_tprod (hπ : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) {t t' : V ⊗[𝕜] V}
    (ht : t ∈ (tprod π π).invariants) (ht0 : t ≠ 0)
    (ht' : t' ∈ (tprod π π).invariants) :
    ∃ c : 𝕜, t' = c • t := by
  let _ : Representation.IsIrreducible π.toRepresentation := hirr
  set b := stdOrthonormalBasis 𝕜 V
  have hbij := tensorSquareEquivEnd_bijective_of_mem_invariants b π hπ hirr ht ht0
  set E : V ≃ₗ[𝕜] V := LinearEquiv.ofBijective (tensorSquareEquivEnd b t) hbij
  have hEapply : ∀ x : V, E x = tensorSquareEquivEnd b t x := fun _ ↦ (rfl)
  -- `E` transports the action of `π` back to the action of the conjugate representation.
  have hEsymm : ∀ (g : G) (u : V), E.symm (π g u) = conjCLM b (π g) (E.symm u) := by
    intro g u
    refine E.injective ?_
    rw [E.apply_symm_apply, hEapply,
      tensorSquareEquivEnd_conjCLM_of_mem_invariants b π hπ ht, ← hEapply, E.apply_symm_apply]
  -- The second contraction, precomposed with `E⁻¹`, is a self-intertwiner of `π`.
  set A : Representation.IntertwiningMap π.toRepresentation π.toRepresentation :=
    ((tensorSquareEquivEnd b t').comp E.symm.toLinearMap).intertwiningMap_of_isIntertwiningMap
      π.toRepresentation π.toRepresentation (fun g u ↦ by
        have h : tensorSquareEquivEnd b t' (E.symm (π g u))
            = π g (tensorSquareEquivEnd b t' (E.symm u)) := by
          rw [hEsymm g u, tensorSquareEquivEnd_conjCLM_of_mem_invariants b π hπ ht']
        exact h) with hA
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := π.toRepresentation)).2 A
  have hAx : ∀ x : V, A x = c • x := by
    intro x
    rw [← hc]
    simp [Algebra.algebraMap_eq_smul_one]
  have hkey : ∀ x : V, tensorSquareEquivEnd b t' (E.symm x) = c • x := by
    intro x
    have h := hAx x
    rw [hA] at h
    exact h
  refine ⟨c, (tensorSquareEquivEnd b).injective (LinearMap.ext fun x ↦ ?_)⟩
  have hx := hkey (E x)
  rw [E.symm_apply_apply, hEapply] at hx
  rw [hx, map_smul, LinearMap.smul_apply]

/-- **The invariant tensors of an irreducible unitary representation are at most a line.** They are
all proportional to any nonzero one of them. -/
theorem finrank_invariants_tprod_self_le_one (hπ : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    finrank 𝕜 (tprod π π).invariants ≤ 1 := by
  rcases eq_or_ne (tprod π π).invariants ⊥ with h | h
  · rw [h, finrank_bot]
    exact Nat.zero_le 1
  · obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hle : (tprod π π).invariants ≤ 𝕜 ∙ t := by
      intro t' ht'
      obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_invariants_tprod hπ hirr ht ht0 ht'
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self t)
    calc finrank 𝕜 (tprod π π).invariants
        ≤ finrank 𝕜 (𝕜 ∙ t) := Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton ht0

end Irreducible

section Squares

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Monoid G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

/-- **The two invariant counts the Frobenius-Schur indicator subtracts add up to at most `1`.** The
symmetric and the antisymmetric tensors meet in `0`, so their invariants sit in direct sum inside
the invariants of the tensor square, which are at most a line. -/
theorem finrank_invariants_squares_le_one (hπ : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    finrank 𝕜 (symmetricSquare π).invariants + finrank 𝕜 (exteriorSquare π).invariants ≤ 1 := by
  set S := Submodule.map (symmetricTensors 𝕜 V).subtype (symmetricSquare π).invariants
  set A := Submodule.map (antisymmetricTensors 𝕜 V).subtype (exteriorSquare π).invariants
  have hSfr : finrank 𝕜 S = finrank 𝕜 (symmetricSquare π).invariants :=
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq.symm
  have hAfr : finrank 𝕜 A = finrank 𝕜 (exteriorSquare π).invariants :=
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq.symm
  have hinf : S ⊓ A = ⊥ := by
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    have hxS : x ∈ symmetricTensors 𝕜 V := by
      obtain ⟨y, -, rfl⟩ := hx.1
      exact y.2
    have hxA : x ∈ antisymmetricTensors 𝕜 V := by
      obtain ⟨y, -, rfl⟩ := hx.2
      exact y.2
    have hbot := (isCompl_symmetricTensors_antisymmetricTensors 𝕜 V).inf_eq_bot
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot x (Submodule.mem_inf.mpr ⟨hxS, hxA⟩)
  have hSle : S ≤ (tprod π π).invariants := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_invariants_symmetricSquare_iff π).mp hx
  have hAle : A ≤ (tprod π π).invariants := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_invariants_exteriorSquare_iff π).mp hx
  rw [← hSfr, ← hAfr]
  exact le_trans
    (finrank_add_finrank_le_of_inf_eq_bot (K := 𝕜) (W := V ⊗[𝕜] V) hSle hAle hinf)
    (finrank_invariants_tprod_self_le_one hπ hirr)

end Squares

end ContRepresentation
