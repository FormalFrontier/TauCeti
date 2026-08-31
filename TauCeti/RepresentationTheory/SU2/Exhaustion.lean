/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The home of `Complex.isAlgClosed`: the scalar half of Schur's lemma, which the first
-- orthogonality relation below runs on, needs `IsAlgClosed ℂ`.
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Analysis.Normed.Module.Multilinear
public import TauCeti.RepresentationTheory.Compact.Character.Basic
public import TauCeti.RepresentationTheory.Compact.UnitaryModel
public import TauCeti.RepresentationTheory.Continuous.Schur
public import TauCeti.RepresentationTheory.SU2.Borel
public import TauCeti.RepresentationTheory.SU2.Completeness
public import TauCeti.RepresentationTheory.SU2.Irreducible

/-!
# The symmetric powers exhaust the irreducibles of `SU(2)`

`TauCeti/RepresentationTheory/SU2/Irreducible.lean` shows the symmetric powers `Symᵈ(ℂ²)` of the
standard representation of `SU(2)` are irreducible and pairwise inequivalent, and
`TauCeti/RepresentationTheory/SU2/Completeness.lean` shows their characters span a uniformly dense
subspace of the continuous class functions. This file closes the classification: **every**
finite-dimensional irreducible continuous representation of `SU(2)` is one of them
(`TauCeti.SU2.exists_nonempty_equiv_symPower`), and the degree is unique
(`TauCeti.SU2.existsUnique_nonempty_equiv_symPower`), so `d ↦ Symᵈ(ℂ²)` is a bijection from `ℕ`
onto the isomorphism classes.

The deduction is the classical one: an irreducible not in the list has a character orthogonal to
every `χ_d`, hence -- by continuity of the `L²` pairing along the uniform approximation -- to
every class function, hence to itself, contradicting `‖χ_π‖ = 1`. What is new here is the
plumbing that lets the general orthogonality relations of
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean` reach `Symᵈ(ℂ²)` at all: those
relations are about a `ContRepresentation` on a *normed* space, whereas `Symᵈ(ℂ²)` is a symmetric
tensor power, carrying no topology. So the weight basis is used to carry the symmetric power onto
the standard model `ℂ^{d+1}` (`TauCeti.SU2.symPowerModel`), and its action is shown to be
continuous.

That continuity is the one genuinely analytic step. A group element acts on a pure symmetric
tensor factor by factor, so the action is the composition of the continuous map
`g ↦ (g·v₁, …, g·v_d)` with the multilinear map `⨂ₛ`, read in coordinates; multilinear maps on
finite-dimensional spaces are continuous
(`MultilinearMap.continuous_of_finiteDimensional`), and expanding an arbitrary vector in
the weight basis extends the conclusion from pure tensors to all of `Symᵈ(ℂ²)`.

Unitarity of `Symᵈ(ℂ²)` is *not* established, and is not needed: the second orthogonality
relation asks for unitarity only of the representation being tested, and even that hypothesis is
discharged by Weyl's unitarian trick, so the statements below assume none. The transported model
carries the inner product making the weight basis orthonormal, which for `d ≥ 2` is not the
`SU(2)`-invariant one.

## Main definitions

* `TauCeti.SU2.symPowerModel`: `Symᵈ(ℂ²)` as a continuous representation on `ℂ^{d+1}`.

## Main results

* `TauCeti.SU2.exists_nonempty_equiv_symPower`: every finite-dimensional irreducible continuous
  representation of `SU(2)` is equivalent to some `Symᵈ(ℂ²)`.
* `TauCeti.SU2.existsUnique_nonempty_equiv_symPower`: the degree `d` is unique.

## References

This is the `su2Irrep_exhaust` target of the `SU(2)` engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`. The route taken is the
character-theoretic one, not the Lie-algebra highest-weight argument that the roadmap names; it
runs on the irreducibility and weight results of `TauCeti/RepresentationTheory/SU2/Irreducible.lean`
together with the density of the character span. It is not circular. Peter-Weyl is nowhere used;
the density is Stone-Weierstrass applied to the Chebyshev recursion for `χ_d`; and the
orthogonality relations invoked are the general compact-group ones of
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean`, which know nothing of `SU(2)`, rather
than the concrete `SU(2)` orthonormality that is computed from the Weyl integration formula.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 3.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §4-5.
-/

public section

open Matrix
open scoped InnerProductSpace TensorProduct

namespace TauCeti

namespace SU2

variable (d : ℕ)

/-- The weight basis read as an identification of `Symᵈ(ℂ²)` with the standard model space
`ℂ^{d+1}`. -/
noncomputable def weightEquiv : Sym[ℂ]^d(Fin 2 → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1)) :=
  (weightBasis d).equiv (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis (Equiv.refl _)

/-- The `d`-th symmetric power of the standard representation of `SU(2)`, carried onto the
standard model space `ℂ^{d+1}` by the weight basis. -/
noncomputable def symPowerModel : ContRepresentation ℂ SU2 (EuclideanSpace ℂ (Fin (d + 1))) :=
  .ofMonoidHom
    { toFun g := LinearMap.toContinuousLinearMap ((weightEquiv d).conj (symPower d g))
      map_one' := by ext x; simp [LinearEquiv.conj_apply]
      map_mul' g h := by ext x; simp [LinearEquiv.conj_apply] }

/-- The identification sends the `i`-th weight vector to the `i`-th standard basis vector. -/
@[simp]
theorem weightEquiv_weightBasis (i : Fin (d + 1)) :
    weightEquiv d (weightBasis d i) = EuclideanSpace.single i 1 := by
  rw [weightEquiv, Module.Basis.equiv_apply, OrthonormalBasis.coe_toBasis,
    Equiv.refl_apply, EuclideanSpace.basisFun_apply]

/-- The identification sends the `i`-th standard basis vector back to the `i`-th weight vector. -/
@[simp]
theorem weightEquiv_symm_single (i : Fin (d + 1)) :
    (weightEquiv d).symm (EuclideanSpace.single i 1) = weightBasis d i :=
  (LinearEquiv.symm_apply_eq _).2 (weightEquiv_weightBasis d i).symm

@[simp]
theorem symPowerModel_apply (g : SU2) (x : EuclideanSpace ℂ (Fin (d + 1))) :
    symPowerModel d g x = weightEquiv d (symPower d g ((weightEquiv d).symm x)) := (rfl)

/-! ### Continuity -/

private theorem continuous_mulVec (w : Fin 2 → ℂ) :
    Continuous fun g : SU2 ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ w := by
  refine continuous_pi fun i ↦ ?_
  simp only [Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ ↦ Continuous.mul ?_ continuous_const
  exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

private theorem continuous_weightEquiv_symPower_tprod (v : Fin d → (Fin 2 → ℂ)) :
    Continuous fun g : SU2 ↦ weightEquiv d (symPower d g (⨂ₛ[ℂ] j, v j)) := by
  have hΦ : Continuous
      ((weightEquiv d).toLinearMap.compMultilinearMap (SymmetricPower.tprod ℂ)) :=
    MultilinearMap.continuous_of_finiteDimensional _
  have hv : Continuous fun g : SU2 ↦ fun j ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v j :=
    continuous_pi fun j ↦ continuous_mulVec (v j)
  exact (hΦ.comp hv).congr fun g ↦ by simp

private theorem continuous_weightEquiv_symPower (x : Sym[ℂ]^d(Fin 2 → ℂ)) :
    Continuous fun g : SU2 ↦ weightEquiv d (symPower d g x) := by
  have hb : ∀ i : Fin (d + 1),
      Continuous fun g : SU2 ↦ weightEquiv d (symPower d g (weightBasis d i)) := fun i ↦ by
    obtain ⟨f, hf⟩ := exists_weightBasis_eq_tprod d i
    rw [hf]
    exact continuous_weightEquiv_symPower_tprod d _
  have hx : (fun g : SU2 ↦ weightEquiv d (symPower d g x)) =
      fun g : SU2 ↦ ∑ i, (weightBasis d).repr x i •
        weightEquiv d (symPower d g (weightBasis d i)) := by
    funext g
    calc weightEquiv d (symPower d g x)
        = weightEquiv d (symPower d g (∑ i, (weightBasis d).repr x i • weightBasis d i)) := by
          rw [(weightBasis d).sum_repr x]
      _ = ∑ i, (weightBasis d).repr x i • weightEquiv d (symPower d g (weightBasis d i)) := by
          simp only [map_sum, map_smul]
  rw [hx]
  exact continuous_finsetSum _ fun i _ ↦
    (continuous_const_smul ((weightBasis d).repr x i)).comp (hb i)

/-- **The model action is continuous.** A pure symmetric tensor moves multilinearly in its
factors, and a multilinear map on finite-dimensional spaces is continuous, so the coordinates of
the action are continuous in the group element. -/
theorem continuous_symPowerModel : Continuous (symPowerModel d) :=
  continuous_clm_apply.2 fun y ↦ by
    simpa using continuous_weightEquiv_symPower d ((weightEquiv d).symm y)

/-! ### What the model inherits -/

/-- The model is equivalent to the symmetric power it is transported from. -/
noncomputable def symPowerModelEquiv : (symPower d).Equiv (symPowerModel d).toRepresentation :=
  Representation.Equiv.mk (weightEquiv d) fun g ↦ LinearMap.ext fun v ↦ by
    simp [_root_.ContRepresentation.toMonoidHom_apply]

/-- The equivalence to the model is the weight-basis identification. -/
@[simp]
theorem symPowerModelEquiv_toLinearEquiv :
    (symPowerModelEquiv d).toLinearEquiv = weightEquiv d := by
  rw [symPowerModelEquiv, Representation.Equiv.toLinearEquiv_mk']

@[simp]
theorem symPowerModelEquiv_apply (x : Sym[ℂ]^d(Fin 2 → ℂ)) :
    symPowerModelEquiv d x = weightEquiv d x := by
  rw [symPowerModelEquiv, Representation.Equiv.mk_apply]

/-- The character of the model is the character of the symmetric power: the trace does not see the
transport. -/
@[simp]
theorem character_symPowerModel :
    ContRepresentation.character (symPowerModel d) (continuous_symPowerModel d) =
      symPowerCharacter d :=
  ContinuousMap.ext fun g ↦ by
    rw [symPowerCharacter_apply, Representation.char_iso (symPowerModelEquiv d)]
    exact congrFun (ContRepresentation.coe_character _ _) g

/-- The model is irreducible, being equivalent to `Symᵈ(ℂ²)`. -/
theorem isIrreducible_symPowerModel :
    Representation.IsIrreducible (symPowerModel d).toRepresentation :=
  Representation.isIrreducible_of_linearEquiv (weightEquiv d)
    (fun g v ↦ by simp [_root_.ContRepresentation.toMonoidHom_apply])
    (isIrreducible_symPower d)

/-! ### Exhaustion -/

/-- The unitary case of `TauCeti.SU2.exists_nonempty_equiv_symPower`, which is where the argument
runs; the general case is reduced to it by the unitarian trick. -/
private theorem exists_nonempty_equiv_symPower_of_isUnitary {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (π : ContRepresentation ℂ SU2 V)
    (hπ : Continuous π) (hunitary : ContRepresentation.IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    ∃ d : ℕ, Nonempty ((symPower d).Equiv π.toRepresentation) := by
  by_contra hcon
  have hne : ∀ d : ℕ, ¬ Nonempty ((symPower d).Equiv π.toRepresentation) := fun d h ↦ hcon ⟨d, h⟩
  -- the character of `π` is orthogonal to every character of the family
  have hzero : ∀ d : ℕ, ⟪ContRepresentation.characterLp π hπ,
      ContRepresentation.characterLp (symPowerModel d) (continuous_symPowerModel d)⟫_ℂ = 0 := by
    intro d
    refine ContRepresentation.character_orthonormal_distinct π hπ _ _ hunitary fun f ↦ ?_
    have hempty : IsEmpty (_root_.ContRepresentation.Equiv (symPowerModel d) π) :=
      ⟨fun φ ↦ hne d ⟨(symPowerModelEquiv d).trans
        (ContRepresentation.nonempty_equiv_iff.1 ⟨φ⟩).some⟩⟩
    rw [ContRepresentation.eq_zero_of_isEmpty_equiv (isIrreducible_symPowerModel d) hirr hempty f]
    simp
  -- pairing against that character is a continuous functional killing the span of the family
  let Λ : C(SU2, ℂ) →L[ℂ] ℂ := (innerSL ℂ (ContRepresentation.characterLp π hπ)).comp
    (ContinuousMap.toLp 2 (haarProb SU2) ℂ)
  have hΛ : ∀ F : C(SU2, ℂ), (Λ : C(SU2, ℂ) →ₗ[ℂ] ℂ) F = ⟪ContRepresentation.characterLp π hπ,
        ContinuousMap.toLp 2 (haarProb SU2) ℂ F⟫_ℂ := fun F ↦ by simp [Λ]
  have hspan : characterSpan ≤ LinearMap.ker (Λ : C(SU2, ℂ) →ₗ[ℂ] ℂ) :=
    characterSpan_le_iff.2 fun d ↦ LinearMap.mem_ker.2 <| by
      rw [hΛ, ← character_symPowerModel d,
        ← ContRepresentation.characterLp_def (symPowerModel d) (continuous_symPowerModel d)]
      exact hzero d
  have hclosure : characterSpan.topologicalClosure ≤ LinearMap.ker (Λ : C(SU2, ℂ) →ₗ[ℂ] ℂ) :=
    Submodule.topologicalClosure_minimal _ hspan Λ.isClosed_ker
  -- but that character is a class function, hence in the closure of the span, and has norm one
  have hmem : ContRepresentation.character π hπ ∈ characterSpan.topologicalClosure :=
    mem_topologicalClosure_characterSpan_iff.2 fun u g ↦ by
      simp only [ContRepresentation.coe_character]
      exact Representation.char_conj π.toRepresentation g u
  have hker := LinearMap.mem_ker.1 (hclosure hmem)
  rw [hΛ, ← ContRepresentation.characterLp_def π hπ] at hker
  exact one_ne_zero
    ((ContRepresentation.character_orthonormal_self π hπ hunitary hirr).symm.trans hker)

/-- The inner-product case of `TauCeti.SU2.exists_nonempty_equiv_symPower`, where the characters
live; the general normed case is reduced to it by transport to a Euclidean model.

Suppose not. Then `π` is inequivalent to every `Symᵈ(ℂ²)`, so by Schur's lemma there is no nonzero
intertwiner between them, and the second character orthogonality relation makes the character of
`π` orthogonal in `L²(SU(2))` to every `χ_d`. Pairing with the character of `π` is a *continuous*
functional on `C(SU(2), ℂ)`, so it then kills the whole uniform closure of the span of the `χ_d`,
which by `TauCeti.SU2.mem_topologicalClosure_characterSpan_iff` is all of the continuous class
functions. But the character of `π` is itself a class function, and pairs with itself to `1` by
the first orthogonality relation.

Unitarity is not assumed: Weyl's unitarian trick
(`TauCeti.ContRepresentation.exists_isUnitary_congr`) makes any such representation unitary after
conjugating by an automorphism of the carrier, and the conjugation is an equivalence, so it
changes neither the hypotheses nor the conclusion. -/
private theorem exists_nonempty_equiv_symPower_of_innerProductSpace {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (π : ContRepresentation ℂ SU2 V)
    (hπ : Continuous π) (hirr : Representation.IsIrreducible π.toRepresentation) :
    ∃ d : ℕ, Nonempty ((symPower d).Equiv π.toRepresentation) := by
  obtain ⟨e, he⟩ := ContRepresentation.exists_isUnitary_congr π hπ
  obtain ⟨d, hd⟩ := exists_nonempty_equiv_symPower_of_isUnitary (ContRepresentation.congr e π)
    (ContRepresentation.continuous_congr e hπ) he (ContRepresentation.isIrreducible_congr e hirr)
  refine ⟨d, ⟨hd.some.trans (Representation.Equiv.mk (e.symm : V ≃ₗ[ℂ] V) fun g ↦ ?_)⟩⟩
  exact LinearMap.ext fun v ↦ by
    simp [_root_.ContRepresentation.toMonoidHom_apply]

/-- **The symmetric powers exhaust the irreducibles of `SU(2)`.** Every finite-dimensional
irreducible continuous representation of `SU(2)` is equivalent to `Symᵈ(ℂ²)` for some `d`.

Neither an inner product nor unitarity is assumed of the carrier. A finite-dimensional normed
space over `ℂ` is continuously linearly equivalent to `ℂ^{dim V}` by dimension count, and
transporting `π` along that equivalence changes neither the hypotheses nor the conclusion, so the
argument may be run on a Euclidean carrier, where the characters live; there Weyl's unitarian
trick disposes of unitarity in the same way. -/
theorem exists_nonempty_equiv_symPower {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (π : ContRepresentation ℂ SU2 V) (hπ : Continuous π)
    (hirr : Representation.IsIrreducible π.toRepresentation) :
    ∃ d : ℕ, Nonempty ((symPower d).Equiv π.toRepresentation) := by
  let e : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  obtain ⟨d, hd⟩ := exists_nonempty_equiv_symPower_of_innerProductSpace
    (ContRepresentation.congr e π) (ContRepresentation.continuous_congr e hπ)
    (ContRepresentation.isIrreducible_congr e hirr)
  refine ⟨d, ⟨hd.some.trans (Representation.Equiv.mk
    (e.symm : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) ≃ₗ[ℂ] V) fun g ↦ ?_)⟩⟩
  exact LinearMap.ext fun v ↦ by
    simp [_root_.ContRepresentation.toMonoidHom_apply]

/-- **The classification of the irreducible representations of `SU(2)`.** A finite-dimensional
irreducible continuous representation of `SU(2)` is `Symᵈ(ℂ²)` for exactly one `d`, so
`d ↦ Symᵈ(ℂ²)` is a bijection from `ℕ` onto the isomorphism classes. Exhaustion is
`TauCeti.SU2.exists_nonempty_equiv_symPower` and uniqueness is
`TauCeti.SU2.nonempty_equiv_symPower_iff`. -/
theorem existsUnique_nonempty_equiv_symPower {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] (π : ContRepresentation ℂ SU2 V)
    (hπ : Continuous π) (hirr : Representation.IsIrreducible π.toRepresentation) :
    ∃! d : ℕ, Nonempty ((symPower d).Equiv π.toRepresentation) := by
  obtain ⟨d, hd⟩ := exists_nonempty_equiv_symPower π hπ hirr
  exact ⟨d, hd, fun e he ↦ (nonempty_equiv_symPower_iff (d := e) d).1
    ⟨he.some.trans hd.some.symm⟩⟩

end SU2

end TauCeti
