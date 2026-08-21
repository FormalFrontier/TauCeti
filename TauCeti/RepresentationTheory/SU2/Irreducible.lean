/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Coordinates
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.SU2.Weight

/-!
# The symmetric powers of the standard representation of `SU(2)` are irreducible

`TauCeti/RepresentationTheory/SU2/Weight.lean` decomposes `Symᵈ(ℂ²)` under the maximal torus: the
monomial basis `TauCeti.SU2.weightBasis` consists of weight vectors, the `d + 1` weights are
pairwise distinct, and consequently a torus-stable subspace is spanned by the weight vectors it
contains.  That is one half of the highest-weight argument; this file supplies the other half and
concludes that `Symᵈ(ℂ²)` is an **irreducible** representation of `SU(2)`, for every `d`.

The torus alone cannot see irreducibility: it is abelian, and every span of weight vectors is
torus-stable.  What breaks the weight vectors apart is a single element of `SU(2)` off the torus.
Fix the rotation `u = !![3/5, -4/5; 4/5, 3/5]`, an element of `SU(2)` **none of whose entries
vanishes**, and let `W ≠ 0` be an invariant subspace.  Then:

* `W` is torus-stable, so it contains some weight vector, `TauCeti.SU2.weightBasis d i`.
* The coordinate of `u · (weight vector)` at the **highest** weight is a product of entries of `u`,
  one for each tensor factor, hence nonzero: the highest weight is indexed by a *constant*
  unordered tuple, and only the constant ordered tuple orders it, so the coordinate is the single
  product `∏ⱼ u₀,ₖⱼ` with no cancellation
  (`SymmetricPower.repr_basis_symmetricPower_tprod_ofFn_const`).  Torus-stability then puts the
  highest weight vector `e₀^d` into `W`.
* `u · e₀^d` is the **pure power** `(u e₀)^d`, and a pure power of a vector with nonzero
  coordinates has *every* coordinate nonzero
  (`SymmetricPower.repr_basis_symmetricPower_tprod_const_ne_zero`); the terms of the coordinate sum
  all coincide, so again nothing cancels.  Torus-stability now puts **every** weight vector into
  `W`, so `W` is everything.

The choice of `u` matters only through the non-vanishing of its four entries, and the rational
rotation is taken to keep that check arithmetic.  It is a device of the proof and stays private to
this file, as `TauCeti.SU2.genericTorus` does in the weight file.

## Main results

* `TauCeti.SU2.isIrreducible_symPower`: `Symᵈ(ℂ²)` is an irreducible representation of `SU(2)`.
* `TauCeti.SU2.nonempty_equiv_symPower_iff`: two of them are equivalent exactly when they have the
  same degree, so the `Symᵈ(ℂ²)` are pairwise inequivalent.

Exhaustion -- that every finite-dimensional irreducible representation of `SU(2)` is one of these
-- is *not* proved here; it is the remaining half of the classification.

## References

This is the "the `su2Irrep n` are irreducible, pairwise inequivalent" half of the classification
asked for by the `SU(2)` engine case of
`TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md`, which insists that the
classification be proved by the weight/highest-weight argument rather than read off Peter-Weyl.

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 3.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §5.
-/

public section

open Finset Matrix Module
open scoped TensorProduct

namespace TauCeti

namespace SU2

variable (d : ℕ)

/-! ### A rotation with no zero entry -/

/-- **The separating element of the proof**: the rotation `!![3/5, -4/5; 4/5, 3/5]`, an element of
`SU(2)` none of whose entries vanishes.  Only that non-vanishing is used; the rational entries
keep the check that it lies in `SU(2)` arithmetic. -/
private noncomputable def mixMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 / 5, -(4 / 5); 4 / 5, 3 / 5]

private theorem mixMatrix_apply_ne_zero (i j : Fin 2) : mixMatrix i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [mixMatrix]

private theorem mixMatrix_mem : mixMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mixMatrix, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] <;> norm_num
  · rw [mixMatrix, Matrix.det_fin_two_of]
    norm_num

/-- The rotation `TauCeti.SU2.mixMatrix`, as an element of `SU(2)`. -/
private noncomputable def mixElement : SU2 := ⟨mixMatrix, mixMatrix_mem⟩

/-- The matrix underlying `TauCeti.SU2.mixElement`. -/
private theorem coe_mixElement :
    (mixElement : Matrix (Fin 2) (Fin 2) ℂ) = mixMatrix := (rfl)

/-- The rotation acts on a pure symmetric tensor factor by factor. -/
private theorem symPower_mixElement_tprod (v : Fin d → (Fin 2 → ℂ)) :
    symPower d mixElement (⨂ₛ[ℂ] i, v i) = ⨂ₛ[ℂ] i, mixMatrix *ᵥ v i := by
  simp only [symPower_apply, symPowerRep, Representation.symmetricPower_apply_tprod,
    stdRep_apply_apply, coe_toGL, coe_mixElement]

/-- The coordinates of the image of a standard basis vector are the entries of the matrix. -/
private theorem repr_mulVec_basisFun (A : Matrix (Fin 2) (Fin 2) ℂ) (k l : Fin 2) :
    (Pi.basisFun ℂ (Fin 2)).repr (A *ᵥ Pi.basisFun ℂ (Fin 2) k) l = A l k := by
  simp [Matrix.mulVec_single]

/-! ### The weight basis as the monomial basis -/

/-- The weight basis is the monomial basis of `Symᵈ(ℂ²)` reindexed by the number of factors equal
to the first standard basis vector; this is `TauCeti.SU2.weightBasis_apply` promoted from the
basis vectors to the basis itself, so that coordinates may be compared. -/
private theorem weightBasis_eq_reindex :
    weightBasis d = ((Pi.basisFun ℂ (Fin 2)).symmetricPower d).reindex (symFinTwoEquiv d) :=
  DFunLike.coe_injective (funext fun i => (weightBasis_apply d i).trans
    (Basis.reindex_apply _ _ i).symm)

/-- The index of the highest weight is the constant unordered tuple `(0, …, 0)`: the monomial that
is the `d`-th power of the first standard basis vector. -/
private theorem symFinTwoEquiv_symm_last :
    (symFinTwoEquiv d).symm (Fin.last d) = TauCeti.Sym.ofFn fun _ : Fin d => (0 : Fin 2) := by
  refine Sym.coe_injective ?_
  rw [coe_symFinTwoEquiv_symm_apply, TauCeti.Sym.coe_ofFn, List.ofFn_const, Multiset.coe_replicate]
  simp

/-- Every weight vector is a pure symmetric tensor of standard basis vectors. -/
private theorem exists_weightBasis_eq_tprod (i : Fin (d + 1)) :
    ∃ f : Fin d → Fin 2, weightBasis d i = ⨂ₛ[ℂ] j, Pi.basisFun ℂ (Fin 2) (f j) := by
  obtain ⟨f, hf⟩ := TauCeti.Sym.ofFn_surjective ((symFinTwoEquiv d).symm i)
  exact ⟨f, by rw [weightBasis_apply, ← hf, Basis.symmetricPower_apply,
    SymmetricPower.tprodOfSym_ofFn]⟩

/-! ### The rotated weight vectors have nonzero coordinates -/

/-- **The image of a weight vector has a nonzero coordinate at the highest weight.**  The highest
weight is indexed by a constant unordered tuple, whose only ordering is the constant one, so that
coordinate is a single product of entries of `TauCeti.SU2.mixMatrix`, and no entry vanishes.  The
image itself is of course not a weight vector, only a combination with this coordinate nonzero. -/
private theorem repr_symPower_mixElement_weightBasis_last_ne_zero (i : Fin (d + 1)) :
    (weightBasis d).repr (symPower d mixElement (weightBasis d i)) (Fin.last d) ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_weightBasis_eq_tprod d i
  rw [hf, weightBasis_eq_reindex, Basis.repr_reindex_apply, symFinTwoEquiv_symm_last,
    symPower_mixElement_tprod, SymmetricPower.repr_basis_symmetricPower_tprod_ofFn_const]
  exact Finset.prod_ne_zero_iff.2 fun j _ => by
    rw [repr_mulVec_basisFun]; exact mixMatrix_apply_ne_zero 0 (f j)

/-- **The image of the highest weight vector has a nonzero coordinate at every weight.**  That
image is the pure power `(u e₀)^d`, and every coordinate of a pure power of a vector with nonzero
coordinates is nonzero. -/
private theorem repr_symPower_mixElement_weightBasis_last_ne_zero' (i : Fin (d + 1)) :
    (weightBasis d).repr (symPower d mixElement (weightBasis d (Fin.last d))) i ≠ 0 := by
  have hf : weightBasis d (Fin.last d) =
      ⨂ₛ[ℂ] (_ : Fin d), Pi.basisFun ℂ (Fin 2) 0 := by
    rw [weightBasis_apply, symFinTwoEquiv_symm_last, Basis.symmetricPower_apply,
      SymmetricPower.tprodOfSym_ofFn]
  rw [hf, weightBasis_eq_reindex, Basis.repr_reindex_apply, symPower_mixElement_tprod]
  exact SymmetricPower.repr_basis_symmetricPower_tprod_const_ne_zero _
    (fun l => by rw [repr_mulVec_basisFun]; exact mixMatrix_apply_ne_zero l 0) _

/-! ### Irreducibility -/

/-- **The symmetric powers of the standard representation of `SU(2)` are irreducible.**  A nonzero
invariant subspace is torus-stable, hence spanned by the weight vectors it contains.  The image
under the rotation `TauCeti.SU2.mixMatrix` of one of those weight vectors has a nonzero coordinate
at the highest weight, which puts the highest weight vector in the subspace; the image of the
highest weight vector in turn has a nonzero coordinate at *every* weight, which puts every weight
vector in the subspace.  So the subspace is everything.

This is the highest-weight half of the classification of the irreducibles of `SU(2)`; the
character orthonormality of `TauCeti/RepresentationTheory/SU2/Weyl/Orthogonality.lean` validates
it but does not prove it. -/
theorem isIrreducible_symPower : Representation.IsIrreducible (symPower d) := by
  have hnt : Nontrivial (Sym[ℂ]^d(Fin 2 → ℂ)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_symPower]; omega)
  have hntsub : Nontrivial (Subrepresentation (symPower d)) := by
    refine ⟨⊥, ⊤, fun hbot => absurd (congrArg Subrepresentation.toSubmodule hbot) ?_⟩
    rw [Subrepresentation.toSubmodule_bot, Subrepresentation.toSubmodule_top]
    exact bot_ne_top
  refine { eq_bot_or_eq_top := fun σ => ?_ }
  rcases eq_or_ne σ ⊥ with hσ | hσ
  · exact Or.inl hσ
  refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
  rw [Subrepresentation.toSubmodule_top]
  have hW : ∀ (z : Circle) (v : Sym[ℂ]^d(Fin 2 → ℂ)), v ∈ σ.toSubmodule →
      symPower d (torusHom z) v ∈ σ.toSubmodule :=
    fun z _ hv => σ.apply_mem_toSubmodule (torusHom z) hv
  -- a nonzero invariant subspace contains a weight vector
  have hex : ∃ i, weightBasis d i ∈ σ.toSubmodule := by
    by_contra hcon
    -- otherwise the set of weight vectors lying in `σ`, which spans it, is empty
    have hempty : {v : Sym[ℂ]^d(Fin 2 → ℂ) | ∃ i, weightBasis d i = v ∧ v ∈ σ.toSubmodule} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (by rintro v ⟨i, rfl, hv⟩; exact hcon ⟨i, hv⟩)
    refine hσ (Subrepresentation.toSubmodule_injective ?_)
    rw [Subrepresentation.toSubmodule_bot, eq_span_weightBasis_mem hW, hempty,
      Submodule.span_empty]
  -- the image of that weight vector reaches the highest weight, and its image reaches every weight
  obtain ⟨i, hi⟩ := hex
  have hlast : weightBasis d (Fin.last d) ∈ σ.toSubmodule :=
    weightBasis_mem_of_repr_ne_zero hW (σ.apply_mem_toSubmodule mixElement hi)
      (repr_symPower_mixElement_weightBasis_last_ne_zero d i)
  have hall : ∀ i, weightBasis d i ∈ σ.toSubmodule := fun i =>
    weightBasis_mem_of_repr_ne_zero hW (σ.apply_mem_toSubmodule mixElement hlast)
      (repr_symPower_mixElement_weightBasis_last_ne_zero' d i)
  rw [eq_top_iff, ← (weightBasis d).span_eq]
  exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hall i)

/-- **The symmetric powers are pairwise inequivalent**: they are equivalent exactly when they have
the same degree, their dimensions `d + 1` being distinct.  With
`TauCeti.SU2.isIrreducible_symPower` this exhibits `Symᵈ(ℂ²)` as a family of pairwise
non-isomorphic irreducibles of `SU(2)`, one in each dimension. -/
@[simp]
theorem nonempty_equiv_symPower_iff (e : ℕ) :
    Nonempty ((symPower d).Equiv (symPower e)) ↔ d = e := by
  refine ⟨fun ⟨f⟩ => ?_, fun h => h ▸ ⟨Representation.Equiv.refl _⟩⟩
  have hrank : Module.finrank ℂ (Sym[ℂ]^d(Fin 2 → ℂ)) = Module.finrank ℂ (Sym[ℂ]^e(Fin 2 → ℂ)) :=
    f.toLinearEquiv.finrank_eq
  rw [finrank_symPower, finrank_symPower] at hrank
  omega

end SU2

end TauCeti
