/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight
public import Mathlib.Algebra.Lie.LieTheorem
public import Mathlib.Algebra.Lie.Sl2
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# Every finite-dimensional `gl n`-module has a dominant highest weight vector

Let `K` be a field of characteristic zero and let `M` be a nonzero finite-dimensional module over
`gl n K = Matrix n n K`. This file proves that `M` carries a highest weight vector for the matrix
unit positive system, and that the weight of any highest weight vector of a finite-dimensional
module is dominant integral. Read for an irreducible `M`, the two statements say that every
finite-dimensional irreducible `gl n`-module has a dominant highest weight, which is the existence
half of the classification of the irreducibles of `gl n`.

## The argument

Existence is Lie's theorem followed by a maximality argument, and both halves are needed. Lie's
theorem is applied to the *abelian* diagonal Cartan subalgebra rather than to the Borel subalgebra
of upper triangular matrices, which is the other classical route: a common eigenvector of the
Borel is a highest weight vector outright, but that route first needs the Borel to be solvable and
its derived subalgebra to contain the raising matrix units, neither of which is available.

The diagonal Cartan subalgebra is abelian, hence solvable, so over an algebraically closed field
Lie's theorem (`LieModule.exists_nontrivial_weightSpace_of_isSolvable`) produces a nonzero
simultaneous eigenvector of the diagonal matrix units. Algebraic closure is not a convenience
here: over `ℝ` a simultaneous eigenvector need not exist at all. Neither may one replace this step
by the argument used for a semisimple Lie algebra, where the generalized weight spaces are refined
to honest eigenspaces once and for all: `gl 1` acting on `K²` by a nilpotent Jordan block is a
finite-dimensional module on which the Cartan subalgebra does not act semisimply, so a highest
weight vector has to be produced one vector at a time rather than as a whole weight space.

Such an eigenvector need not be annihilated by the raising matrix units, and the second half of
the argument moves it up until it is. Bracketing with `Eₚq` sends an eigenvector of weight `μ` to
an eigenvector of weight `μ + εₚ - ε_q`, so, writing `ht μ` for the value of `μ` on the fixed
diagonal matrix `∑ i, -i · Eᵢᵢ`, one raising step with `p < q` increases `ht` by the positive
natural number `q - p`. All the vectors so produced are eigenvectors of a *single* operator, the
action of that fixed diagonal matrix, with pairwise distinct eigenvalues, so there are only
finitely many of them: the set of naturals `m` for which an eigenvector of `ht`-value `ht μ₀ + m`
exists is finite. A vector realizing its greatest element is moved by no raising operator, which
is exactly a highest weight vector.

Dominance is the rank-one reduction. For `p < q` the matrix units `Eₚq`, `E_qp` and their
commutator `Eₚₚ - E_qq` form an `sl₂` triple, and a highest weight vector is a primitive vector
for it with eigenvalue `μ p - μ q`; Mathlib's `IsSl2Triple.HasPrimitiveVectorWith.exists_nat` then
makes that eigenvalue a natural number. Only finite-dimensionality of `M` is used, so dominance
needs neither irreducibility nor an algebraically closed field.

## Main results

* `TauCeti.exists_isGlHighestWeightVector`: a nonzero finite-dimensional module over `gl n K`, for
  `K` algebraically closed of characteristic zero, has a highest weight vector.
* `TauCeti.IsGlHighestWeightVector.isGlDominantIntegral`: the weight of a highest weight vector in
  a finite-dimensional `gl n K`-module is dominant integral.
* `TauCeti.lie_single_self_lie_single_eq_smul`: bracketing with a matrix unit shifts the weight of
  a simultaneous eigenvector of the diagonal.
* `TauCeti.exists_isGlHighestWeightVector_and_isGlDominantIntegral`: the two main results
  together.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991), §15.
* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255 (2009),
  Chapter 5.

This is the first target of the "classification and the named carrier" item of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: *"Every finite-dimensional
`gl_n`-irreducible has a dominant highest weight"*.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

/-! ### Simultaneous eigenvectors of the diagonal -/

section Eigenvector

variable {K : Type u} [Field K] {n : Type v} [Fintype n] [DecidableEq n]
variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule (Matrix n n K) M]
  [LieModule K (Matrix n n K) M]

/-- **Lie's theorem for the diagonal Cartan subalgebra**: over an algebraically closed field of
characteristic zero a nonzero finite-dimensional `gl n`-module has a nonzero simultaneous
eigenvector of the diagonal matrix units.

The eigenvector is not asserted to be annihilated by the raising matrix units; that is what
`TauCeti.exists_isGlHighestWeightVector` adds. -/
theorem exists_ne_zero_forall_lie_single_self_eq_smul [CharZero K] [IsAlgClosed K]
    [FiniteDimensional K M] [Nontrivial M] :
    ∃ (mu : n → K) (v : M), v ≠ 0 ∧ ∀ i : n, ⁅(single i i 1 : Matrix n n K), v⁆ = mu i • v := by
  obtain ⟨chi, hchi⟩ :=
    LieModule.exists_nontrivial_weightSpace_of_isSolvable K (diagonalCartan K n) M
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : LieModule.weightSpace M chi)
  have hv0' : v ≠ 0 := by simpa [Submodule.mk_eq_zero] using hv0
  refine ⟨(glWeightEquiv K n).symm chi, v, hv0', fun i => ?_⟩
  have h := (LieModule.mem_weightSpace _ _).mp hv
    ⟨single i i 1, single_self_mem_diagonalCartan i 1⟩
  have hchi' : chi ⟨single i i 1, single_self_mem_diagonalCartan i 1⟩
      = ((glWeightEquiv K n).symm chi) i := by
    conv_lhs => rw [← (glWeightEquiv K n).apply_symm_apply chi]
    rw [glWeightEquiv_apply]
    simp [single_apply, Finset.sum_ite_eq]
  rw [LieSubalgebra.coe_bracket_of_module, hchi'] at h
  exact h

/-- **Raising a weight vector.** Bracketing a simultaneous eigenvector of the diagonal matrix units
of weight `μ` with the matrix unit `Eₚq` gives a simultaneous eigenvector of weight
`μ + εₚ - ε_q`, whenever the result is nonzero. -/
theorem lie_single_self_lie_single_eq_smul {mu : n → K} {v : M}
    (hv : ∀ i : n, ⁅(single i i 1 : Matrix n n K), v⁆ = mu i • v) (p q : n) (i : n) :
    ⁅(single i i 1 : Matrix n n K), ⁅(single p q 1 : Matrix n n K), v⁆⁆
      = (mu + (Pi.single p 1 - Pi.single q 1) : n → K) i •
        ⁅(single p q 1 : Matrix n n K), v⁆ := by
  have hpp : (single i i (1 : K)) p p = (Pi.single p 1 : n → K) i := by
    simp [single_apply, Pi.single_apply, eq_comm]
  have hqq : (single i i (1 : K)) q q = (Pi.single q 1 : n → K) i := by
    simp [single_apply, Pi.single_apply, eq_comm]
  have hlie : ⁅(single i i 1 : Matrix n n K), (single p q 1 : Matrix n n K)⁆
      = ((Pi.single p 1 : n → K) i - (Pi.single q 1 : n → K) i) • single p q 1 := by
    rw [lie_single_of_mem_diagonalCartan (single_self_mem_diagonalCartan i 1) p q 1, hpp, hqq]
  rw [leibniz_lie, hlie, smul_lie, hv i, lie_smul]
  simp only [Pi.add_apply, Pi.sub_apply, add_smul, sub_smul]
  abel

end Eigenvector

/-! ### Existence of a highest weight vector -/

section Existence

variable {K : Type u} [Field K] {N : ℕ}
variable {M : Type w} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M] [LieModule K (Matrix (Fin N) (Fin N) K) M]

variable (K N) in
/-- The diagonal matrix `∑ i, -i · Eᵢᵢ`. A raising step strictly increases the value of a weight
on it, which is what makes the maximality argument of
`TauCeti.exists_isGlHighestWeightVector` terminate. -/
private noncomputable def heightMatrix : Matrix (Fin N) (Fin N) K :=
  ∑ i : Fin N, (-((i : ℕ) : K)) • single i i 1

/-- The value of a weight on `TauCeti.heightMatrix`. -/
private def glHeight (mu : Fin N → K) : K := ∑ i : Fin N, (-((i : ℕ) : K)) * mu i

private theorem glHeight_add (mu nu : Fin N → K) :
    glHeight (mu + nu) = glHeight mu + glHeight nu := by
  simp only [glHeight, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

private theorem glHeight_sub (mu nu : Fin N → K) :
    glHeight (mu - nu) = glHeight mu - glHeight nu := by
  simp only [glHeight, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem glHeight_single (p : Fin N) (c : K) :
    glHeight (Pi.single p c) = -((p : ℕ) : K) * c := by
  rw [glHeight, Finset.sum_eq_single p (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
    (fun h => absurd (Finset.mem_univ p) h), Pi.single_eq_same]

private theorem glHeight_single_sub_single {p q : Fin N} (hpq : p < q) :
    glHeight (Pi.single p (1 : K) - Pi.single q 1) = (((q : ℕ) - (p : ℕ) : ℕ) : K) := by
  rw [glHeight_sub, glHeight_single, glHeight_single,
    Nat.cast_sub (le_of_lt (Fin.lt_def.mp hpq))]
  ring

private theorem lie_heightMatrix_eq_smul {mu : Fin N → K} {v : M}
    (hv : ∀ i : Fin N, ⁅(single i i 1 : Matrix (Fin N) (Fin N) K), v⁆ = mu i • v) :
    ⁅heightMatrix K N, v⁆ = glHeight mu • v := by
  rw [heightMatrix, sum_lie, glHeight, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_lie, hv i, smul_smul]

/-- **Existence of a highest weight vector for `gl n`.** Over an algebraically closed field of
characteristic zero every nonzero finite-dimensional `gl N`-module has a highest weight vector for
the matrix unit positive system.

Neither irreducibility nor a choice of generator is assumed; for irreducible `M` this is the
existence half of the classification of the finite-dimensional irreducibles of `gl N`. -/
theorem exists_isGlHighestWeightVector [CharZero K] [IsAlgClosed K] [FiniteDimensional K M]
    [Nontrivial M] : ∃ (mu : Fin N → K) (v : M), IsGlHighestWeightVector mu v := by
  classical
  obtain ⟨mu₀, v₀, hv₀, hmu₀⟩ :=
    exists_ne_zero_forall_lie_single_self_eq_smul (K := K) (n := Fin N) (M := M)
  -- The naturals by which the height of a weight vector can exceed that of the starting one.
  set S : Set ℕ := {m | ∃ (mu : Fin N → K) (v : M), v ≠ 0 ∧
    (∀ i : Fin N, ⁅(single i i 1 : Matrix (Fin N) (Fin N) K), v⁆ = mu i • v) ∧
    glHeight mu = glHeight mu₀ + m}
  have hmem : ∀ m : S, ∃ (mu : Fin N → K) (v : M), v ≠ 0 ∧
      (∀ i : Fin N, ⁅(single i i 1 : Matrix (Fin N) (Fin N) K), v⁆ = mu i • v) ∧
      glHeight mu = glHeight mu₀ + ((m : ℕ) : K) := fun m => m.2
  choose weight vec hvec0 hveceig hvecht using hmem
  -- Those vectors are eigenvectors of one operator, with pairwise distinct eigenvalues.
  set T := LieModule.toEnd K (Matrix (Fin N) (Fin N) K) M (heightMatrix K N) with hT
  have hinj : Function.Injective fun m : S => glHeight mu₀ + ((m : ℕ) : K) := by
    intro a b hab
    exact Subtype.ext (by exact_mod_cast add_right_injective (glHeight mu₀) hab)
  have heig : ∀ m : S, T.HasEigenvector (glHeight mu₀ + ((m : ℕ) : K)) (vec m) :=
    fun m => ⟨Module.End.mem_eigenspace_iff.2
      (by simpa [hT, ← hvecht m] using lie_heightMatrix_eq_smul (hveceig m)), hvec0 m⟩
  have _i : Finite S := (T.eigenvectors_linearIndependent' _ hinj _ heig).finite
  -- So `S` has a greatest element, and its weight vector cannot be raised.
  have hne : S.Nonempty := ⟨0, mu₀, v₀, hv₀, hmu₀, by simp⟩
  have hbdd : BddAbove S := Set.Finite.bddAbove (Set.toFinite S)
  have hmS : sSup S ∈ S := Nat.sSup_mem hne hbdd
  refine ⟨weight ⟨_, hmS⟩, vec ⟨_, hmS⟩, isGlHighestWeightVector_iff.mpr
    ⟨hvec0 ⟨_, hmS⟩, hveceig ⟨_, hmS⟩, fun p q hpq => ?_⟩⟩
  by_contra hraise
  have hstep : sSup S + ((q : ℕ) - (p : ℕ)) ∈ S :=
    ⟨weight ⟨_, hmS⟩ + (Pi.single p 1 - Pi.single q 1), _, hraise,
      fun i => lie_single_self_lie_single_eq_smul (hveceig ⟨_, hmS⟩) p q i, by
        rw [glHeight_add, glHeight_single_sub_single hpq, hvecht ⟨_, hmS⟩]
        push_cast
        ring⟩
  have hlt : 0 < (q : ℕ) - (p : ℕ) := by
    have := Fin.lt_def.mp hpq
    omega
  have := le_csSup hbdd hstep
  omega

end Existence

/-! ### Dominance of the highest weight -/

section Dominant

variable {K : Type u} [Field K] [CharZero K] {N : ℕ}
variable {M : Type w} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M] [LieModule K (Matrix (Fin N) (Fin N) K) M]
variable {mu : Fin N → K} {v : M}

/-- **The `sl₂` triple of a pair of indices in `gl n`.** For `p ≠ q` the matrix units `Eₚq` and
`E_qp` together with their commutator `Eₚₚ - E_qq` satisfy the `sl₂` relations; this is the
rank-one subalgebra of `gl n` along which dominance is read off.

It is the standard triple `TauCeti.isSl2Triple_single` of `sl n K`, pushed forward along the
inclusion of `sl n K` in `gl n K`. -/
theorem isSl2Triple_matrix_single (p q : Fin N) (hpq : p ≠ q) :
    IsSl2Triple (single p p (1 : K) - single q q 1) (single p q (1 : K)) (single q p 1) := by
  have hne : (LieAlgebra.SpecialLinear.sl (Fin N) K).incl
      (LieAlgebra.SpecialLinear.singleSubSingle p q 1) ≠ 0 := fun hzero =>
    singleSubSingle_ne_zero hpq one_ne_zero (Subtype.ext (by simpa using hzero))
  simpa [LieAlgebra.SpecialLinear.val_single,
    LieAlgebra.SpecialLinear.val_singleSubSingle] using
    (isSl2Triple_single (R := K) hpq).map (LieAlgebra.SpecialLinear.sl (Fin N) K).incl hne

/-- **The weight of a highest weight vector is dominant integral.** Restricting to the `sl₂` triple
of a pair `p < q` makes the highest weight vector a primitive vector of eigenvalue `μ p - μ q`, and
the eigenvalue of a primitive vector in a finite-dimensional module is a natural number.

Neither irreducibility of `M` nor algebraic closure of `K` is used. -/
theorem IsGlHighestWeightVector.isGlDominantIntegral [FiniteDimensional K M]
    (hv : IsGlHighestWeightVector mu v) : IsGlDominantIntegral mu := by
  rw [isGlDominantIntegral_iff_forall_le]
  intro p q hpq
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact ⟨0, by simp⟩
  have hprim : (isSl2Triple_matrix_single (K := K) p q hlt.ne).HasPrimitiveVectorWith v
      (mu p - mu q) := by
    refine ⟨hv.ne_zero, ?_, hv.lie_single_eq_zero hlt⟩
    rw [sub_lie, hv.lie_single_self_eq_smul, hv.lie_single_self_eq_smul, sub_smul]
  exact hprim.exists_nat

/-- **Every nonzero finite-dimensional `gl N`-module has a dominant highest weight vector.** Over
an algebraically closed field of characteristic zero, combining the existence of a highest weight
vector with the dominance of its weight.

For an irreducible `M` this is the statement that a finite-dimensional irreducible `gl N`-module
has a dominant highest weight, the first half of the classification of the irreducibles of
`gl N`. -/
theorem exists_isGlHighestWeightVector_and_isGlDominantIntegral [IsAlgClosed K]
    [FiniteDimensional K M] [Nontrivial M] :
    ∃ (mu : Fin N → K) (v : M), IsGlHighestWeightVector mu v ∧ IsGlDominantIntegral mu := by
  obtain ⟨mu, v, hv⟩ := exists_isGlHighestWeightVector (K := K) (N := N) (M := M)
  exact ⟨mu, v, hv, hv.isGlDominantIntegral⟩

end Dominant

end TauCeti
