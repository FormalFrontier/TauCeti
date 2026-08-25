/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The Casimir element of a universal enveloping algebra

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ` is
nondegenerate.  Choosing a basis `x₁, …, xₙ` of `L` and the basis `y₁, …, yₙ` dual to it under `κ`,
the **Casimir element** is

`Ω = ∑ᵢ xᵢ yᵢ ∈ U(L)`,

a distinguished element of the universal enveloping algebra.  In the classical setting of a split
semisimple Lie algebra in characteristic zero it is the source of Weyl's complete reducibility
theorem: it is central, so it acts on any module by a module endomorphism, and on a highest weight
module by a scalar that separates the trivial module from the others.  Those extra hypotheses are
needed only for that application; centrality, the statement proved here, needs nothing beyond a
nondegenerate Killing form.

Two facts make `Ω` an invariant of `L` rather than of the chosen basis, and both are proved here.

* `Ω` does not depend on the basis.  The mechanism is `TauCeti.sum_apply_killingDualBasis_eq`:
  for *every* `K`-bilinear map `f` out of `L × L`, the value `∑ᵢ f xᵢ yᵢ` is the same for all
  bases, because expanding one basis in the other exchanges the two dual bases.  The Casimir
  element is the instance `f x y = x * y` in `U(L)`, so `TauCeti.casimirElement_eq_sum` computes
  it from any basis at all, and the chosen basis in the definition is immaterial.
* `Ω` is central (`TauCeti.casimirElement_mem_center`).  The same bilinear mechanism gives
  `TauCeti.sum_apply_lie_killingDualBasis_add_eq_zero`, the statement that the element
  `∑ᵢ xᵢ ⊗ yᵢ` is annihilated by the adjoint action of `L`; this is exactly the invariance
  `κ ⁅z, x⁆ y = -κ x ⁅z, y⁆` of the Killing form, summed.  Feeding it the commutator identity
  `ι z * ι x - ι x * ι z = ι ⁅z, x⁆` turns it into `ι z * Ω = Ω * ι z`, and the canonical Lie
  generators generate `U(L)` (`TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι`), so `Ω`
  commutes with everything.

Only nondegeneracy, symmetry and invariance of the Killing form are used, so the argument below
would go through for any invariant nondegenerate symmetric form once the definitions and lemmas
are parameterised by such a form; as written they are stated for the Killing form, which is the
canonical choice this development needs and the one the roadmap pins.

## Main definitions

* `TauCeti.killingDualBasis`: the basis dual to a given one under the Killing form.
* `TauCeti.casimirElement`: the Casimir element of `U(L)`.

## Main results

* `TauCeti.sum_killingForm_killingDualBasis_eq_trace`: the sum `∑ᵢ κ (p xᵢ) yᵢ` is the trace of the
  endomorphism `p`.
* `TauCeti.sum_apply_killingDualBasis_of_isAdjointPair`: a pair of endomorphisms adjoint for the
  Killing form may be moved from the first slot of `f` to the second.
* `TauCeti.casimirElement_eq_sum`: the Casimir element is `∑ᵢ xᵢ yᵢ` for **any** basis `x` of `L`
  and its Killing-dual basis `y`, so the basis chosen in the definition does not matter.
* `TauCeti.representation_casimirElement_apply_eq_zero_of_isTrivial`: the Casimir element acts by
  zero on a module with trivial Lie action.
* `TauCeti.ι_mul_casimirElement`: the Casimir element commutes with every canonical Lie generator.
* `TauCeti.casimirElement_mem_center`: **the Casimir element is central in `U(L)`.**

The remaining statement about `casimirElement`, that it acts on a highest weight module of weight
`λ` by the scalar `⟨λ + ρ, λ + ρ⟩ - ⟨ρ, ρ⟩`, is not proved here but in
`TauCeti/Algebra/Lie/HighestWeight/Casimir.lean`, which is where the highest weight vectors and the
invariant form on weights that it is phrased in are available.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*, Chapter I, §3, no. 7 ("Casimir
  element"), Proposition 11: given an invariant bilinear form whose restriction to an ideal `a` is
  nondegenerate, the element `c = Σᵢ eᵢ eᵢ'` built from a basis of `a` and the dual basis of `a`
  is independent of that basis and commutes with the whole Lie algebra.  Taking `a` to be all of
  `L` and the form to be the Killing form gives the two statements proved here; Bourbaki is
  strictly more general, since the form may be degenerate on `L` and the sum then runs over a basis
  of the proper ideal `a`, which is beyond the generality noted above.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §6.2, which builds
  the Casimir element of the trace form of a faithful representation of a semisimple Lie algebra;
  the Killing form is the case of the adjoint representation.
* [Highest weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 5, "The Casimir element".
-/

public section

open Finset LieAlgebra LieModule UniversalEnvelopingAlgebra

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L]

/-! ### The Killing-dual basis -/

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [LieAlgebra.IsKilling K L] in
/-- The Killing form is symmetric, in the bundled `LinearMap.BilinForm.IsSymm` form that the
dual-basis API asks for; Mathlib supplies it as the unbundled `LieModule.traceForm_isSymm`. -/
private theorem killingForm_isSymm : (killingForm K L).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ LieModule.traceForm_comm K L L x y

/-- The basis of `L` **dual to `b` under the Killing form**: `κ (b i) (killingDualBasis b j)` is
`1` when `i = j` and `0` otherwise (`TauCeti.killingForm_killingDualBasis`). -/
noncomputable def killingDualBasis (b : Module.Basis ι K L) : Module.Basis ι K L :=
  (killingForm K L).dualBasis (LieAlgebra.IsKilling.killingForm_nondegenerate K L) b

/-- The defining biorthogonality of the Killing-dual basis. -/
@[simp]
theorem killingForm_killingDualBasis (b : Module.Basis ι K L) (i j : ι) :
    killingForm K L (b i) (killingDualBasis b j) = if i = j then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_right _ killingForm_isSymm b i j

/-- Coordinates in the Killing-dual basis are Killing pairings against `b`. -/
@[simp]
theorem killingDualBasis_repr (b : Module.Basis ι K L) (v : L) (i : ι) :
    (killingDualBasis b).repr v i = killingForm K L (b i) v :=
  (LinearMap.BilinForm.dualBasis_repr_apply _ b v i).trans
    (LieModule.traceForm_comm K L L v (b i))

/-- Conjugating twice returns the original basis: the Killing-dual basis of the Killing-dual
basis of `b` is `b`. -/
@[simp]
theorem killingDualBasis_killingDualBasis (b : Module.Basis ι K L) :
    killingDualBasis (killingDualBasis b) = b :=
  LinearMap.BilinForm.dualBasis_dualBasis _ killingForm_isSymm b

/-- Coordinates in `b` are Killing pairings against the Killing-dual basis. -/
theorem repr_eq_killingForm (b : Module.Basis ι K L) (v : L) (i : ι) :
    b.repr v i = killingForm K L v (killingDualBasis b i) := by
  conv_lhs => rw [← killingDualBasis_killingDualBasis b]
  rw [killingDualBasis_repr, LieModule.traceForm_comm]

/-- **Expansion in `b`**, with the coefficients read off by the Killing-dual basis. -/
theorem sum_killingForm_smul_basis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L v (killingDualBasis b i) • b i = v := by
  conv_rhs => rw [← b.sum_repr v]
  exact sum_congr rfl fun i _ ↦ by rw [repr_eq_killingForm]

/-- **Expansion in the Killing-dual basis**, with the coefficients read off by `b`. -/
theorem sum_killingForm_smul_killingDualBasis (b : Module.Basis ι K L) (v : L) :
    ∑ i, killingForm K L (b i) v • killingDualBasis b i = v := by
  conv_rhs => rw [← (killingDualBasis b).sum_repr v]
  exact sum_congr rfl fun i _ ↦ by rw [killingDualBasis_repr]

/-- **The sum `∑ᵢ κ (p xᵢ) yᵢ` along a basis and its Killing-dual basis is the trace of `p`.**  The
Killing-dual basis reads off the coordinates in `b` (`TauCeti.repr_eq_killingForm`), so the sum is
the sum of the diagonal entries of the matrix of `p`. -/
theorem sum_killingForm_killingDualBasis_eq_trace (b : Module.Basis ι K L) (p : L →ₗ[K] L) :
    ∑ i, killingForm K L (p (b i)) (killingDualBasis b i) = LinearMap.trace K L p := by
  rw [LinearMap.trace_eq_matrix_trace K b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact sum_congr rfl fun i _ ↦ (repr_eq_killingForm b (p (b i)) i).symm

end DualBasis

/-! ### The canonical invariant element `∑ᵢ xᵢ ⊗ yᵢ`

Both properties of the Casimir element proved below come from two facts about the sum
`∑ᵢ f (b i) (killingDualBasis b i)` of a bilinear map `f` along a basis and its Killing-dual
basis: it does not depend on the basis, and it is annihilated by the adjoint action.  Stating them
for an arbitrary bilinear `f` keeps the arguments free of any computation inside `U(L)`. -/

section Bilinear

variable {W : Type w} [AddCommGroup W] [Module K W] (f : L →ₗ[K] L →ₗ[K] W)

/-- **The sum `∑ᵢ f xᵢ yᵢ` of a bilinear map along a basis and its Killing-dual basis does not
depend on the basis.**  Expanding each `c j` in the basis `b` produces exactly the coefficients
that expand `killingDualBasis b i` in `killingDualBasis c`. -/
theorem sum_apply_killingDualBasis_eq {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι']
    [Fintype ι'] (b : Module.Basis ι K L) (c : Module.Basis ι' K L) :
    ∑ i, f (b i) (killingDualBasis b i) = ∑ j, f (c j) (killingDualBasis c j) := by
  have expand : ∀ j : ι', f (c j) (killingDualBasis c j)
      = ∑ i, killingForm K L (c j) (killingDualBasis b i) • f (b i) (killingDualBasis c j) := by
    intro j
    conv_lhs => rw [← sum_killingForm_smul_basis b (c j)]
    rw [map_sum, LinearMap.sum_apply]
    exact sum_congr rfl fun i _ ↦ by rw [map_smul, LinearMap.smul_apply]
  rw [sum_congr rfl fun j _ ↦ expand j, Finset.sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  conv_lhs => rw [← sum_killingForm_smul_killingDualBasis c (killingDualBasis b i)]
  rw [map_sum]
  exact sum_congr rfl fun j _ ↦ map_smul _ _ _

/-- **A Killing-adjoint pair of operators may be moved from one slot to the other.**  If `κ (p x) y`
is `κ x (q y)` then applying `p` to the basis vectors and applying `q` to their Killing duals give
the same sum, because both expand to `∑ᵢ ∑ⱼ κ (p xᵢ) yⱼ • f xⱼ yᵢ`. -/
theorem sum_apply_killingDualBasis_of_isAdjointPair {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) {p q : L →ₗ[K] L}
    (hpq : LinearMap.IsAdjointPair (killingForm K L) (killingForm K L) p q) :
    ∑ i, f (p (b i)) (killingDualBasis b i) = ∑ i, f (b i) (q (killingDualBasis b i)) := by
  have expand₁ : ∀ i : ι, f (p (b i)) (killingDualBasis b i)
      = ∑ j, killingForm K L (p (b i)) (killingDualBasis b j) •
          f (b j) (killingDualBasis b i) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_basis b (p (b i))]
    rw [map_sum, LinearMap.sum_apply]
    exact sum_congr rfl fun j _ ↦ by rw [map_smul, LinearMap.smul_apply]
  have expand₂ : ∀ i : ι, f (b i) (q (killingDualBasis b i))
      = ∑ j, killingForm K L (p (b j)) (killingDualBasis b i) •
          f (b i) (killingDualBasis b j) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_killingDualBasis b (q (killingDualBasis b i))]
    rw [map_sum]
    exact sum_congr rfl fun j _ ↦ by rw [map_smul, hpq (b j) (killingDualBasis b i)]
  rw [sum_congr rfl fun i _ ↦ expand₁ i, sum_congr rfl fun i _ ↦ expand₂ i, Finset.sum_comm]

/-- **The element `∑ᵢ xᵢ ⊗ yᵢ` is invariant under the adjoint action.**  Read through a bilinear
map `f`, the Leibniz expansion of the adjoint action of `z` vanishes, because the two coefficient
families it produces are negatives of each other by the invariance of the Killing form. -/
theorem sum_apply_lie_killingDualBasis_add_eq_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι K L) (z : L) :
    ∑ i, f ⁅z, b i⁆ (killingDualBasis b i) + ∑ i, f (b i) ⁅z, killingDualBasis b i⁆ = 0 := by
  have expand₁ : ∀ i : ι, f ⁅z, b i⁆ (killingDualBasis b i)
      = ∑ j, killingForm K L ⁅z, b i⁆ (killingDualBasis b j) •
          f (b j) (killingDualBasis b i) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_basis b ⁅z, b i⁆]
    rw [map_sum, LinearMap.sum_apply]
    exact sum_congr rfl fun j _ ↦ by rw [map_smul, LinearMap.smul_apply]
  have expand₂ : ∀ i : ι, f (b i) ⁅z, killingDualBasis b i⁆
      = ∑ j, killingForm K L (b j) ⁅z, killingDualBasis b i⁆ •
          f (b i) (killingDualBasis b j) := by
    intro i
    conv_lhs => rw [← sum_killingForm_smul_killingDualBasis b ⁅z, killingDualBasis b i⁆]
    rw [map_sum]
    exact sum_congr rfl fun j _ ↦ map_smul _ _ _
  rw [sum_congr rfl fun i _ ↦ expand₁ i, sum_congr rfl fun i _ ↦ expand₂ i, Finset.sum_comm,
    ← Finset.sum_add_distrib]
  refine sum_eq_zero fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine sum_eq_zero fun j _ ↦ ?_
  rw [← add_smul, LieModule.traceForm_apply_lie_apply' K L L z (b j) (killingDualBasis b i),
    neg_add_cancel, zero_smul]

end Bilinear

/-! ### The Casimir element -/

variable [FiniteDimensional K L]

variable (K L) in
/-- Multiplying two canonical Lie generators of `U(L)`, as a `K`-bilinear map.  This is the
bilinear map that turns the invariance of `∑ᵢ xᵢ ⊗ yᵢ` into the centrality of the Casimir
element. -/
private noncomputable def genMul :
    L →ₗ[K] L →ₗ[K] UniversalEnvelopingAlgebra K L :=
  LinearMap.mk₂ K (fun x y ↦ ι K x * ι K y)
    (fun _ _ _ ↦ by rw [map_add, add_mul]) (fun _ _ _ ↦ by rw [map_smul, smul_mul_assoc])
    (fun _ _ _ ↦ by rw [map_add, mul_add]) (fun _ _ _ ↦ by rw [map_smul, mul_smul_comm])

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem genMul_apply (x y : L) : genMul K L x y = ι K x * ι K y := (rfl)

variable (K L) in
/-- **The Casimir element** `Ω = ∑ᵢ xᵢ yᵢ ∈ U(L)` of a Lie algebra with nondegenerate Killing
form, built from a basis `x` of `L` and the basis `y` dual to it under the Killing form.

The definition names a particular basis, but the element does not depend on it:
`TauCeti.casimirElement_eq_sum` evaluates `Ω` against an arbitrary basis. -/
noncomputable def casimirElement : UniversalEnvelopingAlgebra K L :=
  ∑ i, ι K (Module.finBasis K L i) * ι K (killingDualBasis (Module.finBasis K L) i)

/-- **The Casimir element is `∑ᵢ xᵢ yᵢ` for every basis `x` of `L`** and its Killing-dual basis
`y`, so the basis chosen in the definition is immaterial. -/
theorem casimirElement_eq_sum {ι' : Type*} [DecidableEq ι'] [Fintype ι']
    (b : Module.Basis ι' K L) :
    casimirElement K L = ∑ i, ι K (b i) * ι K (killingDualBasis b i) := by
  simp only [casimirElement, ← genMul_apply]
  exact sum_apply_killingDualBasis_eq (genMul K L) (Module.finBasis K L) b

/-- **The Casimir element acts by zero on a module with trivial action.** Every summand
`xᵢ yᵢ` of `Ω` acts by a double bracket, and brackets vanish. -/
@[simp]
theorem representation_casimirElement_apply_eq_zero_of_isTrivial
    {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [LieModule.IsTrivial L M] (m : M) :
    UniversalEnvelopingAlgebra.representation K L M (casimirElement K L) m = 0 := by
  classical
  rw [casimirElement_eq_sum (Module.finBasis K L), map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [map_mul, Module.End.mul_apply, UniversalEnvelopingAlgebra.representation_ι,
    UniversalEnvelopingAlgebra.representation_ι]
  simp [trivial_lie_zero]

/-- **The Casimir element commutes with every canonical Lie generator.**  Expanding the commutator
of `ι z` with each summand `xᵢ yᵢ` by the Leibniz rule replaces the bracket by the adjoint action
on `∑ᵢ xᵢ ⊗ yᵢ`, which vanishes. -/
theorem ι_mul_casimirElement (z : L) :
    ι K z * casimirElement K L = casimirElement K L * ι K z := by
  classical
  set b := Module.finBasis K L with hb
  rw [← sub_eq_zero, casimirElement_eq_sum b, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  have hcomm : ∀ x y : L, ι K x * ι K y - ι K y * ι K x = ι K (⁅x, y⁆ : L) := fun x y ↦ by
    simpa using TauCeti.UniversalEnvelopingAlgebra.mul_sub_mul_eq_map_ι_lie
      (AlgHom.id K (UniversalEnvelopingAlgebra K L)) x y
  have step : ∀ i, ι K z * (ι K (b i) * ι K (killingDualBasis b i))
      - ι K (b i) * ι K (killingDualBasis b i) * ι K z
      = genMul K L ⁅z, b i⁆ (killingDualBasis b i)
        + genMul K L (b i) ⁅z, killingDualBasis b i⁆ := by
    intro i
    rw [genMul_apply, genMul_apply, ← hcomm z (b i), ← hcomm z (killingDualBasis b i)]
    noncomm_ring
  rw [sum_congr rfl fun i _ ↦ step i, Finset.sum_add_distrib]
  exact sum_apply_lie_killingDualBasis_add_eq_zero (genMul K L) b z

variable (K L) in
/-- **The Casimir element is central in `U(L)`.**  It commutes with the canonical Lie generators,
which generate `U(L)` as an algebra. -/
theorem casimirElement_mem_center :
    casimirElement K L ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L) := by
  refine Subalgebra.mem_center_iff.mpr fun u ↦ ?_
  induction u using TauCeti.UniversalEnvelopingAlgebra.induction_ι with
  | ι z => exact ι_mul_casimirElement (K := K) z
  | algebraMap r => exact Algebra.commutes r _
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | mul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

end TauCeti
