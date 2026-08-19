/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.DualBasis
public import TauCeti.Algebra.Lie.UniversalEnveloping.Representation
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

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

* `TauCeti.casimirElement`: the Casimir element of `U(L)`.

## Main results

* `TauCeti.casimirElement_eq_sum`: the Casimir element is `∑ᵢ xᵢ yᵢ` for **any** basis `x` of `L`
  and its Killing-dual basis `y`, so the basis chosen in the definition does not matter.
* `TauCeti.ι_mul_casimirElement`: the Casimir element commutes with every canonical Lie generator.
* `TauCeti.casimirElement_mem_center`: **the Casimir element is central in `U(L)`.**
* `TauCeti.representation_casimirElement_apply`: the Casimir element acts on a Lie module by the
  double bracket along any basis of `L` and its Killing-dual basis.

That scalar is computed in `TauCeti/Algebra/Lie/HighestWeight/Casimir.lean`, in
`TauCeti.IsHighestWeightVector.representation_casimirElement_apply_eq_smul_weylVector` and
`TauCeti.IsHighestWeightVector.representation_casimirElement_apply_eq_smul_of_lieSpan_eq_top`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §6.2.
* [Highest weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 5, "The Casimir element".
-/

public section

open Finset LieAlgebra LieModule UniversalEnvelopingAlgebra

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L]

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
  have hu : u ∈ (⊤ : Subalgebra K (UniversalEnvelopingAlgebra K L)) := Algebra.mem_top
  rw [← TauCeti.UniversalEnvelopingAlgebra.adjoin_range_ι K L] at hu
  induction hu using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ι_mul_casimirElement (K := K) z
  | algebraMap r => exact Algebra.commutes r _
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

/-! ### The action on a Lie module -/

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

open _root_.TauCeti.UniversalEnvelopingAlgebra (representation representation_ι_apply) in
/-- **The Casimir element acts by the double bracket along any basis** of `L` and its Killing-dual
basis: the two canonical generators of each summand act one after the other. -/
theorem representation_casimirElement_apply {ι' : Type*} [DecidableEq ι'] [Fintype ι']
    (bs : Module.Basis ι' K L) (m : M) :
    representation K L M (casimirElement K L) m = ∑ i, ⁅bs i, ⁅killingDualBasis bs i, m⁆⁆ := by
  rw [casimirElement_eq_sum bs, map_sum, LinearMap.sum_apply]
  exact sum_congr rfl fun i _ ↦ by
    rw [map_mul, Module.End.mul_apply, representation_ι_apply, representation_ι_apply]

end TauCeti
