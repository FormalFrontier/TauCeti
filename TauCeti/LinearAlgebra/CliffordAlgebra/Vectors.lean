/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# The vectors and the scalars inside a Clifford algebra

The generators of a Clifford algebra are the elements `ι Q m`, and the first thing one wants to
know about them is that they are a faithful copy of `M`: that `ι Q` is injective, so that `M` is
*the* module of vectors `LinearMap.range (ι Q)` sitting inside `CliffordAlgebra Q`, and that no
nonzero vector is a scalar.

Mathlib proves all of this for the exterior algebra, which is the Clifford algebra of the zero
form (`ExteriorAlgebra.ι_leftInverse`, `ExteriorAlgebra.ι_inj`,
`ExteriorAlgebra.ι_eq_algebraMap_iff`, `ExteriorAlgebra.ι_range_disjoint_one`), using the
square-zero extension `TrivSqZeroExt R M` as an auxiliary algebra. That trick is unavailable for a
general `Q`: in `TrivSqZeroExt R M` the square of a vector is `0`, so it computes `Q = 0` and
nothing else. What is available instead is Mathlib's module isomorphism
`CliffordAlgebra.equivExterior Q : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M`, valid in
characteristic not two, which sends generators to generators and scalars to scalars. This file
transports the exterior-algebra statements along it, so all of them hold for an arbitrary
quadratic form over a commutative ring in which `2` is invertible; no hypothesis on `Q` — no
nondegeneracy, no finiteness, no freeness — is needed.

The payoff is `TauCeti.CliffordAlgebra.ιRangeEquiv`, the linear equivalence `M ≃ₗ[R] range (ι Q)`.
It is what turns a statement about elements of `CliffordAlgebra Q` that happen to lie in
`range (ι Q)` into a statement about vectors of `M`: Mathlib's twisted conjugation lemmas
(`lipschitzGroup.conjAct_smul_range_ι`, `spinGroup.involute_act_ι_mem_range_ι`) say only that the
Lipschitz and spin groups act on `range (ι Q)`, and it is `ιRangeEquiv` that converts such an
action into an honest linear automorphism of `M`, hence into an element of the orthogonal group of
`Q`.

Against the degree filtration `TauCeti.CliffordAlgebra.filtration`, whose first step is spanned by
the scalars and the vectors, the disjointness of the two pins that step down to `R ⊕ M`:
`TauCeti.CliffordAlgebra.filtrationOneEquiv`.

## Main definitions

* `TauCeti.CliffordAlgebra.ιInv`: the linear left inverse of `ι Q`, the *vector part* of an
  element of the Clifford algebra.
* `TauCeti.CliffordAlgebra.ιRangeEquiv`: the vector equivalence `M ≃ₗ[R] range (ι Q)`.
* `TauCeti.CliffordAlgebra.scalarAddVector` and
  `TauCeti.CliffordAlgebra.filtrationOneEquiv`: the map `(r, m) ↦ r + ι Q m` out of `R × M`, and
  the equivalence with the first step of the degree filtration that it induces.

## Main results

* `TauCeti.CliffordAlgebra.ι_injective`, `TauCeti.CliffordAlgebra.ι_inj` and
  `TauCeti.CliffordAlgebra.ι_eq_zero_iff`: the generators are a faithful copy of `M`.
* `TauCeti.CliffordAlgebra.algebraMap_injective` and the instance
  `TauCeti.CliffordAlgebra.faithfulSMul` it provides: the scalars are a faithful copy of `R`, so
  Mathlib's `FaithfulSMul` simp lemmas apply.
* `TauCeti.CliffordAlgebra.ι_eq_algebraMap_iff`, `TauCeti.CliffordAlgebra.ι_ne_one` and
  `TauCeti.CliffordAlgebra.ι_range_disjoint_one`: a vector is a scalar only when both vanish.
* `TauCeti.CliffordAlgebra.mem_ι_range_iff`: membership of `range (ι Q)` is detected by the vector
  part.
* `TauCeti.CliffordAlgebra.finrank_ι_range` and
  `TauCeti.CliffordAlgebra.finrank_filtration_one`: the vectors have the dimension of `M`, and the
  first step of the degree filtration has one more.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 2, "Vectors from the Clifford algebra".
* N. Bourbaki, *Algebra I, Chapters 1-3* (1989), §9.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti

namespace CliffordAlgebra

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-! ### The comparison with the exterior algebra

Mathlib's `CliffordAlgebra.equivExterior` is only a linear equivalence, but the two facts that make
it useful here — that it fixes generators and fixes scalars — are immediate from its definition as
a `changeForm`, and are recorded once. -/

/-- `CliffordAlgebra.equivExterior` sends a generator to the corresponding generator of the
exterior algebra. -/
theorem equivExterior_ι (m : M) : equivExterior Q (ι Q m) = ExteriorAlgebra.ι R m :=
  changeForm_ι changeForm.associated_neg_proof m

/-- `CliffordAlgebra.equivExterior` sends a scalar to the corresponding scalar of the exterior
algebra. -/
theorem equivExterior_algebraMap (r : R) :
    equivExterior Q (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (ExteriorAlgebra R M) r :=
  changeForm_algebraMap changeForm.associated_neg_proof r

/-! ### The vector part -/

/-- The vector part of an element of a Clifford algebra: a linear left inverse of `ι Q`.

This is `ExteriorAlgebra.ιInv` transported along `CliffordAlgebra.equivExterior`, which is where
the hypothesis `[Invertible (2 : R)]` comes from; the square-zero extension that builds
`ExteriorAlgebra.ιInv` directly sees only the zero quadratic form. -/
def ιInv : CliffordAlgebra Q →ₗ[R] M :=
  ExteriorAlgebra.ιInv ∘ₗ (equivExterior Q).toLinearMap

@[simp]
theorem ιInv_ι (m : M) : ιInv Q (ι Q m) = m := by
  rw [ιInv, LinearMap.comp_apply, LinearEquiv.coe_coe, equivExterior_ι,
    ExteriorAlgebra.ι_leftInverse m]

theorem ι_leftInverse : Function.LeftInverse (ιInv Q) (ι Q) := ιInv_ι Q

@[simp]
theorem ιInv_algebraMap (r : R) : ιInv Q (algebraMap R (CliffordAlgebra Q) r) = 0 := by
  rw [ιInv, LinearMap.comp_apply, LinearEquiv.coe_coe, equivExterior_algebraMap]
  simp [ExteriorAlgebra.ιInv, TrivSqZeroExt.sndHom, TrivSqZeroExt.algebraMap_eq_inl]

/-! ### `ι` is injective -/

/-- **The generators of a Clifford algebra are a faithful copy of `M`.** In characteristic not two
this needs no hypothesis on `Q`. -/
theorem ι_injective : Function.Injective (ι Q) := (ι_leftInverse Q).injective

@[simp]
theorem ι_inj (m n : M) : ι Q m = ι Q n ↔ m = n := (ι_injective Q).eq_iff

@[simp]
theorem ι_eq_zero_iff (m : M) : ι Q m = 0 ↔ m = 0 := by
  rw [← ι_inj Q m 0, map_zero]

/-! ### `algebraMap` is injective -/

/-- **The scalars of a Clifford algebra are a faithful copy of `R`.** -/
theorem algebraMap_injective : Function.Injective (algebraMap R (CliffordAlgebra Q)) := by
  intro r s hrs
  have h := congrArg (equivExterior Q) hrs
  rwa [equivExterior_algebraMap, equivExterior_algebraMap,
    ExteriorAlgebra.algebraMap_inj M] at h

/-- With this instance the `iff` forms come from Mathlib: `algebraMap.coe_inj`,
`FaithfulSMul.algebraMap_eq_zero_iff` and `FaithfulSMul.algebraMap_eq_one_iff` are all `simp`
lemmas already. -/
instance faithfulSMul : FaithfulSMul R (CliffordAlgebra Q) :=
  (faithfulSMul_iff_algebraMap_injective R (CliffordAlgebra Q)).2 (algebraMap_injective Q)

/-! ### Vectors are not scalars -/

/-- A generator is a scalar only in the trivial way: both the vector and the scalar vanish. -/
@[simp]
theorem ι_eq_algebraMap_iff (m : M) (r : R) :
    ι Q m = algebraMap R (CliffordAlgebra Q) r ↔ m = 0 ∧ r = 0 := by
  rw [← (equivExterior Q).injective.eq_iff, equivExterior_ι, equivExterior_algebraMap,
    ExteriorAlgebra.ι_eq_algebraMap_iff]

@[simp]
theorem ι_ne_one [Nontrivial R] (m : M) : ι Q m ≠ 1 := by
  rw [← map_one (algebraMap R (CliffordAlgebra Q)), Ne, ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right

/-- **The vectors of a Clifford algebra are disjoint from its scalars.** Together with
`TauCeti.CliffordAlgebra.filtration_one`, which writes the first step of the degree filtration as
`1 ⊔ LinearMap.range (ι Q)`, this is what makes that step a direct sum of `R` and `M`; see
`TauCeti.CliffordAlgebra.filtrationOneEquiv`. -/
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι Q)) (1 : Submodule R (CliffordAlgebra Q)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨m, rfl⟩ hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx
  rw [eq_comm, ι_eq_algebraMap_iff] at hr
  rw [hr.1, map_zero]

/-! ### The vector equivalence -/

/-- **The vector equivalence**: `M` is the module of vectors `LinearMap.range (ι Q)` inside its
Clifford algebra.

Mathlib's twisted-conjugation lemmas say that the Lipschitz and spin groups act on
`LinearMap.range (ι Q)`; this equivalence is what converts such an action into a linear
automorphism of `M`, and so into an element of the orthogonal group of `Q`. -/
noncomputable def ιRangeEquiv : M ≃ₗ[R] LinearMap.range (ι Q) :=
  LinearEquiv.ofInjective (ι Q) (ι_injective Q)

@[simp]
theorem coe_ιRangeEquiv (m : M) : (ιRangeEquiv Q m : CliffordAlgebra Q) = ι Q m := by
  rw [ιRangeEquiv, LinearEquiv.ofInjective_apply]

@[simp]
theorem ι_ιRangeEquiv_symm (x : LinearMap.range (ι Q)) :
    ι Q ((ιRangeEquiv Q).symm x) = x := by
  rw [← coe_ιRangeEquiv, LinearEquiv.apply_symm_apply]

/-- The vector part reconstructs a vector. -/
theorem ι_ιInv_of_mem {x : CliffordAlgebra Q} (hx : x ∈ LinearMap.range (ι Q)) :
    ι Q (ιInv Q x) = x := by
  obtain ⟨m, rfl⟩ := hx
  rw [ιInv_ι]

/-- Membership of the module of vectors is detected by the vector part. -/
theorem mem_ι_range_iff {x : CliffordAlgebra Q} :
    x ∈ LinearMap.range (ι Q) ↔ ι Q (ιInv Q x) = x :=
  ⟨ι_ιInv_of_mem Q, fun h => ⟨_, h⟩⟩

/-- On a vector, the retraction `ιInv` computes the inverse of the vector equivalence. -/
theorem ιRangeEquiv_symm_apply (x : LinearMap.range (ι Q)) :
    (ιRangeEquiv Q).symm x = ιInv Q x :=
  (ι_injective Q) <| by rw [ι_ιRangeEquiv_symm, ι_ιInv_of_mem Q x.2]

/-- The module of vectors has the rank of `M`, being a copy of it. -/
theorem finrank_ι_range :
    Module.finrank R (LinearMap.range (ι Q)) = Module.finrank R M :=
  (ιRangeEquiv Q).finrank_eq.symm

/-! ### The first step of the degree filtration -/

/-- The elements of degree at most one, as a map out of `R × M`: `(r, m) ↦ r + ι Q m`. It is
injective with image `TauCeti.CliffordAlgebra.filtration Q 1`. -/
def scalarAddVector : R × M →ₗ[R] CliffordAlgebra Q :=
  LinearMap.coprod (Algebra.linearMap R (CliffordAlgebra Q)) (ι Q)

omit [Invertible (2 : R)] in
@[simp]
theorem scalarAddVector_apply (x : R × M) :
    scalarAddVector Q x = algebraMap R (CliffordAlgebra Q) x.1 + ι Q x.2 := by
  rw [scalarAddVector, LinearMap.coprod_apply, Algebra.linearMap_apply]

omit [Invertible (2 : R)] in
/-- The scalars and the vectors span exactly the first step of the degree filtration. -/
theorem range_scalarAddVector : LinearMap.range (scalarAddVector Q) = filtration Q 1 := by
  rw [scalarAddVector, LinearMap.range_coprod, ← Submodule.one_eq_range, ← filtration_one]

/-- A scalar and a vector summing to zero both vanish, by `ι_eq_algebraMap_iff`. -/
theorem scalarAddVector_injective : Function.Injective (scalarAddVector Q) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨r, m⟩ hx
  rw [LinearMap.mem_ker, scalarAddVector_apply] at hx
  have h : ι Q m = algebraMap R (CliffordAlgebra Q) (-r) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_right hx
  rw [ι_eq_algebraMap_iff] at h
  simp [Prod.ext_iff, h.1, neg_eq_zero.mp h.2]

/-- **The first step of the degree filtration is `R ⊕ M`.** The scalars and the vectors span it
(`TauCeti.CliffordAlgebra.filtration_one`) and meet only in `0`
(`TauCeti.CliffordAlgebra.ι_range_disjoint_one`), so together they parametrize it faithfully. -/
noncomputable def filtrationOneEquiv : (R × M) ≃ₗ[R] filtration Q 1 :=
  (LinearEquiv.ofInjective _ (scalarAddVector_injective Q)).trans
    (LinearEquiv.ofEq _ _ (range_scalarAddVector Q))

@[simp]
theorem coe_filtrationOneEquiv (x : R × M) :
    (filtrationOneEquiv Q x : CliffordAlgebra Q)
      = algebraMap R (CliffordAlgebra Q) x.1 + ι Q x.2 := by
  rw [filtrationOneEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply, scalarAddVector_apply]

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V) [Invertible (2 : K)]

/-- Counting dimensions in `TauCeti.CliffordAlgebra.filtrationOneEquiv`: the first step of the
degree filtration is one dimension bigger than the space of vectors. -/
theorem finrank_filtration_one [FiniteDimensional K V] :
    Module.finrank K (filtration Q 1) = Module.finrank K V + 1 := by
  rw [← (filtrationOneEquiv Q).finrank_eq, Module.finrank_prod, Module.finrank_self,
    Nat.add_comm]

end Field

end CliffordAlgebra

end TauCeti
