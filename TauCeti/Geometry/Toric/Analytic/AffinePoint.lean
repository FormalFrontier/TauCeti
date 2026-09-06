/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Finiteness

/-!
# Complex points of an affine semigroup and their monomial-embedding topology

The complex points of the affine scheme of a commutative additive monoid `S` are the
`ℂ`-algebra homomorphisms `ℂ[S] →ₐ[ℂ] ℂ` out of the monoid algebra, equivalently the
multiplicative characters `Multiplicative S →* ℂ`. Evaluating such a point on a finite family
`g : Fin r → S` that generates `S` as an additive monoid gives a map into `ℂ^r`, and the
topology of the complex points is the one induced by that map.

This file constructs that topology and proves the facts a chart needs before any coordinates
are chosen: the evaluation map is injective, its range is the closed subset of `ℂ^r` cut out
by the binomial relations of the generating family, and the induced topology does not depend
on which finite generating family is used. Consequently the complex points form a Hausdorff,
second countable, locally compact space, and evaluation at every monomial is continuous.

Independence of the generating family is what makes the space, rather than one presentation of
it, the object of study: a semigroup that arises as the dual of a cone has no preferred finite
generating family, and later coordinate descriptions must be compared with a topology that was
not defined using them.

## Main declarations

* `TauCeti.Toric.AffineSemigroupComplexPoint`: the complex points of an affine semigroup.
* `TauCeti.Toric.AddGeneratingFamily`: a finite family generating an additive monoid, which
  exists exactly for a finitely generated additive monoid.
* `TauCeti.Toric.monomialEmbedding`: evaluation of a complex point on such a family.
* `TauCeti.Toric.range_monomialEmbedding`: the range of the monomial embedding is the locus of
  the binomial relations of the family.
* `TauCeti.Toric.affinePointTopology`: the topology induced by a monomial embedding.
* `TauCeti.Toric.affinePointTopology_eq`: it does not depend on the generating family.
* `TauCeti.Toric.isClosedEmbedding_monomialEmbedding`: the monomial embedding is a closed
  embedding, whence the Hausdorff, second countable and locally compact conclusions.

## References

* `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`,
  "Affine complex points and an independent topology".
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1–1.3.
* W. Fulton, *Introduction to Toric Varieties*, §1.2.
-/

public section

open Multiplicative Topology

namespace TauCeti.Toric

variable {S : Type*} [AddCommMonoid S] {r r' : ℕ}

/-- The complex points of the affine scheme attached to a commutative additive monoid `S`: the
`ℂ`-algebra homomorphisms out of the monoid algebra of `S`. This is the functor-of-points
carrier; no topology is part of the data. -/
abbrev AffineSemigroupComplexPoint (S : Type*) [AddCommMonoid S] :=
  MonoidAlgebra ℂ (Multiplicative S) →ₐ[ℂ] ℂ

/-- Evaluating an affine complex point at the monomial of an `ℕ`-combination `∑ j, a j • v j`
gives the corresponding monomial in the evaluations at the `v j`. -/
theorem apply_single_ofAdd_sum (v : Fin r → S) (a : Fin r → ℕ)
    (x : AffineSemigroupComplexPoint S) :
    x (MonoidAlgebra.single (ofAdd (∑ j, a j • v j)) 1) =
      ∏ j, x (MonoidAlgebra.single (ofAdd (v j)) 1) ^ a j := by
  have key : ∀ s : S, x (MonoidAlgebra.single (ofAdd s) 1) =
      (MonoidAlgebra.lift ℂ ℂ (Multiplicative S)).symm x (ofAdd s) := fun s =>
    (MonoidAlgebra.lift_symm_apply x (ofAdd s)).symm
  simp only [key]
  simp only [ofAdd_sum, ofAdd_nsmul, map_prod, map_pow]

/-- A finite family generating a commutative additive monoid. The affine complex points of `S`
are topologized through evaluation on such a family, so the chosen indexed family, and not just
the finite generation of `S`, is part of the data. -/
@[ext]
structure AddGeneratingFamily (S : Type*) [AddCommMonoid S] (r : ℕ) where
  /-- The family of generators. -/
  toFun : Fin r → S
  /-- The family generates the additive monoid. -/
  spans : AddSubmonoid.closure (Set.range toFun) = ⊤

/-- A monoid with a finite generating family is finitely generated. -/
theorem AddGeneratingFamily.fg (g : AddGeneratingFamily S r) : AddMonoid.FG S := by
  classical
  exact ⟨⟨Finset.univ.image g.toFun, by simpa using g.spans⟩⟩

/-- Conversely, a finitely generated additive monoid carries a finite generating family, so the
constructions below apply to every finitely generated additive monoid. -/
theorem exists_addGeneratingFamily (S : Type*) [AddCommMonoid S] [AddMonoid.FG S] :
    ∃ r, Nonempty (AddGeneratingFamily S r) := by
  obtain ⟨T, hT⟩ := AddMonoid.FG.fg_top (M := S)
  refine ⟨T.card, ⟨⟨((↑) : {x // x ∈ T} → S) ∘ T.equivFin.symm, ?_⟩⟩⟩
  rw [T.equivFin.symm.surjective.range_comp]
  simpa using hT

/-- Evaluation of the affine complex points of `S` on a finite generating family. -/
noncomputable def monomialEmbedding (g : AddGeneratingFamily S r) :
    AffineSemigroupComplexPoint S → Fin r → ℂ :=
  fun x j ↦ x (MonoidAlgebra.single (ofAdd (g.toFun j)) 1)

/-- The `j`-th coordinate of the monomial embedding is evaluation at the monomial of the `j`-th
generator. -/
@[simp]
theorem monomialEmbedding_apply (g : AddGeneratingFamily S r)
    (x : AffineSemigroupComplexPoint S) (j : Fin r) :
    monomialEmbedding g x j = x (MonoidAlgebra.single (ofAdd (g.toFun j)) 1) := (rfl)

/-- Evaluation at any monomial is a monomial in the coordinates of a monomial embedding, with
exponents given by any expression of the monoid element through the generating family. -/
theorem apply_single_eq_prod_monomialEmbedding (g : AddGeneratingFamily S r) {s : S}
    {a : Fin r → ℕ} (ha : s = ∑ j, a j • g.toFun j) (x : AffineSemigroupComplexPoint S) :
    x (MonoidAlgebra.single (ofAdd s) 1) = ∏ j, monomialEmbedding g x j ^ a j := by
  rw [ha, apply_single_ofAdd_sum]
  simp

/-- An affine complex point is determined by its values on a finite generating family. -/
theorem monomialEmbedding_injective (g : AddGeneratingFamily S r) :
    Function.Injective (monomialEmbedding g) := by
  intro x y hxy
  refine (MonoidAlgebra.lift ℂ ℂ (Multiplicative S)).symm.injective (MonoidHom.ext fun m ↦ ?_)
  obtain ⟨a, ha⟩ := AddSubmonoid.exists_of_mem_closure_range g.toFun (toAdd m) (by
    rw [g.spans]
    trivial)
  have hm : m = ofAdd (∑ j, a j • g.toFun j) := congrArg ofAdd ha
  rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.lift_symm_apply, hm,
    apply_single_eq_prod_monomialEmbedding g rfl, apply_single_eq_prod_monomialEmbedding g rfl,
    hxy]

/-- The range of a monomial embedding is the locus of the binomial relations of the generating
family: a point of `ℂ^r` extends to an affine complex point exactly when every additive relation
between the generators is matched by the corresponding multiplicative relation. -/
theorem range_monomialEmbedding (g : AddGeneratingFamily S r) :
    Set.range (monomialEmbedding g) =
      {z : Fin r → ℂ | ∀ a b : Fin r → ℕ, ∑ j, a j • g.toFun j = ∑ j, b j • g.toFun j →
        ∏ j, z j ^ a j = ∏ j, z j ^ b j} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ a b hab
    rw [← apply_single_eq_prod_monomialEmbedding g rfl x,
      ← apply_single_eq_prod_monomialEmbedding g rfl x, hab]
  · intro hz
    choose a ha using fun s ↦ AddSubmonoid.exists_of_mem_closure_range g.toFun s (by
      rw [g.spans]
      trivial)
    -- The relations satisfied by `z` make `s ↦ ∏ j, z j ^ a s j` a well-defined character.
    have hprod : ∀ b : Fin r → ℕ, ∀ s : S, s = ∑ j, b j • g.toFun j →
        ∏ j, z j ^ a s j = ∏ j, z j ^ b j := fun b s hs ↦ hz _ _ (by rw [← ha s, ← hs])
    have hone : ∏ j, z j ^ a 0 j = 1 := by
      rw [hprod 0 0 (by simp)]
      simp
    have hmul : ∀ s t : S, ∏ j, z j ^ a (s + t) j =
        (∏ j, z j ^ a s j) * ∏ j, z j ^ a t j := by
      intro s t
      rw [hprod (a s + a t) (s + t)
        (by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← ha])]
      simp [pow_add, Finset.prod_mul_distrib]
    refine ⟨MonoidAlgebra.lift ℂ ℂ (Multiplicative S)
      ⟨⟨fun m ↦ ∏ j, z j ^ a (toAdd m) j, hone⟩, fun m n ↦ hmul _ _⟩, ?_⟩
    funext j
    have hsingle : g.toFun j = ∑ k, (Pi.single j 1 : Fin r → ℕ) k • g.toFun k := by
      simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq']
    simp only [monomialEmbedding_apply, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd]
    rw [hprod (Pi.single j 1) (g.toFun j) hsingle]
    simp [Pi.single_apply, pow_ite, Finset.prod_ite_eq']

/-- The range of a monomial embedding is closed: it is the common zero locus of the differences
of the binomials attached to the additive relations of the generating family. -/
theorem isClosed_range_monomialEmbedding (g : AddGeneratingFamily S r) :
    IsClosed (Set.range (monomialEmbedding g)) := by
  rw [range_monomialEmbedding]
  have : {z : Fin r → ℂ | ∀ a b : Fin r → ℕ, ∑ j, a j • g.toFun j = ∑ j, b j • g.toFun j →
        ∏ j, z j ^ a j = ∏ j, z j ^ b j} =
      ⋂ a : Fin r → ℕ, ⋂ b : Fin r → ℕ,
        ⋂ _ : ∑ j, a j • g.toFun j = ∑ j, b j • g.toFun j,
          {z : Fin r → ℂ | ∏ j, z j ^ a j = ∏ j, z j ^ b j} := by
    ext z; simp
  rw [this]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_iInter fun _ ↦
    isClosed_eq (by fun_prop) (by fun_prop)

/-- The topology on the affine complex points of `S` induced by evaluation on a finite
generating family. It is independent of the family by `affinePointTopology_eq`. -/
@[instance_reducible]
noncomputable def affinePointTopology (g : AddGeneratingFamily S r) :
    TopologicalSpace (AffineSemigroupComplexPoint S) :=
  TopologicalSpace.induced (monomialEmbedding g) inferInstance

/-- The monomial-embedding topology is, by definition, the topology induced by the monomial
embedding of the family. -/
theorem affinePointTopology_def (g : AddGeneratingFamily S r) :
    affinePointTopology g = TopologicalSpace.induced (monomialEmbedding g) inferInstance := (rfl)

/-- The monomial embedding is continuous for the topology it induces. -/
theorem continuous_monomialEmbedding (g : AddGeneratingFamily S r) :
    Continuous[affinePointTopology g, inferInstance] (monomialEmbedding g) :=
  continuous_iff_le_induced.mpr (affinePointTopology_def g).le

/-- Evaluation at a fixed monomial is continuous for the monomial-embedding topology: it is a
monomial in the coordinates of the embedding. -/
theorem continuous_apply_single (g : AddGeneratingFamily S r) (s : S) :
    Continuous[affinePointTopology g, inferInstance]
      fun x : AffineSemigroupComplexPoint S ↦ x (MonoidAlgebra.single (ofAdd s) 1) := by
  -- install the induced topology as an instance so that the continuity combinators apply
  let _ := affinePointTopology g
  obtain ⟨a, ha⟩ := AddSubmonoid.exists_of_mem_closure_range g.toFun s (by
    rw [g.spans]
    trivial)
  simp only [apply_single_eq_prod_monomialEmbedding g ha]
  exact continuous_finsetProd _ fun k _ ↦
    ((continuous_apply k).comp (continuous_monomialEmbedding g)).pow _

/-- Evaluation at a fixed element of the coordinate ring is continuous for the
monomial-embedding topology: such an element is a finite linear combination of monomials, and
evaluation at each monomial is continuous. -/
theorem continuous_eval_const (g : AddGeneratingFamily S r)
    (f : MonoidAlgebra ℂ (Multiplicative S)) :
    Continuous[affinePointTopology g, inferInstance]
      fun x : AffineSemigroupComplexPoint S ↦ x f := by
  let _ := affinePointTopology g
  have hf : ∀ x : AffineSemigroupComplexPoint S,
      x f = ∑ m ∈ f.coeff.support, f.coeff m * x (MonoidAlgebra.single m 1) := by
    intro x
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single f]
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    have hsingle : MonoidAlgebra.single m (f.coeff m) =
        f.coeff m • MonoidAlgebra.single (R := ℂ) m 1 := by
      rw [MonoidAlgebra.smul_single', mul_one]
    rw [hsingle, map_smul, smul_eq_mul]
  simp only [hf]
  exact continuous_finsetSum _ fun m _ ↦
    continuous_const.mul (continuous_apply_single g (toAdd m))

/-- The monomial-embedding topology is the coarsest one making evaluation at every monomial
continuous. This description mentions no generating family, so it identifies the topologies
induced by any two of them. -/
theorem affinePointTopology_eq_iInf (g : AddGeneratingFamily S r) :
    affinePointTopology g =
      ⨅ s : S, TopologicalSpace.induced
        (fun x : AffineSemigroupComplexPoint S ↦ x (MonoidAlgebra.single (ofAdd s) 1))
        inferInstance := by
  refine le_antisymm (le_iInf fun s ↦ (continuous_apply_single g s).le_induced) ?_
  rw [affinePointTopology_def, induced_to_pi]
  simp only [monomialEmbedding_apply]
  exact le_iInf fun j ↦ iInf_le _ (g.toFun j)

/-- The monomial-embedding topology does not depend on the chosen finite generating family. -/
theorem affinePointTopology_eq (g : AddGeneratingFamily S r) (h : AddGeneratingFamily S r') :
    affinePointTopology g = affinePointTopology h :=
  (affinePointTopology_eq_iInf g).trans (affinePointTopology_eq_iInf h).symm

/-- A monomial embedding is a closed embedding for the topology it induces. -/
theorem isClosedEmbedding_monomialEmbedding (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    Topology.IsClosedEmbedding (monomialEmbedding g) :=
  letI := affinePointTopology g
  ⟨⟨⟨affinePointTopology_def g⟩, monomialEmbedding_injective g⟩,
    isClosed_range_monomialEmbedding g⟩

/-- The affine complex points of a finitely generated additive monoid are Hausdorff. -/
theorem t2Space_affinePointTopology (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    T2Space (AffineSemigroupComplexPoint S) :=
  letI := affinePointTopology g
  (isClosedEmbedding_monomialEmbedding g).isEmbedding.t2Space

/-- The affine complex points of a finitely generated additive monoid are second countable. -/
theorem secondCountableTopology_affinePointTopology (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    SecondCountableTopology (AffineSemigroupComplexPoint S) :=
  letI := affinePointTopology g
  (isClosedEmbedding_monomialEmbedding g).isEmbedding.secondCountableTopology

/-- The affine complex points of a finitely generated additive monoid are locally compact: the
monomial embedding realizes them as a closed subset of a complex affine space. -/
theorem locallyCompactSpace_affinePointTopology (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    LocallyCompactSpace (AffineSemigroupComplexPoint S) :=
  letI := affinePointTopology g
  (isClosedEmbedding_monomialEmbedding g).locallyCompactSpace

end TauCeti.Toric
