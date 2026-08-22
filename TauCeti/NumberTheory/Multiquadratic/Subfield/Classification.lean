/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import TauCeti.Data.Finset.Basic
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Subfield
public import TauCeti.NumberTheory.Multiquadratic.Subfield.Count

/-!
# The quadratic subfields are exactly the subset-product subfields

For square roots `root i` of radicands `d i ∈ K` over a field `K` with `2 ≠ 0`, the nonempty
subset products `∏_{i ∈ S} root i` generate quadratic subfields of the multiquadratic field
`M = K(rootᵢ : i)`, and under square-class independence distinct nonempty subsets give distinct
subfields (`TauCeti.NumberTheory.Multiquadratic.Quadratic.Subfield`). Separately, `M` has exactly
`2ⁿ - 1` quadratic subfields (`TauCeti.NumberTheory.Multiquadratic.Subfield.Count`). Since the
nonempty subsets of an `n`-element index type also number `2ⁿ - 1`, the injective subset-product
assignment is forced by counting to be a **bijection**: every quadratic subfield of `M` is
`K(∏_{i ∈ S} root i)` for a unique nonempty subset `S`.

This completes the arithmetic description of the quadratic subfield family: the abstract
subfield/subspace dictionary counts the quadratic subfields as hyperplanes of `𝔽₂ⁿ`, and this file
identifies each of them concretely as a subset-product radical extension, the form the genus-field
constructions consume.

## Main results

* `TauCeti.Multiquadratic.quadraticSubfieldOfFinset`: the well-defined assignment
  `S ↦ K(∏_{i ∈ S} root i)` from the nonempty subsets of the index type to the quadratic subfields
  of `M`.
* `TauCeti.Multiquadratic.quadraticSubfieldOfFinset_bijective`: that assignment is a bijection.
* `TauCeti.Multiquadratic.exists_finset_of_finrank_two`: **classification** — every quadratic
  subfield of `M` is a subset-product subfield `K(∏_{i ∈ S} root i)` for some nonempty `S`.
* `TauCeti.Multiquadratic.nonemptyFinsetEquivQuadraticSubfield`: the bijection packaged as an
  equivalence.

## Provenance

The two ingredients this synthesises — the injective subset-product family and the hyperplane
count of the quadratic subfields — are built, with the rest of the multiquadratic Layer 0, on the
square-class machinery migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization of
L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

/-- The subset-product root of `S`, as an element of the multiquadratic field
`M = K(rootᵢ : i)`. -/
@[expose] def prodRootMem (root : ι → L) (S : Finset ι) :
    ↥(adjoin K (Set.range root)) :=
  ⟨∏ i ∈ S, root i, prod_root_mem_adjoin S⟩

@[simp] theorem prodRootMem_coe (S : Finset ι) :
    (prodRootMem (K := K) root S : L) = ∏ i ∈ S, root i := rfl

/-- **The square of a subset-product root, computed inside `M`.** The `M`-level companion of
`prod_root_sq`: `prodRootMem root S` squares to the image under `K → M` of the radicand product
`∏_{i ∈ S} d i`. -/
theorem prodRootMem_sq (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (S : Finset ι) :
    prodRootMem (K := K) root S ^ 2 = algebraMap K (adjoin K (Set.range root)) (∏ i ∈ S, d i) := by
  apply Subtype.ext
  have h := prod_root_sq hroot S
  norm_num at h ⊢
  exact h

/-- **A nonempty subset-product subfield of `M` is quadratic.** Computed inside `M`, the simple
extension `K(∏_{i ∈ S} root i)` has the same degree as its `L`-level counterpart, which is `2`
when the radicand product `∏_{i ∈ S} d i` is not a square. -/
theorem finrank_adjoin_prodRootMem [NeZero (2 : K)] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    {S : Finset ι} (hSsq : ¬ IsSquare (∏ i ∈ S, d i)) :
    Module.finrank K (adjoin K {prodRootMem (K := K) root S}) = 2 := by
  -- Transport the degree across the `M`-into-`L` lift algebra equivalence.
  rw [LinearEquiv.finrank_eq (liftAlgEquiv (adjoin K {prodRootMem (K := K) root S})).toLinearEquiv,
    lift_adjoin_simple, prodRootMem_coe]
  exact finrank_adjoin_prod_root hroot hSsq

variable (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
  (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))

/-- **The subset-product quadratic subfield of `M` attached to a nonempty subset.** Under
square-class independence, each nonempty subset `S` of the index type names the quadratic subfield
`K(∏_{i ∈ S} root i)` of `M = K(rootᵢ : i)`. -/
@[expose] def quadraticSubfieldOfFinset [NeZero (2 : K)] (S : {S : Finset ι // S.Nonempty}) :
    {F : IntermediateField K (adjoin K (Set.range root)) // Module.finrank K F = 2} :=
  ⟨adjoin K {prodRootMem (K := K) root S.1}, finrank_adjoin_prodRootMem hroot (hindep S.1 S.2)⟩

/-- The subfield underlying `quadraticSubfieldOfFinset hroot hindep S` is
`K(∏_{i ∈ S} root i)`. -/
@[simp] theorem quadraticSubfieldOfFinset_val [NeZero (2 : K)] (S : {S : Finset ι // S.Nonempty}) :
    (quadraticSubfieldOfFinset hroot hindep S : IntermediateField K (adjoin K (Set.range root)))
      = adjoin K {prodRootMem (K := K) root S.1} := rfl

include hroot hindep in
/-- **Distinct nonempty subsets give distinct quadratic subfields.** The subset-product assignment
`quadraticSubfieldOfFinset` is injective: this is the `M`-level reading of
`eq_of_adjoin_prod_root_eq`, transported across the lift. -/
theorem quadraticSubfieldOfFinset_injective [NeZero (2 : K)] :
    Function.Injective (quadraticSubfieldOfFinset hroot hindep) := by
  rintro ⟨S, hS⟩ ⟨T, hT⟩ h
  refine Subtype.ext (eq_of_adjoin_prod_root_eq hroot hindep hS ?_)
  -- The `M`-level equality of subfields lifts to an `L`-level equality of subset-product fields.
  have h' : adjoin K {prodRootMem (K := K) root S} = adjoin K {prodRootMem (K := K) root T} := by
    have hval := congrArg Subtype.val h
    rwa [quadraticSubfieldOfFinset_val, quadraticSubfieldOfFinset_val] at hval
  have := congrArg IntermediateField.lift h'
  rwa [lift_adjoin_simple, lift_adjoin_simple, prodRootMem_coe, prodRootMem_coe] at this

include hroot hindep in
/-- **The subset-product assignment is a bijection.** Injective by
`quadraticSubfieldOfFinset_injective`, its domain (the nonempty subsets) and codomain (the
quadratic subfields) both have cardinality `2ⁿ - 1`, so the injection is a bijection. -/
theorem quadraticSubfieldOfFinset_bijective [Finite ι] [NeZero (2 : K)] :
    Function.Bijective (quadraticSubfieldOfFinset hroot hindep) := by
  classical
  let := Fintype.ofFinite ι
  -- The quadratic subfields form a finite type: they inject into the finite subspace lattice.
  have : Finite (Submodule (ZMod 2) (ι → ZMod 2)) :=
    Finite.of_injective _ (SetLike.coe_injective (A := Submodule (ZMod 2) (ι → ZMod 2)))
  have : Finite (IntermediateField K (adjoin K (Set.range root))) :=
    Finite.of_equiv _
      ((intermediateFieldEquivSubmodule hroot hindep).toEquiv.trans OrderDual.ofDual).symm
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨quadraticSubfieldOfFinset_injective hroot hindep, ?_⟩
  rw [card_nonempty_finset, card_quadratic_intermediateField_adjoin_range hroot hindep]

include hroot hindep in
/-- **Classification of the quadratic subfields.** Under square-class independence, every quadratic
subfield `F` of the multiquadratic field `M = K(rootᵢ : i)` is a subset-product subfield: there is a
nonempty subset `S` with `F = K(∏_{i ∈ S} root i)`. (The subset is in fact unique, by
`quadraticSubfieldOfFinset_bijective`, but this statement asserts only existence.) -/
theorem exists_finset_of_finrank_two [Finite ι] [NeZero (2 : K)]
    (F : IntermediateField K (adjoin K (Set.range root))) (hF : Module.finrank K F = 2) :
    ∃ S : Finset ι, S.Nonempty ∧ F = adjoin K {prodRootMem (K := K) root S} := by
  obtain ⟨⟨S, hS⟩, hSeq⟩ :=
    (quadraticSubfieldOfFinset_bijective hroot hindep).surjective ⟨F, hF⟩
  refine ⟨S, hS, ?_⟩
  have hval := congrArg Subtype.val hSeq
  rw [quadraticSubfieldOfFinset_val] at hval
  exact hval.symm

/-- **Classification inside a generated ambient field.** If the roots `root i` generate `L` over
`K`, every quadratic intermediate field of `L / K` is generated by a product of a nonempty finite
subset of those roots. This is the whole-field form of `exists_finset_of_finrank_two`, which
states the same classification for the intermediate fields of the adjoin presentation
`K(root i : i)`; use this version when `L` is presented as a field in its own right. -/
theorem exists_finset_of_finrank_two_of_adjoin_eq_top [Finite ι] [NeZero (2 : K)]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (htop : adjoin K (Set.range root) = ⊤) (F : IntermediateField K L)
    (hF : Module.finrank K F = 2) :
    ∃ S : Finset ι, S.Nonempty ∧ F = adjoin K {∏ i ∈ S, root i} := by
  let e : adjoin K (Set.range root) ≃ₐ[K] L :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  let F' : IntermediateField K (adjoin K (Set.range root)) := F.comap e.toAlgHom
  have hmapF' : F'.map e.toAlgHom = F :=
    IntermediateField.map_comap_eq_self_of_surjective e.surjective F
  let eF : F' ≃ₐ[K] F :=
    (IntermediateField.equivMap F' e.toAlgHom).trans (IntermediateField.equivOfEq hmapF')
  have hF' : Module.finrank K F' = 2 :=
    (LinearEquiv.finrank_eq eF.toLinearEquiv).trans hF
  obtain ⟨S, hS, hF'S⟩ := exists_finset_of_finrank_two hroot hindep F' hF'
  refine ⟨S, hS, ?_⟩
  have hmap := congrArg (IntermediateField.map e.toAlgHom) hF'S
  rw [hmapF', IntermediateField.adjoin_map, Set.image_singleton] at hmap
  simpa [e, prodRootMem] using hmap

include hroot hindep in
/-- **The quadratic subfields of `M` are indexed by the nonempty subsets.** The bijection
`quadraticSubfieldOfFinset`, packaged as an equivalence between the nonempty subsets of the index
type and the quadratic subfields of the multiquadratic field. -/
@[expose] noncomputable def nonemptyFinsetEquivQuadraticSubfield [Finite ι] [NeZero (2 : K)] :
    {S : Finset ι // S.Nonempty} ≃
      {F : IntermediateField K (adjoin K (Set.range root)) // Module.finrank K F = 2} :=
  Equiv.ofBijective _ (quadraticSubfieldOfFinset_bijective hroot hindep)

include hroot hindep in
/-- `nonemptyFinsetEquivQuadraticSubfield` sends a nonempty subset `S` to the subset-product
subfield `quadraticSubfieldOfFinset hroot hindep S`. -/
@[simp] theorem nonemptyFinsetEquivQuadraticSubfield_apply [Finite ι] [NeZero (2 : K)]
    (S : {S : Finset ι // S.Nonempty}) :
    nonemptyFinsetEquivQuadraticSubfield hroot hindep S
      = quadraticSubfieldOfFinset hroot hindep S :=
  rfl

end TauCeti.Multiquadratic
