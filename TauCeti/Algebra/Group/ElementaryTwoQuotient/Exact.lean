/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic

/-!
# Right exactness of the maximal elementary-2 quotient

For a surjection `f : G →* H` of commutative groups, the induced map on maximal elementary-2
quotients `G/G² → H/H²` (`TauCeti.elementaryTwoQuotientMap`) is again surjective, and its kernel is
exactly the image of `ker f / (ker f)²`. In other words `G ↦ G/G²` is right exact: applying it to a
short exact sequence `1 → N → G → H → 1` of commutative groups leaves the sequence

`N/N² → G/G² → H/H² → 0`

exact. (It is not left exact: the first map need not be injective, since an element of `N` can
become a square in `G` without being a square in `N`.)

The rank consequences are the reason for the file. Writing `twoRank` for the `𝔽₂`-dimension of the
elementary-2 quotient, a surjection `G ↠ H` gives, under the finite-dimensionality hypotheses in
the statements below,

`twoRank H ≤ twoRank G ≤ twoRank H + twoRank (ker f)`,

so a quotient can only lose 2-rank, and can lose no more than the kernel carries. The functoriality
already available for `G ↦ G/G²` produces the induced map, inverts it when `f` is an isomorphism,
and gives the resulting equality of 2-ranks (`TauCeti.twoRank_eq_of_mulEquiv`), but says nothing
about the kernel of the induced map, nor about 2-ranks along a non-injective surjection. The
consumer is `TauCeti.NumberTheory.NumberField.NarrowClassGroup.ElementaryTwoQuotient`, which
applies these results to the forgetful surjection `Cl⁺(K) ↠ Cl(K)` to compare the narrow and the
ordinary `2`-rank of a number field — the comparison the genus-theory `2`-rank formula `t - 1`
needs for a real quadratic field (`TauCetiRoadmap/Multiquadratic/README.md`, "Layer 3: the genus
field and the 2-rank theorem").

## Main results

* `TauCeti.elementaryTwoQuotientMap_surjective`: the induced map is surjective.
* `TauCeti.ker_elementaryTwoQuotientMap`: **right exactness** — its kernel is the range of the map
  induced by `ker f ↪ G`; `TauCeti.elementaryTwoQuotientMap_eq_zero_iff` is the elementwise form.
* `TauCeti.twoRank_le_twoRank_of_surjective`: `twoRank H ≤ twoRank G` when `G/G²` is
  finite-dimensional.
* `TauCeti.twoRank_le_twoRank_add_twoRank_ker`: `twoRank G ≤ twoRank H + twoRank (ker f)` when
  `G/G²` and `ker f / (ker f)²` are finite-dimensional.
* `TauCeti.elementaryTwoQuotientMap_injective_iff_forall_isSquare_of_mem_ker` and
  `TauCeti.twoRank_eq_of_forall_isSquare_of_mem_ker`: the induced map is injective, and the two
  ranks agree when `ker f` consists of squares.
-/

public section

namespace TauCeti

variable {G H : Type*} [CommGroup G] [CommGroup H] {f : G →* H}

/-- **A surjection of commutative groups induces a surjection of elementary-2 quotients.** -/
theorem elementaryTwoQuotientMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (elementaryTwoQuotientMap f) := by
  intro y
  obtain ⟨h, rfl⟩ := elementaryTwoQuotientMk_surjective (G := H) y
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨elementaryTwoQuotientMk g, elementaryTwoQuotientMap_mk f g⟩

/-- The classes coming from `ker f` are killed by the induced map. This is the easy inclusion of
`TauCeti.ker_elementaryTwoQuotientMap`, and needs no surjectivity. -/
theorem range_elementaryTwoQuotientMap_ker_subtype_le_ker :
    LinearMap.range (elementaryTwoQuotientMap f.ker.subtype) ≤
      LinearMap.ker (elementaryTwoQuotientMap f) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := f.ker) y
  have hfg : f (g : G) = 1 := MonoidHom.mem_ker.1 g.2
  rw [LinearMap.mem_ker, elementaryTwoQuotientMap_mk, elementaryTwoQuotientMap_mk,
    Subgroup.coe_subtype, hfg, elementaryTwoQuotientMk_one]

/-- **Right exactness of the elementary-2 quotient.** For a surjection `f : G →* H`, an element of
`G/G²` dies in `H/H²` exactly when it is the class of an element of `ker f`. Equivalently, the
sequence `ker f / (ker f)² → G/G² → H/H² → 0` is exact. -/
theorem ker_elementaryTwoQuotientMap (hf : Function.Surjective f) :
    LinearMap.ker (elementaryTwoQuotientMap f) =
      LinearMap.range (elementaryTwoQuotientMap f.ker.subtype) := by
  refine le_antisymm ?_ range_elementaryTwoQuotientMap_ker_subtype_le_ker
  intro x hx
  obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) x
  rw [LinearMap.mem_ker, elementaryTwoQuotientMap_mk, elementaryTwoQuotientMk_eq_zero_iff] at hx
  obtain ⟨h, hh⟩ := hx
  obtain ⟨a, rfl⟩ := hf h
  -- Correcting `g` by the square `a ^ 2` produces a representative in `ker f` …
  have hmem : g * (a ^ 2)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hh, pow_two, mul_inv_cancel]
  refine ⟨elementaryTwoQuotientMk ⟨g * (a ^ 2)⁻¹, hmem⟩, ?_⟩
  -- … with the same class in `G/G²`, since the class of a square vanishes.
  rw [elementaryTwoQuotientMap_mk, Subgroup.coe_subtype, elementaryTwoQuotientMk_mul,
    elementaryTwoQuotientMk_inv, elementaryTwoQuotientMk_pow_two_eq_zero, neg_zero, add_zero]

/-- Elementwise form of `TauCeti.ker_elementaryTwoQuotientMap`: for a surjection `f`, a class in
`G/G²` maps to zero in `H/H²` iff it is represented by an element of `ker f`. -/
@[simp] theorem elementaryTwoQuotientMap_eq_zero_iff (hf : Function.Surjective f)
    (x : ElementaryTwoQuotient G) :
    elementaryTwoQuotientMap f x = 0 ↔
      ∃ g ∈ f.ker, elementaryTwoQuotientMk g = x := by
  rw [← LinearMap.mem_ker, ker_elementaryTwoQuotientMap hf, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := f.ker) y
    refine ⟨(g : G), g.2, ?_⟩
    rw [elementaryTwoQuotientMap_mk, Subgroup.coe_subtype]
  · rintro ⟨g, hg, rfl⟩
    exact ⟨elementaryTwoQuotientMk ⟨g, hg⟩, by rw [elementaryTwoQuotientMap_mk,
      Subgroup.coe_subtype]⟩

/-- **A quotient group can only lose 2-rank.** If `f : G →* H` is surjective and `G/G²` is
finite-dimensional, then `twoRank H ≤ twoRank G`. -/
theorem twoRank_le_twoRank_of_surjective [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)]
    (hf : Function.Surjective f) : twoRank H ≤ twoRank G :=
  LinearMap.finrank_le_finrank_of_surjective (elementaryTwoQuotientMap_surjective hf)

/-- **A quotient group loses no more 2-rank than its kernel carries.** If `f : G →* H` is
surjective, and both `G/G²` and `ker f / (ker f)²` are finite-dimensional, then
`twoRank G ≤ twoRank H + twoRank (ker f)`. -/
theorem twoRank_le_twoRank_add_twoRank_ker
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)]
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient f.ker)]
    (hf : Function.Surjective f) : twoRank G ≤ twoRank H + twoRank f.ker := by
  have hrk := (elementaryTwoQuotientMap f).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (elementaryTwoQuotientMap_surjective hf), finrank_top] at hrk
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (elementaryTwoQuotientMap f)) ≤
      twoRank f.ker := by
    rw [ker_elementaryTwoQuotientMap hf]
    exact LinearMap.finrank_range_le _
  simp only [twoRank_def] at hker ⊢
  omega

/-- **When a quotient loses no 2-rank at all.** For a surjection `f : G →* H`, the induced map on
elementary-2 quotients is injective — hence an isomorphism — exactly when every element of `ker f`
is already a square in `G`. -/
theorem elementaryTwoQuotientMap_injective_iff_forall_isSquare_of_mem_ker
    (hf : Function.Surjective f) :
    Function.Injective (elementaryTwoQuotientMap f) ↔ ∀ g ∈ f.ker, IsSquare g := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  constructor
  · intro h g hg
    have hfg : f g = 1 := MonoidHom.mem_ker.1 hg
    refine (elementaryTwoQuotientMk_eq_zero_iff g).1 (h _ ?_)
    rw [LinearMap.mem_ker, elementaryTwoQuotientMap_mk, hfg, elementaryTwoQuotientMk_one]
  · intro h x hx
    obtain ⟨g, hg, rfl⟩ := (elementaryTwoQuotientMap_eq_zero_iff hf x).1 hx
    exact (elementaryTwoQuotientMk_eq_zero_iff g).2 (h g hg)

/-- **A quotient by a kernel of squares preserves the 2-rank.** If `f : G →* H` is surjective and
every element of `ker f` is a square in `G`, then `twoRank G = twoRank H`. -/
theorem twoRank_eq_of_forall_isSquare_of_mem_ker (hf : Function.Surjective f)
    (h : ∀ g ∈ f.ker, IsSquare g) : twoRank G = twoRank H := by
  have hbij : Function.Bijective (elementaryTwoQuotientMap f) :=
    ⟨(elementaryTwoQuotientMap_injective_iff_forall_isSquare_of_mem_ker hf).2 h,
      elementaryTwoQuotientMap_surjective hf⟩
  simpa only [twoRank_def] using (LinearEquiv.ofBijective _ hbij).finrank_eq

end TauCeti
