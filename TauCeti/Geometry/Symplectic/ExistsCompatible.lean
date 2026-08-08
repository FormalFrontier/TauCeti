/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Every symplectic vector space carries a compatible almost complex structure

Tameness and compatibility of an almost complex structure `J` with a symplectic form `ω` are the
standing hypotheses of the analytic Heegaard Floer roadmap, and until now nothing said that they
can be met: `TauCeti.stdSymplecticForm` exhibits one compatible triple on a doubled inner product
space `V × V`, but an arbitrary symplectic form on an arbitrary finite-dimensional real vector
space came with no supply of structures at all. This file removes that gap, proving

`TauCeti.SymplecticForm.exists_compatible`: for every symplectic form `ω` on a finite-dimensional
real vector space `V` there is an almost complex structure `J` with `ω.Compatible J`.

The proof is the classical linear normal-form induction, splitting off one *hyperbolic pair* at a
time rather than diagonalizing a metric. Nondegeneracy provides, for any `x ≠ 0`, a partner `y`
with `ω x y = 1`; the plane `L = span {x, y}` meets its symplectic complement `L^ω` only in `0`, so
`ω` restricts nondegenerately to both, `V = L ⊕ L^ω`, and `ω` is the product of the two
restrictions. On `L` the pair `(x, y)` identifies `(L, ω|_L)` with the standard plane `(ℝ × ℝ, ω₀)`
of `TauCeti.stdSymplecticForm`, which is compatible with
`TauCeti.AlmostComplexStructure.product`; on `L^ω`, whose dimension has dropped by two, the
inductive hypothesis applies. The two structures are recombined by
`TauCeti.SymplecticForm.prod_compatible` and transported back along the splitting. This is the
linear half of the standard statement that the space of `ω`-compatible almost complex structures is
nonempty and contractible, in the conventions of McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, Section 2.2, which `TauCeti/Geometry/Symplectic/AlmostComplex.lean` already
follows.

## Main declarations

* `TauCeti.SymplecticForm.restrict`: the restriction of `ω` to a subspace on which it stays
  nondegenerate, again a symplectic form.
* `TauCeti.SymplecticForm.nondegenerate_restrict_of_disjoint_orthogonal` and
  `TauCeti.SymplecticForm.isCompl_orthogonal_iff_disjoint`: a subspace meeting its symplectic
  complement only in `0` carries a nondegenerate restriction and is complementary to it.
* `TauCeti.SymplecticForm.isSymplectomorphism_prodEquivOfIsCompl`: along such a splitting `ω` is
  the product of its two restrictions, and
  `TauCeti.SymplecticForm.exists_compatible_of_splitting` assembles compatible structures on the
  two summands into one on the whole space.
* `TauCeti.SymplecticForm.exists_apply_eq_one`: nondegeneracy produces a hyperbolic partner;
  `TauCeti.SymplecticForm.apply_smul_add_smul` evaluates `ω` in the coordinates the pair gives, and
  `TauCeti.SymplecticForm.disjoint_orthogonal_span_pair` says the plane it spans is a symplectic
  subspace.
* `TauCeti.SymplecticForm.exists_compatible` and `TauCeti.SymplecticForm.exists_tames`: the
  existence theorems.
* `TauCeti.SymplecticForm.even_finrank` and `TauCeti.SymplecticForm.isEmpty_of_odd_finrank`: a
  symplectic vector space has even dimension, so an odd-dimensional space carries no symplectic
  form at all.
* `TauCeti.SymplecticForm.IsLagrangian.exists_compatible_isMaximalTotallyReal`: every Lagrangian
  subspace is maximal totally real for some compatible structure, so the totally real boundary
  conditions of Lanes F3 and F4 are never vacuous.

The splitting lemmas are stated for a general subspace rather than only for the hyperbolic planes
of the induction, since the symplectic complement splitting is what symplectic reduction and the
`Sym^g` local models will use again.
-/

public section

namespace TauCeti

namespace SymplecticForm

open Module

universe u

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Restricting a symplectic form to a subspace -/

/-- The restriction of a symplectic form to a subspace on which it remains nondegenerate.

Nondegeneracy is genuinely a hypothesis: `ω` restricts to `0` on any isotropic subspace. -/
@[expose] def restrict (ω : SymplecticForm V) (L : Submodule ℝ V)
    (h : (ω.toBilinForm.restrict L).Nondegenerate) : SymplecticForm L where
  toBilinForm := ω.toBilinForm.restrict L
  isAlt v := ω.isAlt (v : V)
  nondegenerate := h

@[simp]
lemma restrict_apply (ω : SymplecticForm V) (L : Submodule ℝ V)
    (h : (ω.toBilinForm.restrict L).Nondegenerate) (v w : L) :
    ω.restrict L h v w = ω (v : V) (w : V) :=
  rfl

/-- A subspace meeting its symplectic complement only in `0` carries a nondegenerate restriction
of `ω`. -/
lemma nondegenerate_restrict_of_disjoint_orthogonal (ω : SymplecticForm V) {L : Submodule ℝ V}
    (h : Disjoint L (ω.orthogonal L)) : (ω.toBilinForm.restrict L).Nondegenerate :=
  ω.toBilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω.isRefl h

/-- Bilinear expansion of `ω` on the plane spanned by a pair of vectors: only the mixed term
`ω x y` survives. -/
lemma apply_smul_add_smul (ω : SymplecticForm V) (x y : V) (a b c d : ℝ) :
    ω (a • x + b • y) (c • x + d • y) = (a * d - b * c) * ω x y := by
  have hyx : ω y x = -ω x y := (ω.neg_eq x y).symm
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    self_eq_zero, hyx]
  ring

/-- For a hyperbolic pair `ω x y = 1`, pairing a vector of the plane it spans against `y` reads
off the first coordinate. -/
lemma apply_smul_add_smul_right (ω : SymplecticForm V) {x y : V} (h : ω x y = 1) (a b : ℝ) :
    ω (a • x + b • y) y = a := by
  simp [h]

/-- For a hyperbolic pair `ω x y = 1`, pairing `x` against a vector of the plane it spans reads
off the second coordinate. -/
lemma apply_smul_add_smul_left (ω : SymplecticForm V) {x y : V} (h : ω x y = 1) (a b : ℝ) :
    ω x (a • x + b • y) = b := by
  simp [h]

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- A subspace is complementary to its symplectic complement exactly when it meets it only in
`0`. -/
lemma isCompl_orthogonal_iff_disjoint (ω : SymplecticForm V) (L : Submodule ℝ V) :
    IsCompl L (ω.orthogonal L) ↔ Disjoint L (ω.orthogonal L) :=
  LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint ω.isRefl

/-- The symplectic complement of a subspace disjoint from it is itself disjoint from *its*
symplectic complement, so `ω` restricts nondegenerately to it as well. -/
lemma disjoint_orthogonal_orthogonal (ω : SymplecticForm V) {L : Submodule ℝ V}
    (h : Disjoint L (ω.orthogonal L)) :
    Disjoint (ω.orthogonal L) (ω.orthogonal (ω.orthogonal L)) := by
  rw [ω.orthogonal_orthogonal L]
  exact h.symm

end FiniteDimensional

/-- Along the splitting `V = L ⊕ L^ω`, the symplectic form is the product of its restrictions to
the two summands: the cross terms vanish by the very definition of the symplectic complement. -/
lemma isSymplectomorphism_prodEquivOfIsCompl (ω : SymplecticForm V) {L : Submodule ℝ V}
    (hL : (ω.toBilinForm.restrict L).Nondegenerate)
    (hL' : (ω.toBilinForm.restrict (ω.orthogonal L)).Nondegenerate)
    (hcompl : IsCompl L (ω.orthogonal L)) :
    IsSymplectomorphism ((ω.restrict L hL).prod (ω.restrict (ω.orthogonal L) hL')) ω
      (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hcompl) := by
  rw [isSymplectomorphism_iff]
  intro p q
  have h₁ : ω (p.1 : V) (q.2 : V) = 0 := mem_orthogonal_iff.1 q.2.2 _ p.1.2
  have h₂ : ω (p.2 : V) (q.1 : V) = 0 := mem_orthogonal_iff'.1 p.2.2 _ q.1.2
  simp only [Submodule.coe_prodEquivOfIsCompl', prod_apply, restrict_apply, map_add,
    LinearMap.add_apply, h₁, h₂]
  ring

/-- Compatible structures on the two halves of a symplectic splitting `V = L ⊕ L^ω` assemble into
a compatible structure on `V`. -/
lemma exists_compatible_of_splitting (ω : SymplecticForm V) {L : Submodule ℝ V}
    (hL : (ω.toBilinForm.restrict L).Nondegenerate)
    (hL' : (ω.toBilinForm.restrict (ω.orthogonal L)).Nondegenerate)
    (hcompl : IsCompl L (ω.orthogonal L))
    (hJ : ∃ J : AlmostComplexStructure L, (ω.restrict L hL).Compatible J)
    (hJ' : ∃ J : AlmostComplexStructure (ω.orthogonal L),
      (ω.restrict (ω.orthogonal L) hL').Compatible J) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J := by
  obtain ⟨JL, hJL⟩ := hJ
  obtain ⟨JL', hJL'⟩ := hJ'
  refine ⟨(JL.prod JL').transport (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hcompl), ?_⟩
  have hcomp := (prod_compatible hJL hJL').transport
    (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hcompl)
  rwa [isSymplectomorphism_iff_transport_eq.1
    (ω.isSymplectomorphism_prodEquivOfIsCompl hL hL' hcompl)] at hcomp

/-! ### Hyperbolic pairs and the standard plane -/

/-- Nondegeneracy supplies a **hyperbolic partner**: every nonzero vector `x` admits a vector `y`
with `ω x y = 1`. -/
lemma exists_apply_eq_one (ω : SymplecticForm V) {x : V} (hx : x ≠ 0) : ∃ y : V, ω x y = 1 := by
  obtain ⟨y, hy⟩ : ∃ y : V, ω x y ≠ 0 := by
    by_contra hcon
    exact hx (ω.separatingLeft x fun y => not_not.1 fun hne => hcon ⟨y, hne⟩)
  exact ⟨(ω x y)⁻¹ • y, by simp [inv_mul_cancel₀ hy]⟩

section Plane

variable (ω : SymplecticForm V) {x y : V}

/-- The parametrization `(a, b) ↦ a • x + b • y` of the plane spanned by a pair of vectors. -/
private def pairMap (x y : V) : (ℝ × ℝ) →ₗ[ℝ] V :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight x + (LinearMap.snd ℝ ℝ ℝ).smulRight y

private lemma pairMap_apply (x y : V) (p : ℝ × ℝ) : pairMap x y p = p.1 • x + p.2 • y := rfl

private lemma pairMap_injective (h : ω x y = 1) : Function.Injective (pairMap x y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  rw [pairMap_apply] at hp
  have ha : p.1 = 0 :=
    (ω.apply_smul_add_smul_right h p.1 p.2).symm.trans (by rw [hp]; simp)
  have hb : p.2 = 0 :=
    (ω.apply_smul_add_smul_left h p.1 p.2).symm.trans (by rw [hp]; simp)
  exact Prod.ext_iff.2 ⟨ha, hb⟩

private lemma range_pairMap (x y : V) :
    LinearMap.range (pairMap x y) = Submodule.span ℝ ({x, y} : Set V) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨p, rfl⟩
    rw [pairMap_apply]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    rintro v hv
    rcases hv with rfl | hv
    · exact ⟨(1, 0), by simp [pairMap_apply]⟩
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨(0, 1), by simp [pairMap_apply]⟩

/-- The plane spanned by a hyperbolic pair `x, y` with `ω x y = 1`, presented as a linear copy of
the standard plane `ℝ × ℝ`. -/
private noncomputable def planeEquiv (h : ω x y = 1) :
    (ℝ × ℝ) ≃ₗ[ℝ] (Submodule.span ℝ ({x, y} : Set V)) :=
  (LinearEquiv.ofInjective (pairMap x y) (ω.pairMap_injective h)).trans
    (LinearEquiv.ofEq _ _ (range_pairMap x y))

private lemma coe_planeEquiv_apply (h : ω x y = 1) (p : ℝ × ℝ) :
    ((ω.planeEquiv h p : Submodule.span ℝ ({x, y} : Set V)) : V) = p.1 • x + p.2 • y := rfl

/-- A hyperbolic pair spans a symplectic plane: it is disjoint from its own symplectic
complement, so `ω` restricts to it nondegenerately. -/
lemma disjoint_orthogonal_span_pair (h : ω x y = 1) :
    Disjoint (Submodule.span ℝ ({x, y} : Set V))
      (ω.orthogonal (Submodule.span ℝ ({x, y} : Set V))) := by
  rw [Submodule.disjoint_def]
  intro v hv hv'
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  have hxmem : x ∈ Submodule.span ℝ ({x, y} : Set V) := Submodule.subset_span (by simp)
  have hymem : y ∈ Submodule.span ℝ ({x, y} : Set V) := Submodule.subset_span (by simp)
  have ha : a = 0 :=
    (ω.apply_smul_add_smul_right h a b).symm.trans (mem_orthogonal_iff'.1 hv' y hymem)
  have hb : b = 0 :=
    (ω.apply_smul_add_smul_left h a b).symm.trans (mem_orthogonal_iff.1 hv' x hxmem)
  simp [ha, hb]

/-- Read through the parametrization by a hyperbolic pair, `ω` becomes the standard symplectic
form of the plane `ℝ × ℝ`. -/
private lemma isSymplectomorphism_planeEquiv (h : ω x y = 1)
    (hL : (ω.toBilinForm.restrict (Submodule.span ℝ ({x, y} : Set V))).Nondegenerate) :
    IsSymplectomorphism (stdSymplecticForm (V := ℝ))
      (ω.restrict (Submodule.span ℝ ({x, y} : Set V)) hL) (ω.planeEquiv h) := by
  rw [isSymplectomorphism_iff]
  intro p q
  rw [restrict_apply, coe_planeEquiv_apply, coe_planeEquiv_apply, ω.apply_smul_add_smul, h,
    stdSymplecticForm_apply, Real.inner_apply, Real.inner_apply]
  ring

/-- The plane spanned by a hyperbolic pair carries a compatible almost complex structure,
transported from the standard compatible triple on `ℝ × ℝ`. -/
private lemma exists_compatible_restrict_span_pair (h : ω x y = 1)
    (hL : (ω.toBilinForm.restrict (Submodule.span ℝ ({x, y} : Set V))).Nondegenerate) :
    ∃ J : AlmostComplexStructure (Submodule.span ℝ ({x, y} : Set V)),
      (ω.restrict (Submodule.span ℝ ({x, y} : Set V)) hL).Compatible J := by
  refine ⟨(AlmostComplexStructure.product ℝ).transport (ω.planeEquiv h), ?_⟩
  have hcomp := (stdSymplecticForm_compatible_product (V := ℝ)).transport (ω.planeEquiv h)
  rwa [isSymplectomorphism_iff_transport_eq.1 (ω.isSymplectomorphism_planeEquiv h hL)] at hcomp

end Plane

/-! ### Existence of a compatible almost complex structure -/

/-- On a zero-dimensional space the zero endomorphism is an almost complex structure, and it is
compatible with the unique symplectic form. This is the base of the induction. -/
lemma exists_compatible_of_subsingleton [Subsingleton V] (ω : SymplecticForm V) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J := by
  refine ⟨⟨0, by ext v; simp [Subsingleton.elim v (0 : V)]⟩, Compatible.of_tames ?_ ?_⟩
  · rw [invariant_iff]
    intro v w
    rw [Subsingleton.elim v (0 : V), Subsingleton.elim w (0 : V)]
    simp
  · exact fun v hv => absurd (Subsingleton.elim v (0 : V)) hv

private theorem exists_compatible_aux (n : ℕ) :
    ∀ {U : Type u} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U] (ω : SymplecticForm U),
      finrank ℝ U ≤ n → ∃ J : AlmostComplexStructure U, ω.Compatible J := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U _ _ _ ω hn
    rcases subsingleton_or_nontrivial U with _ | _
    · exact ω.exists_compatible_of_subsingleton
    obtain ⟨x, hx⟩ := exists_ne (0 : U)
    obtain ⟨y, hxy⟩ := ω.exists_apply_eq_one hx
    have hdisj : Disjoint (Submodule.span ℝ ({x, y} : Set U))
        (ω.orthogonal (Submodule.span ℝ ({x, y} : Set U))) := ω.disjoint_orthogonal_span_pair hxy
    have hL := ω.nondegenerate_restrict_of_disjoint_orthogonal hdisj
    have hL' := ω.nondegenerate_restrict_of_disjoint_orthogonal
      (ω.disjoint_orthogonal_orthogonal hdisj)
    have hcompl := (ω.isCompl_orthogonal_iff_disjoint _).2 hdisj
    refine ω.exists_compatible_of_splitting hL hL' hcompl
      (ω.exists_compatible_restrict_span_pair hxy hL) ?_
    have hxmem : x ∈ Submodule.span ℝ ({x, y} : Set U) := Submodule.subset_span (by simp)
    have hUpos : 0 < finrank ℝ U := Module.finrank_pos_iff_exists_ne_zero.2 ⟨x, hx⟩
    have hLpos : 0 < finrank ℝ (Submodule.span ℝ ({x, y} : Set U)) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hxmem⟩, by simpa using hx⟩
    have hlt : finrank ℝ (ω.orthogonal (Submodule.span ℝ ({x, y} : Set U))) < finrank ℝ U := by
      rw [ω.finrank_orthogonal _]
      exact Nat.sub_lt hUpos hLpos
    exact ih _ (lt_of_lt_of_le hlt hn) (ω.restrict _ hL') le_rfl

/-- **Every symplectic vector space carries a compatible almost complex structure.**

For a symplectic form `ω` on a finite-dimensional real vector space there is an almost complex
structure `J` that is `ω`-invariant and satisfies `ω(v, Jv) > 0` for `v ≠ 0`. In particular the
tameness and compatibility hypotheses used throughout the analytic Heegaard Floer roadmap are
never vacuous. -/
theorem exists_compatible [FiniteDimensional ℝ V] (ω : SymplecticForm V) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J :=
  exists_compatible_aux _ ω le_rfl

/-- Every finite-dimensional symplectic vector space is tamed by some almost complex structure. -/
theorem exists_tames [FiniteDimensional ℝ V] (ω : SymplecticForm V) :
    ∃ J : AlmostComplexStructure V, ω.Tames J :=
  let ⟨J, hJ⟩ := ω.exists_compatible
  ⟨J, hJ.tames⟩

/-- A finite-dimensional symplectic vector space has even dimension: a compatible almost complex
structure makes it a complex vector space. -/
theorem even_finrank [FiniteDimensional ℝ V] (ω : SymplecticForm V) : Even (finrank ℝ V) :=
  let ⟨J, _⟩ := ω.exists_compatible
  J.even_finrank_real

/-- A real vector space of odd dimension carries no symplectic form. -/
theorem isEmpty_of_odd_finrank [FiniteDimensional ℝ V] (h : Odd (finrank ℝ V)) :
    IsEmpty (SymplecticForm V) :=
  ⟨fun ω => (Nat.not_even_iff_odd.2 h) ω.even_finrank⟩

/-- Every Lagrangian subspace of a finite-dimensional symplectic vector space is maximal totally
real for some compatible almost complex structure, so the totally real boundary conditions of
Lagrangian Floer homology are never vacuous. -/
theorem IsLagrangian.exists_compatible_isMaximalTotallyReal [FiniteDimensional ℝ V]
    {ω : SymplecticForm V} {L : Submodule ℝ V} (hL : ω.IsLagrangian L) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J ∧ IsMaximalTotallyReal J.toLinearMap L :=
  let ⟨J, hJ⟩ := ω.exists_compatible
  ⟨J, hJ, hL.isMaximalTotallyReal_of_compatible hJ⟩

end SymplecticForm

end TauCeti
