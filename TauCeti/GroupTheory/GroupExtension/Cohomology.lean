/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# Factor sets up to cohomology are the second cohomology group

A factor set `α : FactorSet G M` is by definition a normalized multiplicative `2`-cocycle, so it
has a class in `H²(G, M) = groupCohomology.H2 (Rep.ofMulDistribMulAction G M)`. This file builds
that class and proves that it is a *complete* invariant of `α` modulo coboundaries: the map

`FactorSet G M ⧸ (cohomologous) → H²(G, M)`

is a bijection (`TauCeti.FactorSet.cohomologyClassEquiv`). Both halves need an argument. Two factor
sets have the same class exactly when their quotient is a coboundary — the interesting direction
here is that a coboundary witnessing this is automatically normalized, so no compatibility with the
normalization of `α` and `β` has to be arranged. And every class is the class of a factor set: an
arbitrary `2`-cocycle need not be normalized, but dividing it by the coboundary of the constant
function `f (1, 1)` normalizes it without moving its class
(`TauCeti.FactorSet.ofIsMulCocycle₂`).

Read through the group extensions of `TauCeti/GroupTheory/GroupExtension/Of/FactorSet.lean` and
`TauCeti/GroupTheory/GroupExtension/FactorSetOfSection.lean`, this says several things about
extensions of `G` by an abelian kernel `M` inducing the given action: the class read off an
extension does not depend on the normalized section it is read from
(`TauCeti.GroupExtension.cohomologyClass_factorSet_eq`) and is unchanged by an equivalence of
extensions, and two such extensions are equivalent exactly when their classes agree
(`TauCeti.GroupExtension.nonempty_equiv_iff_cohomologyClass_factorSet_eq`), so the class is a
complete invariant of the extension. The class vanishes exactly on the split extensions.
Specializing the action to the trivial action of `G` on
`M = kˣ` gives `H²(G, kˣ)`, the group that classifies the factor sets of projective representations
of `G`, equivalently the central extensions of `G` by `kˣ` up to equivalence.

## Universes

`Rep ℤ G` puts the group and the module in the universe of `ℤ`, so the whole file is stated for
`G M : Type`. This is the same restriction Mathlib's own multiplicative interface to
`groupCohomology.cocycles₂` carries; `FactorSet G M` itself is universe-polymorphic and stays so.

## Main definitions

* `TauCeti.FactorSet.toCocycles₂`: a factor set read as a `2`-cocycle valued in `Additive M`.
* `TauCeti.FactorSet.cohomologyClass`: its class in `H²(G, M)`.
* `TauCeti.FactorSet.IsCohomologous`: two factor sets whose quotient is a multiplicative
  `2`-coboundary, with `TauCeti.FactorSet.isCohomologousSetoid` the equivalence relation it cuts
  out, presented as the kernel of the cohomology class.
* `TauCeti.FactorSet.ofIsMulCocycle₂`: the normalization of an arbitrary multiplicative
  `2`-cocycle.

## Main results

* `TauCeti.FactorSet.cohomologyClass_eq_iff`: two factor sets have the same class exactly when they
  are cohomologous.
* `TauCeti.FactorSet.exists_cohomologyClass_eq`: every class in `H²(G, M)` is the class of a factor
  set.
* `TauCeti.FactorSet.cohomologyClassEquiv`: **`H²(G, M)` classifies factor sets up to cohomology.**
* `TauCeti.FactorSet.cohomologyClass_eq_zero_iff` and
  `TauCeti.FactorSet.nonempty_splitting_iff_cohomologyClass_eq_zero`: the class vanishes exactly
  for the coboundaries, equivalently for the factor sets whose extension splits.
* `TauCeti.GroupExtension.cohomologyClass_factorSet_eq`: the class of the factor set of a
  normalized section does not depend on the section.
* `TauCeti.GroupExtension.nonempty_equiv_iff_cohomologyClass_factorSet_eq`: **`H²(G, M)` classifies
  group extensions of `G` by `M` inducing the given action, up to equivalence.**

## References

This is the second-cohomology target of Layer 7 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md` ("projective representations,
factor sets, and the Schur multiplier"), which asks for `groupCohomology.H2` of the module of
scalars together with a proof that it classifies factor sets up to cohomology. See
G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 1, and
K. S. Brown, *Cohomology of Groups*, Springer GTM 87 (1982), Ch. IV.3.
-/

public section

namespace TauCeti

open groupCohomology

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

namespace FactorSet

/-! ### The class of a factor set -/

section Class

variable (α β : FactorSet G M)

/-- **A factor set is a `2`-cocycle** for the `ℤ`-linear representation of `G` on `Additive M`
induced by the action. -/
theorem mem_cocycles₂ :
    (fun p : G × G => Additive.ofMul (α p)) ∈ cocycles₂ (Rep.ofMulDistribMulAction G M) :=
  (cocyclesOfIsMulCocycle₂ α.isMulCocycle₂).2

/-- A factor set, read as a `2`-cocycle valued in `Additive M`. -/
def toCocycles₂ : cocycles₂ (Rep.ofMulDistribMulAction G M) :=
  ⟨_, α.mem_cocycles₂⟩

@[simp]
theorem coe_toCocycles₂ : ⇑α.toCocycles₂ = fun p : G × G => Additive.ofMul (α p) := (rfl)

/-- **The cohomology class of a factor set** in `H²(G, M)`. Rescaling the factor set by a
coboundary does not move it (`TauCeti.FactorSet.cohomologyClass_eq_iff`), and every class arises
this way (`TauCeti.FactorSet.exists_cohomologyClass_eq`). -/
noncomputable def cohomologyClass : H2 (Rep.ofMulDistribMulAction G M) :=
  H2π (Rep.ofMulDistribMulAction G M) α.toCocycles₂

theorem cohomologyClass_def :
    α.cohomologyClass = H2π (Rep.ofMulDistribMulAction G M) α.toCocycles₂ :=
  (rfl)

@[simp]
theorem cohomologyClass_trivial : (trivial G M).cohomologyClass = 0 := by
  have h : (trivial G M).toCocycles₂ = 0 :=
    cocycles₂_ext fun _ _ => by
      simp only [coe_toCocycles₂, trivial_apply, ofMul_one]
      rfl
  rw [cohomologyClass_def, h, map_zero]

/-- The pointwise quotient of two factor sets is the difference of the cocycles they name. -/
theorem coe_toCocycles₂_sub :
    ⇑α.toCocycles₂ - ⇑β.toCocycles₂ = fun p : G × G => Additive.ofMul (α p / β p) := by
  ext p
  simp only [coe_toCocycles₂, ofMul_div]
  rfl

/-- **Two factor sets have the same cohomology class exactly when their quotient is a
multiplicative `2`-coboundary.** -/
theorem cohomologyClass_eq_iff :
    α.cohomologyClass = β.cohomologyClass ↔ IsMulCoboundary₂ fun p : G × G => α p / β p := by
  rw [cohomologyClass_def, cohomologyClass_def, H2π_eq_iff, coe_toCocycles₂_sub]
  exact ⟨fun h => isMulCoboundary₂_of_mem_coboundaries₂ _ h, fun h =>
    (coboundariesOfIsMulCoboundary₂ h).2⟩

/-- **The class of a factor set vanishes exactly when it is a multiplicative `2`-coboundary.** -/
theorem cohomologyClass_eq_zero_iff : α.cohomologyClass = 0 ↔ IsMulCoboundary₂ ⇑α := by
  rw [← cohomologyClass_trivial (G := G) (M := M), cohomologyClass_eq_iff]
  simp

end Class

/-! ### Normalizing a cocycle -/

section Normalize

variable {f : G × G → M} (hf : IsMulCocycle₂ f)

include hf

/-- **Every multiplicative `2`-cocycle is normalized by a coboundary.** Dividing `f` by the
function `p ↦ p.1 • f (1, 1)` — the coboundary of the function constant at `f (1, 1)` — leaves a
factor set: the cocycle identity survives because the divisor is itself a cocycle, and the value at
`(1, 1)` becomes `1`. -/
def ofIsMulCocycle₂ : FactorSet G M where
  toFun p := f p / p.1 • f (1, 1)
  isMulCocycle₂' g h j := by
    have key := hf g h j
    simp only [smul_div', mul_smul, div_mul_div_comm]
    rw [key, mul_comm (g • h • f (1, 1))]
  map_one_one' := by simp

@[simp]
theorem coe_ofIsMulCocycle₂ :
    ⇑(ofIsMulCocycle₂ hf) = fun p : G × G => f p / p.1 • f (1, 1) :=
  (rfl)

/-- The normalization of a cocycle is cohomologous to it, in the pointwise sense that their
quotient is a coboundary. -/
theorem isMulCoboundary₂_div_ofIsMulCocycle₂ :
    IsMulCoboundary₂ fun p : G × G => ofIsMulCocycle₂ hf p / f p :=
  ⟨fun _ => (f (1, 1))⁻¹, fun g h => by
    simp only [coe_ofIsMulCocycle₂, smul_inv']
    rw [div_right_comm, div_self', one_div, div_mul_cancel]⟩

end Normalize

/-! ### The classification -/

/-- **Every class in `H²(G, M)` is the class of a factor set.** -/
theorem exists_cohomologyClass_eq (x : H2 (Rep.ofMulDistribMulAction G M)) :
    ∃ α : FactorSet G M, α.cohomologyClass = x := by
  induction x using H2_induction_on with
  | _ y =>
    refine ⟨ofIsMulCocycle₂ (isMulCocycle₂_of_mem_cocycles₂ _ y.2), ?_⟩
    rw [cohomologyClass_def, H2π_eq_iff]
    exact (coboundariesOfIsMulCoboundary₂
      (isMulCoboundary₂_div_ofIsMulCocycle₂ (isMulCocycle₂_of_mem_cocycles₂ _ y.2))).2

/-- **Cohomologous factor sets**: their pointwise quotient is a multiplicative `2`-coboundary,
equivalently (`TauCeti.FactorSet.cohomologyClass_eq_iff`) they have the same class in `H²(G, M)`.
This is the relation under which the factor sets of a projective representation, or of a group
extension with abelian kernel, are well defined. -/
def IsCohomologous (α β : FactorSet G M) : Prop :=
  IsMulCoboundary₂ fun p : G × G => α p / β p

@[simp]
theorem isCohomologous_iff_cohomologyClass_eq {α β : FactorSet G M} :
    IsCohomologous α β ↔ α.cohomologyClass = β.cohomologyClass :=
  (cohomologyClass_eq_iff α β).symm

variable (G M) in
/-- Being cohomologous is an equivalence relation on factor sets: by
`TauCeti.FactorSet.isCohomologous_iff_cohomologyClass_eq` it is the kernel of the cohomology
class. -/
noncomputable def isCohomologousSetoid : Setoid (FactorSet G M) :=
  Setoid.ker (cohomologyClass : FactorSet G M → H2 (Rep.ofMulDistribMulAction G M))

/-- The relation of `TauCeti.FactorSet.isCohomologousSetoid` is being cohomologous, so a coboundary
witness gives `Quotient.sound`. -/
@[simp]
theorem isCohomologousSetoid_apply {α β : FactorSet G M} :
    isCohomologousSetoid G M α β ↔ IsCohomologous α β :=
  Setoid.ker_def.trans isCohomologous_iff_cohomologyClass_eq.symm

variable (G M) in
/-- **`H²(G, M)` classifies factor sets up to cohomology.** The cohomology class descends to a
bijection from the factor sets of `G` with values in `M`, taken modulo the cohomologous relation,
onto the second cohomology group. -/
noncomputable def cohomologyClassEquiv :
    Quotient (isCohomologousSetoid G M) ≃ H2 (Rep.ofMulDistribMulAction G M) :=
  Setoid.quotientKerEquivOfSurjective _ exists_cohomologyClass_eq

@[simp]
theorem cohomologyClassEquiv_apply_mk (α : FactorSet G M) :
    cohomologyClassEquiv G M (Quotient.mk _ α) = α.cohomologyClass :=
  (rfl)

/-! ### Reading the classification on extensions -/

section Extension

variable {α : FactorSet G M}

/-- **The class of a factor set vanishes exactly when its extension splits.** A splitting is a
section that is a homomorphism, so its `M`-components form (the inverse of) a function whose
coboundary is `α`; conversely a function with that coboundary is exactly what makes `g ↦ ⟨_, g⟩` a
homomorphism. -/
theorem nonempty_splitting_iff_cohomologyClass_eq_zero :
    Nonempty α.groupExtension.Splitting ↔ α.cohomologyClass = 0 := by
  rw [cohomologyClass_eq_zero_iff]
  constructor
  · rintro ⟨s⟩
    -- A splitting is a section, so its `G`-component is the identity, and multiplicativity reads
    -- its `M`-component `a` against `α`: `a (g * h) = a g * g • a h * α (g, h)`. So `a⁻¹` is a
    -- function whose coboundary is `α`.
    have hr : ∀ g : G, (s.toMonoidHom g).right = g := fun g => by
      simpa using s.rightInverse_rightHom g
    refine ⟨fun g => ((s.toMonoidHom g).left)⁻¹, fun g h => ?_⟩
    have key := congrArg Extension.left (map_mul s.toMonoidHom g h)
    simp only [Extension.mul_left, hr] at key
    simp only [smul_inv', key]
    -- what is left is an identity in the commutative group `M`
    rw [← div_eq_one]
    simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  · rintro ⟨y, hy⟩
    -- Conversely `g ↦ ⟨(y g)⁻¹, g⟩` is a section, and the coboundary identity for `y` is exactly
    -- its multiplicativity; normalization of `α` forces `y 1 = 1`, giving `map_one`.
    have hy₁ : y 1 = 1 := by simpa using hy 1 1
    refine ⟨GroupExtension.Splitting.mk
      { toFun g := ⟨(y g)⁻¹, g⟩
        map_one' := by ext <;> simp [hy₁]
        map_mul' g h := by
          ext
          · simp only [Extension.mul_left, ← hy g h, smul_inv']
            rw [eq_comm, ← div_eq_one]
            simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
          · rfl } fun _ => by simp⟩

end Extension

end FactorSet

namespace GroupExtension

variable {E E' : Type*} [Group E] [Group E'] {S : GroupExtension M E G}
  {S' : GroupExtension M E' G}

/-- **The cohomology class of the factor set of an extension does not depend on the section.**
So the class in `H²(G, M)` is an invariant of the extension, and by
`TauCeti.GroupExtension.factorSetToGroupExtensionEquiv` the extension is recovered from any one of
these factor sets. -/
theorem cohomologyClass_factorSet_eq (σ σ' : S.Section) (hσ : σ 1 = 1) (hσ' : σ' 1 = 1)
    (hact : InducesAction S) :
    (factorSet σ hσ hact).cohomologyClass = (factorSet σ' hσ' hact).cohomologyClass :=
  (FactorSet.cohomologyClass_eq_iff _ _).2 (isMulCoboundary₂_div σ σ' hσ hσ' hact)

/-- **`H²(G, M)` classifies group extensions up to equivalence.** Two extensions of `G` by the
abelian kernel `M`, both inducing the ambient action, are equivalent exactly when the factor sets
of normalized sections of them have the same class.

The forward direction is the invariance of the class under an equivalence `e`: the transported
section `e ∘ σ` is a normalized section of `S'` with literally the same factor set as `σ`, and by
`TauCeti.GroupExtension.cohomologyClass_factorSet_eq` the class of `S'` does not see which of its
sections it is read from. The backward direction is
`TauCeti.FactorSet.nonempty_groupExtensionEquiv`, carried across the two identifications
`TauCeti.GroupExtension.factorSetToGroupExtensionEquiv`. -/
theorem nonempty_equiv_iff_cohomologyClass_factorSet_eq (σ : S.Section) (σ' : S'.Section)
    (hσ : σ 1 = 1) (hσ' : σ' 1 = 1) (hact : InducesAction S) (hact' : InducesAction S') :
    Nonempty (S.Equiv S') ↔
      (factorSet σ hσ hact).cohomologyClass = (factorSet σ' hσ' hact').cohomologyClass := by
  constructor
  · rintro ⟨e⟩
    -- `τ = e ∘ σ` is a section of `S'` because `e` commutes with the projections
    let τ : S'.Section :=
      ⟨fun g => e (σ g), fun g => (GroupExtension.Equiv.rightHom_map e (σ g)).trans (by simp)⟩
    have hτ₁ : τ 1 = 1 := by simp [τ, hσ]
    -- and `e` carries the defining equation of the factor set of `σ` to that of `τ`
    have hfac : factorSet τ hτ₁ hact' = factorSet σ hσ hact := by
      ext p
      obtain ⟨g, h⟩ := p
      refine S'.inl_injective ?_
      rw [inl_factorSet, ← GroupExtension.Equiv.map_inl e, inl_factorSet]
      simp [τ]
    rw [← hfac]
    exact cohomologyClass_factorSet_eq τ σ' hτ₁ hσ' hact'
  · intro h
    obtain ⟨e⟩ := FactorSet.nonempty_groupExtensionEquiv _ _
      ((FactorSet.cohomologyClass_eq_iff _ _).1 h)
    exact ⟨((factorSetToGroupExtensionEquiv σ hσ hact).symm.trans e).trans
      (factorSetToGroupExtensionEquiv σ' hσ' hact')⟩

end GroupExtension

end TauCeti
