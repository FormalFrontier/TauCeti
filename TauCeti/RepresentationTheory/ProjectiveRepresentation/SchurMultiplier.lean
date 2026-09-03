/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Cohomology
public import TauCeti.RepresentationTheory.ProjectiveRepresentation.Extension

/-!
# The Schur multiplier and the class of a projective representation

The factor set `α` of a projective representation `ρ : G → (V ≃ₗ[k] V)` is a normalized
multiplicative `2`-cocycle of `G` with values in `kˣ`, so it has a class in

`H²(G, kˣ) = TauCeti.schurMultiplier k G`,

the **Schur multiplier** of `G` over `k`. The factor set itself is not an invariant of the
projective action: replacing the lift `ρ` by `g ↦ c g • ρ g` multiplies `α` by the coboundary of
`c`. Its class is, and that is the point of this file.

Because the lift can be rescaled, the honest statements are these. The class is unchanged by
rescaling (`TauCeti.IsProjectiveRep.cohomologyClass_rescale`), so two lifts of the same projective
action have the same class (`TauCeti.IsProjectiveRep.cohomologyClass_eq_of_eq_smul`). The class
**vanishes exactly when the projective representation is a linear representation in disguise**
(`TauCeti.IsProjectiveRep.cohomologyClass_eq_zero_iff`): the obstruction to rescaling `ρ` into a
homomorphism `G →* (V ≃ₗ[k] V)` is precisely the class of its factor set. Every class occurs
(`TauCeti.exists_isProjectiveRep_cohomologyClass_eq`), already on the twisted regular
representation, so `H²(G, kˣ)` is exactly the set of classes of projective representations of `G`
over `k`. And the twisted monoid algebra `k_α[G]` sees only the class
(`TauCeti.TwistedMonoidAlgebra.nonempty_algEquiv_of_cohomologyClass_eq`).

Two of these need `kˣ` to act faithfully on `V`, and genuinely so: on `V = 0` every lift is the
zero map and every normalized factor set whatsoever is a factor set for it, so nothing about `α`
can be read off `ρ` there. Only scalars in `kˣ` are ever compared, so faithfulness is asked of the
units; `k` itself acting faithfully — on a nonzero vector space, say — supplies it. The two
directions of the lifting criterion are therefore also recorded separately, the direction that does
not need faithfulness being stated for an arbitrary module.

## The action on the scalars

`TauCeti.FactorSet` and its cohomology class are set up for an arbitrary `MulDistribMulAction` of
`G` on the coefficients, whereas a projective representation carries none: its factor set takes
values in the *central* `kˣ`. So the whole file runs under the trivial action
`TauCeti.trivialMulDistribMulAction`, installed as a local instance exactly as in
`TauCeti/RepresentationTheory/ProjectiveRepresentation/Extension.lean`. The roadmap spells the
coefficient module `Rep.trivial ℤ G (Additive kˣ)`; `Rep.ofMulDistribMulAction G kˣ` for the
trivial action is that module, and it is the spelling that both Mathlib's multiplicative interface
to `groupCohomology.cocycles₂` and `TauCeti.FactorSet.cohomologyClass` are stated in, so it is the
one used here.

`Rep ℤ G` puts the group and the coefficients in the universe of `ℤ`, so `k` and `G` are pinned to
`Type`; this is the same restriction `TauCeti/GroupTheory/GroupExtension/Cohomology.lean` carries.
The module `V` stays universe-polymorphic.

`TauCeti.schurMultiplier` deliberately carries no result-type ascription. Writing `ModuleCat ℤ`
would elaborate the `Ring ℤ` argument by instance search, whereas `groupCohomology.H2` produces it
from the `CommRing ℤ` of `Rep ℤ G`; the two are the same instance up to unfolding but not
syntactically, and rewriting across the difference then fails.

## Main definitions

* `TauCeti.schurMultiplier`: the Schur multiplier `H²(G, kˣ)`.
* `TauCeti.IsProjectiveRep.factorSet`: the factor set of a projective representation, bundled as a
  `TauCeti.FactorSet` for the trivial action.
* `TauCeti.IsProjectiveRep.cohomologyClass`: its class in the Schur multiplier.

## Main results

* `TauCeti.IsProjectiveRep.cohomologyClass_of_monoidHom`: a linear representation has
  vanishing class.
* `TauCeti.IsProjectiveRep.cohomologyClass_rescale`: rescaling the lift does not move the class,
  and `TauCeti.IsProjectiveRep.cohomologyClass_eq_of_eq_smul`: two lifts differing by scalars have
  the same class.
* `TauCeti.IsProjectiveRep.cohomologyClass_eq_zero_iff`: **the class vanishes exactly when the lift
  is a linear representation rescaled by scalars**, with
  `TauCeti.IsProjectiveRep.exists_monoidHom_of_cohomologyClass_eq_zero` and
  `TauCeti.IsProjectiveRep.cohomologyClass_eq_zero_of_monoidHom` its two directions.
* `TauCeti.exists_isProjectiveRep_cohomologyClass_eq`: **every class in the Schur multiplier is the
  class of a projective representation**, so the Schur multiplier is exactly the set of classes of
  factor sets of projective representations of `G` over `k`.
* `TauCeti.TwistedMonoidAlgebra.nonempty_algEquiv_of_cohomologyClass_eq`: the twisted monoid algebra
  depends only on the class.

## References

This is the Schur-multiplier target of Layer 7 of the
[induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/InductionRestriction/README.md),
"projective representations, factor sets, and the Schur multiplier", whose `schurMultiplier` is the
group defined here.

* G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 1 and 3.
* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Ch. 11.
-/

public section

namespace TauCeti

open groupCohomology

/-! ### Rearrangements in a commutative group

The coboundary bookkeeping below is a handful of identities in the commutative group `kˣ`, isolated
here so that the arguments about factor sets are not interrupted by them. Read `a, b, d` as the
values of a rescaling at `g₁`, `g₂` and `g₁ * g₂`.
-/

private theorem coboundary_aux {M : Type*} [CommGroup M] (a b d : M) : b / d * a = a * b * d⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

private theorem coboundary_inv_aux {M : Type*} [CommGroup M] (a b d : M) :
    a⁻¹ * b⁻¹ * (d⁻¹)⁻¹ * (b / d * a) = 1 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
  abel

private theorem cohomologous_aux {M : Type*} [CommGroup M] (a b u v z : M)
    (h : v / z * u = a / b) : a * z = b * (u * v) := by
  have ha : a = v / z * u * b := div_eq_iff_eq_mul.1 h.symm
  subst ha
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

section TrivialAction

attribute [local instance] trivialMulDistribMulAction

variable {k G : Type} [CommSemiring k] [Group G] {V : Type*} [AddCommMonoid V] [Module k V]

/-- **The Schur multiplier** `H²(G, kˣ)` of a group `G` over a commutative semiring `k`: the second
cohomology of `G` with coefficients in the units of `k` under the trivial action. By
`TauCeti.exists_isProjectiveRep_cohomologyClass_eq` and
`TauCeti.IsProjectiveRep.cohomologyClass_rescale` it is exactly the set of classes of factor sets
of projective representations of `G` over `k`, equivalently — through
`TauCeti.FactorSet.cohomologyClassEquiv` — the set of central extensions of `G` by `kˣ` up to
equivalence.

The body is exposed because `TauCeti.schurMultiplier k G` is used in type position, through the
`CoeSort` on `ModuleCat ℤ`: a statement relating an element of it to an element of
`groupCohomology.H2 (Rep.ofMulDistribMulAction G kˣ)` — such as
`TauCeti.IsProjectiveRep.cohomologyClass_def` below — does not elaborate otherwise. -/
@[expose]
noncomputable def schurMultiplier (k G : Type) [CommSemiring k] [Group G] :=
  H2 (Rep.ofMulDistribMulAction G kˣ)

/-- The Schur multiplier is the second cohomology of `G` with coefficients in the units of `k`. -/
theorem schurMultiplier_def (k G : Type) [CommSemiring k] [Group G] :
    schurMultiplier k G = H2 (Rep.ofMulDistribMulAction G kˣ) :=
  rfl

variable {ρ : G → V ≃ₗ[k] V} {α : G → G → kˣ}

/-- The factor set of a projective representation, bundled as a `TauCeti.FactorSet` over the
trivial action of `G` on `kˣ` — the action for which the extension it names is central. This is
`TauCeti.IsFactorSet.toFactorSet` applied to the factor-set axioms the projective representation
carries, so no `TauCeti.IsFactorSet` instance need be in scope. -/
def IsProjectiveRep.factorSet (h : IsProjectiveRep ρ α) : FactorSet G kˣ :=
  letI := h.isFactorSet
  IsFactorSet.toFactorSet α trivialMulDistribMulAction_smul

@[simp]
theorem IsProjectiveRep.factorSet_apply (h : IsProjectiveRep ρ α) (p : G × G) :
    h.factorSet p = α p.1 p.2 :=
  letI := h.isFactorSet
  IsFactorSet.toFactorSet_apply α trivialMulDistribMulAction_smul p

/-- **The class of a projective representation in the Schur multiplier**: the class of its factor
set in `H²(G, kˣ)`. Unlike the factor set itself it depends only on the underlying projective
action, by `TauCeti.IsProjectiveRep.cohomologyClass_eq_of_eq_smul`. -/
noncomputable def IsProjectiveRep.cohomologyClass (h : IsProjectiveRep ρ α) :
    schurMultiplier k G :=
  h.factorSet.cohomologyClass

/-- The class of a projective representation is the class of its bundled factor set. The body of
`TauCeti.IsProjectiveRep.cohomologyClass` is not exposed, so this is how an importing module unfolds
it. It is deliberately not a `simp` lemma: the class is the normal form, and the lemmas below
evaluate it directly. -/
theorem IsProjectiveRep.cohomologyClass_def (h : IsProjectiveRep ρ α) :
    h.cohomologyClass = h.factorSet.cohomologyClass :=
  (rfl)

/-- The class of a projective representation depends on the lift only through its factor set — not
even through the module it acts on. -/
theorem IsProjectiveRep.cohomologyClass_congr {W : Type*} [AddCommMonoid W] [Module k W]
    {ρ₁ : G → V ≃ₗ[k] V} {ρ₂ : G → W ≃ₗ[k] W} {α₁ α₂ : G → G → kˣ}
    (h₁ : IsProjectiveRep ρ₁ α₁) (h₂ : IsProjectiveRep ρ₂ α₂) (hα : α₁ = α₂) :
    h₁.cohomologyClass = h₂.cohomologyClass := by
  subst hα
  rfl

/-- **A linear representation has vanishing class**: its factor set is the trivial one. This is the
easy half of `TauCeti.IsProjectiveRep.cohomologyClass_eq_zero_iff`, stated before any rescaling and
so without a faithfulness hypothesis. -/
@[simp]
theorem IsProjectiveRep.cohomologyClass_of_monoidHom (π : G →* (V ≃ₗ[k] V)) :
    (IsProjectiveRep.of_monoidHom π).cohomologyClass = 0 := by
  have h : (IsProjectiveRep.of_monoidHom π).factorSet = FactorSet.trivial G kˣ :=
    FactorSet.ext fun p ↦ by simp
  rw [IsProjectiveRep.cohomologyClass_def, h]
  exact FactorSet.cohomologyClass_trivial

/-! ### Rescaling the lift -/

/-- **Rescaling the lift does not move the class.** Multiplying `ρ` by units `c : G → kˣ`
multiplies its factor set by the coboundary of `c` (`TauCeti.IsProjectiveRep.rescale`), and that is
exactly what `H²` quotients out. -/
theorem IsProjectiveRep.cohomologyClass_rescale (h : IsProjectiveRep ρ α) (c : G → kˣ)
    (hc : c 1 = 1) : (h.rescale c hc).cohomologyClass = h.cohomologyClass := by
  refine (FactorSet.cohomologyClass_eq_iff _ _).2 ⟨c, fun g₁ g₂ ↦ ?_⟩
  simp only [IsProjectiveRep.factorSet_apply, trivialMulDistribMulAction_smul]
  rw [mul_div_cancel_right]
  exact coboundary_aux _ _ _

/-- A lift obtained from another by multiplying by units is again normalized: the scalars take the
value `1` at `1`. Faithfulness is what lets a scalar be read off from its action, and only scalars
in `kˣ` are compared, so the faithful action of the units is what is asked for. -/
theorem IsProjectiveRep.eq_one_of_eq_smul [FaithfulSMul kˣ V] {ρ' : G → V ≃ₗ[k] V}
    {β : G → G → kˣ} (h : IsProjectiveRep ρ α) (h' : IsProjectiveRep ρ' β) (c : G → kˣ)
    (hc : ∀ g, ρ' g = (ρ g).trans (LinearEquiv.smulOfUnit (c g))) : c 1 = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul fun x : V ↦ ?_
  have hx : ρ' 1 x = (c 1 : k) • ρ 1 x := by
    rw [hc 1, LinearEquiv.trans_apply, LinearEquiv.smulOfUnit_apply]
  rw [h.map_one, h'.map_one] at hx
  simpa [Units.smul_def] using hx.symm

/-- **Two lifts of the same projective action have the same class.** The hypothesis is that the two
lifts differ by the units `c`, which is what it means for them to induce the same homomorphism into
the projective linear group. -/
theorem IsProjectiveRep.cohomologyClass_eq_of_eq_smul [FaithfulSMul kˣ V] {ρ' : G → V ≃ₗ[k] V}
    {β : G → G → kˣ} (h : IsProjectiveRep ρ α) (h' : IsProjectiveRep ρ' β) (c : G → kˣ)
    (hc : ∀ g, ρ' g = (ρ g).trans (LinearEquiv.smulOfUnit (c g))) :
    h'.cohomologyClass = h.cohomologyClass := by
  have hc1 : c 1 = 1 := h.eq_one_of_eq_smul h' c hc
  have hρ : ρ' = fun g ↦ (ρ g).trans (LinearEquiv.smulOfUnit (c g)) := funext hc
  subst hρ
  exact (h'.cohomologyClass_congr (h.rescale c hc1) (h'.factorSet_eq (h.rescale c hc1))).trans
    (h.cohomologyClass_rescale c hc1)

/-! ### The class as the obstruction to linearizing -/

/-- **A projective representation whose class vanishes is a linear representation rescaled by
scalars.** The factor set is then the coboundary of some `x : G → kˣ`, and dividing the lift by `x`
turns it into a homomorphism. No faithfulness is needed in this direction. -/
theorem IsProjectiveRep.exists_monoidHom_of_cohomologyClass_eq_zero (h : IsProjectiveRep ρ α)
    (h0 : h.cohomologyClass = 0) :
    ∃ (c : G → kˣ) (π : G →* (V ≃ₗ[k] V)),
      c 1 = 1 ∧ ∀ g, ρ g = (π g).trans (LinearEquiv.smulOfUnit (c g)) := by
  obtain ⟨x, hx⟩ := (FactorSet.cohomologyClass_eq_zero_iff h.factorSet).1 h0
  have hx' : ∀ g₁ g₂ : G, x g₂ / x (g₁ * g₂) * x g₁ = α g₁ g₂ := fun g₁ g₂ ↦ by
    simpa only [trivialMulDistribMulAction_smul, IsProjectiveRep.factorSet_apply] using hx g₁ g₂
  have hx1 : x 1 = 1 := by
    have h11 := hx' 1 1
    rw [mul_one, h.isFactorSet.one_left] at h11
    simpa using h11
  have hrs := h.rescale (fun g ↦ (x g)⁻¹) (by simp [hx1])
  have hone : (fun g₁ g₂ ↦ (x g₁)⁻¹ * (x g₂)⁻¹ * ((x (g₁ * g₂))⁻¹)⁻¹ * α g₁ g₂)
      = (1 : G → G → kˣ) := by
    funext g₁ g₂
    simp only [Pi.one_apply]
    rw [← hx' g₁ g₂]
    exact coboundary_inv_aux _ _ _
  rw [hone] at hrs
  refine ⟨x, hrs.toMonoidHom, hx1, fun g ↦ ?_⟩
  refine LinearEquiv.ext fun v ↦ ?_
  have hg : hrs.toMonoidHom g = (ρ g).trans (LinearEquiv.smulOfUnit (x g)⁻¹) :=
    congrFun hrs.coe_toMonoidHom g
  -- rescaling by `(x g)⁻¹` and then by `x g` multiplies by `↑(x g) * ↑(x g)⁻¹ = 1`
  simp [hg, smul_smul]

/-- **A linear representation rescaled by scalars has vanishing class.** Faithfulness is what makes
the factor set of the rescaled lift *be* the coboundary of `c`, rather than merely some factor set
acting the same way. -/
theorem IsProjectiveRep.cohomologyClass_eq_zero_of_monoidHom [FaithfulSMul kˣ V]
    (h : IsProjectiveRep ρ α) (c : G → kˣ) (π : G →* (V ≃ₗ[k] V))
    (hc : ∀ g, ρ g = (π g).trans (LinearEquiv.smulOfUnit (c g))) : h.cohomologyClass = 0 := by
  have hπ := IsProjectiveRep.of_monoidHom π
  have hc1 : c 1 = 1 := hπ.eq_one_of_eq_smul h c hc
  have hρ : ρ = fun g ↦ ((π : G → V ≃ₗ[k] V) g).trans (LinearEquiv.smulOfUnit (c g)) := funext hc
  subst hρ
  have hα := h.factorSet_eq (hπ.rescale c hc1)
  refine (FactorSet.cohomologyClass_eq_zero_iff h.factorSet).2 ⟨c, fun g₁ g₂ ↦ ?_⟩
  simp only [IsProjectiveRep.factorSet_apply, trivialMulDistribMulAction_smul,
    congrFun (congrFun hα g₁) g₂, Pi.one_apply, mul_one]
  exact coboundary_aux _ _ _

/-- **The class of a projective representation vanishes exactly when it linearizes**: exactly when
its lift is a homomorphism `G →* (V ≃ₗ[k] V)` rescaled by units of `k`. So the Schur-multiplier
class is the complete obstruction to a projective representation being an ordinary linear
representation in disguise. -/
theorem IsProjectiveRep.cohomologyClass_eq_zero_iff [FaithfulSMul kˣ V]
    (h : IsProjectiveRep ρ α) :
    h.cohomologyClass = 0 ↔
      ∃ (c : G → kˣ) (π : G →* (V ≃ₗ[k] V)),
        ∀ g, ρ g = (π g).trans (LinearEquiv.smulOfUnit (c g)) :=
  ⟨fun h0 ↦
      let ⟨c, π, _, hc⟩ := h.exists_monoidHom_of_cohomologyClass_eq_zero h0
      ⟨c, π, hc⟩,
    fun ⟨c, π, hc⟩ ↦ h.cohomologyClass_eq_zero_of_monoidHom c π hc⟩

/-! ### Every class is realized -/

/-- **Every class in the Schur multiplier is the class of a projective representation of `G` over
`k`**, already on `G →₀ k`: normalize a cocycle representing the class to a factor set
(`TauCeti.FactorSet.exists_cohomologyClass_eq`) and take the twisted regular representation of that
factor set. Together with `TauCeti.IsProjectiveRep.cohomologyClass_rescale` this says that
`H²(G, kˣ)` is exactly the set of classes of projective representations of `G` over `k`. -/
theorem exists_isProjectiveRep_cohomologyClass_eq (x : schurMultiplier k G) :
    ∃ (α : G → G → kˣ) (ρ : G → (G →₀ k) ≃ₗ[k] (G →₀ k)) (h : IsProjectiveRep ρ α),
      h.cohomologyClass = x := by
  obtain ⟨γ, hγ⟩ := FactorSet.exists_cohomologyClass_eq (G := G) (M := kˣ) x
  have hfs : IsFactorSet (Function.curry ⇑γ) :=
    γ.isFactorSet_curry trivialMulDistribMulAction_smul
  refine ⟨Function.curry ⇑γ, twistedRegularRep k G (Function.curry ⇑γ),
    isProjectiveRep_twistedRegularRep k G (Function.curry ⇑γ), ?_⟩
  have hfactorSet : (isProjectiveRep_twistedRegularRep k G (Function.curry ⇑γ)).factorSet = γ :=
    FactorSet.ext fun p ↦
      (isProjectiveRep_twistedRegularRep k G (Function.curry ⇑γ)).factorSet_apply p
  rw [← hγ, IsProjectiveRep.cohomologyClass_def, hfactorSet]

/-! ### The twisted monoid algebra sees only the class -/

/-- **The twisted monoid algebra depends only on the class of its factor set.** Cohomologous factor
sets differ by a coboundary, and rescaling the basis elements by it is an algebra isomorphism
(`TauCeti.TwistedMonoidAlgebra.equivOfCoboundary`). So `k_α[G]` is an invariant of the class of `α`
in the Schur multiplier. -/
theorem TwistedMonoidAlgebra.nonempty_algEquiv_of_cohomologyClass_eq {α β : G → G → kˣ}
    [IsFactorSet α] [IsFactorSet β]
    (h : (IsFactorSet.toFactorSet α trivialMulDistribMulAction_smul).cohomologyClass
      = (IsFactorSet.toFactorSet β trivialMulDistribMulAction_smul).cohomologyClass) :
    Nonempty (twistedMonoidAlgebra k G α ≃ₐ[k] twistedMonoidAlgebra k G β) := by
  obtain ⟨y, hy⟩ := (FactorSet.cohomologyClass_eq_iff _ _).1 h
  refine ⟨TwistedMonoidAlgebra.equivOfCoboundary β α y fun g₁ g₂ ↦ ?_⟩
  have hy' := hy g₁ g₂
  simp only [trivialMulDistribMulAction_smul, IsFactorSet.toFactorSet_apply] at hy'
  exact cohomologous_aux _ _ _ _ _ hy'

end TrivialAction

end TauCeti
