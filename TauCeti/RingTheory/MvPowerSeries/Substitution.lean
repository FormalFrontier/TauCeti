/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Evaluating a substitution over coefficients that need not be discrete

Mathlib evaluates a substitution only over discrete coefficients: `MvPowerSeries.eval₂_subst` and
`MvPowerSeries.comp_subst_apply` both carry `[DiscreteUniformity R] [DiscreteUniformity S]` on the
two coefficient rings. That is unsatisfiable exactly where the statement is wanted. Substituting a
parameter into a formal expansion over an adic ring and evaluating back into that same ring needs
the coefficients and the evaluation target to be the *same* type, and one type cannot carry both
the adic and the discrete uniformity as instances.

`MvPowerSeries.aeval_subst` is that conclusion with an arbitrary uniform structure on the
coefficients. Nothing topological beyond a uniformity is asked of the ring the substituted family
lives over, and the evaluation target carries exactly the hypotheses of `MvPowerSeries.comp_aeval`.
That generality is available because Mathlib's evaluation API asks for no discreteness anywhere:
discreteness enters its substitution API only through `MvPowerSeries.substAlgHom_eq_aeval`, from
how `subst` is tied to `aeval`, and not from the composition fact itself. So all three rings may
be instantiated at one adic ring with no `letI` at the use site.

Discreteness is recovered inside the proof, where it belongs. `MvPowerSeries.subst` is by
definition an evaluation for the discrete uniformities; the pi topology those induce is finer than
the ambient one (`MvPowerSeries.WithPiTopology.instTopologicalSpace_mono`); and a map continuous
for the ambient source topology is continuous for a finer one (`continuous_le_dom`). In the
discrete world both sides are therefore continuous algebra homomorphisms out of
`MvPowerSeries σ R`; `MvPowerSeries.aeval_unique` identifies each with an evaluation; and the two
evaluations agree because both send `X s` to `ε (a s)`. Every ambient fact is taken before the
uniformities are shadowed, so the evaluation the statement is about is never re-elaborated.

## Main results

* `MvPowerSeries.aeval_subst` : a continuous algebra homomorphism applied to a substitution is the
  evaluation at the substituted family.
* `PowerSeries.aeval_subst` : the same for a substitution into a univariate series.
* `PowerSeries.eval₂_toMvPowerSeries` and `PowerSeries.eval₂_id_toMvPowerSeries` : evaluating a
  univariate series viewed in several variables is evaluating it at the matching entry of the
  family — the case of `aeval_subst` at a single variable, which is how a one-variable series
  meets a two-variable evaluation.

The two `aeval_subst` results are wanted for the formal group of an elliptic curve over a complete
local ring, where the group law is a power series over the very ring it is evaluated in: the
involution relating the `w`-expansion to the formal inverse is an identity between two such
evaluated substitutions. The two `toMvPowerSeries` results serve the same development from the
other side: the chord construction is a two-variable series, and its identities are proved by
evaluating one-variable series — `w`, the slope, the formal inverse — at entries of the pair.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file
`EllipticCurves/Mathlib/Chabauty/MvPSeries.lean`, where this is
`ChabautyColeman.MvPSeries.eval_subst`, stated for a single ring and for that development's own
`eval`. Here the three rings are independent and the statement is about Mathlib's
`MvPowerSeries.aeval`; it equally generalises Mathlib's `MvPowerSeries.eval₂_subst`, whose
`DiscreteUniformity` hypotheses it removes.

`PowerSeries.eval₂_toMvPowerSeries` and `PowerSeries.eval₂_id_toMvPowerSeries` are the same
source file's `eval_pair_rename` and `eval_pair_subst_single`, respelled: the source moves a
one-variable series into two variables along `MvPowerSeries.rename (fun _ ↦ i)`, whereas these
transport along `PowerSeries.toMvPowerSeries i`.

The proof is not the source's. That one establishes continuity of `subst` for the ambient product
topologies (its own `MvPowerSeries.continuous_subst'`) and applies uniqueness there; refining the
source topology to the discrete one instead lets Mathlib's own `MvPowerSeries.continuous_subst` do
the work, so no new continuity lemma is needed.
-/

public section

namespace MvPowerSeries

open WithPiTopology

variable {σ τ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalSemiring R]
variable {S : Type*} [CommRing S] [UniformSpace S] [Algebra R S]
variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T] [T2Space T] [CompleteSpace T]
    [Algebra R T] [ContinuousSMul R T]

/-- Applying a continuous algebra homomorphism to a substitution is evaluating at the substituted
family — with no discreteness asked of either coefficient ring.

This is `MvPowerSeries.comp_subst_apply` without its `DiscreteUniformity` hypotheses; the
evaluation target carries exactly the hypotheses of `MvPowerSeries.comp_aeval`. The evaluation of
the substituted family is a hypothesis rather than `MvPowerSeries.HasSubst.hasEval`, because that
one is stated for the discrete topology on `S`, which is not the topology this statement is
about. -/
theorem aeval_subst {a : σ → MvPowerSeries τ S} {ε : MvPowerSeries τ S →ₐ[R] T} (ha : HasSubst a)
    (hε : Continuous ε) (hb : HasEval (fun s ↦ ε (a s))) (f : MvPowerSeries σ R) :
    ε (subst a f) = aeval hb f := by
  -- Everything about the ambient instances is taken first: the goal's `aeval hb` carries them,
  -- and nothing below may re-elaborate it.
  have h2 : Continuous (aeval hb) := continuous_aeval (R := R) hb
  have hx : ∀ s, aeval hb (X s) = ε (a s) := fun s ↦ by
    rw [coe_aeval (R := R) hb, eval₂_X]
  -- The discrete pi topology is finer than the ambient one, compared while both are nameable.
  have hRle : @instTopologicalSpace σ R (⊥ : UniformSpace R).toTopologicalSpace ≤
      @instTopologicalSpace σ R inferInstance :=
    instTopologicalSpace_mono σ (by rw [UniformSpace.toTopologicalSpace_bot]; exact bot_le)
  have hSle : @instTopologicalSpace τ S (⊥ : UniformSpace S).toTopologicalSpace ≤
      @instTopologicalSpace τ S inferInstance :=
    instTopologicalSpace_mono τ (by rw [UniformSpace.toTopologicalSpace_bot]; exact bot_le)
  -- The discrete uniformities enter only as the source topology; `T` is never touched.
  let uR : UniformSpace R := ⊥
  let uS : UniformSpace S := ⊥
  have dR : DiscreteUniformity R := ⟨rfl⟩
  have dS : DiscreteUniformity S := ⟨rfl⟩
  have csm : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
  -- Both algebra homomorphisms are continuous for the finer source topology.
  have h1 : Continuous (⇑(ε.comp (substAlgHom ha)) : MvPowerSeries σ R → T) := by
    simpa only [AlgHom.coe_comp, coe_substAlgHom] using
      (continuous_le_dom hSle hε).comp (continuous_subst ha)
  have h2' := continuous_le_dom hRle h2
  -- A continuous algebra homomorphism out of `MvPowerSeries σ R` is determined by its values on
  -- the variables, and both of ours send `X s` to `ε (a s)`.
  have mid : (aeval (HasEval.X.map h1) : MvPowerSeries σ R →ₐ[R] T) =
      aeval (HasEval.X.map h2') := by
    apply DFunLike.ext'
    rw [coe_aeval, coe_aeval]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply,
      substAlgHom_X, hx]
  simpa only [AlgHom.coe_comp, Function.comp_apply, substAlgHom_apply] using DFunLike.congr_fun
    ((aeval_unique h1).symm.trans (mid.trans (aeval_unique h2'))) f

end MvPowerSeries

namespace PowerSeries

open MvPowerSeries.WithPiTopology

variable {τ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalSemiring R]
variable {S : Type*} [CommRing S] [UniformSpace S] [Algebra R S]
variable {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T] [T2Space T] [CompleteSpace T]
    [Algebra R T] [ContinuousSMul R T]

/-- `MvPowerSeries.aeval_subst` for a substitution into a univariate power series: applying a
continuous algebra homomorphism to `PowerSeries.subst a f` evaluates `f` at the value of `a`. -/
theorem aeval_subst {a : MvPowerSeries τ S} {ε : MvPowerSeries τ S →ₐ[R] T} (ha : HasSubst a)
    (hε : Continuous ε) (hb : HasEval (ε a)) (f : PowerSeries R) :
    ε (subst a f) = aeval hb f :=
  MvPowerSeries.aeval_subst ha.const hε (hasEval hb) f

/-- Evaluating the image of a univariate series under `PowerSeries.toMvPowerSeries i` at a family
`a` is evaluating the series itself at the entry `a i`: sending the single variable to the `i`-th
one and then evaluating is evaluating at `a i`.

`toMvPowerSeries` is a substitution, so this is `aeval_subst` at the family `MvPowerSeries.X i`;
it is stated for `eval₂` rather than `aeval` because the evaluation of a family is what consumers
hold, and the `aeval` form would carry the `HasEval` proof in a position where two propositionally
equal parameters are not definitionally equal. -/
@[simp]
theorem eval₂_toMvPowerSeries {σ : Type*} {a : σ → T} (ha : MvPowerSeries.HasEval a) (i : σ)
    (f : PowerSeries R) :
    MvPowerSeries.eval₂ (algebraMap R T) a (toMvPowerSeries i f) =
      eval₂ (algebraMap R T) (a i) f := by
  have hX : MvPowerSeries.aeval ha (MvPowerSeries.X i) = a i :=
    (congrFun (MvPowerSeries.coe_aeval (R := R) ha) (MvPowerSeries.X i)).trans
      (MvPowerSeries.eval₂_X (algebraMap R T) a i)
  have h := aeval_subst (HasSubst.X i) (MvPowerSeries.continuous_aeval ha) (hX ▸ ha.hpow i) f
  rw [← toMvPowerSeries_eq_subst] at h
  rw [← congrFun (MvPowerSeries.coe_aeval (R := R) ha) (toMvPowerSeries i f), h,
    congrFun (coe_aeval (hX ▸ ha.hpow i)) f, hX]

section SelfEval

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsLinearTopology R R] [T2Space R] [CompleteSpace R]

/-- `PowerSeries.eval₂_toMvPowerSeries` at the identity ring homomorphism.

The specialization exists so that consumers phrased over `RingHom.id` need not perform the
normalization themselves. `algebraMap R R` and `RingHom.id R` are definitionally equal but not
syntactically so, and `algebraMap` is not reducible; that is easy to discharge once, as the
`simpa` below does, but it means the general lemma does not fire as a `simp` *rewrite rule*
against a goal phrased over `RingHom.id`. An evaluation layer whose coefficients and values are
the same ring — what the formal group of a curve over an adic ring needs — is phrased that way
throughout, so it is this form its `simp` sets can use. -/
@[simp]
theorem eval₂_id_toMvPowerSeries {σ : Type*} {a : σ → R} (ha : MvPowerSeries.HasEval a) (i : σ)
    (f : PowerSeries R) :
    MvPowerSeries.eval₂ (RingHom.id R) a (toMvPowerSeries i f) =
      eval₂ (RingHom.id R) (a i) f := by
  simpa using eval₂_toMvPowerSeries (R := R) (T := R) ha i f

end SelfEval

end PowerSeries
