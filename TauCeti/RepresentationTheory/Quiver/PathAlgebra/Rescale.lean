/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path.Weight
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# Rescaling the arrows of a path algebra

A labelling of the arrows of a quiver by scalars multiplies out along a path to the *weight* of
that path, and rescaling every basis path by its weight is an algebra endomorphism of the path
algebra: weights are multiplicative under concatenation and trivial on the vertex idempotents,
which is exactly what the universal property `TauCeti.PathAlgebra.liftAlgHom` asks for. Two
rescalings compose by multiplying labellings, and the constant labelling `1` rescales by the
identity, so a labelling by units rescales by an algebra automorphism, inverted by the labelling
by inverses.

These rescalings are the gauge transformations of a quiver with relations: each fixes every vertex
idempotent and multiplies each arrow by its label, so it carries a relation to the correspondingly
rescaled relation.

## Implementation notes

A labelling of the arrows is spelled out as the dependent function type `∀ ⦃a b⦄, (a ⟶ b) → k`
rather than through Mathlib's `Quiver.Labelling`, which is a non-reducible definition of the same
type: rewriting with a lemma whose labelling argument is a metavariable of that type fails, since
the metavariable cannot be applied to an arrow before the definition is unfolded.

## Main definitions

* `TauCeti.PathAlgebra.rescale`: the algebra endomorphism multiplying each basis path by its
  weight.

## Main results

* `TauCeti.PathAlgebra.rescale_ofArrow`: an arrow is multiplied by its own label.
* `TauCeti.PathAlgebra.rescale_vertexIdempotent`: the vertex idempotents are fixed.
* `TauCeti.PathAlgebra.rescale_comp_rescale`: rescalings compose by multiplying labellings.
* `TauCeti.PathAlgebra.rescale_one`: the constant labelling `1` rescales by the identity.
* `TauCeti.PathAlgebra.rescale_congr`: pointwise equal labellings give equal rescalings.

## References

This is infrastructure for the gauge-change clause of Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks for the algebra isomorphisms rescaling
the arrows of a doubled quiver by signs, and for their generalization to an arbitrary
antisymmetric scalar labelling.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

/-! ### Properties of path weights -/

section Weight

variable {k : Type w} {Q : Type u} [Monoid k] [Quiver.{v} Q]

variable (c d : ∀ ⦃a b : Q⦄, (a ⟶ b) → k)

@[simp]
theorem _root_.Quiver.Path.weight_toPath {a b : Q} (e : a ⟶ b) :
    _root_.Quiver.Path.weight (fun {_ _} f => c f) e.toPath = c e := by
  rw [_root_.Quiver.Hom.toPath, _root_.Quiver.Path.weight_cons,
    _root_.Quiver.Path.weight_nil, one_mul]

/-- Pointwise equal labellings give equal weights. -/
theorem _root_.Quiver.Path.weight_congr (h : ∀ ⦃a b : Q⦄ (e : a ⟶ b), c e = d e) {a b : Q}
    (p : _root_.Quiver.Path a b) :
    _root_.Quiver.Path.weight (fun {_ _} e => c e) p =
      _root_.Quiver.Path.weight (fun {_ _} e => d e) p := by
  induction p with
  | nil => simp
  | cons p f ih =>
    rw [_root_.Quiver.Path.weight_cons, _root_.Quiver.Path.weight_cons, ih, h f]

/-- Every path has weight one under the constant labelling by one. -/
@[simp]
theorem _root_.Quiver.Path.weight_one {a b : Q} (p : _root_.Quiver.Path a b) :
    _root_.Quiver.Path.weight (fun {_ _} _ => (1 : k)) p = 1 := by
  induction p with
  | nil => simp
  | cons p f ih => rw [_root_.Quiver.Path.weight_cons, ih, one_mul]

end Weight

section WeightMul

variable {k : Type w} {Q : Type u} [CommMonoid k] [Quiver.{v} Q]
variable (c d : ∀ ⦃a b : Q⦄, (a ⟶ b) → k)

/-- The weight under a pointwise product of labellings is the product of the weights. -/
theorem _root_.Quiver.Path.weight_mul {a b : Q} (p : _root_.Quiver.Path a b) :
    _root_.Quiver.Path.weight (fun {_ _} e => c e * d e) p
      = _root_.Quiver.Path.weight (fun {_ _} e => c e) p *
        _root_.Quiver.Path.weight (fun {_ _} e => d e) p := by
  induction p with
  | nil => simp
  | cons p f ih =>
    rw [_root_.Quiver.Path.weight_cons, _root_.Quiver.Path.weight_cons,
      _root_.Quiver.Path.weight_cons, ih, mul_mul_mul_comm]

end WeightMul

namespace PathAlgebra

/-! ### The rescaling endomorphism -/

section Rescale

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q]
variable (c d : ∀ ⦃a b : Q⦄, (a ⟶ b) → k)

private theorem rescale_hcomp {a b e : Q} (p : _root_.Quiver.Path a b)
    (q : _root_.Quiver.Path e a) :
    _root_.Quiver.Path.weight (fun {_ _} f => c f) p •
        (ofPath (⟨a, b, p⟩ : Quiver.TotalPath Q) : pathAlgebra k Q) *
        _root_.Quiver.Path.weight (fun {_ _} f => c f) q •
          (ofPath (⟨e, a, q⟩ : Quiver.TotalPath Q) : pathAlgebra k Q)
      = _root_.Quiver.Path.weight (fun {_ _} f => c f) (q.comp p) •
          ofPath (⟨e, b, q.comp p⟩ : Quiver.TotalPath Q) := by
  simp only [smul_mul_smul_comm, ofPath_mul_ofPath_of_comp,
    _root_.Quiver.Path.weight_comp]
  rw [mul_comm]

private theorem rescale_hzero {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    _root_.Quiver.Path.weight (fun {_ _} f => c f) x.2.2 • (ofPath x : pathAlgebra k Q) *
      _root_.Quiver.Path.weight (fun {_ _} f => c f) y.2.2 • ofPath y = 0 := by
  simp only [smul_mul_smul_comm, ofPath_mul_ofPath_of_not_composable h, smul_zero]

private theorem rescale_hone :
    letI := Fintype.ofFinite Q
    ∑ v : Q, _root_.Quiver.Path.weight (fun {_ _} f => c f)
        (⟨v, v, _root_.Quiver.Path.nil⟩ : Quiver.TotalPath Q).2.2 •
      (ofPath (⟨v, v, _root_.Quiver.Path.nil⟩ : Quiver.TotalPath Q) : pathAlgebra k Q) = 1 := by
  simp only [_root_.Quiver.Path.weight_nil, one_smul, ← vertexIdempotent_eq_ofPath]
  exact (@one_def k Q _ _ _ (Fintype.ofFinite Q)).symm

/-- The **arrow rescaling** attached to a labelling `c` of the arrows of `Q` by scalars: the algebra
endomorphism of the path algebra multiplying each basis path by its weight. Equivalently it fixes
every vertex idempotent and multiplies each arrow by its label. -/
noncomputable def rescale : pathAlgebra k Q →ₐ[k] pathAlgebra k Q :=
  liftAlgHom k
    (fun x => _root_.Quiver.Path.weight (fun {_ _} f => c f) x.2.2 • ofPath x)
      (rescale_hcomp c) (rescale_hzero c) (rescale_hone c)

/-- Rescaling a basis path multiplies it by the path's weight. -/
@[simp]
theorem rescale_ofPath (x : Quiver.TotalPath Q) :
    rescale c (ofPath x) =
      _root_.Quiver.Path.weight (fun {_ _} f => c f) x.2.2 • ofPath x := by
  rw [rescale]
  exact liftAlgHom_ofPath k
    (fun y : Quiver.TotalPath Q =>
      _root_.Quiver.Path.weight (fun {_ _} f => c f) y.2.2 • ofPath y)
      (rescale_hcomp c) (rescale_hzero c) (rescale_hone c) x

/-- Every vertex idempotent is fixed by arrow rescaling. -/
@[simp]
theorem rescale_vertexIdempotent (v : Q) :
    rescale c (vertexIdempotent k v) = vertexIdempotent k v := by
  rw [vertexIdempotent_eq_ofPath, rescale_ofPath, _root_.Quiver.Path.weight_nil, one_smul]

/-- Rescaling an arrow multiplies it by its label. -/
theorem rescale_ofArrow {a b : Q} (e : a ⟶ b) : rescale c (ofArrow e) = c e • ofArrow e := by
  rw [ofArrow_eq_ofPath, rescale_ofPath, _root_.Quiver.Path.weight_toPath]

/-- Rescaling by the constant labelling one is the identity. -/
@[simp]
theorem rescale_one : rescale (fun _ _ _ => (1 : k)) = AlgHom.id k (pathAlgebra k Q) :=
  AlgHom.toLinearMap_injective <| (pathAlgebraBasis k Q).ext fun x => by
    simp only [AlgHom.toLinearMap_apply, coe_pathAlgebraBasis, rescale_ofPath,
      _root_.Quiver.Path.weight_one, one_smul, AlgHom.id_apply]

/-- **Rescalings compose by multiplying labellings.** -/
@[simp]
theorem rescale_comp_rescale :
    (rescale c).comp (rescale d) = rescale (fun _ _ e => c e * d e) :=
  AlgHom.toLinearMap_injective <| (pathAlgebraBasis k Q).ext fun x => by
    simp only [AlgHom.toLinearMap_apply, coe_pathAlgebraBasis, AlgHom.comp_apply, rescale_ofPath,
      map_smul, _root_.Quiver.Path.weight_mul, mul_smul,
      smul_comm (_root_.Quiver.Path.weight (fun {_ _} f => c f) x.2.2)]

/-- Pointwise equal labellings give equal rescalings. -/
theorem rescale_congr (h : ∀ ⦃a b : Q⦄ (e : a ⟶ b), c e = d e) : rescale c = rescale d :=
  AlgHom.toLinearMap_injective <| (pathAlgebraBasis k Q).ext fun x => by
    simp only [AlgHom.toLinearMap_apply, coe_pathAlgebraBasis, rescale_ofPath,
      _root_.Quiver.Path.weight_congr c d h]

end Rescale

end PathAlgebra

end TauCeti
