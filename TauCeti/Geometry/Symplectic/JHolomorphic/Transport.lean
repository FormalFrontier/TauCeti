/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Transporting constant-structure `J`-holomorphic maps along linear coordinate changes

This file records that the local constant-structure `J`-holomorphic predicate is invariant under
continuous
real-linear changes of source and target coordinates. If `f : V → W` is constant-structure
`J`-holomorphic and
`eV : V ≃L[ℝ] V'`, `eW : W ≃L[ℝ] W'`, then the transported map
`v' ↦ eW (f (eV.symm v'))` is constant-structure `J`-holomorphic for the transported almost complex
structures.

These are the chart-change lemmas needed before the analytic Heegaard Floer roadmap upgrades the
normed-vector-space Cauchy--Riemann equation to tangent charts on almost complex manifolds. The
almost complex structures themselves are transported by the linear-algebra API in
`TauCeti.Geometry.Symplectic.Transport`; this file adds the matching map-level calculus.

## Main declarations

* `TauCeti.IsConstStructureJHolomorphicAt.transport`: pointwise transport of constant-structure
`J`-holomorphicity.
* `TauCeti.IsConstStructureJHolomorphicWithinAt.transport`: within-set transport along a source
coordinate
  change whose inverse maps the transported source set back into the original source set.
* `TauCeti.IsConstStructureJHolomorphicOn.transport` and
`TauCeti.IsConstStructureJHolomorphic.transport`: setwise and
  global transport.
* `TauCeti.isConstStructureJHolomorphicAt_transport_iff`,
  `TauCeti.isConstStructureJHolomorphicWithinAt_transport_iff`,
  `TauCeti.isConstStructureJHolomorphicOn_transport_iff`,
  and `TauCeti.isConstStructureJHolomorphic_transport_iff`: transport equivalences, obtained by
  applying the
  forward statement in both directions.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: constant-structure `J`-holomorphicity is the Cauchy--Riemann equation
`df ∘ J = J' ∘ df`, and coordinate changes conjugate both `J` and `df`.
-/

public section

namespace TauCeti

variable {V W V' W' : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable [NormedAddCommGroup W'] [NormedSpace ℝ W']

section Transport

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}

/-- Transport a pointwise constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates. -/
lemma IsConstStructureJHolomorphicAt.transport {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV x) := by
  have hsource :
      IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) J
        (fun y : V' => eV.symm y) (eV x) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eV.symm.toContinuousLinearMap
      (eV x)).mpr
      (AlmostComplexStructure.isComplexLinearMap_symm_transport J eV.toLinearEquiv)
  have htarget :
      IsConstStructureJHolomorphicAt J' (J'.transport eW.toLinearEquiv) (fun y : W => eW y)
        (f (eV.symm (eV x))) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eW.toContinuousLinearMap
      (f (eV.symm (eV x)))).mpr
      (AlmostComplexStructure.isComplexLinearMap_transport J' eW.toLinearEquiv)
  have hmiddle : IsConstStructureJHolomorphicAt J J' f (eV.symm (eV x)) := by
    simpa
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicAt.comp
      (J := J.transport eV.toLinearEquiv) (J' := J') (J'' := J'.transport eW.toLinearEquiv)
      (f := fun y : V' => f (eV.symm y)) (g := fun y : W => eW y) (x := eV x)
      htarget (hmiddle.comp hsource)

/-- Transport a within-set constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates, for any target-domain set whose points map back into the
original source set. -/
lemma IsConstStructureJHolomorphicWithinAt.transport {f : V → W} {s : Set V} {x : V} {t : Set V'}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    Set.MapsTo (fun y : V' => eV.symm y) t s →
    IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv)
      (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) t (eV x) := by
  intro hts
  have hsourceAt :
      IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) J
        (fun y : V' => eV.symm y) (eV x) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eV.symm.toContinuousLinearMap
      (eV x)).mpr
      (AlmostComplexStructure.isComplexLinearMap_symm_transport J eV.toLinearEquiv)
  have hsource :
      IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv) J
        (fun y : V' => eV.symm y) t (eV x) :=
    hsourceAt.isConstStructureJHolomorphicWithinAt
  have htargetAt :
      IsConstStructureJHolomorphicAt J' (J'.transport eW.toLinearEquiv) (fun y : W => eW y)
        (f (eV.symm (eV x))) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eW.toContinuousLinearMap
      (f (eV.symm (eV x)))).mpr
      (AlmostComplexStructure.isComplexLinearMap_transport J' eW.toLinearEquiv)
  have htarget :
      IsConstStructureJHolomorphicWithinAt J' (J'.transport eW.toLinearEquiv)
        (fun y : W => eW y) Set.univ (f (eV.symm (eV x))) :=
    htargetAt.isConstStructureJHolomorphicWithinAt
  have hmiddle : IsConstStructureJHolomorphicWithinAt J J' f s (eV.symm (eV x)) := by
    simpa
  have hinner : IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv) J'
      (fun y : V' => f (eV.symm y)) t (eV x) := by
    simpa [Function.comp_def] using hmiddle.comp hsource hts
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicWithinAt.comp
      (J := J.transport eV.toLinearEquiv) (J' := J') (J'' := J'.transport eW.toLinearEquiv)
      (f := fun y : V' => f (eV.symm y)) (g := fun y : W => eW y) (s := t)
      (t := Set.univ) (x := eV x) htarget hinner (fun _ _ => Set.mem_univ _)

/-- Transport a setwise constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates, for any target-domain set whose points map back into the
original source set. -/
lemma IsConstStructureJHolomorphicOn.transport {f : V → W} {s : Set V} {t : Set V'}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    Set.MapsTo (fun y : V' => eV.symm y) t s →
    IsConstStructureJHolomorphicOn (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) t := by
  intro hts
  exact isConstStructureJHolomorphicOn_of_forall fun y hy => by
    simpa [eV.apply_symm_apply y] using
      (hf.isConstStructureJHolomorphicWithinAt (hts hy)).transport eV eW hts

/-- Transport a globally constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates. -/
lemma IsConstStructureJHolomorphic.transport {f : V → W} (hf : IsConstStructureJHolomorphic J J' f)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphic (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) := by
  exact isConstStructureJHolomorphic_of_forall fun y => by
    simpa [eV.apply_symm_apply y] using
      (hf.isConstStructureJHolomorphicAt (eV.symm y)).transport eV eW

/-- Pointwise constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate changes. -/
@[simp]
lemma isConstStructureJHolomorphicAt_transport_iff (f : V → W) (x : V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV x) ↔ IsConstStructureJHolomorphicAt J J' f x := by
  refine ⟨fun h => ?_, fun h => h.transport eV eW⟩
  have hback := h.transport eV.symm eW.symm
  simpa [AlmostComplexStructure.transport_symm_transport, eV.symm_apply_apply,
    eW.symm_apply_apply] using hback

/-- Within-set constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate
changes, with the source set sent to its image. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_transport_iff (f : V → W) (s : Set V) (x : V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv)
      (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV '' s) (eV x) ↔
        IsConstStructureJHolomorphicWithinAt J J' f s x := by
  refine ⟨fun h => ?_, fun h => h.transport eV eW ?_⟩
  · have hmaps : Set.MapsTo (fun y : V => eV.symm.symm y) s (eV '' s) := by
      intro y hy
      refine ⟨y, hy, ?_⟩
      simp
    have hback := h.transport eV.symm eW.symm (t := s) hmaps
    simpa [AlmostComplexStructure.transport_symm_transport, eV.symm_apply_apply,
      eW.symm_apply_apply] using hback
  · rintro y ⟨z, hz, rfl⟩
    simpa using hz

/-- Setwise constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate changes,
with the source set sent to its image. -/
@[simp]
lemma isConstStructureJHolomorphicOn_transport_iff (f : V → W) (s : Set V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicOn (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV '' s) ↔ IsConstStructureJHolomorphicOn J J' f s := by
  refine ⟨fun h => isConstStructureJHolomorphicOn_of_forall fun x hx => ?_,
    fun h => h.transport eV eW ?_⟩
  · exact (isConstStructureJHolomorphicWithinAt_transport_iff f s x eV eW).mp
      (h.isConstStructureJHolomorphicWithinAt ⟨x, hx, rfl⟩)
  · rintro y ⟨z, hz, rfl⟩
    simpa using hz

/-- Global constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate changes. -/
@[simp]
lemma isConstStructureJHolomorphic_transport_iff (f : V → W) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphic (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) ↔ IsConstStructureJHolomorphic J J' f := by
  refine ⟨fun h => isConstStructureJHolomorphic_of_forall fun x => ?_,
    fun h => h.transport eV eW⟩
  exact (isConstStructureJHolomorphicAt_transport_iff f x eV eW).mp
    (h.isConstStructureJHolomorphicAt (eV x))

end Transport

end TauCeti
