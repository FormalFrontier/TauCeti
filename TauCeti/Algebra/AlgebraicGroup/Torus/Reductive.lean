/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Tori are reductive

A torus over a field is smooth and geometrically connected, and its geometric fibre is a
diagonalizable group. Every closed subgroup of a diagonalizable group has only semisimple
geometric points. If such a subgroup is also smooth and unipotent, smoothness makes its
coordinate ring reduced, while semisimple--unipotent rigidity makes it trivial. Thus a torus
has no nontrivial connected normal smooth unipotent closed subgroup and is reductive.

The proof applies equally to non-split tori: all subgroup tests in the definition of reductivity
are made after extension to an algebraic closure, where the torus is split.

## Main declarations

* `TauCeti.torusCommHopfAlgProperty.reductive`: every torus is reductive.
* `TauCeti.splitTorusCommHopfAlgProperty.reductive`: every split torus is reductive.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 12.41 and §21.a.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.

This completes the torus worked example requested in Layers 4 and 6 of the ReductiveGroups
roadmap. It uses geometric unipotence, rather than complete reducibility, so it is valid in every
characteristic.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace torusCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Every torus over a field is reductive.**

This uses the geometric-unipotent-radical characterization, and hence holds in arbitrary
characteristic. -/
@[grind →]
theorem reductive (hH : torusCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty k H := by
  rw [reductiveCommHopfAlgProperty_iff]
  refine ⟨(smoothCommHopfAlgProperty_iff H.obj).mp (hH.smooth k H),
    hH.geometricallyConnected k H, ?_⟩
  intro I _ _ hI
  have hI' := (smoothUnipotentCommHopfAlgProperty_iff (AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I)).mp hI
  let _ : Algebra.Smooth (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) := hI'.1
  let _ : IsReduced
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I) :=
    isReduced_of_smooth_of_field (AlgebraicClosure k) _
  apply (hH.multiplicativeType k H).eq_augmentation_of_geometricallyUnipotent k H I
  exact (geometricallyUnipotentPointsCommHopfAlgProperty_iff (AlgebraicClosure k) _).mpr hI'.2

end torusCommHopfAlgProperty

namespace splitTorusCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Every split torus over a field is reductive.** -/
@[grind →]
theorem reductive (hH : splitTorusCommHopfAlgProperty k H) :
    reductiveCommHopfAlgProperty k H :=
  (hH.torus k H).reductive

end splitTorusCommHopfAlgProperty

end TauCeti
