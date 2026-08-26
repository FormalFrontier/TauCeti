/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Coordinate

/-!
# Algebraic criteria for central isogenies

Let `f : H ⟶ K` be a morphism of commutative Hopf algebras over a field. Contravariantly it
induces a homomorphism of affine group schemes

```text
Spec K ⟶ Spec H.
```

This homomorphism is an isogeny exactly when the coordinate ring map `f` is finite and faithfully
flat. Finiteness translates directly across `Spec`; flatness together with surjectivity translates
to faithful flatness. Combining this with the existing coordinate criterion for central kernels
shows that it is a central isogeny exactly when, in addition, its scheme-theoretic kernel Hopf
ideal is central.

The criteria are stated both as equivalences and as constructors and projections. Thus a
coordinate construction can establish a central isogeny without leaving commutative algebra, and
a scheme-theoretic central isogeny immediately exposes the finiteness and faithful-flatness facts
needed by later arguments.

## Main declarations

* `TauCeti.GroupScheme.isIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat`: the coordinate
  criterion for an isogeny.
* `TauCeti.GroupScheme.isCentralIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat_and_isCentral`:
  the corresponding criterion for a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 14 and 16.

This completes the Hopf-coordinate interface for central isogenies required in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k]
variable {H K : CommHopfAlgCat.{u} k}

/-- **Coordinate criterion for an isogeny.** The affine group-scheme morphism induced by a
commutative Hopf-algebra morphism is an isogeny exactly when the coordinate morphism is finite and
faithfully flat. -/
theorem isIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat (f : H ⟶ K) :
    IsIsogeny ((hopfSpec (CommRingCat.of k)).map f.op) ↔
      f.hom.toAlgHom.toRingHom.Finite ∧ f.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  rw [isIsogeny_iff]
  -- The three scheme properties retain the group-object wrappers around the underlying map;
  -- unfold that projection to `Spec.map` before applying Mathlib's affine criteria.
  change
    (IsFinite (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ∧
      Flat (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)) ∧
        Surjective (Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom))) ↔ _
  rw [IsFinite.SpecMap_iff, flat_and_surjective_SpecMap_iff]
  rfl

/-- A finite faithfully flat morphism of commutative Hopf algebras induces an isogeny of affine
group schemes. -/
theorem isIsogeny_hopfSpec_map_of_finite_of_faithfullyFlat (f : H ⟶ K)
    (hfinite : f.hom.toAlgHom.toRingHom.Finite)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    IsIsogeny ((hopfSpec (CommRingCat.of k)).map f.op) :=
  (isIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat f).2 ⟨hfinite, hflat⟩

namespace IsIsogeny

/-- The coordinate morphism of an affine group-scheme isogeny is finite. -/
theorem hom_finite {f : H ⟶ K}
    (hf : IsIsogeny ((hopfSpec (CommRingCat.of k)).map f.op)) :
    f.hom.toAlgHom.toRingHom.Finite :=
  (isIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat f).1 hf |>.1

/-- The coordinate morphism of an affine group-scheme isogeny is faithfully flat. -/
theorem hom_faithfullyFlat {f : H ⟶ K}
    (hf : IsIsogeny ((hopfSpec (CommRingCat.of k)).map f.op)) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat :=
  (isIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat f).1 hf |>.2

end IsIsogeny

/-- **Coordinate criterion for a central isogeny.** The affine group-scheme morphism induced by
`f` is a central isogeny exactly when `f` is finite and faithfully flat and its kernel Hopf ideal
is central. -/
theorem isCentralIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat_and_isCentral (f : H ⟶ K) :
    IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op) ↔
      f.hom.toAlgHom.toRingHom.Finite ∧
        f.hom.toAlgHom.toRingHom.FaithfullyFlat ∧
          (CommHopfAlgCat.kernelHopfIdeal f).IsCentral := by
  rw [isCentralIsogeny_hopfSpec_map_iff,
    isIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat, and_assoc]

/-- A finite faithfully flat morphism of commutative Hopf algebras with central kernel induces a
central isogeny of affine group schemes. -/
theorem isCentralIsogeny_hopfSpec_map_of_finite_of_faithfullyFlat_of_isCentral (f : H ⟶ K)
    (hfinite : f.hom.toAlgHom.toRingHom.Finite)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hcentral : (CommHopfAlgCat.kernelHopfIdeal f).IsCentral) :
    IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op) :=
  (isCentralIsogeny_hopfSpec_map_iff_finite_and_faithfullyFlat_and_isCentral f).2
    ⟨hfinite, hflat, hcentral⟩

namespace IsCentralIsogeny

/-- The coordinate morphism of an affine central isogeny is finite. -/
theorem hom_finite {f : H ⟶ K}
    (hf : IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op)) :
    f.hom.toAlgHom.toRingHom.Finite :=
  hf.isIsogeny.hom_finite

/-- The coordinate morphism of an affine central isogeny is faithfully flat. -/
theorem hom_faithfullyFlat {f : H ⟶ K}
    (hf : IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op)) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat :=
  hf.isIsogeny.hom_faithfullyFlat

/-- The kernel Hopf ideal of an affine central isogeny is central. -/
theorem isCentral_kernelHopfIdeal {f : H ⟶ K}
    (hf : IsCentralIsogeny ((hopfSpec (CommRingCat.of k)).map f.op)) :
    (CommHopfAlgCat.kernelHopfIdeal f).IsCentral :=
  (isCentralIsogeny_hopfSpec_map_iff f).1 hf |>.2

end IsCentralIsogeny

end TauCeti.GroupScheme
