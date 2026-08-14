/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice

/-!
# Cocharacter lattices of tori

For a torus `T` over a field `k`, the geometric cocharacter lattice is canonically the integral
dual of the geometric character lattice:

```text
X_*(T) = Hom_ℤ(X*(T), ℤ).
```

This dual description is specific to tori. It would be false for general affine groups: for
example, a semisimple group can have trivial character group and nontrivial cocharacters. The
definition is therefore made only for an object of `TorusCommHopfAlgCat k`, whose property
ensures that its character group is finite free.

The absolute Galois action on `X_*(T)` is the contragredient of its action on `X*(T)`. The
evaluation pairing is invariant under the diagonal action and is perfect over `ℤ`. For the
standard split torus, the intrinsic dual is identified with the existing group of genuine
cocharacters, and the Galois representation is shown to be trivial.

## Main declarations

* `TauCeti.TorusCommHopfAlgCat.cocharacterLattice`: the geometric cocharacter lattice of a
  torus.
* `TauCeti.TorusCommHopfAlgCat.cocharacterGaloisRepresentation`: its contragredient absolute
  Galois representation.
* `TauCeti.TorusCommHopfAlgCat.characterCocharacterPairing`: the evaluation pairing between
  characters and cocharacters, with a perfect-pairing instance.
* `TauCeti.TorusCommHopfAlgCat.cocharacterLattice_module_free` and
  `TauCeti.TorusCommHopfAlgCat.cocharacterLattice_module_finite`: the cocharacter lattice is
  finite free over `ℤ`.
* `TauCeti.SplitTorus.cocharacterLatticeEquiv`: for a standard split torus, the intrinsic
  lattice is its existing group of genuine cocharacters.

## Roadmap

This completes the lattice-and-pairing part of Layer 4, "Tori: split and non-split; the
character lattice `X*(T)` and cocharacter lattice `X_*(T)` with their perfect pairing", in the
reductive-groups roadmap. Continuity of the Galois actions and the descent classification of
non-split tori remain separate steps.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
-/

public section

namespace TauCeti

universe u

namespace TorusCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The geometric cocharacter lattice of a torus, defined as the integral dual of its geometric
character lattice. -/
abbrev cocharacterLattice (T : TorusCommHopfAlgCat k) :=
  Module.Dual ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj)

/-- The contragredient absolute-Galois representation on the cocharacter lattice. Thus a
Galois element `σ` sends a cocharacter functional `f` to `x ↦ f (σ⁻¹ • x)`. -/
noncomputable abbrev cocharacterGaloisRepresentation (T : TorusCommHopfAlgCat k) :
    Representation ℤ (Field.absoluteGaloisGroup k) (cocharacterLattice T) :=
  (Representation.ofMulDistribMulAction (Field.absoluteGaloisGroup k)
    (CommHopfAlgCat.geometricCharacterGroup T.obj.obj)).dual

/-- The contragredient Galois representation evaluates by applying the inverse Galois element
to the character. -/
theorem cocharacterGaloisRepresentation_apply_apply (T : TorusCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k)
    (f : cocharacterLattice T) (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) :
    cocharacterGaloisRepresentation T σ f x = f (σ⁻¹ • x) := by
  rfl

/-- The canonical character--cocharacter pairing of a torus. It is evaluation of a functional
in `X_*(T) = Hom_ℤ(X*(T), ℤ)` on a character. -/
noncomputable abbrev characterCocharacterPairing (T : TorusCommHopfAlgCat k) :
    CommHopfAlgCat.additiveCharacterGroup T.obj.obj →ₗ[ℤ] cocharacterLattice T →ₗ[ℤ] ℤ :=
  Module.Dual.eval ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj)

/-- The character--cocharacter pairing is evaluation. -/
@[simp]
theorem characterCocharacterPairing_apply (T : TorusCommHopfAlgCat k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    characterCocharacterPairing T x f = f x :=
  Module.Dual.eval_apply ℤ _ x f

/-- The character--cocharacter pairing is invariant under the diagonal absolute-Galois action. -/
theorem characterCocharacterPairing_galois (T : TorusCommHopfAlgCat k)
    (σ : Field.absoluteGaloisGroup k)
    (x : CommHopfAlgCat.additiveCharacterGroup T.obj.obj) (f : cocharacterLattice T) :
    characterCocharacterPairing T (σ • x) (cocharacterGaloisRepresentation T σ f) =
      characterCocharacterPairing T x f := by
  rw [characterCocharacterPairing_apply, cocharacterGaloisRepresentation_apply_apply,
    inv_smul_smul, characterCocharacterPairing_apply]

/-- The character--cocharacter pairing of a torus is perfect. -/
noncomputable instance instCharacterCocharacterPairingIsPerfPair (T : TorusCommHopfAlgCat k) :
    (characterCocharacterPairing T).IsPerfPair := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  infer_instance

/-- The cocharacter lattice of a torus is free over the integers. -/
theorem cocharacterLattice_module_free (T : TorusCommHopfAlgCat k) :
    Module.Free ℤ (cocharacterLattice T) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  infer_instance

/-- The cocharacter lattice of a torus is finitely generated over the integers. -/
theorem cocharacterLattice_module_finite (T : TorusCommHopfAlgCat k) :
    Module.Finite ℤ (cocharacterLattice T) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  infer_instance

/-- The character and cocharacter lattices of a torus have the same rank. -/
theorem finrank_cocharacterLattice_eq_characterLattice (T : TorusCommHopfAlgCat k) :
    Module.finrank ℤ (cocharacterLattice T) =
      Module.finrank ℤ (CommHopfAlgCat.additiveCharacterGroup T.obj.obj) := by
  let _ := characterLattice_module_free_of_torus k T.obj T.property
  let _ := characterLattice_module_finite_of_torus k T.obj T.property
  exact (Module.finrank_of_isPerfPair (characterCocharacterPairing T)).symm

/-- A torus cocharacter lattice is noncanonically a finite-rank free abelian group, of the same
rank as its character lattice. -/
theorem exists_cocharacterLattice_linearEquiv (T : TorusCommHopfAlgCat k) :
    ∃ n : ℕ, Nonempty (cocharacterLattice T ≃ₗ[ℤ] (Fin n → ℤ)) := by
  obtain ⟨n, ⟨e⟩⟩ := exists_characterLattice_addEquiv_of_torus k T.obj T.property
  exact ⟨n, ⟨e.toIntLinearEquiv.symm.dualMap.trans (Finsupp.llift ℤ ℤ ℤ (Fin n)).symm⟩⟩

end TorusCommHopfAlgCat

namespace SplitTorus

/-- The standard rank-`σ` split torus, regarded as an object of the category of tori. -/
noncomputable abbrev toTorusCommHopfAlgCat
    (k : Type u) [Field k] (σ : Type u) [Finite σ] : TorusCommHopfAlgCat k :=
  ⟨DiagonalizableGroup.coordinateRing k (characterGroup σ),
    (splitTorus_coordinateRing k σ).torus k _⟩

/-- The intrinsic cocharacter lattice of a standard split torus in the coordinates `σ → ℤ`. -/
noncomputable def cocharacterLatticeCoordEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ) ≃ₗ[ℤ]
      (σ → ℤ) :=
  (characterLatticeEquiv k σ).toIntLinearEquiv.symm.dualMap |>.trans
    (Finsupp.llift ℤ ℤ ℤ σ).symm

/-- The intrinsic cocharacter lattice of a standard split torus is its existing group of genuine
cocharacters `Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ`. -/
noncomputable def cocharacterLatticeEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ) ≃ₗ[ℤ]
      Additive (Multiplicative (σ →₀ ℤ) →* Multiplicative ℤ) :=
  (cocharacterLatticeCoordEquiv k σ).trans cocharAddEquiv.toIntLinearEquiv.symm

/-- Under the intrinsic split-torus cocharacter equivalence, the usual cocharacter coordinates
are obtained by applying the functional to the corresponding standard characters. -/
@[simp]
theorem cocharAddEquiv_cocharacterLatticeEquiv_apply
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (f : TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) (i : σ) :
    cocharAddEquiv (cocharacterLatticeEquiv k σ f) i =
      f ((characterLatticeEquiv k σ).symm (Finsupp.single i 1)) := by
  simp [cocharacterLatticeEquiv, cocharacterLatticeCoordEquiv, Finsupp.llift_symm_apply]

/-- The absolute-Galois representation on the intrinsic cocharacter lattice of a standard split
torus is trivial. -/
theorem cocharacterGaloisRepresentation_apply_eq_self
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (γ : Field.absoluteGaloisGroup k)
    (f : TorusCommHopfAlgCat.cocharacterLattice (toTorusCommHopfAlgCat k σ)) :
    TorusCommHopfAlgCat.cocharacterGaloisRepresentation
      (toTorusCommHopfAlgCat k σ) γ f = f := by
  ext x
  rw [TorusCommHopfAlgCat.cocharacterGaloisRepresentation_apply_apply,
    smul_characterLattice_eq_self]

end SplitTorus

end TauCeti
