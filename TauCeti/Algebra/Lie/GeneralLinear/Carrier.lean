/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Restriction
public import TauCeti.Algebra.Lie.GeneralLinear.Twist
public import TauCeti.Algebra.Lie.GeneralLinear.Uniqueness
public import TauCeti.Algebra.Lie.Submodule.Atom

/-!
# The named irreducible `gl N`-module of a dominant weight

Let `K` be a field of characteristic zero. Every dominant integral weight `mu : Fin N → K` is the
highest weight of a finite-dimensional irreducible `gl N K`-module, and that module is unique up to
isomorphism. This file names it: `TauCeti.glIrreducible N mu`, the `L(mu)` of the general linear
Lie algebra.

## The construction

Both halves of the classification are already available, and the carrier is assembled from them.
`TauCeti.exists_isGlHighestWeightVector_of_isGlDominantIntegral` realizes `mu` as the weight of a
highest weight vector `v` in a finite-dimensional module, namely a trace twist of an exterior power
of a standard module; `TauCeti.nonempty_lieModuleEquiv_of_isGlHighestWeightVector` says that an
irreducible module carrying such a vector is determined by `mu`. What is missing between the two is
that an irreducible one exists at all. The complete-reducibility API currently available in Tau Ceti
applies to Killing-semisimple Lie algebras over algebraically closed fields, not directly to
`gl N K`; this file instead uses a quotient construction available at the stated generality. The Lie
submodule `v` generates is finite-dimensional, so its lattice of Lie submodules has a coatom, and
`TauCeti.isIrreducible_quotient_iff_isCoatom` makes the quotient by that coatom irreducible, with
the class of `v` a highest weight vector of weight `mu` still.

This quotient route avoids requiring a separate complete-reducibility transfer from `sl N K` to
the particular trace-twisted exterior-power module. Such a transfer can recover a submodule
realization because the identity acts by one scalar there, but that result is not part of the
available API used by this construction.

Two choices go into the carrier, the decomposition of `mu` as an antitone tuple of natural numbers
translated along the central direction and the coatom, and the construction singles out neither:
both are made with `Classical.choice`, and nothing is claimed about which. The carrier is therefore
characterized not by its construction but by
`TauCeti.nonempty_lieModuleEquiv_glIrreducible`, which identifies it with *any* irreducible module
carrying a highest weight vector of weight `mu`. Off the dominant weights the carrier is junk —
still a finite-dimensional `gl N K`-module, but with no claim about it — as with the other
total-by-convention constructions of the roadmap.

## Main definitions

* `TauCeti.glIrreducible N mu`: the named carrier `L(mu)`, with its `K`-module and `gl N K`-module
  structures and its finite-dimensionality.
* `TauCeti.glIrreducibleGenerator N mu`: its distinguished generator, the class of the chosen
  highest weight vector. Like the carrier itself it depends on the two choices above, so what is
  known of it is what the results below say.

The construction itself — the chosen decomposition of `mu`, the chosen highest weight vector, the
Lie submodule it generates, the chosen coatom, and the lemmas about them — is private to this file
and is no part of the interface. The data-carrying module instances transported from the quotient
are marked `@[no_expose]`, which is what lets their bodies name those private constants.

## Main results

* `TauCeti.isIrreducible_glIrreducible`: **`L(mu)` is irreducible** for dominant integral `mu`.
* `TauCeti.isGlHighestWeightVector_glIrreducibleGenerator`, with its existential form
  `TauCeti.exists_isGlHighestWeightVector_glIrreducible`: **its distinguished generator is a highest
  weight vector of weight `mu` and generates the carrier**, which is what ties the carrier to its
  name; `TauCeti.lieSpan_glIrreducibleGenerator_eq_top` states the generating property explicitly.
* `TauCeti.nonempty_lieModuleEquiv_glIrreducible`: **`L(mu)` is *the* irreducible of highest weight
  `mu`**: every irreducible `gl N K`-module carrying a highest weight vector of weight `mu` is
  isomorphic to it, and `TauCeti.finrank_glIrreducible_le` bounds its dimension by that of any
  finite-dimensional module carrying such a vector.
* `TauCeti.isIrreducible_glIrreducible_restrict_sl`: **`L(mu)` stays irreducible on restriction to
  `sl N K`**, over any characteristic-zero field: by
  `TauCeti.one_lie_glIrreducible_eq_smul` the identity matrix acts by the explicit scalar
  `∑ i, mu i`, so no algebraic closedness is needed to know that the centre acts by scalars.

## References

This is the named carrier `glIrreducible` of Layer 9 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, with the structural pins
`isIrreducible_glIrreducible`, `finiteDimensional_glIrreducible`,
`exists_isGlHighestWeightVector_glIrreducible` and `isIrreducible_glIrreducible_restrict_sl` of its
`Suggested.lean`.

* R. Goodman, N. R. Wallach, *Symmetry, Representations, and Invariants*, GTM 255, §5.5.
-/

public section

namespace TauCeti

open LieModule Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u} [Field K] [CharZero K] {N : ℕ} {mu : Fin N → K}

/-! ### The realizing module and its highest weight vector -/

private theorem exists_glCarrierData (K : Type u) [Field K] [CharZero K] {N : ℕ}
    (mu : Fin N → K) :
    ∃ p : (Fin N → ℕ) × K,
      IsGlDominantIntegral mu →
        Antitone p.1 ∧ mu = (fun i => ((p.1 i : K) + p.2)) ∧
          ∃ v : glTraceTwistedYoungWedge K p.1 p.2, IsGlHighestWeightVector mu v := by
  by_cases hmu : IsGlDominantIntegral mu
  · obtain ⟨a, c, ha, hac, v, hv⟩ :=
      exists_isGlHighestWeightVector_of_isGlDominantIntegral hmu
    exact ⟨(a, c), fun _ => ⟨ha, hac, v, hv⟩⟩
  · exact ⟨(fun _ => 0, 0), fun h => absurd h hmu⟩

variable (K) in
/-- **The decomposition of `mu` chosen to realize it as a highest weight**: an antitone tuple of
natural numbers together with a scalar summing to `mu`, which
`TauCeti.IsGlDominantIntegral.exists_antitone_natCast_add_const` supplies for a dominant `mu`.
The decomposition is not unique, so one is chosen;
for dominant weights its defining property follows from
`TauCeti.exists_isGlHighestWeightVector_of_isGlDominantIntegral`. Off the dominant weights it is an
unspecified choice about which nothing is claimed. -/
private noncomputable def glCarrierData (mu : Fin N → K) : (Fin N → ℕ) × K :=
  (exists_glCarrierData K mu).choose

private theorem exists_glCarrierVector (K : Type u) [Field K] [CharZero K] {N : ℕ}
    (mu : Fin N → K) :
    ∃ v : glTraceTwistedYoungWedge K (glCarrierData K mu).1 (glCarrierData K mu).2,
      IsGlDominantIntegral mu → IsGlHighestWeightVector mu v := by
  by_cases hmu : IsGlDominantIntegral mu
  · obtain ⟨-, -, v, hv⟩ := (exists_glCarrierData K mu).choose_spec hmu
    exact ⟨v, fun _ => hv⟩
  · exact ⟨0, fun h => absurd h hmu⟩

variable (K) in
/-- **The chosen highest weight vector of weight `mu`**, inside the trace-twisted Young wedge named
by `TauCeti.glCarrierData`. For dominant `mu` it is a highest weight vector of weight `mu`
(`isGlHighestWeightVector_glCarrierVector`). Off the dominant weights it is an unspecified choice
about which nothing is claimed. -/
private noncomputable def glCarrierVector (mu : Fin N → K) :
    glTraceTwistedYoungWedge K (glCarrierData K mu).1 (glCarrierData K mu).2 :=
  (exists_glCarrierVector K mu).choose

/-- **The chosen vector realizes a dominant `mu` as a highest weight.** -/
private theorem isGlHighestWeightVector_glCarrierVector (hmu : IsGlDominantIntegral mu) :
    IsGlHighestWeightVector mu (glCarrierVector K mu) :=
  (exists_glCarrierVector K mu).choose_spec hmu

variable (K) in
/-- **The highest weight module the chosen vector generates**, a finite-dimensional
`gl N K`-module of which `L(mu)` is a quotient. -/
private noncomputable def glCarrierSpan (mu : Fin N → K) :
    LieSubmodule K (Matrix (Fin N) (Fin N) K)
      (glTraceTwistedYoungWedge K (glCarrierData K mu).1 (glCarrierData K mu).2) :=
  LieSubmodule.lieSpan K _ {glCarrierVector K mu}

/-- The chosen vector, read inside the Lie submodule it generates. -/
private theorem glCarrierVector_mem_glCarrierSpan : glCarrierVector K mu ∈ glCarrierSpan K mu :=
  LieSubmodule.subset_lieSpan rfl

/-- **Inside the module it generates, the chosen vector is again a highest weight vector.** -/
private theorem isGlHighestWeightVector_glCarrierVector_mem (hmu : IsGlDominantIntegral mu) :
    IsGlHighestWeightVector mu
      (⟨glCarrierVector K mu, glCarrierVector_mem_glCarrierSpan⟩ : glCarrierSpan K mu) :=
  isGlHighestWeightVector_coe_iff.mp (isGlHighestWeightVector_glCarrierVector hmu)

private instance : FiniteDimensional K (glCarrierSpan K mu) :=
  inferInstanceAs (FiniteDimensional K (glCarrierSpan K mu).toSubmodule)

/-! ### The coatom and the carrier -/

private theorem exists_glCarrierCoatom (K : Type u) [Field K] [CharZero K] {N : ℕ}
    (mu : Fin N → K) :
    ∃ P : LieSubmodule K (Matrix (Fin N) (Fin N) K) (glCarrierSpan K mu),
      IsGlDominantIntegral mu → IsCoatom P := by
  by_cases hmu : IsGlDominantIntegral mu
  · have : Nontrivial (glCarrierSpan K mu) :=
      nontrivial_of_ne _ _ (isGlHighestWeightVector_glCarrierVector_mem hmu).ne_zero
    obtain ⟨P, hP⟩ := IsCoatomic.exists_coatom
      (α := LieSubmodule K (Matrix (Fin N) (Fin N) K) (glCarrierSpan K mu))
    exact ⟨P, fun _ => hP⟩
  · exact ⟨⊥, fun h => absurd h hmu⟩

variable (K) in
/-- **The chosen maximal proper Lie submodule** of the module the chosen highest weight vector
generates. It is a coatom of the lattice of Lie submodules for dominant `mu`
(`isCoatom_glCarrierCoatom`). Off the dominant weights it is an unspecified choice about which
nothing is claimed. -/
private noncomputable def glCarrierCoatom (mu : Fin N → K) :
    LieSubmodule K (Matrix (Fin N) (Fin N) K) (glCarrierSpan K mu) :=
  (exists_glCarrierCoatom K mu).choose

/-- **The chosen submodule is a coatom**, for a dominant weight. -/
private theorem isCoatom_glCarrierCoatom (hmu : IsGlDominantIntegral mu) :
    IsCoatom (glCarrierCoatom K mu) :=
  (exists_glCarrierCoatom K mu).choose_spec hmu

/-- **The irreducible `gl N K`-module `L(mu)` of highest weight `mu`**, the quotient of the module
generated by the chosen highest weight vector by the chosen maximal proper submodule of it.

For a dominant integral `mu` this is irreducible (`TauCeti.isIrreducible_glIrreducible`), carries a
highest weight vector of weight `mu`
(`TauCeti.isGlHighestWeightVector_glIrreducibleGenerator`), and is thereby determined up to
isomorphism (`TauCeti.nonempty_lieModuleEquiv_glIrreducible`). Off the dominant weights nothing is
claimed of it; it is total in `mu` only so that statements about it need not carry dominance in
their types. -/
def glIrreducible (N : ℕ) (mu : Fin N → K) : Type u :=
  glCarrierSpan K mu ⧸ glCarrierCoatom K mu

@[no_expose] noncomputable instance : AddCommGroup (glIrreducible N mu) :=
  inferInstanceAs (AddCommGroup (glCarrierSpan K mu ⧸ glCarrierCoatom K mu))

@[no_expose] noncomputable instance : Module K (glIrreducible N mu) :=
  inferInstanceAs (Module K (glCarrierSpan K mu ⧸ glCarrierCoatom K mu))

@[no_expose] noncomputable instance :
    LieRingModule (Matrix (Fin N) (Fin N) K) (glIrreducible N mu) :=
  inferInstanceAs (LieRingModule (Matrix (Fin N) (Fin N) K)
    (glCarrierSpan K mu ⧸ glCarrierCoatom K mu))

noncomputable instance : LieModule K (Matrix (Fin N) (Fin N) K) (glIrreducible N mu) :=
  inferInstanceAs (LieModule K (Matrix (Fin N) (Fin N) K)
    (glCarrierSpan K mu ⧸ glCarrierCoatom K mu))

/-- **`L(mu)` is finite-dimensional**, for every `mu`: it is a quotient of a submodule of an
exterior power of a finite-dimensional standard module. Dominance is needed only to know that it is
not the zero module. -/
instance finiteDimensional_glIrreducible : FiniteDimensional K (glIrreducible N mu) :=
  inferInstanceAs (FiniteDimensional K
    ((glCarrierSpan K mu) ⧸ (glCarrierCoatom K mu).toSubmodule))

/-- **The distinguished generator of `L(mu)`**, the class of the chosen highest weight vector. It
inherits the two choices the carrier is built from and is not canonical; what is known of it is
`TauCeti.isGlHighestWeightVector_glIrreducibleGenerator`. -/
noncomputable def glIrreducibleGenerator (N : ℕ) (mu : Fin N → K) : glIrreducible N mu :=
  LieSubmodule.Quotient.mk' (glCarrierCoatom K mu)
    ⟨glCarrierVector K mu, glCarrierVector_mem_glCarrierSpan⟩

/-! ### The structure of the carrier -/

/-- **`L(mu)` is irreducible**, for a dominant integral `mu`: it is the quotient of a Lie module by
a coatom of its lattice of Lie submodules. -/
theorem isIrreducible_glIrreducible (hmu : IsGlDominantIntegral mu) :
    LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) (glIrreducible N mu) :=
  isIrreducible_quotient_iff_isCoatom.mpr (isCoatom_glCarrierCoatom hmu)

/-- **The distinguished generator of `L(mu)` is a highest weight vector of weight `mu`**, the
statement that ties the carrier to its name. It is nonzero because the chosen vector generates the
module being divided, so a proper submodule cannot contain it. -/
theorem isGlHighestWeightVector_glIrreducibleGenerator (hmu : IsGlDominantIntegral mu) :
    IsGlHighestWeightVector mu (glIrreducibleGenerator N mu) := by
  refine (isGlHighestWeightVector_glCarrierVector_mem hmu).map _ fun hzero => ?_
  have hmem := (LieSubmodule.Quotient.mk_eq_zero _).mp hzero
  exact (isCoatom_glCarrierCoatom (K := K) hmu).1
    (eq_top_of_mem_of_lieSpan_singleton_eq_top hmem
      (lieSpan_singleton_eq_top_of_lieSpan_eq rfl))

/-- **The distinguished highest weight vector generates `L(mu)`.** -/
theorem lieSpan_glIrreducibleGenerator_eq_top (hmu : IsGlDominantIntegral mu) :
    LieSubmodule.lieSpan K (Matrix (Fin N) (Fin N) K) {glIrreducibleGenerator N mu} = ⊤ := by
  let _ := isIrreducible_glIrreducible (K := K) hmu
  exact lieSpan_singleton_eq_top_of_ne_zero
    (isGlHighestWeightVector_glIrreducibleGenerator (K := K) hmu).ne_zero

/-- **`L(mu)` carries a highest weight vector of weight `mu`**, the existential form of
`TauCeti.isGlHighestWeightVector_glIrreducibleGenerator` pinned by the roadmap. -/
theorem exists_isGlHighestWeightVector_glIrreducible (hmu : IsGlDominantIntegral mu) :
    ∃ v : glIrreducible N mu, IsGlHighestWeightVector mu v :=
  ⟨_, isGlHighestWeightVector_glIrreducibleGenerator hmu⟩

variable {M : Type*} [AddCommGroup M] [Module K M]
  [LieRingModule (Matrix (Fin N) (Fin N) K) M] [LieModule K (Matrix (Fin N) (Fin N) K) M]

/-- **`L(mu)` is *the* irreducible of highest weight `mu`.** Any irreducible `gl N K`-module
carrying a highest weight vector of weight `mu` is isomorphic to the carrier, so nothing is lost by
naming one of them. `M` is not assumed finite-dimensional, the classification
`TauCeti.nonempty_lieModuleEquiv_of_isGlHighestWeightVector` needing no finiteness; that `M` then
*is* finite-dimensional is a consequence rather than a hypothesis. -/
theorem nonempty_lieModuleEquiv_glIrreducible
    [LieModule.IsIrreducible K (Matrix (Fin N) (Fin N) K) M] {v : M}
    (hmu : IsGlDominantIntegral mu) (hv : IsGlHighestWeightVector mu v) :
    Nonempty (M ≃ₗ⁅K, Matrix (Fin N) (Fin N) K⁆ glIrreducible N mu) :=
  have := isIrreducible_glIrreducible (K := K) hmu
  nonempty_lieModuleEquiv_of_isGlHighestWeightVector hv
    (isGlHighestWeightVector_glIrreducibleGenerator hmu)

/-- **`L(mu)` has the smallest dimension of the modules of highest weight `mu`**: any
finite-dimensional `gl N K`-module carrying a highest weight vector of weight `mu` has at least the
dimension of the carrier. -/
theorem finrank_glIrreducible_le [FiniteDimensional K M] {v : M}
    (hmu : IsGlDominantIntegral mu) (hv : IsGlHighestWeightVector mu v) :
    finrank K (glIrreducible N mu) ≤ finrank K M :=
  have := isIrreducible_glIrreducible (K := K) hmu
  finrank_le_of_isGlHighestWeightVector (isGlHighestWeightVector_glIrreducibleGenerator hmu) hv

/-- **The identity matrix acts on `L(mu)` by the scalar `∑ i, mu i`.** -/
theorem one_lie_glIrreducible_eq_smul (hmu : IsGlDominantIntegral mu)
    (m : glIrreducible N mu) :
    ⁅(1 : Matrix (Fin N) (Fin N) K), m⁆ = (∑ i, mu i) • m := by
  let _ := isIrreducible_glIrreducible (K := K) hmu
  exact forall_one_lie_eq_sum_smul_of_isGlHighestWeightVector
    (isGlHighestWeightVector_glIrreducibleGenerator (K := K) hmu) m

/-- **`L(mu)` stays irreducible on restriction to `sl N K`**: the identity matrix acts on it by the
scalar `∑ i, mu i` (`TauCeti.one_lie_glIrreducible_eq_smul`), so the centre of `gl N K` acts by
scalars and the `sl N K`-submodules are already `gl N K`-submodules. The explicit scalar is what
lets the statement hold over any characteristic-zero field, algebraic closedness being needed only
where the scalar has to be produced by Schur's lemma. -/
theorem isIrreducible_glIrreducible_restrict_sl (hmu : IsGlDominantIntegral mu) :
    LieModule.IsIrreducible K (LieAlgebra.SpecialLinear.sl (Fin N) K) (glIrreducible N mu) :=
  let _ := isIrreducible_glIrreducible (K := K) hmu
  isIrreducible_restrict_sl_of_isGlHighestWeightVector (fun hN => Nat.cast_ne_zero.mpr hN)
    (isGlHighestWeightVector_glIrreducibleGenerator hmu)

end TauCeti
