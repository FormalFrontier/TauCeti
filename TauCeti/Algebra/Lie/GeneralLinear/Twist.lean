/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.YoungWedge
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Lie.Classical

public section

/-!
# The trace twist of a `gl n`-module, and every dominant weight as a highest weight

Dominance for `gl n` constrains only the consecutive *differences* of a weight
(`TauCeti.IsGlDominantIntegral`), so the dominant weights are the antitone tuples of natural
numbers translated along the central direction `μ ↦ μ + c · (1, …, 1)`, with `c` a free scalar.
`TauCeti.exists_isGlHighestWeightVector_natCast` realizes the natural-number weights as highest
weights inside exterior powers; this file supplies the central direction and, with it, **every**
dominant weight.

## The twist

The trace is a Lie character of `gl n`: it is linear and kills every commutator
(`LieAlgebra.matrix_trace_commutator_zero`). So for a scalar `c` and a `gl n`-module `M` the
formula

`⁅A, m⁆' = ⁅A, m⁆ + c · tr(A) · m`

is again a `gl n`-module structure on the underlying `R`-module of `M`. It is carried by
`TauCeti.GlTraceTwist n c M`, a copy of `M` with the same `R`-module structure and the displayed
bracket; `TauCeti.GlTraceTwist.linearEquiv` is that identification of the underlying `R`-modules,
and `TauCeti.GlTraceTwist.ofTwist_lie` is the defining equation of the bracket.

Since `tr(Eᵢᵢ) = 1` and `tr(Eᵢⱼ) = 0` for `i ≠ j`, twisting shifts the weight of a highest weight
vector by `c` in every coordinate and changes nothing else
(`TauCeti.isGlHighestWeightVector_toTwist`). No invertibility of the size of the matrices is
needed: the shift is read off the diagonal matrix units, not off the identity matrix.

## Every dominant weight is a highest weight

A dominant weight `μ : Fin N → R` is `a + c` for an antitone `a : Fin N → ℕ` and a scalar `c`, by
`TauCeti.IsGlDominantIntegral.exists_antitone_natCast_add_const` in
`TauCeti/Algebra/Lie/GeneralLinear/HighestWeight.lean`. Twisting the exterior-power realization of
`a` by `c` then realizes `μ`, which is
`TauCeti.exists_isGlHighestWeightVector_of_isGlDominantIntegral`. The realizing module
`TauCeti.glTraceTwistedYoungWedge` is finite over `R`, hence finite-dimensional over a field.

## Main definitions

* `TauCeti.GlTraceTwist`: a `gl n`-module twisted by the character `c · tr`.
* `TauCeti.GlTraceTwist.linearEquiv`: the underlying `R`-modules of a module and of its twist.
* `TauCeti.glTraceTwistedYoungWedge`: the trace twist by `c` of the exterior power in which
  `TauCeti.exists_isGlHighestWeightVector_natCast` realizes a tuple `a` of natural numbers; for an
  antitone `a` it carries a highest weight vector of the dominant weight `a + c · (1, …, 1)`.
* `TauCeti.glTraceTwistedYoungWedge.linearEquiv`: the underlying `R`-module of that carrier is the
  exterior power it twists.

## Main results

* `TauCeti.GlTraceTwist.ofTwist_lie`: the defining equation of the twisted bracket.
* `TauCeti.isGlHighestWeightVector_toTwist_iff` and its introduction half
  `TauCeti.isGlHighestWeightVector_toTwist`: twisting by `c` shifts the weight of a highest weight
  vector by `c` in every coordinate, and nothing else;
  `TauCeti.glTraceTwistedYoungWedge.isGlHighestWeightVector_linearEquiv_symm` is that introduction
  rule for the named carrier.
* `TauCeti.exists_isGlHighestWeightVector_of_isGlDominantIntegral`: **every dominant weight of
  `gl N` is the highest weight of a highest weight vector in a module finite over `R`.**

## Implementation notes

Twisting by the trace loses no generality. A Lie character of `gl ι` in the sense of
`LieAlgebra.LieCharacter` vanishes on the derived ideal
(`LieAlgebra.lieCharacter_apply_of_mem_derived`), which is the trace-zero ideal
(`TauCeti.derivedSeries_one_eq_slIdeal`); since a matrix differs from a multiple of a single
diagonal matrix unit by a trace-zero matrix, every character of `gl ι` is `c · tr` for a nonempty
`ι`. So the scalar `c` is a coordinate on the characters, and the twist below is the twist by an
arbitrary one.

`TauCeti.GlTraceTwist` is a one-field structure rather than a bare type synonym, so that the
twisting data `ι` and `c` are honest parameters of the carrier; the module structures are
transported along the resulting equivalence. This is the pattern of Mathlib's `WithLp`, which
carries a phantom exponent in the same way.

## Roadmap context

Layer 9 of the
[highest weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md)
asks for a finite-dimensional irreducible `gl n`-module for each dominant weight, the entries of a
dominant weight being free scalars and only their differences constrained. The existence input for
the weights with natural number entries is
`TauCeti.exists_isGlHighestWeightVector_natCast`; this file supplies the remaining central
direction, so that the existence half of that classification reaches every dominant weight.
Cutting the realizing module down to an irreducible one, and naming the resulting carrier, is not
done here.

## References

* W. Fulton, J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991), §15.5,
  where the rational representations of `GL n` are the determinant twists of the polynomial ones.
-/

namespace TauCeti

open Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

/-! ### The carrier of the trace twist -/

/-- **The trace twist** of a `gl ι`-module `M` by a scalar `c`: a copy of `M` with the same
`R`-module structure and with the bracket `⁅A, m⁆ + c · tr(A) · m`. It is again a `gl ι`-module
because the trace is a Lie character, that is, a linear form killing every commutator.

`TauCeti.GlTraceTwist.linearEquiv` identifies the underlying `R`-modules and
`TauCeti.GlTraceTwist.ofTwist_lie` computes the twisted bracket, so that the twist is used through
its API rather than through the wrapper. -/
structure GlTraceTwist (ι : Type*) {R : Type u} (c : R) (M : Type v) where
  /-- Read a vector of `M` as a vector of the trace twist. -/
  toTwist (ι c) ::
  /-- Read a vector of the trace twist as a vector of `M`. -/
  ofTwist : M

namespace GlTraceTwist

/-- `TauCeti.GlTraceTwist.ofTwist` and `TauCeti.GlTraceTwist.toTwist` as an equivalence: the twist
has the same underlying type. -/
protected def equiv (ι : Type*) {R : Type u} (c : R) (M : Type v) : GlTraceTwist ι c M ≃ M where
  toFun := ofTwist
  invFun := toTwist ι c
  left_inv _ := rfl
  right_inv _ := rfl

section Carrier

variable {R : Type u} {ι : Type*} {c : R} {M : Type v}

instance [Nontrivial M] : Nontrivial (GlTraceTwist ι c M) :=
  (GlTraceTwist.equiv ι c M).nontrivial

instance [AddCommGroup M] : AddCommGroup (GlTraceTwist ι c M) :=
  (GlTraceTwist.equiv ι c M).addCommGroup

variable (ι c M) in
/-- The additive groups of a module and of its trace twist agree. -/
protected def addEquiv [AddCommGroup M] : GlTraceTwist ι c M ≃+ M where
  __ := GlTraceTwist.equiv ι c M
  map_add' _ _ := rfl

instance [Semiring R] [AddCommGroup M] [Module R M] : Module R (GlTraceTwist ι c M) :=
  (GlTraceTwist.addEquiv ι c M).module R

variable (ι c M) in
/-- **A trace twist has the same underlying `R`-module.** Every statement about the twisted bracket
is made against this equivalence, so that the wrapper is never unfolded. -/
protected def linearEquiv [Semiring R] [AddCommGroup M] [Module R M] :
    GlTraceTwist ι c M ≃ₗ[R] M where
  __ := GlTraceTwist.addEquiv ι c M
  map_smul' _ _ := rfl

/-- The underlying-module equivalence of a trace twist is the underlying-vector map. -/
@[simp]
theorem coe_linearEquiv [Semiring R] [AddCommGroup M] [Module R M] :
    ⇑(GlTraceTwist.linearEquiv ι c M) = ofTwist :=
  (rfl)

instance [Semiring R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R (GlTraceTwist ι c M) :=
  Module.Finite.equiv (GlTraceTwist.linearEquiv ι c M).symm

/-- Two vectors of a trace twist with the same underlying vector are equal. -/
theorem ofTwist_injective : Function.Injective (ofTwist : GlTraceTwist ι c M → M) :=
  (GlTraceTwist.equiv ι c M).injective

/-- Reading a vector of `M` into the twist and back returns it. -/
@[simp]
theorem ofTwist_toTwist (m : M) : ofTwist (toTwist ι c m) = m := (rfl)

/-- Reading a vector of the twist into `M` and back returns it. -/
@[simp]
theorem toTwist_ofTwist (m : GlTraceTwist ι c M) : toTwist ι c (ofTwist m) = m := (rfl)

/-- The addition of a trace twist is the addition of the module it twists. -/
@[simp]
theorem ofTwist_add [AddCommGroup M] (m p : GlTraceTwist ι c M) :
    ofTwist (m + p) = ofTwist m + ofTwist p :=
  (rfl)

/-- The zero of a trace twist is the zero of the module it twists. -/
@[simp]
theorem ofTwist_zero [AddCommGroup M] : ofTwist (0 : GlTraceTwist ι c M) = 0 := (rfl)

/-- The scalar action on a trace twist is the scalar action on the module it twists. -/
@[simp]
theorem ofTwist_smul [Semiring R] [AddCommGroup M] [Module R M] (t : R)
    (m : GlTraceTwist ι c M) : ofTwist (t • m) = t • ofTwist m :=
  (rfl)

end Carrier

/-! ### The twisted bracket -/

section Bracket

variable {R : Type u} [CommRing R] {ι : Type*} [DecidableEq ι] [Fintype ι] {c : R}
variable {M : Type v} [AddCommGroup M] [Module R M] [LieRingModule (Matrix ι ι R) M]
  [LieModule R (Matrix ι ι R) M]

instance : LieRingModule (Matrix ι ι R) (GlTraceTwist ι c M) where
  bracket A m := toTwist ι c (⁅A, ofTwist m⁆ + (c * A.trace) • ofTwist m)
  add_lie A B m := ofTwist_injective <| by
    simp only [ofTwist_add, add_lie, Matrix.trace_add, mul_add, add_smul]
    abel
  lie_add A m p := ofTwist_injective <| by
    simp only [ofTwist_add, lie_add, smul_add]
    abel
  leibniz_lie A B m := ofTwist_injective <| by
    simp only [ofTwist_add, lie_add, lie_smul, smul_add, smul_smul,
      LieAlgebra.matrix_trace_commutator_zero, mul_zero, zero_smul, add_zero,
      leibniz_lie A B (ofTwist m)]
    rw [mul_comm (c * B.trace) (c * A.trace)]
    abel

/-- **The defining equation of the twisted bracket**: it adds the scalar `c · tr(A)` to the
untwisted action of `A`. -/
@[simp]
theorem ofTwist_lie (A : Matrix ι ι R) (m : GlTraceTwist ι c M) :
    ofTwist ⁅A, m⁆ = ⁅A, ofTwist m⁆ + (c * A.trace) • ofTwist m :=
  (rfl)

instance : LieModule R (Matrix ι ι R) (GlTraceTwist ι c M) where
  smul_lie t A m := ofTwist_injective <| by
    simp [Matrix.trace_smul, smul_add, smul_smul, mul_left_comm]
  lie_smul t A m := ofTwist_injective <| by
    simp [smul_comm (c * A.trace) t]

end Bracket

end GlTraceTwist

/-! ### Twisting a highest weight vector -/

section HighestWeight

variable {R : Type u} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {c : R}
variable {M : Type v} [AddCommGroup M] [Module R M] [LieRingModule (Matrix ι ι R) M]
  [LieModule R (Matrix ι ι R) M] {mu : ι → R} {v : M}

/-- **Twisting shifts a highest weight by the twisting scalar, and does nothing else.** The diagonal
matrix unit `Eᵢᵢ` has trace `1` and the raising matrix units have trace `0`, so the twisted bracket
adds `c` to every coordinate of the weight and still annihilates the vector along the raising
directions; conversely a highest weight vector of the twist that comes from `M` has a weight of that
shape, with `c` subtracted back off. This is how a twisted highest weight hypothesis is eliminated,
without unfolding the bracket. -/
theorem isGlHighestWeightVector_toTwist_iff :
    IsGlHighestWeightVector (fun i => mu i + c) (GlTraceTwist.toTwist ι c v) ↔
      IsGlHighestWeightVector mu v := by
  constructor
  · intro hv
    refine isGlHighestWeightVector_iff.mpr ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · exact fun h => hv.ne_zero (GlTraceTwist.ofTwist_injective (by simpa using h))
    · simpa [Matrix.trace_single_eq_same, add_smul] using
        congrArg GlTraceTwist.ofTwist (hv.lie_single_self_eq_smul i)
    · simpa [Matrix.trace_single_eq_of_ne _ _ _ hij.ne] using
        congrArg GlTraceTwist.ofTwist (hv.lie_single_eq_zero hij)
  · intro hv
    refine isGlHighestWeightVector_iff.mpr ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · exact fun h => hv.ne_zero (by simpa using congrArg GlTraceTwist.ofTwist h)
    · exact GlTraceTwist.ofTwist_injective <| by
        simp [hv.lie_single_self_eq_smul, Matrix.trace_single_eq_same, add_smul]
    · exact GlTraceTwist.ofTwist_injective <| by
        simp [hv.lie_single_eq_zero hij, Matrix.trace_single_eq_of_ne _ _ _ hij.ne]

/-- **Twisting shifts a highest weight by the twisting scalar**, the introduction half of
`TauCeti.isGlHighestWeightVector_toTwist_iff`. -/
theorem isGlHighestWeightVector_toTwist (hv : IsGlHighestWeightVector mu v) :
    IsGlHighestWeightVector (fun i => mu i + c) (GlTraceTwist.toTwist ι c v) :=
  isGlHighestWeightVector_toTwist_iff.mpr hv

end HighestWeight

/-! ### Every dominant weight is a highest weight -/

section Dominant

variable {R : Type u} [CommRing R] [CharZero R] {N : ℕ} {mu : Fin N → R}

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

variable (R) in
/-- **The trace twist by `c` of the exterior power realizing a tuple `a` of natural numbers**: the
exterior power in which `TauCeti.exists_isGlHighestWeightVector_natCast` realizes `a`, twisted by
`c`. For an antitone `a` it carries a highest weight vector of the dominant weight
`a + c · (1, …, 1)`, which is `TauCeti.exists_isGlHighestWeightVector_of_isGlDominantIntegral`; for
an unrestricted `a` it is just the twisted exterior power.

As with `TauCeti.VermaModule`, the carrier is a definition with its module structures declared one
by one, so that statements about it are made against this name rather than against the exterior
power it is built from; the roadmap will later cut that construction down to an irreducible
quotient.
`TauCeti.glTraceTwistedYoungWedge.linearEquiv` is the identification of the underlying `R`-modules
and `TauCeti.glTraceTwistedYoungWedge.isGlHighestWeightVector_linearEquiv_symm` populates it. It is
finite over `R`, hence finite-dimensional over a field. -/
-- `@[expose]` is mandated by the compiler for a type synonym carrying instances under the module
-- system ("locally inferred compilation type differs from type that would be inferred in other
-- modules ... may need to be `@[expose]`d"); removing it fails the build. Consumers should still
-- go through `linearEquiv` rather than through the body.
@[expose]
def glTraceTwistedYoungWedge (a : ι → ℕ) (c : R) : Type _ :=
  GlTraceTwist ι c (⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R))

instance (a : ι → ℕ) (c : R) : AddCommGroup (glTraceTwistedYoungWedge R a c) :=
  inferInstanceAs (AddCommGroup
    (GlTraceTwist ι c (⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R))))

instance (a : ι → ℕ) (c : R) : Module R (glTraceTwistedYoungWedge R a c) :=
  inferInstanceAs (Module R
    (GlTraceTwist ι c (⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R))))

noncomputable instance (a : ι → ℕ) (c : R) :
    LieRingModule (Matrix ι ι R) (glTraceTwistedYoungWedge R a c) :=
  inferInstanceAs (LieRingModule (Matrix ι ι R)
    (GlTraceTwist ι c (⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R))))

instance (a : ι → ℕ) (c : R) : LieModule R (Matrix ι ι R) (glTraceTwistedYoungWedge R a c) :=
  inferInstanceAs (LieModule R (Matrix ι ι R)
    (GlTraceTwist ι c (⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R))))

instance (a : ι → ℕ) (c : R) : Module.Finite R (glTraceTwistedYoungWedge R a c) :=
  inferInstanceAs (Module.Finite R
    (GlTraceTwist ι c (⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R))))

namespace glTraceTwistedYoungWedge

variable (R) in
/-- **A trace-twisted Young wedge has the exterior power as its underlying `R`-module.** Every
statement about the carrier is made against this equivalence, so that the definition is not
unfolded. -/
def linearEquiv (a : ι → ℕ) (c : R) :
    glTraceTwistedYoungWedge R a c ≃ₗ[R] ⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R) :=
  GlTraceTwist.linearEquiv ι c _

omit [CharZero R] in
/-- **A highest weight vector of the exterior power gives one of the trace-twisted Young wedge**, of
the weight shifted by `c` in every coordinate. This is the introduction rule for the carrier; the
matching elimination rule is `TauCeti.isGlHighestWeightVector_toTwist_iff`. -/
theorem isGlHighestWeightVector_linearEquiv_symm {a : ι → ℕ} {c : R} {nu : ι → R}
    {w : ⋀[R]^(∑ i, a i) (ι × Fin (∑ i, a i) → R)} (hw : IsGlHighestWeightVector nu w) :
    IsGlHighestWeightVector (fun i => nu i + c) ((linearEquiv R a c).symm w) :=
  isGlHighestWeightVector_toTwist hw

end glTraceTwistedYoungWedge

/-- **Every dominant weight of `gl N` is a highest weight**, in a module finite over `R`: write the
weight as an antitone tuple of natural numbers translated along the central direction
(`TauCeti.IsGlDominantIntegral.exists_antitone_natCast_add_const`), realize the tuple in an exterior
power, and twist by the translation. -/
theorem exists_isGlHighestWeightVector_of_isGlDominantIntegral (hmu : IsGlDominantIntegral mu) :
    ∃ (a : Fin N → ℕ) (c : R), Antitone a ∧ mu = (fun i => (a i : R) + c) ∧
      ∃ v : glTraceTwistedYoungWedge R a c, IsGlHighestWeightVector mu v := by
  obtain ⟨a, c, ha, rfl⟩ := hmu.exists_antitone_natCast_add_const
  obtain ⟨w, hw⟩ := exists_isGlHighestWeightVector_natCast (R := R) (ι := Fin N) ha
  exact ⟨a, c, ha, rfl, _, glTraceTwistedYoungWedge.isGlHighestWeightVector_linearEquiv_symm hw⟩

end Dominant

end TauCeti
