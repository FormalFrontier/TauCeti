/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Unramifiedness descends along a tower of number fields

For a tower `L / M / K` of number fields and a prime `𝔭` of `𝓞 K`, unramifiedness over `K` of
every prime of `𝓞 L` above `𝔭` implies unramifiedness over `K` of every prime of `𝓞 M` above
`𝔭`. Every prime `P` of `𝓞 M` above `𝔭` carries a prime of `𝓞 L` above it, and Mathlib's
`Algebra.IsUnramifiedAt.of_liesOver` transfers unramifiedness downwards along that prime.

The hypothesis and conclusion are stated as the quantified `Algebra.IsUnramifiedAt` condition
rather than through `Algebra.IsUnramifiedIn`, which is the form the Artin symbol takes as its
defining side condition.

The same descent, read simultaneously at every prime outside a finite set of finite places of
`K`, is `NumberField.isUnramifiedAway_of_intermediateField`; that is the form a construction
defined away from a finite set of primes consumes, since it turns one hypothesis about the top
field into the corresponding hypothesis about every subextension.

## Main results

* `NumberField.isUnramifiedAt_of_intermediateExtension`: unramifiedness above `𝔭` in the top
  field descends to the intermediate field.
* `NumberField.isUnramifiedAway_of_intermediateField`: unramifiedness outside a finite set of
  finite places descends to an intermediate field.
-/

public section

open IsDedekindDomain

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Unramifiedness descends to an intermediate extension.** If every prime of `L` over `𝔭` is
unramified over `K`, then every prime of an intermediate field `M` over `𝔭` is unramified over
`K` as well. -/
theorem isUnramifiedAt_of_intermediateExtension {M L : Type*} [Field M] [NumberField M]
    [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (𝔭 : Ideal (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∀ (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) P := by
  intro P _ _
  let Q : P.primesOver (𝓞 L) := Classical.choice inferInstance
  let _ : Q.1.IsPrime := Q.2.1
  let _ : Q.1.LiesOver P := Q.2.2
  let _ : Q.1.LiesOver 𝔭 := Ideal.LiesOver.trans Q.1 P 𝔭
  let _ : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hur Q.1
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) P Q.1

/-- **Unramifiedness outside a finite set of finite places descends to an intermediate field.**
If every prime of `L` above a place of `K` outside `S` is unramified over `K`, then so is every
prime of an intermediate field `M` above such a place. This is what makes the unramified
hypothesis for a subextension a consequence of the one for the top field rather than a second
assumption. -/
theorem isUnramifiedAway_of_intermediateField {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (M : IntermediateField K L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q :=
  fun v hv ↦ isUnramifiedAt_of_intermediateExtension (M := M) (L := L) v.asIdeal (hur v hv)

end NumberField
