/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.SelfInjective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Trace

/-!
# The zigzag algebra is self-injective

The zigzag algebra of a finite simple graph without isolated vertices is a symmetric Frobenius
algebra: `TauCeti.zigzagTracePairing` is a symmetric associative bilinear form, and it is perfect
because its Gram matrix in the vertex, arrow and volume basis is the permutation matrix of the
involution exchanging an idempotent with a volume class and a dart with its reverse. This file
draws the module-theoretic consequence over a field: the algebra is **self-injective**, its regular
left module being an injective module.

The argument is the general criterion `LinearMap.IsPerfPair.moduleBaer_self`: the trace turns a map
out of a left ideal into a linear functional, which extends to the whole algebra as a vector space
and is then written as pairing against a fixed element, giving the extension Baer's criterion asks
for. Nothing about the graph enters beyond the Frobenius pairing already constructed.

Because the vertex projective `Z e_i` is a retract of the regular module, it inherits injectivity:
over a zigzag algebra the vertex projectives are also the indecomposable injectives. Their
projectivity is `TauCeti.zigzagProjective_projective`, and their indecomposability is
`TauCeti.isIndecomposableModule_zigzagProjective`.

## Main results

* `TauCeti.moduleInjective_nonisolatedZigzagQuotient`: the zigzag algebra of a finite simple graph
  without isolated vertices is self-injective.
* `TauCeti.moduleInjective_zigzagProjective`: each vertex projective `Z e_i` is an injective
  module.

## References

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, and
Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (hns : ∀ i : V, ∃ j, G.Adj i j)

include hns

/-- **The zigzag algebra is self-injective**, in Baer's form: every linear map from a left ideal to
the regular module is right multiplication by an element of the algebra. -/
theorem moduleBaer_nonisolatedZigzagQuotient :
    Module.Baer (nonisolatedZigzagQuotient k G) (nonisolatedZigzagQuotient k G) :=
  (zigzagTracePairing_isPerfPair k G hns).moduleBaer_self (zigzagTracePairing_mul_assoc k G hns)

/-- **The zigzag algebra of a finite simple graph without isolated vertices is self-injective**: its
regular left module is an injective module. This is the module-theoretic content of the symmetric
Frobenius structure carried by the trace pairing. -/
theorem moduleInjective_nonisolatedZigzagQuotient :
    Module.Injective (nonisolatedZigzagQuotient k G) (nonisolatedZigzagQuotient k G) :=
  Module.Baer.injective (moduleBaer_nonisolatedZigzagQuotient k G hns)

/-- **The vertex projectives of a zigzag algebra are injective modules.** The left ideal `Z e_i` is
a retract of the regular module, which is injective. -/
theorem moduleInjective_zigzagProjective (i : V) :
    Module.Injective (nonisolatedZigzagQuotient k G) (zigzagProjective k G i) :=
  Module.Baer.injective
    ((moduleBaer_nonisolatedZigzagQuotient k G hns).of_isIdempotentElem
      (zigzagMk_vertexIdempotent_mul_self k G i) fun _ => mem_zigzagProjective_iff k G)

end TauCeti
