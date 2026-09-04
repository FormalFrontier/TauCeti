/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Localization.Basic

/-!
# Unramifiedness at a prime transports along an isomorphism of algebras

`Algebra.IsUnramifiedAt R q` says that the localization of the ambient algebra at `q` is formally
unramified over `R`. An isomorphism `ψ : A ≃ₐ[R] B` of `R`-algebras matches the prime complement
of `q` with that of `q.comap ψ`, so it induces an isomorphism of the two localizations over `R`
and carries unramifiedness from `q` to `q.comap ψ`.

## Main results

* `AlgEquiv.isUnramifiedAt_of_eq_comap`: if `B` is unramified at `q` over `R`, then `A` is
  unramified at any prime equal to `q.comap ψ`.
-/

public section

namespace AlgEquiv

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Unramifiedness transports along an isomorphism of `R`-algebras.** If `B` is unramified over
`R` at a prime `q`, then `A` is unramified over `R` at the corresponding prime `q.comap ψ`, stated
for any prime `p` of `A` equal to it. -/
theorem isUnramifiedAt_of_eq_comap (ψ : A ≃ₐ[R] B) {q : Ideal B} [q.IsPrime]
    {p : Ideal A} [p.IsPrime] (hp : p = q.comap ψ) [Algebra.IsUnramifiedAt R q] :
    Algebra.IsUnramifiedAt R p := by
  -- The transported prime is the parameter `p` with the equation `hp`, not the term `q.comap ψ`
  -- itself: `Algebra.IsUnramifiedAt` takes the primality of its ideal as an instance argument, so
  -- `rw` cannot turn a conclusion about `q.comap ψ` into one about `p`, while `subst` can.
  subst hp
  exact Algebra.FormallyUnramified.of_equiv (IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime (q.comap ψ)) (Localization.AtPrime q) ψ
      (Ideal.map_primeCompl_comap_of_surjective ψ ψ.surjective q)).symm

end AlgEquiv
