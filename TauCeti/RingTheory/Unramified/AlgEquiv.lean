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

* `Algebra.isUnramifiedAt_of_eq_comap_algEquiv`: if `B` is unramified at `q` over `R`, then `A` is
  unramified at any prime equal to `q.comap ψ`.
-/

public section

namespace Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Unramifiedness transports along an isomorphism of `R`-algebras.** If `B` is unramified over
`R` at a prime `q`, then `A` is unramified over `R` at the corresponding prime `q.comap ψ`.

The transported prime is a parameter `p` carrying the equation `p = q.comap ψ`, rather than the
term `q.comap ψ` itself: `IsUnramifiedAt` takes the primality of its ideal as an instance
argument, so `rw` cannot turn a conclusion about `q.comap ψ` into one about `p`. -/
theorem isUnramifiedAt_of_eq_comap_algEquiv (ψ : A ≃ₐ[R] B) {q : Ideal B} [q.IsPrime]
    {p : Ideal A} [p.IsPrime] (hp : p = q.comap ψ) [IsUnramifiedAt R q] :
    IsUnramifiedAt R p := by
  subst hp
  have H : Submonoid.map (ψ.symm : B ≃ₐ[R] A) q.primeCompl = (q.comap ψ).primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact fun hx ↦ hy (by rwa [SetLike.mem_coe, Ideal.mem_comap, ψ.apply_symm_apply] at hx)
    · exact fun hx ↦ ⟨ψ x, hx, ψ.symm_apply_apply x⟩
  exact FormallyUnramified.of_equiv (IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime q) (Localization.AtPrime (q.comap ψ)) ψ.symm H)

end Algebra
