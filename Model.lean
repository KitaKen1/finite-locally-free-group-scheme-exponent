/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

@[expose] public section

namespace FiniteLocallyFreeGroupSchemeExponent

open WithConv MonoidAlgebra
universe u v

/-- The group scheme `Spec A` of a commutative Hopf algebra `A` over `R` is killed by `m` when
the `m`-th convolution power of `AlgHom.id R A` is the convolution unit.

The convolution power of `AlgHom.id R A` is the coordinate map of the pointwise power map
`x ↦ x ^ m`, and `1` is the constant map at the identity section. -/
def IsKilledBy (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A]
    (m : ℕ) : Prop :=
  toConv (AlgHom.id R A) ^ m = 1

/-- A positive integer `m` is a universal killing exponent in rank `n` if every finite locally
free group scheme of rank `n`, over every commutative ring, is killed by `m`.

The hypotheses that `A` is finite and projective over `R`, with constant `rankAtStalk` equal to
`n`, express that the group scheme is finite locally free of rank `n`. -/
def IsUniversalKillingExponent (n m : ℕ+) : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Projective R A],
    Module.rankAtStalk (R := R) A = (fun _ ↦ (n : ℕ)) → IsKilledBy R A m

/-- On a group algebra the `m`-th convolution power of the identity is the pointwise `m`-th power:
it sends the group-like element `single g 1` to `single (g ^ m) 1`. -/
theorem pow_apply_single (R : Type u) [CommRing R] (G : Type v) [CommGroup G] (m : ℕ) (g : G) :
    (toConv (AlgHom.id R (MonoidAlgebra R G)) ^ m).ofConv (single g 1) = single (g ^ m) 1 := by
  induction m with
  | zero =>
    simp [AlgHom.convOne_def, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one,
      MonoidAlgebra.one_def]
  | succ k ih =>
    rw [pow_succ, AlgHom.convMul_apply, MonoidAlgebra.comul_single]
    simp [Coalgebra.comul, ih, single_mul_single, pow_succ]

/-- The group scheme `μₙ = Spec R[ℤ/n]` has rank `n`. -/
theorem rankAtStalk_monoidAlgebra (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ) [NeZero n] :
    Module.rankAtStalk (R := R) (MonoidAlgebra R (Multiplicative (ZMod n))) = fun _ ↦ n := by
  ext p
  rw [Module.rankAtStalk_eq_finrank_of_free,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis (Multiplicative (ZMod n)) R)]
  simp

/-- The hypotheses of `IsUniversalKillingExponent` are satisfiable in every rank `n`: they apply
to `μₙ = Spec R[ℤ/n]` over any nontrivial ring. -/
theorem isKilledBy_of_isUniversalKillingExponent (n m : ℕ+)
    (h : IsUniversalKillingExponent.{u, u} n m) (R : Type u) [CommRing R] [Nontrivial R] :
    IsKilledBy R (MonoidAlgebra R (Multiplicative (ZMod (n : ℕ)))) (m : ℕ) :=
  haveI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  h R _ (rankAtStalk_monoidAlgebra R n)

end FiniteLocallyFreeGroupSchemeExponent
