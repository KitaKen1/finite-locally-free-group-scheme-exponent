import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! Ring operations on a finite set, with an exhaustive check of the ring axioms. -/

/-- Ring labels with operations specified by the certificate. -/
structure FiniteRingLabel (k : ℕ) where
  index : Fin k
  deriving DecidableEq

namespace FiniteRingLabel

def equivFin (k : ℕ) : FiniteRingLabel k ≃ Fin k where
  toFun := FiniteRingLabel.index
  invFun := FiniteRingLabel.mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance (k : ℕ) : Fintype (FiniteRingLabel k) := Fintype.ofEquiv (Fin k) (equivFin k).symm

end FiniteRingLabel

/-- The operations of a ring with `k` labelled elements. -/
structure FiniteRingTable (k : ℕ) where
  zero : FiniteRingLabel k
  one : FiniteRingLabel k
  add : FiniteRingLabel k → FiniteRingLabel k → FiniteRingLabel k
  mul : FiniteRingLabel k → FiniteRingLabel k → FiniteRingLabel k
  neg : FiniteRingLabel k → FiniteRingLabel k

namespace FiniteRingTable

instance {k : ℕ} : Fintype (FiniteRingTable k) :=
  Fintype.ofEquiv
    (FiniteRingLabel k × FiniteRingLabel k × (FiniteRingLabel k → FiniteRingLabel k → FiniteRingLabel k) × (FiniteRingLabel k → FiniteRingLabel k → FiniteRingLabel k) × (FiniteRingLabel k → FiniteRingLabel k))
    { toFun := fun ⟨z, o, a, m, n⟩ => ⟨z, o, a, m, n⟩
      invFun := fun t => ⟨t.zero, t.one, t.add, t.mul, t.neg⟩
      left_inv := fun ⟨_, _, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _⟩ => rfl }

variable {k : ℕ} (t : FiniteRingTable k)

/-- These identities suffice for a commutative ring, including the zero ring. -/
def Valid : Prop :=
  (∀ a b c, t.add (t.add a b) c = t.add a (t.add b c)) ∧
  (∀ a, t.add t.zero a = a) ∧
  (∀ a, t.add (t.neg a) a = t.zero) ∧
  (∀ a b c, t.mul (t.mul a b) c = t.mul a (t.mul b c)) ∧
  (∀ a b, t.mul a b = t.mul b a) ∧
  (∀ a, t.mul t.one a = a) ∧
  (∀ a b c, t.mul a (t.add b c) = t.add (t.mul a b) (t.mul a c))

instance : Decidable t.Valid := by
  unfold Valid
  infer_instance

/-- Recover the ring structure from its verified operation table. -/
@[instance_reducible] def commRing (h : t.Valid) : CommRing (FiniteRingLabel k) := by
  letI : Zero (FiniteRingLabel k) := ⟨t.zero⟩
  letI : One (FiniteRingLabel k) := ⟨t.one⟩
  letI : Add (FiniteRingLabel k) := ⟨t.add⟩
  letI : Mul (FiniteRingLabel k) := ⟨t.mul⟩
  letI : Neg (FiniteRingLabel k) := ⟨t.neg⟩
  exact CommRing.ofMinimalAxioms h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2

section Relabel

variable {D : Type*} [CommRing D] (e : D ≃ FiniteRingLabel k)

/-- Label the elements of an existing ring. -/
def ofEquiv : FiniteRingTable k where
  zero := e 0
  one := e 1
  add a b := e (e.symm a + e.symm b)
  mul a b := e (e.symm a * e.symm b)
  neg a := e (-e.symm a)

theorem valid_ofEquiv : (ofEquiv e).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intros <;> simp [ofEquiv, add_assoc, mul_assoc, mul_add]
  rw [mul_comm]

/-- Relabelling preserves all ring operations. -/
def relabel : letI := (ofEquiv e).commRing (valid_ofEquiv e); D ≃+* FiniteRingLabel k := by
  letI := (ofEquiv e).commRing (valid_ofEquiv e)
  refine { e with map_add' := ?_, map_mul' := ?_ }
  · intro a b
    change e (a * b) = e (e.symm (e a) * e.symm (e b))
    rw [e.symm_apply_apply, e.symm_apply_apply]
  · intro a b
    change e (a + b) = e (e.symm (e a) + e.symm (e b))
    rw [e.symm_apply_apply, e.symm_apply_apply]

@[simp] theorem relabel_apply (a : D) : relabel e a = e a := rfl

end Relabel
end FiniteRingTable
