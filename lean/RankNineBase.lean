import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-! The rank-nine example's base and a coefficient functional that detects `3 b²`. -/

namespace RankNineExample

open AddMonoidAlgebra

noncomputable section

private abbrev Exponent := ℕ × ℕ × ℕ × ℕ
private abbrev P := AddMonoidAlgebra (ZMod 9) Exponent
private def term (m : Exponent) : P := single m 1

private inductive Relation where
  | ss | st | tt | sa | tb | sb | ta | degree (i : Fin 7)
  deriving DecidableEq

private instance : Fintype Relation := derive_fintype% Relation

private def relation : Relation → P
  | .ss => term (0, 0, 2, 0)
  | .st => term (0, 0, 1, 1)
  | .tt => term (0, 0, 0, 2)
  | .sa => term (3, 0, 1, 0) - single 0 3
  | .tb => term (0, 3, 0, 1) - single 0 3
  | .sb => term (0, 3, 1, 0)
  | .ta => term (3, 0, 0, 1)
  | .degree i => term (i, 6 - i, 0, 0)

private def I : Ideal P := Ideal.span (Set.range relation)

/-- The coefficient ring for the rank-nine example. -/
abbrev Base := P ⧸ I

private def q : P →+* Base := Ideal.Quotient.mk I

def a : Base := q (term (1, 0, 0, 0))
def b : Base := q (term (0, 1, 0, 0))
def s : Base := q (term (0, 0, 1, 0))
def t : Base := q (term (0, 0, 0, 1))

private theorem relation_zero (r : Relation) : q (relation r) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨r, rfl⟩)

private theorem q_constant_three : q (single (0 : Exponent) (3 : ZMod 9)) = 3 := by
  change q ((singleZeroRingHom : ZMod 9 →+* P) 3) = 3
  exact map_ofNat (q.comp singleZeroRingHom) 3

private theorem square_zero :
    s ^ 2 = 0 ∧ s * t = 0 ∧ t ^ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [s, ← map_pow, term, AddMonoidAlgebra.single_pow, one_pow]
    exact relation_zero .ss
  · simp only [s, t, ← map_mul, term, single_mul_single, one_mul]
    exact relation_zero .st
  · simp only [t, ← map_pow, term, AddMonoidAlgebra.single_pow, one_pow]
    exact relation_zero .tt

theorem s_sq : s ^ 2 = 0 := square_zero.1
theorem st_zero : s * t = 0 := square_zero.2.1
theorem t_sq : t ^ 2 = 0 := square_zero.2.2

theorem nine_zero : (9 : Base) = 0 := by
  have h : (9 : ZMod 9) = 0 := by decide
  let f : ZMod 9 →+* Base := q.comp singleZeroRingHom
  rw [← map_ofNat f 9, h, map_zero]

theorem sa_cube : s * a ^ 3 = 3 := by
  have h := relation_zero .sa
  simp only [relation, map_sub, q_constant_three, sub_eq_zero] at h
  simp only [s, a, ← map_pow, ← map_mul, term, AddMonoidAlgebra.single_pow, single_mul_single,
    one_mul, one_pow]
  exact h

theorem tb_cube : t * b ^ 3 = 3 := by
  have h := relation_zero .tb
  simp only [relation, map_sub, q_constant_three, sub_eq_zero] at h
  simp only [t, b, ← map_pow, ← map_mul, term, AddMonoidAlgebra.single_pow, single_mul_single,
    one_mul, one_pow]
  exact h

theorem sb_cube : s * b ^ 3 = 0 := by
  simp only [s, b, ← map_pow, ← map_mul, term, AddMonoidAlgebra.single_pow, single_mul_single,
    one_mul, one_pow]
  exact relation_zero .sb

theorem ta_cube : t * a ^ 3 = 0 := by
  simp only [t, a, ← map_pow, ← map_mul, term, AddMonoidAlgebra.single_pow, single_mul_single,
    one_mul, one_pow]
  exact relation_zero .ta

theorem degree_six (i : Fin 7) : a ^ (i : ℕ) * b ^ (6 - (i : ℕ)) = 0 := by
  unfold a b
  rw [← map_pow, ← map_pow, ← map_mul]
  unfold term
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow, single_mul_single]
  simp only [one_pow, mul_one]
  have h := relation_zero (.degree i)
  fin_cases i <;> exact h

private def weight (m : Exponent) : ZMod 9 :=
  if m = (0, 2, 0, 0) then 1
  else if m = (3, 2, 1, 0) ∨ m = (0, 5, 0, 1) then 3 else 0

private def witness : P →ₗ[ZMod 9] ZMod 9 :=
  (Finsupp.linearCombination _ weight).comp (coeffLinearEquiv _).toLinearMap

@[simp] private theorem witness_single (m : Exponent) (r : ZMod 9) :
    witness (single m r) = r * weight m := by
  change Finsupp.linearCombination _ weight (Finsupp.single m r) = _
  simp [smul_eq_mul]

private theorem witness_term_relation (m : Exponent) (r : Relation) :
    witness (term m * relation r) = 0 := by
  rcases m with ⟨i, j, k, l⟩
  cases r <;>
    simp only [relation, term, mul_sub, single_mul_single, one_mul, add_zero, map_sub,
      witness_single, weight, Prod.mk_add_mk, Prod.mk.injEq] <;>
    split_ifs
  all_goals first | (exfalso; omega) | (simp_all; done) | decide

private theorem witness_mul_relation (p : P) (r : Relation) :
    witness (p * relation r) = 0 := by
  induction p using AddMonoidAlgebra.induction_on with
  | of m => exact witness_term_relation m r
  | add x y hx hy => simp [add_mul, hx, hy]
  | smul c x hx => simp [smul_mul_assoc, hx]

theorem three_b_sq_ne_zero : (3 : Base) * b ^ 2 ≠ 0 := by
  intro hz
  have hm : single ((0, 2, 0, 0) : Exponent) (3 : ZMod 9) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (single _ _) = 0
    rw [show single ((0, 2, 0, 0) : Exponent) (3 : ZMod 9) =
      single (0 : Exponent) (3 : ZMod 9) * term (0, 1, 0, 0) ^ 2 from by
        simp only [term, AddMonoidAlgebra.single_pow, single_mul_single, one_pow, mul_one]
        rfl]
    simpa only [map_mul, q_constant_three, map_pow, b] using hz
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
  have h := congrArg witness hc
  simp [witness_mul_relation, weight] at h
  exact (by decide : (0 : ZMod 9) ≠ 3) h

instance : Nontrivial Base := ⟨⟨3 * b ^ 2, 0, three_b_sq_ne_zero⟩⟩

end
end RankNineExample

#print axioms RankNineExample.three_b_sq_ne_zero
