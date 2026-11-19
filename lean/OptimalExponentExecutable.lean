import OptimalExponentPresentation
import ExecutablePolynomial
import RankFourExponent
import RankNineExponent
import Mathlib.Data.Nat.Find

/-!
# An executable answer to FC's optimal exponent question

The search interleaves linear-combination proofs and finite-ring countermodels.
The existence of one of these certificates supplies termination for the search.
-/

open HopfStructureConstants
open scoped BigOperators

namespace FiniteLocallyFreeGroupSchemeExponent

private instance {ι : Type*} [Encodable ι] : Encodable (Variable ι) :=
  Encodable.ofEquiv _ (proxy_equiv% (Variable ι)).symm

private instance {ι : Type*} [Encodable ι] : Encodable (Relation ι) :=
  Encodable.ofEquiv _ (proxy_equiv% (Relation ι)).symm

private instance {k : ℕ} : Encodable (FiniteRingLabel k) :=
  Encodable.ofEquiv (Fin k) (FiniteRingLabel.equivFin k)

private instance {k : ℕ} : Encodable (FiniteRingTable k) :=
  Encodable.ofEquiv
    (FiniteRingLabel k × FiniteRingLabel k ×
      (FiniteRingLabel k → FiniteRingLabel k → FiniteRingLabel k) ×
      (FiniteRingLabel k → FiniteRingLabel k → FiniteRingLabel k) ×
      (FiniteRingLabel k → FiniteRingLabel k))
    { toFun := fun t => ⟨t.zero, t.one, t.add, t.mul, t.neg⟩
      invFun := fun ⟨z, o, a, m, g⟩ => ⟨z, o, a, m, g⟩
      left_inv := fun ⟨_, _, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _⟩ => rfl }

private abbrev CoefficientRing (n : ℕ) := ExecutablePolynomial (Variable (Fin n))

private def executableTables (n : ℕ) : Tables (CoefficientRing n) (Fin n) :=
  fromAssignment ExecutablePolynomial.X

private def executableRelation {n : ℕ} (r : Relation (Fin n)) : CoefficientRing n :=
  equation (executableTables n) r

private def executableDefect {n : ℕ} (m : ℕ) (i j : Fin n) : CoefficientRing n :=
  powerTable (executableTables n) m i j - convolutionUnit (executableTables n) i j

private theorem eval_comp_toPolynomial {σ : Type*} [DecidableEq σ] :
    ExecutablePolynomial.toPolynomial.comp
      (MvPolynomial.eval₂Hom (Int.castRingHom (ExecutablePolynomial σ)) ExecutablePolynomial.X) =
        RingHom.id (MvPolynomial σ ℤ) := by
  ext x <;> simp

@[simp] private theorem toPolynomial_relation {n : ℕ} (r : Relation (Fin n)) :
    ExecutablePolynomial.toPolynomial (executableRelation r) = relationPolynomial r := by
  rw [executableRelation, executableTables, ← eval_relationPolynomial]
  exact DFunLike.congr_fun eval_comp_toPolynomial (relationPolynomial r)

@[simp] private theorem toPolynomial_defect {n : ℕ} (m : ℕ) (i j : Fin n) :
    ExecutablePolynomial.toPolynomial (executableDefect m i j) = powerDefect m i j := by
  rw [executableDefect, executableTables, ← eval_powerDefect]
  exact DFunLike.congr_fun eval_comp_toPolynomial (powerDefect m i j)

private abbrev Multipliers (n : ℕ) :=
  Fin n → Fin n → Relation (Fin n) → CoefficientRing n

private def checkMultipliers (n m : ℕ) (cs : Multipliers n) : Bool :=
  decide (∀ i j, ExecutablePolynomial.isZero
    ((∑ r, cs i j r * executableRelation r) - executableDefect m i j) = true)

private def positiveAt (n m code : ℕ) : Bool :=
  match Encodable.decode (α := Multipliers n) code with
  | some cs => checkMultipliers n m cs
  | none => false

private theorem exists_positiveAt_iff (n : ℕ+) (m : ℕ) :
    (∃ code, positiveAt n m code = true) ↔ polynomialExponentTest n m := by
  classical
  have check (cs : Multipliers n) :
      checkMultipliers n m cs = true ↔ ∀ i j,
      (∑ r, ExecutablePolynomial.toPolynomial (cs i j r) * relationPolynomial r) =
        powerDefect m i j := by
    simp [checkMultipliers, map_sub, sub_eq_zero, map_sum, map_mul]
  constructor
  · rintro ⟨code, h⟩
    cases hcode : Encodable.decode (α := Multipliers n) code with
    | none => simp [positiveAt, hcode] at h
    | some cs =>
        have hc := (check cs).mp (by simpa [positiveAt, hcode] using h)
        intro i j
        exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨_, hc i j⟩
  · intro h
    have hc (i j : Fin (n : ℕ)) := Ideal.mem_span_range_iff_exists_fun.mp (h i j)
    let cs : Multipliers n := fun i j r => ⟨(hc i j).choose r⟩
    exact ⟨Encodable.encode cs, by
      rw [positiveAt, Encodable.encodek]
      exact (check cs).mpr fun i j => (hc i j).choose_spec⟩

private abbrev Countermodel (n : ℕ) :=
  Σ k, FiniteRingTable k × (Variable (Fin n) → FiniteRingLabel k) × Fin n × Fin n

private def negativeAt (n m code : ℕ) : Bool :=
  match Encodable.decode (α := Countermodel n) code with
  | some ⟨_, t, a, i, j⟩ => checkFiniteCounterexample (m := m) t a i j
  | none => false

private theorem exists_negativeAt_iff (n m : ℕ+) :
    (∃ code, negativeAt n m code = true) ↔ ¬ IsUniversalKillingExponent.{0, 0} n m := by
  rw [not_isUniversalKillingExponent_iff_finite_table]
  simp only [hasFiniteCounterexample, decide_eq_true_eq]
  constructor
  · rintro ⟨code, h⟩
    cases hcode : Encodable.decode (α := Countermodel n) code with
    | none => simp [negativeAt, hcode] at h
    | some c =>
        rcases c with ⟨k, t, a, i, j⟩
        exact ⟨k, t, a, i, j, by simpa [negativeAt, hcode] using h⟩
  · rintro ⟨k, t, a, i, j, h⟩
    refine ⟨Encodable.encode (⟨k, t, a, i, j⟩ : Countermodel n), ?_⟩
    simpa [negativeAt, Encodable.encodek] using h

private theorem exists_certificate (n m : ℕ+) :
    ∃ code, positiveAt n m code = true ∨ negativeAt n m code = true := by
  classical
  by_cases h : IsUniversalKillingExponent.{0, 0} n m
  · obtain ⟨code, hc⟩ := (exists_positiveAt_iff n m).mpr
      ((isUniversalKillingExponent_iff_polynomial n m).mp h)
    exact ⟨code, Or.inl hc⟩
  · obtain ⟨code, hc⟩ := (exists_negativeAt_iff n m).mpr h
    exact ⟨code, Or.inr hc⟩

/-- Search for the first certificate; both checks are decidable and one must succeed. -/
def universalExponentTest (n m : ℕ+) : Bool :=
  if (m : ℕ) = factorialBound n then true
  else if (m : ℕ) % (n : ℕ) ≠ 0 then false
  else positiveAt n m (Nat.find (exists_certificate n m))

theorem universalExponentTest_eq_true (n m : ℕ+) :
    universalExponentTest n m = true ↔ IsUniversalKillingExponent.{0, 0} n m := by
  unfold universalExponentTest
  split
  · rename_i h
    constructor
    · intro _ R _ A _ _ _ _ rank
      rw [h]
      exact isKilledBy_factorialBound n rank
    · intro _
      rfl
  split
  · rename_i hn
    constructor
    · intro hf
      contradiction
    · intro hm
      exact (hn (Nat.dvd_iff_mod_eq_zero.mp (rank_dvd_universalExponent n m hm))).elim
  constructor
  · intro h
    exact (isUniversalKillingExponent_iff_polynomial n m).mpr
      ((exists_positiveAt_iff n m).mp ⟨_, h⟩)
  · intro h
    rcases Nat.find_spec (exists_certificate n m) with hp | hn
    · exact hp
    · exact False.elim (((exists_negativeAt_iff n m).mp ⟨_, hn⟩) h)

private def checkPositiveExponent (n : ℕ+) (m : ℕ) : Bool :=
  if hm : 0 < m then universalExponentTest n ⟨m, hm⟩ else false

/-- The least universal exponent. Use the proved values in ranks four and nine,
and the terminating certificate search in the other ranks. -/
def answerExecutable (n : ℕ+) : ℕ :=
  if n = 4 then 8
  else if n = 9 then 27
  else boundedExponentSearch n (checkPositiveExponent n)

/-- The executable answer satisfies the statement of FC's `optimal_exponent`. -/
theorem optimal_exponent_executable (n : ℕ+) :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} n m} : Set ℕ) =
      answerExecutable n := by
  unfold answerExecutable
  split
  · rename_i h
    subst n
    exact rank_four_optimal_exponent
  split
  · rename_i h
    subst n
    exact rank_nine_optimal_exponent
  apply boundedExponentSearch_spec n
  intro m _
  have hm : (⟨(m : ℕ), m.pos⟩ : ℕ+) = m := Subtype.ext rfl
  rw [checkPositiveExponent, dif_pos m.pos, hm, universalExponentTest_eq_true]

#guard answerExecutable 1 == 1
#guard answerExecutable 4 == 8
#guard answerExecutable 9 == 27

end FiniteLocallyFreeGroupSchemeExponent

#print axioms FiniteLocallyFreeGroupSchemeExponent.universalExponentTest_eq_true
#print axioms FiniteLocallyFreeGroupSchemeExponent.optimal_exponent_executable
