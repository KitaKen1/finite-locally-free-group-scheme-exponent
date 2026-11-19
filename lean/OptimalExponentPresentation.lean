import OptimalExponent
import HopfStructureConstants
import IntegerIdealSeparation
import FiniteRingCertificate

/-!
# The universal exponent as an integer polynomial ideal-membership test

This file connects the structure-constant equations to the original Formal
Conjectures statement. Both directions use actual Hopf algebras and the
convolution power in the FC definition.
-/

open HopfStructureConstants

namespace FiniteLocallyFreeGroupSchemeExponent

noncomputable section

def hopfRelationIdeal (n : ℕ+) : Ideal (MvPolynomial (Variable (Fin (n : ℕ))) ℤ) :=
  Ideal.span (Set.range relationPolynomial)

/-- Every coefficient of the power-map defect belongs to the integer relation ideal. -/
def polynomialExponentTest (n : ℕ+) (m : ℕ) : Prop :=
  ∀ i j : Fin (n : ℕ), powerDefect m i j ∈ hopfRelationIdeal n

theorem isUniversalKillingExponent_iff_polynomial (n m : ℕ+) :
    IsUniversalKillingExponent.{0, 0} n m ↔ polynomialExponentTest n m := by
  constructor
  · intro universal i j
    apply (mem_relationIdeal_iff_forall_eval relationPolynomial (powerDefect (m : ℕ) i j)).mpr
    intro K _ assignment eqs
    let t := fromAssignment assignment
    have ht : HopfLaws t := (hopfLaws_iff_equations t).mpr fun r => by
      have hr := eqs r
      change MvPolynomial.eval₂Hom (Int.castRingHom K) assignment (relationPolynomial r) = 0 at hr
      rwa [eval_relationPolynomial] at hr
    rcases subsingleton_or_nontrivial K with hK | hK
    · exact @Subsingleton.elim K hK _ _
    · let : Nontrivial K := hK
      obtain ⟨A, _, _, b, agree⟩ := exists_hopf_realization t ht
      have hu := (isUniversalKillingExponent_iff_basis n m).mp universal K A b
      have hz := (power_eq_unit_iff agree m).mp hu i
      change MvPolynomial.eval₂Hom (Int.castRingHom K) assignment (powerDefect (m : ℕ) i j) = 0
      rw [eval_powerDefect, sub_eq_zero]
      exact congrFun hz j
  · intro check
    apply (isUniversalKillingExponent_iff_basis n m).mpr
    intro K _ _ A _ _ b
    let t := tablesOf b
    let a := assignmentOf t
    have eqs (r : Relation (Fin (n : ℕ))) :
        MvPolynomial.eval₂ (Int.castRingHom K) a (relationPolynomial r) = 0 := by
      change MvPolynomial.eval₂Hom (Int.castRingHom K) a (relationPolynomial r) = 0
      rw [eval_relationPolynomial, fromAssignment_assignmentOf]
      exact (hopfLaws_iff_equations t).mp (tablesOf_laws b) r
    apply (power_eq_unit_iff (show tablesOf b = t from rfl) m).mpr
    intro i
    funext j
    have hm := (mem_relationIdeal_iff_forall_eval relationPolynomial (powerDefect (m : ℕ) i j)).mp
      (check i j) K a eqs
    change MvPolynomial.eval₂Hom (Int.castRingHom K) a (powerDefect (m : ℕ) i j) = 0 at hm
    rwa [eval_powerDefect, fromAssignment_assignmentOf, sub_eq_zero] at hm

/-- The exact bounded formula expressed entirely in terms of the integer polynomial system. -/
noncomputable def answerByPolynomialIdeal (n : ℕ+) : ℕ := by
  classical
  exact boundedExponentSearch n (fun m => decide (polynomialExponentTest n m))

/-- The FC answer in terms of integer polynomial ideal membership. This equality does not
assume a correctness theorem for an external Gröbner basis implementation. -/
theorem optimal_exponent_by_polynomial_ideal (n : ℕ+) :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} n m} : Set ℕ) =
      answerByPolynomialIdeal n := by
  classical
  unfold answerByPolynomialIdeal
  apply boundedExponentSearch_spec n
  intro m _
  simp only [decide_eq_true_eq, isUniversalKillingExponent_iff_polynomial]

end

/-- Verify that an operation table and an assignment give a specific nonzero defect. -/
def checkFiniteCounterexample {n m k : ℕ} (t : FiniteRingTable k)
    (a : Variable (Fin n) → FiniteRingLabel k) (i j : Fin n) : Bool :=
  if h : t.Valid then
    letI := t.commRing h
    let T := fromAssignment a
    decide ((∀ r, equation T r = 0) ∧
      powerTable T m i j - convolutionUnit T i j ≠ 0)
  else false

private theorem checkFiniteCounterexample_eq_true {n m k : ℕ} (t : FiniteRingTable k)
    (a : Variable (Fin n) → FiniteRingLabel k) (i j : Fin n) :
    checkFiniteCounterexample (m := m) t a i j = true ↔
      ∃ h : t.Valid, letI := t.commRing h
        (∀ r, MvPolynomial.eval₂Hom (Int.castRingHom (FiniteRingLabel k)) a (relationPolynomial r) = 0) ∧
        MvPolynomial.eval₂Hom (Int.castRingHom (FiniteRingLabel k)) a (powerDefect m i j) ≠ 0 := by
  by_cases h : t.Valid <;> simp [checkFiniteCounterexample, h]

/-- Search the finite ring tables of cardinality `k` for a counterexample. -/
def hasFiniteCounterexample (n m k : ℕ) : Bool :=
  decide (∃ (t : FiniteRingTable k) (a : Variable (Fin n) → FiniteRingLabel k) (i j : Fin n),
    checkFiniteCounterexample (m := m) t a i j = true)

/-- A candidate fails exactly when some finite operation table witnesses failure. -/
theorem not_isUniversalKillingExponent_iff_finite_table (n m : ℕ+) :
    ¬ IsUniversalKillingExponent.{0, 0} n m ↔ ∃ k, hasFiniteCounterexample n m k = true := by
  classical
  rw [isUniversalKillingExponent_iff_polynomial]
  simp only [polynomialExponentTest, not_forall, hasFiniteCounterexample, decide_eq_true_eq]
  constructor
  · rintro ⟨i, j, h⟩
    obtain ⟨D, _, hD, a, eqs, hx⟩ :=
      (IntegerIdealSeparation.not_mem_iff_finite_assignment relationPolynomial
        (powerDefect (m : ℕ) i j)).mp h
    letI := Fintype.ofFinite D
    let k := Fintype.card D
    let e : D ≃ FiniteRingLabel k := (Fintype.equivFin D).trans (FiniteRingLabel.equivFin k).symm
    let t := FiniteRingTable.ofEquiv e
    let hT := FiniteRingTable.valid_ofEquiv e
    letI := t.commRing hT
    let f : D →+* FiniteRingLabel k := (FiniteRingTable.relabel e).toRingHom
    have transport (p : MvPolynomial (Variable (Fin (n : ℕ))) ℤ) :
        MvPolynomial.eval₂Hom (Int.castRingHom (FiniteRingLabel k)) (f ∘ a) p =
          f (MvPolynomial.eval₂Hom (Int.castRingHom D) a p) := by
      change _ = (f.comp (MvPolynomial.eval₂Hom (Int.castRingHom D) a)) p
      congr 1
      ext x <;> simp
    refine ⟨k, t, f ∘ a, i, j, (checkFiniteCounterexample_eq_true t _ i j).mpr
      ⟨hT, ?_, ?_⟩⟩
    · intro r
      rw [transport, eqs, map_zero]
    · rw [transport, ← map_zero f]
      exact fun hz => hx ((FiniteRingTable.relabel e).injective hz)
  · rintro ⟨k, t, a, i, j, h⟩
    obtain ⟨hT, h⟩ := (checkFiniteCounterexample_eq_true t a i j).mp h
    exact ⟨i, j, (IntegerIdealSeparation.not_mem_iff_finite_assignment relationPolynomial
      (powerDefect (m : ℕ) i j)).mpr ⟨FiniteRingLabel k, t.commRing hT, inferInstance, a, h⟩⟩

end FiniteLocallyFreeGroupSchemeExponent

#print axioms FiniteLocallyFreeGroupSchemeExponent.isUniversalKillingExponent_iff_polynomial
#print axioms FiniteLocallyFreeGroupSchemeExponent.optimal_exponent_by_polynomial_ideal
#print axioms FiniteLocallyFreeGroupSchemeExponent.not_isUniversalKillingExponent_iff_finite_table
