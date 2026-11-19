import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Derivative

/-! Newton's recurrence for the reverse characteristic polynomial over any commutative ring. -/

open scoped BigOperators Polynomial
open Polynomial

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

private theorem derivative_det_cols (B : Matrix ι ι R[X]) :
    derivative B.det = ∑ i, (B.updateCol i (fun j => derivative (B j i))).det := by
  simp only [Matrix.det_apply, map_sum, Units.smul_def, map_zsmul, derivative_prod_finset,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun σ _ => ?_))
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j => B.updateCol i (fun k => derivative (B k i)) (σ j) j) (Finset.mem_univ i)]
  rw [Matrix.updateCol_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj =>
    (Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)).symm

private theorem derivative_det_trace (B : Matrix ι ι R[X]) :
    derivative B.det = (B.adjugate * B.map derivative).trace := by
  rw [derivative_det_cols, Matrix.trace]
  simp only [Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

private def matrixCoeff (B : Matrix ι ι R[X]) (k : ℕ) : Matrix ι ι R :=
  B.map (fun p => p.coeff k)

private theorem matrixCoeff_mul_const (B : Matrix ι ι R[X]) (M : Matrix ι ι R) (k : ℕ) :
    matrixCoeff (B * M.map C) k = matrixCoeff B k * M := by
  ext i j
  simp [matrixCoeff, Matrix.mul_apply, finsetSum_coeff, coeff_mul_C]

private theorem matrixCoeff_X_smul (B : Matrix ι ι R[X]) (k : ℕ) :
    matrixCoeff ((X : R[X]) • B) (k + 1) = matrixCoeff B k := by
  ext i j
  simp [matrixCoeff, Matrix.smul_apply, smul_eq_mul, coeff_X_mul]

private theorem matrixCoeff_scalar (p : R[X]) (k : ℕ) :
    matrixCoeff (p • (1 : Matrix ι ι R[X])) k = p.coeff k • (1 : Matrix ι ι R) := by
  ext i j
  by_cases h : i = j <;> simp [matrixCoeff, Matrix.smul_apply, Matrix.one_apply, h]

private theorem matrixCoeff_sub (B D : Matrix ι ι R[X]) (k : ℕ) :
    matrixCoeff (B - D) k = matrixCoeff B k - matrixCoeff D k := by
  ext i j
  simp [matrixCoeff]

private theorem coeff_trace (B : Matrix ι ι R[X]) (k : ℕ) :
    B.trace.coeff k = (matrixCoeff B k).trace := by
  simp [matrixCoeff, Matrix.trace, finsetSum_coeff]

/-- If `C(z) = det(1 - z M)`, the coefficient of its derivative is the
corresponding coefficient of `-C(z) ∑ᵢ trace(M^(i+1)) zⁱ`. -/
theorem charpolyRev_newton (M : Matrix ι ι R) (k : ℕ) :
    ((k + 1 : ℕ) : R) * M.charpolyRev.coeff (k + 1) =
      -∑ i ∈ Finset.range (k + 1), M.charpolyRev.coeff (k - i) * (M ^ (i + 1)).trace := by
  let B : Matrix ι ι R[X] := 1 - (X : R[X]) • M.map C
  let C₀ := M.charpolyRev
  have Bdet : B.det = C₀ := rfl
  have derivB : B.map derivative = -(M.map C) := by
    ext i j
    by_cases h : i = j <;>
      simp [B, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, h]
  have adjZero : matrixCoeff B.adjugate 0 = (1 : Matrix ι ι R) := by
    have hB : B.map (Polynomial.eval 0) = (1 : Matrix ι ι R) := by
      ext i j
      by_cases h : i = j <;> simp [B, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, h]
    change B.adjugate.map (fun p => p.coeff 0) = _
    simp only [coeff_zero_eq_eval_zero]
    change (Polynomial.evalRingHom (0 : R)).mapMatrix B.adjugate = _
    rw [RingHom.map_adjugate]
    simpa [RingHom.mapMatrix_apply, hB]
  have CZero : C₀.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]
    exact Matrix.eval_charpolyRev
  have adjSucc (j : ℕ) :
      matrixCoeff B.adjugate (j + 1) =
        C₀.coeff (j + 1) • (1 : Matrix ι ι R) + matrixCoeff B.adjugate j * M := by
    have e := congrArg (fun N => matrixCoeff N (j + 1)) (Matrix.adjugate_mul B)
    change matrixCoeff (B.adjugate * (1 - (X : R[X]) • M.map C)) (j + 1) =
      matrixCoeff (B.det • (1 : Matrix ι ι R[X])) (j + 1) at e
    rw [mul_sub, mul_one, Matrix.mul_smul, matrixCoeff_sub, matrixCoeff_X_smul,
      matrixCoeff_mul_const, matrixCoeff_scalar, Bdet, sub_eq_iff_eq_add] at e
    exact e
  have adjFormula (j : ℕ) :
      matrixCoeff B.adjugate j =
        ∑ i ∈ Finset.range (j + 1), C₀.coeff (j - i) • M ^ i := by
    induction j with
    | zero => simp [adjZero, CZero]
    | succ j ih =>
      rw [adjSucc, ih, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [pow_zero, tsub_zero, add_comm _ (C₀.coeff _ • (1 : Matrix ι ι R))]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.smul_mul, ← pow_succ, Nat.succ_sub_succ_eq_sub]
  have h := congrArg (fun p : R[X] => p.coeff k) (derivative_det_trace B)
  rw [derivB, mul_neg, Matrix.trace_neg, coeff_neg, coeff_trace, matrixCoeff_mul_const,
    adjFormula, Finset.sum_mul, Matrix.trace_sum, coeff_derivative, Bdet, mul_comm] at h
  simp_rw [Matrix.smul_mul, ← pow_succ, Matrix.trace_smul, smul_eq_mul] at h
  simpa [C₀] using h

end Matrix
