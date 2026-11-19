import OptimalExponent
import TranslationNewton

/-! Power bounds for the small ranks, using the characteristic polynomial of translation. -/

open WithConv
open scoped BigOperators IsMulCommutative Polynomial

namespace FiniteLocallyFreeGroupSchemeExponent

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]

namespace RankPoint

abbrev Points := WithConv (A →ₐ[R] R)

abbrev CyclicAlgebra (g : Points (R := R) (A := A)) :=
  Algebra.adjoin R (Set.range fun i : ℤ => linearPoint (g ^ i))

instance (g : Points (R := R) (A := A)) : IsMulCommutative (CyclicAlgebra g) := by
  apply Algebra.isMulCommutative_adjoin
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
  change linearPoint (g ^ i) * linearPoint (g ^ j) =
    linearPoint (g ^ j) * linearPoint (g ^ i)
  rw [← map_mul, ← map_mul, ← zpow_add, ← zpow_add, add_comm i j]

def cyclicUnit (g : Points (R := R) (A := A)) : (CyclicAlgebra g)ˣ where
  val := ⟨linearPoint g, Algebra.subset_adjoin ⟨1, congrArg linearPoint (zpow_one g)⟩⟩
  inv := ⟨linearPoint g⁻¹, Algebra.subset_adjoin ⟨-1, congrArg linearPoint (zpow_neg_one g)⟩⟩
  val_inv := Subtype.ext (by change linearPoint g * linearPoint g⁻¹ = 1; rw [← map_mul, mul_inv_cancel, map_one])
  inv_val := Subtype.ext (by change linearPoint g⁻¹ * linearPoint g = 1; rw [← map_mul, inv_mul_cancel, map_one])

def translationMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R A) : Points (R := R) (A := A) →* Matrix ι ι R :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp translation

theorem trace_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R A) (f : Points (R := R) (A := A)) :
    (translationMatrix b f).trace = LinearMap.trace R A (translation f) := by
  rw [LinearMap.trace_eq_matrix_trace R b]
  rfl

theorem moments [Nontrivial R] [Module.Free R A] [Module.Finite R A]
    (g : Points (R := R) (A := A)) {n : ℕ} (rank : Module.finrank R A = n) (k : ℕ) :
    let x := ((cyclicUnit g) : CyclicAlgebra g)
    ∑ j ∈ Finset.range (n + 1),
      algebraMap R (CyclicAlgebra g) ((translation g).charpoly.coeff j) * (x ^ j) ^ k = 0 := by
  intro x
  apply Subtype.ext
  simpa [x, cyclicUnit, Algebra.smul_def] using translation_charpoly_moments g rank k

theorem trace_annihilates [Module.Free R A] [Module.Finite R A]
    (g : Points (R := R) (A := A)) (z : CyclicAlgebra g) (f : Points (R := R) (A := A))
    (hz : z.val = linearPoint f) :
    algebraMap R (CyclicAlgebra g) (LinearMap.trace R A (translation f)) * (z - 1) = 0 := by
  rw [← Algebra.smul_def]
  apply Subtype.ext
  change LinearMap.trace R A (translation f) • (z.val - 1) = 0
  rw [hz]
  apply WithConv.ext
  ext a
  simpa [linearPoint, smul_eq_mul] using translation_trace_annihilates f a

theorem reverse_coeff {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial R]
    (T : Matrix ι ι R) (j : ℕ) (hj : j ≤ Fintype.card ι) :
    T.charpolyRev.coeff j = T.charpoly.coeff (Fintype.card ι - j) := by
  rw [← T.reverse_charpoly, Polynomial.coeff_reverse, T.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le hj]

end RankPoint

open RankPoint

private theorem quartic_power {C : Type*} [CommRing C] (x y a b' c d e t₂ : C)
    (xy : x * y = 1)
    (pOne : 1 - a + c - d * b' + e = 0)
    (px : x ^ 4 - a * x ^ 3 + c * x ^ 2 - d * b' * x + e = 0)
    (py : y ^ 4 - a * y ^ 3 + c * y ^ 2 - d * b' * y + e = 0)
    (fromTrace₁ : a * (x - 1) = 0) (fromTraceInv : b' * (y - 1) = 0)
    (invTrace₁ : b' * (x - 1) = 0) (fromTrace₂ : t₂ * (x ^ 2 - 1) = 0)
    (newton : 2 * c = a ^ 2 - t₂) : x ^ 8 = 1 := by
  have red : x ^ 4 - 1 = -c * (x ^ 2 - 1) := by
    linear_combination px - pOne + (x ^ 2 + x + 1) * fromTrace₁ + d * invTrace₁
  have torsion : 2 * (x ^ 4 - 1) = 0 := by
    linear_combination 2 * red - (x ^ 2 - 1) * newton -
      a * (x + 1) * fromTrace₁ + fromTrace₂
  have redY : y ^ 4 - 1 = -c * (y ^ 2 - 1) := by
    have traceY : a * (y - 1) = 0 := by
      linear_combination -y * fromTrace₁ + a * xy
    linear_combination py - pOne + (y ^ 2 + y + 1) * traceY + d * fromTraceInv
  have xy₂ : x ^ 2 * y ^ 2 = 1 := by rw [← mul_pow, xy, one_pow]
  have xy₄ : x ^ 4 * y ^ 4 = 1 := by rw [← mul_pow, xy, one_pow]
  have reverse : x ^ 4 - 1 = -c * x ^ 2 * (x ^ 2 - 1) := by
    linear_combination -x ^ 4 * redY + xy₄ + c * x ^ 2 * xy₂
  have diff : (x ^ 4 - 1) * (x ^ 2 - 1) = 0 := by
    linear_combination x ^ 2 * red - reverse
  linear_combination (x ^ 2 + 1) * diff + torsion

set_option maxHeartbeats 1500000 in
private theorem rank_four_kills_point [Nontrivial R] [Module.Free R A] [Module.Finite R A]
    (g : Points (R := R) (A := A)) (rank : Module.finrank R A = 4) : g ^ 8 = 1 := by
  classical
  let b := Module.Free.chooseBasis R A
  have card₄ : Fintype.card (Module.Free.ChooseBasisIndex R A) = 4 :=
    (Module.finrank_eq_card_chooseBasisIndex R A).symm.trans rank
  letI : Nonempty (Module.Free.ChooseBasisIndex R A) := Fintype.card_pos_iff.mp (by omega)
  let mat := translationMatrix b
  let T := mat g
  let T' := mat (g⁻¹)
  have leftInv : T' * T = 1 := by
    change mat (g⁻¹) * mat g = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  have inverse : T⁻¹ = T' := Matrix.inv_eq_left_inv leftInv
  have rightInv : T * T' = 1 := by
    change mat g * mat g⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]
  have unitT : IsUnit T := ⟨⟨T, T', rightInv, leftInv⟩, rfl⟩
  have P : T.charpoly = (translation g).charpoly :=
    (translation g).charpoly_toMatrix b
  have lead : T.charpoly.coeff 4 = 1 := by
    rw [← card₄, ← T.charpoly_natDegree_eq_dim]
    exact T.charpoly_monic
  have third : T.charpoly.coeff 3 = -T.trace := by
    have h := Matrix.trace_eq_neg_charpoly_coeff T
    rw [card₄] at h
    norm_num at h
    linear_combination h
  have first : T.charpoly.coeff 1 = -T.det * T'.trace := by
    have hinv := congrArg (fun Q : R[X] => Q.coeff 3) (Matrix.charpoly_inv T unitT)
    have hc : T'.charpoly.coeff 3 = -T'.trace := by
      have h := Matrix.trace_eq_neg_charpoly_coeff T'
      rw [card₄] at h
      norm_num at h
      linear_combination h
    have hrev : T.charpolyRev.coeff 3 = T.charpoly.coeff 1 := by
      rw [reverse_coeff T 3 (by omega), card₄]
    have e : -T'.trace = Ring.inverse T.det * T.charpoly.coeff 1 := by
      have hsign : (-1 : R[X]) ^ (4 : ℕ) = 1 := by ring
      rw [inverse, hc, card₄, hsign, one_mul, Polynomial.coeff_C_mul, hrev] at hinv
      exact hinv
    have unitDet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det _).mp unitT
    have cancel := Ring.mul_inverse_cancel _ unitDet
    linear_combination -T.det * e - T.charpoly.coeff 1 * cancel
  have secondNewton : 2 * T.charpoly.coeff 2 = T.trace ^ 2 - (T ^ 2).trace := by
    have e := Matrix.charpolyRev_newton T 1
    have rev₂ : T.charpolyRev.coeff 2 = T.charpoly.coeff 2 := by
      rw [reverse_coeff T 2 (by omega), card₄]
    have he : 2 * T.charpoly.coeff 2 =
        -((-T.trace) * T.trace + (T ^ 2).trace) := by
      simpa [Finset.sum_range_succ, Finset.sum_range_one, rev₂, Polynomial.coeff_zero_eq_eval_zero]
        using e
    linear_combination he
  let C := CyclicAlgebra g
  let x : C := cyclicUnit g
  let y : C := ↑((cyclicUnit g)⁻¹)
  let φ := algebraMap R C
  let a := φ T.trace
  let b' := φ T'.trace
  let c := φ (T.charpoly.coeff 2)
  let d := φ T.det
  have xy : x * y = 1 := (cyclicUnit g).mul_inv
  have fromTrace₁ : a * (x - 1) = 0 := by
    change φ T.trace * (x - 1) = 0
    rw [show T.trace = LinearMap.trace R A (translation g) from trace_eval b g]
    exact trace_annihilates g x g rfl
  have fromTraceInv : b' * (y - 1) = 0 := by
    change φ T'.trace * (y - 1) = 0
    rw [show T'.trace = LinearMap.trace R A (translation g⁻¹) from trace_eval b g⁻¹]
    exact trace_annihilates g y g⁻¹ rfl
  have invTrace₁ : b' * (x - 1) = 0 := by linear_combination -x * fromTraceInv + b' * xy
  have fromTrace₂ : φ ((T ^ 2).trace) * (x ^ 2 - 1) = 0 := by
    rw [show T ^ 2 = mat (g ^ 2) from (map_pow mat g 2).symm, trace_eval]
    apply trace_annihilates g _ (g ^ 2)
    change linearPoint g ^ 2 = _
    rw [map_pow]
  have newton : 2 * c = a ^ 2 - φ ((T ^ 2).trace) := by
    simpa only [c, a, φ, map_mul, map_ofNat, map_pow, map_sub] using congrArg φ secondNewton
  have polynomial (k : ℕ) :
      (x ^ k) ^ 4 - a * (x ^ k) ^ 3 + c * (x ^ k) ^ 2 - d * b' * x ^ k +
        φ (T.charpoly.coeff 0) = 0 := by
    have e := moments g rank k
    rw [← P] at e
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, lead, third,
      first, map_one, map_neg, map_mul, one_mul, pow_zero, one_pow] at e
    simp_rw [← pow_mul, Nat.mul_comm _ k, pow_mul] at e
    dsimp [a, b', c, d, φ, x]
    linear_combination e
  have pOne := polynomial 0
  simp only [pow_zero, one_pow, mul_one] at pOne
  have px := polynomial 1
  simp only [pow_one] at px
  let k := factorialBound 4 - 1
  have hk : k + 1 = factorialBound 4 := by decide
  have ord := factorialBound_kills_point g (by decide : 0 < 4) rank
  have allPow : x ^ factorialBound 4 = 1 := by
    apply Subtype.ext
    change linearPoint g ^ factorialBound 4 = 1
    rw [← map_pow, ord, map_one]
  have xk : x ^ k = y := by
    have e : x * x ^ k = x * y := by rw [xy, ← pow_succ', hk, allPow]
    simpa [← mul_assoc, mul_comm y x, xy] using congrArg (y * ·) e
  have py := polynomial k
  rw [xk] at py
  have x8 : x ^ 8 = 1 :=
    quartic_power x y a b' c d (φ (T.charpoly.coeff 0)) (φ ((T ^ 2).trace))
      xy pOne px py fromTrace₁ fromTraceInv invTrace₁ fromTrace₂ newton
  apply linearPoint_injective
  rw [map_pow, map_one]
  exact congrArg Subtype.val x8

/-- Every finite locally free group scheme of rank four is killed by eight. -/
theorem rank_four_universal_eight : IsUniversalKillingExponent.{0, 0} 4 8 := by
  intro R _ A _ _ _ _ rank
  apply isKilledBy_of_localized_points 4 8 rank
  intro p _ K _ g hg
  exact rank_four_kills_point g hg

end
end FiniteLocallyFreeGroupSchemeExponent

#print axioms FiniteLocallyFreeGroupSchemeExponent.rank_four_universal_eight
