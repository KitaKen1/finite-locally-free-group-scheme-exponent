import SmallRankUpperBounds
import HopfPointOrder
import NinePowerCalculation
import RankNineExample

/-! The exact rank-nine value of the Formal Conjectures exponent. -/

open WithConv
open scoped BigOperators Polynomial IsMulCommutative

namespace FiniteLocallyFreeGroupSchemeExponent

open RankPoint

noncomputable section

private theorem sum_defect {C : Type*} [CommRing C] (coef value : ℕ → C)
    (relation : ∑ j ∈ Finset.range 10, coef j * value j = 0)
    (atOne : ∑ j ∈ Finset.range 10, coef j = 0) :
    ∑ j ∈ Finset.range 10, coef j * (value j - 1) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, mul_one, relation, atOne, sub_zero]

set_option maxHeartbeats 900000 in
private theorem rank_nine_kills_point {R A : Type*} [CommRing R] [IsLocalRing R]
    [CommRing A] [HopfAlgebra R A] [Module.Free R A] [Module.Finite R A]
    (g : Points (R := R) (A := A)) (rank : Module.finrank R A = 9) : g ^ 27 = 1 := by
  classical
  obtain h | ⟨hp, ord⟩ := rank_nine_local_cases g rank
  · calc
      g ^ 27 = (g ^ 9) ^ 3 := pow_mul g 9 3
      _ = 1 := by rw [h, one_pow]
  let : CharP (IsLocalRing.ResidueField R) 3 := hp
  let b := Module.Free.chooseBasis R A
  have card₉ : Fintype.card (Module.Free.ChooseBasisIndex R A) = 9 :=
    (Module.finrank_eq_card_chooseBasisIndex R A).symm.trans rank
  let mat := translationMatrix b
  let T := mat g
  have charpoly : T.charpoly = (translation g).charpoly := (translation g).charpoly_toMatrix b
  let C := CyclicAlgebra g
  let x : C := cyclicUnit g
  let φ := algebraMap R C
  let coef (j : ℕ) := φ (T.charpolyRev.coeff j)
  let trace (i : ℕ) := φ ((T ^ i).trace)
  have ordx : x ^ (3 ^ 20 : ℕ) = 1 := by
    apply Subtype.ext
    change linearPoint g ^ (3 ^ 20 : ℕ) = 1
    rw [← map_pow, ord, map_one]
  have newton (j : ℕ) (hj : 0 < j) : (j : C) * coef j =
      -(∑ i ∈ Finset.range j, coef (j - 1 - i) * trace (i + 1)) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    simpa only [coef, trace, map_mul, map_neg, map_sum, map_natCast, Nat.succ_eq_add_one,
      Nat.add_sub_cancel] using congrArg φ (Matrix.charpolyRev_newton T k)
  have tr (i : ℕ) : trace i * (x ^ i - 1) = 0 := by
    change φ ((T ^ i).trace) * (x ^ i - 1) = 0
    rw [show T ^ i = mat (g ^ i) from (map_pow mat g i).symm, trace_eval]
    apply trace_annihilates g _ (g ^ i)
    change linearPoint g ^ i = _
    rw [map_pow]
  have units (j : ℕ) (hj : ¬ 3 ∣ j) : IsUnit (j : C) := by
    have hR : IsUnit (j : R) := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff _ 3]
      exact hj
    simpa only [map_natCast] using hR.map φ
  have leading : coef 0 = 1 := by
    change φ (T.charpolyRev.coeff 0) = 1
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev, map_one]
  have forward (k : ℕ) : ∑ j ∈ Finset.range 10, φ (T.charpoly.coeff j) * (x ^ k) ^ j = 0 := by
    have e := moments g rank k
    change ∑ j ∈ Finset.range 10, φ ((translation g).charpoly.coeff j) * (x ^ j) ^ k = 0 at e
    rw [← charpoly] at e
    refine (Finset.sum_congr rfl fun j _ => ?_).trans e
    rw [← pow_mul, ← pow_mul, Nat.mul_comm k j]
  have rev (k : ℕ) : ∑ j ∈ Finset.range 10, coef j * (x ^ k) ^ (9 - j) = 0 := by
    calc
      _ = ∑ j ∈ Finset.range 10, φ (T.charpoly.coeff (9 - j)) * (x ^ k) ^ (9 - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ Fintype.card (Module.Free.ChooseBasisIndex R A) := by
          rw [card₉]
          exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        change φ (T.charpolyRev.coeff j) * (x ^ k) ^ (9 - j) = _
        rw [reverse_coeff T j hj', card₉]
      _ = _ :=
        (Finset.sum_range_reflect (fun j => φ (T.charpoly.coeff j) * (x ^ k) ^ j) 10).trans (forward k)
  have mom (k : ℕ) : ∑ j ∈ Finset.range 10, coef j * ((x ^ k) ^ (9 - j) - 1) = 0 := by
    have e := rev 0
    simp only [pow_zero, one_pow, mul_one] at e
    exact sum_defect coef (fun j => (x ^ k) ^ (9 - j)) (rev k) e
  have hx : x ^ 27 = 1 := by
    have bound := @NinePowerCalculation.pow_twenty_seven C
      (inferInstanceAs (CommRing (CyclicAlgebra g))) (cyclicUnit g) coef trace
    refine bound ?_ ?_ ?_ ?_ ?_ ?_
    · exact ordx
    · exact newton
    · intro i _ _
      exact tr i
    · exact units
    · exact leading
    · exact mom
  apply linearPoint_injective
  rw [map_pow, map_one]
  exact congrArg Subtype.val hx

/-- Every finite locally free group scheme of rank nine is killed by twenty-seven. -/
theorem rank_nine_universal_twenty_seven : IsUniversalKillingExponent.{0, 0} 9 27 := by
  intro R _ A _ _ _ _ rank
  apply isKilledBy_of_localized_points 9 27 rank
  intro p _ K _ g hg
  exact rank_nine_kills_point g hg

/-- The universal point of the rank-nine example forces every universal exponent to be
a multiple of twenty-seven. -/
theorem twenty_seven_dvd_rank_nine_exponent (m : ℕ+) (h : IsUniversalKillingExponent.{0, 0} 9 m) :
    27 ∣ (m : ℕ) := by
  have hrank : Module.rankAtStalk (R := RankNineExample.Base)
      RankNineExample.Coordinate = fun _ => 9 := by
    rw [Module.rankAtStalk_eq_finrank_of_free, RankNineExample.coordinate_finrank]
    rfl
  have hz : RankNineExample.universalPoint ^ (m : ℕ) = 1 :=
    h RankNineExample.Base RankNineExample.Coordinate hrank
  have hd : orderOf RankNineExample.universalPoint ∣ (m : ℕ) := orderOf_dvd_iff_pow_eq_one.mpr hz
  rwa [RankNineExample.orderOf_universalPoint] at hd

theorem rank_nine_optimal_exponent :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 9 m} : Set ℕ) = 27 := by
  apply optimal_exponent_of_excluding_proper_divisors 9 27 rank_nine_universal_twenty_seven
  intro m _ hm universal
  exact (Nat.not_le_of_lt hm) (Nat.le_of_dvd m.pos (twenty_seven_dvd_rank_nine_exponent m universal))

end
end FiniteLocallyFreeGroupSchemeExponent

#print axioms FiniteLocallyFreeGroupSchemeExponent.rank_nine_optimal_exponent
