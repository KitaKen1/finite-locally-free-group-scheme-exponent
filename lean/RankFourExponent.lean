import SmallRankUpperBounds
import Counterexamples.GrothendieckPower

/-! The exact rank-four value of the Formal Conjectures exponent. -/

namespace FiniteLocallyFreeGroupSchemeExponent

/-- The rank-four example of order eight forces every universal exponent to be a multiple of eight. -/
theorem eight_dvd_rank_four_exponent (m : ℕ+) (h : IsUniversalKillingExponent.{0, 0} 4 m) :
    8 ∣ (m : ℕ) := by
  have hrank : Module.rankAtStalk (R := Counterexample.GrothendieckPower.R)
      Counterexample.GrothendieckPower.A = fun _ => 4 := by
    rw [Module.rankAtStalk_eq_finrank_of_free, Counterexample.GrothendieckPower.finrank_A]
    rfl
  have hz : Counterexample.GrothendieckPower.universalPoint ^ (m : ℕ) = 1 :=
    h Counterexample.GrothendieckPower.R Counterexample.GrothendieckPower.A hrank
  simpa only [Counterexample.GrothendieckPower.orderOf_universalPoint]
    using orderOf_dvd_of_pow_eq_one hz

theorem rank_four_optimal_exponent :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 4 m} : Set ℕ) = 8 := by
  apply optimal_exponent_of_excluding_proper_divisors 4 8 rank_four_universal_eight
  intro m _ hm universal
  exact (Nat.not_le_of_lt hm) (Nat.le_of_dvd m.pos (eight_dvd_rank_four_exponent m universal))

end FiniteLocallyFreeGroupSchemeExponent

#print axioms FiniteLocallyFreeGroupSchemeExponent.rank_four_optimal_exponent
