import OptimalExponentExecutable

namespace FiniteLocallyFreeGroupSchemeExponent

/-- Executable value of the optimal exponent in each positive rank. -/
def optimal_exponent.answer : ℕ+ → ℕ := answerExecutable

theorem optimal_exponent :
    ∀ n, sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} n m} : Set ℕ) =
      optimal_exponent.answer n :=
  optimal_exponent_executable

theorem optimal_exponent.rank_four :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 4 m} : Set ℕ) = 8 :=
  rank_four_optimal_exponent

theorem optimal_exponent.rank_nine :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 9 m} : Set ℕ) = 27 :=
  rank_nine_optimal_exponent

end FiniteLocallyFreeGroupSchemeExponent
