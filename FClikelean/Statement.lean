module

public import Model

@[expose] public section

namespace FiniteLocallyFreeGroupSchemeExponent

-- Comparator substitutes the solution's executable definition for this challenge hole.
set_option warn.sorry false in
def optimal_exponent.answer : ℕ+ → ℕ := by
  sorry

set_option warn.sorry false in
theorem optimal_exponent :
    ∀ n, sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} n m} : Set ℕ) =
      optimal_exponent.answer n := by
  sorry

set_option warn.sorry false in
theorem optimal_exponent.rank_four :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 4 m} : Set ℕ) = 8 := by
  sorry

set_option warn.sorry false in
theorem optimal_exponent.rank_nine :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 9 m} : Set ℕ) = 27 := by
  sorry

end FiniteLocallyFreeGroupSchemeExponent
