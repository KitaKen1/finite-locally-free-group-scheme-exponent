import Solution

open FiniteLocallyFreeGroupSchemeExponent

example (n : ℕ+) :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} n m} : Set ℕ) =
      optimal_exponent.answer n :=
  optimal_exponent n

example : sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 4 m} : Set ℕ) = 8 :=
  optimal_exponent.rank_four

example : sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 9 m} : Set ℕ) = 27 :=
  optimal_exponent.rank_nine

#guard optimal_exponent.answer 1 == 1
#guard optimal_exponent.answer 4 == 8
#guard optimal_exponent.answer 9 == 27

#print axioms optimal_exponent.answer
#print axioms optimal_exponent
#print axioms optimal_exponent.rank_four
#print axioms optimal_exponent.rank_nine
