# Third-party sources

- [Model.lean](Model.lean) includes the definitions `IsKilledBy` and
  `IsUniversalKillingExponent`, with three group-algebra lemmas, from the Formal Conjectures authors, with their
  original copyright notice and [Apache 2.0 license](licenses/Apache-2.0.txt).
  The package uses these declarations in Lean's module system.
  [Pinned upstream file](https://github.com/google-deepmind/formal-conjectures/blob/2de491f90132d3f3fac934edf5bd72acb3dfd15c/FormalConjectures/Paper/FiniteLocallyFreeGroupSchemeExponent.lean)
- Akhil Mathew's rank-four counterexample is imported from Mathlib. See the
  source header and Mathlib license for its attribution and terms.
  [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Counterexamples/GrothendieckPower.lean)
- The README structure, challenge/solution layout, and verification workflow follow the
  [unit-circumradius triples repository](https://github.com/KitaKen1/erdos104-variant-unit-circumradius-triples).
