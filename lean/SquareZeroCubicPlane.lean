import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Free

/-! A plane algebra with two cubic relations whose correction terms have square-zero coefficients. -/

open AddMonoidAlgebra

namespace SquareZeroCubicPlane

noncomputable section

variable {R : Type*} [CommRing R]

abbrev Monomials := ℕ × ℕ
abbrev Standard := Fin 3 × Fin 3
abbrev Polynomials (R : Type*) [CommRing R] := AddMonoidAlgebra R Monomials

def monomial (m : Monomials) : Polynomials R := single m 1

@[simp] theorem monomial_mul (m n : Monomials) :
    (monomial m : Polynomials R) * monomial n = monomial (m + n) := by
  simp [monomial, single_mul_single]

@[simp] theorem monomial_pow (m : Monomials) (k : ℕ) :
    (monomial m : Polynomials R) ^ k = monomial (k • m) := by
  simp [monomial]

def evalMonomials {S : Type*} [CommRing S] [Algebra R S] (x y : S) :
    Polynomials R →ₐ[R] S :=
  AddMonoidAlgebra.lift R S Monomials
    { toFun := fun i => x ^ i.toAdd.1 * y ^ i.toAdd.2
      map_one' := by simp
      map_mul' := fun a b => by
        change x ^ (a.toAdd.1 + b.toAdd.1) * y ^ (a.toAdd.2 + b.toAdd.2) = _
        rw [pow_add, pow_add]
        ac_rfl }

@[simp] theorem eval_monomial {S : Type*} [CommRing S] [Algebra R S] (x y : S) (m : Monomials) :
    evalMonomials (R := R) x y (monomial m) = x ^ m.1 * y ^ m.2 := by
  simp [evalMonomials, monomial]

theorem monomial_xy (m : Monomials) : (monomial m : Polynomials R) =
    monomial (1, 0) ^ m.1 * monomial (0, 1) ^ m.2 := by
  rw [monomial_pow, monomial_pow, monomial_mul]
  congr 1
  ext <;> simp

variable (s t : R) (W : Polynomials R)

def cubic (i : Bool) : Polynomials R :=
  if i then monomial (3, 0) + s • W else monomial (0, 3) + t • W

def ideal : Ideal (Polynomials R) := Ideal.span (Set.range (cubic s t W))
abbrev Coord := Polynomials R ⧸ ideal s t W

def quotient : Polynomials R →ₐ[R] Coord s t W := Ideal.Quotient.mkₐ R _
def X : Coord s t W := quotient s t W (monomial (1, 0))
def Y : Coord s t W := quotient s t W (monomial (0, 1))

theorem quotient_cubic (i : Bool) : quotient s t W (cubic s t W i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

theorem X_relation : X s t W ^ 3 = -s • quotient s t W W := by
  have h := quotient_cubic s t W true
  have em : (monomial (1, 0) : Polynomials R) ^ 3 = monomial (3, 0) := by
    rw [monomial_pow]; rfl
  rw [X, ← map_pow, em]
  simpa [cubic, map_add, map_smul, eq_neg_iff_add_eq_zero] using h

theorem Y_relation : Y s t W ^ 3 = -t • quotient s t W W := by
  have h := quotient_cubic s t W false
  have em : (monomial (0, 1) : Polynomials R) ^ 3 = monomial (0, 3) := by
    rw [monomial_pow]; rfl
  rw [Y, ← map_pow, em]
  simpa [cubic, map_add, map_smul, eq_neg_iff_add_eq_zero] using h

def lift {S : Type*} [CommRing S] [Algebra R S] (x y : S)
    (hx : x ^ 3 = -s • evalMonomials (R := R) x y W)
    (hy : y ^ 3 = -t • evalMonomials (R := R) x y W) : Coord s t W →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (evalMonomials x y) (by
    change ideal s t W ≤ RingHom.ker (evalMonomials x y).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change evalMonomials x y (cubic s t W i) = 0
    cases i <;> simp [cubic, hx, hy, neg_smul])

@[simp] theorem lift_X {S : Type*} [CommRing S] [Algebra R S] (x y : S) (hx) (hy) :
    lift s t W x y hx hy (X s t W) = x := by
  change evalMonomials (R := R) x y (monomial (1, 0)) = x
  exact (eval_monomial (R := R) x y (1, 0)).trans (by simp)

@[simp] theorem lift_Y {S : Type*} [CommRing S] [Algebra R S] (x y : S) (hx) (hy) :
    lift s t W x y hx hy (Y s t W) = y := by
  change evalMonomials (R := R) x y (monomial (0, 1)) = y
  exact (eval_monomial (R := R) x y (0, 1)).trans (by simp)

theorem algHom_ext {S : Type*} [Semiring S] [Algebra R S] {f g : Coord s t W →ₐ[R] S}
    (hx : f (X s t W) = g (X s t W)) (hy : f (Y s t W) = g (Y s t W)) : f = g := by
  ext v
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective v
  change f (quotient s t W p) = g (quotient s t W p)
  induction p using AddMonoidAlgebra.induction_on with
  | of m =>
    change f (quotient s t W (monomial m)) = g (quotient s t W (monomial m))
    simp only [monomial_xy m, map_mul, map_pow]
    change f (X s t W) ^ m.1 * f (Y s t W) ^ m.2 = _
    rw [hx, hy]
    rfl
  | add p q hp hq => simp [map_add, hp, hq]
  | smul c p hp => simp [map_smul, hp]

private abbrev Coords (R : Type*) [CommRing R] := Standard →₀ R

private def onMonomials {V : Type*} [AddCommGroup V] [Module R V]
    (f : Monomials → V) : Polynomials R →ₗ[R] V :=
  (Finsupp.linearCombination R f).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] private theorem onMonomials_apply {V : Type*} [AddCommGroup V] [Module R V]
    (f : Monomials → V) (m : Monomials) :
    onMonomials f (monomial m : Polynomials R) = f m := by
  change Finsupp.linearCombination R f (Finsupp.single m 1) = _
  simp

private def truncMon (m : Monomials) : Coords R :=
  if hx : m.1 < 3 then
    if hy : m.2 < 3 then Finsupp.single (⟨m.1, hx⟩, ⟨m.2, hy⟩) 1 else 0
  else 0

private def trunc : Polynomials R →ₗ[R] Coords R := onMonomials truncMon

@[simp] private theorem trunc_monomial (m : Monomials) :
    trunc (monomial m : Polynomials R) = truncMon m := onMonomials_apply _ _

private theorem trunc_mul_of_large (m : Monomials) (hm : 3 ≤ m.1 ∨ 3 ≤ m.2) (p : Polynomials R) :
    trunc (monomial m * p) = 0 := by
  induction p using AddMonoidAlgebra.induction_on with
  | of n =>
    change trunc (monomial m * monomial n : Polynomials R) = 0
    rw [monomial_mul, trunc_monomial]
    rcases hm with hx | hy
    · have hh : ¬ m.1 + n.1 < 3 := by omega
      simp [truncMon, hh]
    · have hh : ¬ m.2 + n.2 < 3 := by omega
      simp [truncMon, hh]
  | add a b ha hb => simp [mul_add, ha, hb]
  | smul c a ha => simp [ha]

private def normalMon (m : Monomials) : Coords R :=
  if 3 ≤ m.1 then -s • trunc (monomial (m.1 - 3, m.2) * W)
  else if 3 ≤ m.2 then -t • trunc (monomial (m.1, m.2 - 3) * W)
  else truncMon m

private def normal : Polynomials R →ₗ[R] Coords R := onMonomials (normalMon s t W)

@[simp] private theorem normal_monomial (m : Monomials) :
    normal s t W (monomial m) = normalMon s t W m := onMonomials_apply _ _

private theorem smul_normal (c : R) (cs : c * s = 0) (ct : c * t = 0) (p : Polynomials R) :
    c • normal s t W p = c • trunc p := by
  induction p using AddMonoidAlgebra.induction_on with
  | of m =>
    change c • normal s t W (monomial m) = c • trunc (monomial m : Polynomials R)
    rw [normal_monomial, trunc_monomial]
    by_cases hx : 3 ≤ m.1
    · simp [normalMon, truncMon, hx, not_lt_of_ge hx, smul_smul, mul_neg, cs]
    · by_cases hy : 3 ≤ m.2 <;>
        simp [normalMon, truncMon, hx, hy, not_lt_of_ge, smul_smul, mul_neg, ct]
  | add a b ha hb => simp [smul_add, ha, hb]
  | smul d a ha => simp only [map_smul, smul_comm c d, ha]

variable (ss : s * s = 0) (st : s * t = 0) (tt : t * t = 0)

include ss st tt

private theorem normal_monomial_cubic (m : Monomials) (i : Bool) :
    normal s t W (monomial m * cubic s t W i) = 0 := by
  rcases m with ⟨u, v⟩
  cases i
  · simp only [cubic, Bool.false_eq_true, if_false, mul_add, monomial_mul,
      map_add, mul_smul_comm, map_smul, normal_monomial, Prod.mk_add_mk, add_zero]
    rw [smul_normal s t W t (by rwa [mul_comm]) tt]
    by_cases h : 3 ≤ u
    · simp only [normalMon, h, if_true]
      rw [trunc_mul_of_large _ (Or.inr (by simp)) W,
        trunc_mul_of_large _ (Or.inl h) W, smul_zero, smul_zero, zero_add]
    · have hv : 3 ≤ v + 3 := by omega
      simp [normalMon, h, hv, neg_smul]
  · simp only [cubic, if_true, mul_add, monomial_mul, map_add,
      mul_smul_comm, map_smul, normal_monomial, Prod.mk_add_mk, add_zero]
    rw [smul_normal s t W s ss st]
    have hu : 3 ≤ u + 3 := by omega
    simp [normalMon, hu, neg_smul]

private theorem normal_cubic_mul (p : Polynomials R) (i : Bool) :
    normal s t W (p * cubic s t W i) = 0 := by
  induction p using AddMonoidAlgebra.induction_on with
  | of m => exact normal_monomial_cubic s t W ss st tt m i
  | add a b ha hb => simp [add_mul, ha, hb]
  | smul c a ha => simp [ha]

private def coordinates : Coord s t W →ₗ[R] Coords R :=
  ((ideal s t W).restrictScalars R).liftQ (normal s t W) (by
    intro p hp
    change p ∈ ideal s t W at hp
    rcases Ideal.mem_span_range_iff_exists_fun.mp hp with ⟨f, hf⟩
    change normal s t W p = 0
    rw [← hf, map_sum]
    simp [normal_cubic_mul s t W ss st tt])

private def standardMonomial (i : Standard) : Coord s t W :=
  quotient s t W (monomial (i.1, i.2))

private theorem coordinates_standard (i : Standard) :
    coordinates s t W ss st tt (standardMonomial s t W i) = Finsupp.single i 1 := by
  change normal s t W (monomial ((i.1 : ℕ), (i.2 : ℕ))) = _
  simp [normalMon, truncMon, i.1.isLt, i.2.isLt, not_le_of_gt]

private theorem span_standard :
    Submodule.span R (Set.range (standardMonomial s t W)) = ⊤ := by
  classical
  let span := Submodule.span R (Set.range (standardMonomial s t W))
  let q := quotient s t W
  have qX : q (monomial (3, 0)) = -s • q W := by
    rw [← show (monomial (1, 0) : Polynomials R) ^ 3 = monomial (3, 0) by rw [monomial_pow]; rfl,
      map_pow]
    exact X_relation s t W
  have qY : q (monomial (0, 3)) = -t • q W := by
    rw [← show (monomial (0, 1) : Polynomials R) ^ 3 = monomial (0, 3) by rw [monomial_pow]; rfl,
      map_pow]
    exact Y_relation s t W
  have low (m : Monomials) (hx : m.1 < 3) (hy : m.2 < 3) : q (monomial m) ∈ span :=
    Submodule.subset_span ⟨(⟨m.1, hx⟩, ⟨m.2, hy⟩), rfl⟩
  have shift (c : R) (cs : c * s = 0) (ct : c * t = 0) (m : Monomials) :
      c • q (monomial m) ∈ span := by
    by_cases hx : m.1 < 3
    · by_cases hy : m.2 < 3
      · exact span.smul_mem c (low _ hx hy)
      · have e : m = (0, 3) + (m.1, m.2 - 3) := by ext <;> simp <;> omega
        rw [e, ← monomial_mul, map_mul, qY]
        rw [← smul_mul_assoc, smul_smul, mul_neg, ct, neg_zero, zero_smul, zero_mul]
        exact span.zero_mem
    · have e : m = (3, 0) + (m.1 - 3, m.2) := by ext <;> simp <;> omega
      rw [e, ← monomial_mul, map_mul, qX]
      rw [← smul_mul_assoc, smul_smul, mul_neg, cs, neg_zero, zero_smul, zero_mul]
      exact span.zero_mem
  have shiftPolynomial (c : R) (cs : c * s = 0) (ct : c * t = 0) (p : Polynomials R) :
      c • q p ∈ span := by
    induction p using AddMonoidAlgebra.induction_on with
    | of m => exact shift c cs ct m
    | add a b ha hb => simpa [smul_add] using span.add_mem ha hb
    | smul r a ha => simpa [smul_comm c r] using span.smul_mem r ha
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change q p ∈ span
  induction p using AddMonoidAlgebra.induction_on with
  | of m =>
    change q (monomial m) ∈ span
    by_cases hx : m.1 < 3
    · by_cases hy : m.2 < 3
      · exact low _ hx hy
      · have e : m = (0, 3) + (m.1, m.2 - 3) := by ext <;> simp <;> omega
        rw [e, ← monomial_mul, map_mul, qY, smul_mul_assoc, ← map_mul]
        exact shiftPolynomial (-t) (by rw [neg_mul, mul_comm t s, st, neg_zero]) (by simp [tt]) _
    · have e : m = (3, 0) + (m.1 - 3, m.2) := by ext <;> simp <;> omega
      rw [e, ← monomial_mul, map_mul, qX, smul_mul_assoc, ← map_mul]
      exact shiftPolynomial (-s) (by simp [ss]) (by simp [st]) _
  | add a b ha hb => rw [map_add]; exact span.add_mem ha hb
  | smul r a ha => rw [map_smul]; exact span.smul_mem r ha

/-- The nine monomials with both exponents below three freely span the quotient. -/
def basis : Module.Basis Standard R (Coord s t W) :=
  Module.Basis.mk (v := standardMonomial s t W)
    (by
      have h := (Finsupp.basisSingleOne : Module.Basis Standard R (Coords R)).linearIndependent
      apply LinearIndependent.of_comp (coordinates s t W ss st tt)
      simpa [Function.comp_def, coordinates_standard] using h)
    (by rw [span_standard s t W ss st tt])

theorem basis_apply (i : Standard) :
    basis s t W ss st tt i = X s t W ^ (i.1 : ℕ) * Y s t W ^ (i.2 : ℕ) := by
  rw [basis, Module.Basis.mk_apply]
  change quotient s t W (monomial ((i.1 : ℕ), (i.2 : ℕ))) = _
  refine (congrArg (quotient s t W) (monomial_xy ((i.1 : ℕ), (i.2 : ℕ)))).trans ?_
  rw [map_mul, map_pow, map_pow]
  rfl

end
end SquareZeroCubicPlane
