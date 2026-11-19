import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Data.Finsupp.Encodable

/-! Computable integer polynomial arithmetic that refines Mathlib's multivariate polynomials. -/

open scoped BigOperators

/-- An integer multivariate polynomial with operations using explicit decidable equality. -/
structure ExecutablePolynomial (σ : Type*) where
  polynomial : MvPolynomial σ ℤ

namespace ExecutablePolynomial

variable {σ α R : Type*}

private def supported [Zero R] [DecidableEq R] (s : Finset α) (f : α → R)
    (within : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ R :=
  ⟨s.filter (fun a => f a ≠ 0), f, fun a => by aesop⟩

private def single [DecidableEq α] [Zero R] [DecidableEq R] (a : α) (r : R) : α →₀ R :=
  supported {a} (fun b => if a = b then r else 0) (by
    intro b h
    by_cases e : a = b
    · simpa using e.symm
    · simp [e] at h)

private theorem single_eq [DecidableEq α] [Zero R] [DecidableEq R] (a : α) (r : R) :
    single a r = Finsupp.single a r := by
  ext b
  simp [single, supported, Finsupp.single_apply]

variable [DecidableEq σ]

private def addExponent (a b : σ →₀ ℕ) : σ →₀ ℕ :=
  supported (a.support ∪ b.support) (fun i => a i + b i) (by
    intro i h
    by_contra hi
    have ha : i ∉ a.support := fun hm => hi (Finset.mem_union_left _ hm)
    have hb : i ∉ b.support := fun hm => hi (Finset.mem_union_right _ hm)
    exact h (by simp [Finsupp.notMem_support_iff.mp ha, Finsupp.notMem_support_iff.mp hb]))

private theorem addExponent_eq (a b : σ →₀ ℕ) : addExponent a b = a + b := by
  ext i
  rfl

private def monomial (a : σ →₀ ℕ) (c : ℤ) : ExecutablePolynomial σ :=
  ⟨AddMonoidAlgebra.ofCoeff (single a c)⟩

@[simp] private theorem polynomial_monomial (a : σ →₀ ℕ) (c : ℤ) :
    (monomial a c).polynomial = MvPolynomial.monomial a c := by
  simp [monomial, single_eq, ← MvPolynomial.single_eq_monomial]

def X (i : σ) : ExecutablePolynomial σ := monomial (single i (1 : ℕ)) 1

@[simp] theorem polynomial_X (i : σ) : (X i).polynomial = MvPolynomial.X i := by
  simp [X, MvPolynomial.X, single_eq]

private def add (p q : ExecutablePolynomial σ) : ExecutablePolynomial σ :=
  ⟨AddMonoidAlgebra.ofCoeff <|
    supported (p.polynomial.support ∪ q.polynomial.support)
      (fun a => p.polynomial.coeff a + q.polynomial.coeff a) (by
        intro i h
        have hs : i ∈ (p.polynomial + q.polynomial).support :=
          MvPolynomial.mem_support_iff.mpr (by simpa [MvPolynomial.coeff_add] using h)
        exact MvPolynomial.support_add hs)⟩

private theorem polynomial_add (p q : ExecutablePolynomial σ) :
    (add p q).polynomial = p.polynomial + q.polynomial := by
  ext a
  exact (MvPolynomial.coeff_add a p.polynomial q.polynomial).symm

private def neg (p : ExecutablePolynomial σ) : ExecutablePolynomial σ :=
  ⟨AddMonoidAlgebra.ofCoeff <|
    supported p.polynomial.support (fun a => -p.polynomial.coeff a)
      (fun _ h => MvPolynomial.mem_support_iff.mpr (neg_ne_zero.mp h))⟩

private theorem polynomial_neg (p : ExecutablePolynomial σ) :
    (neg p).polynomial = -p.polynomial := by
  ext a
  rfl

private def productSupport (p q : MvPolynomial σ ℤ) : Finset (σ →₀ ℕ) :=
  (p.support ×ˢ q.support).image (fun t => addExponent t.1 t.2)

private def productCoeff (p q : MvPolynomial σ ℤ) (a : σ →₀ ℕ) : ℤ :=
  ∑ b ∈ p.support, ∑ c ∈ q.support, if addExponent b c = a then p.coeff b * q.coeff c else 0

private theorem productCoeff_eq (p q : MvPolynomial σ ℤ) (a : σ →₀ ℕ) :
    productCoeff p q a = (p * q).coeff a := by
  rw [MvPolynomial.mul_def]
  simp only [Finsupp.sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    productCoeff, addExponent_eq]
  rfl

private def mul (p q : ExecutablePolynomial σ) : ExecutablePolynomial σ :=
  ⟨AddMonoidAlgebra.ofCoeff <|
    supported (productSupport p.polynomial q.polynomial) (productCoeff p.polynomial q.polynomial)
      (by
        intro a ha
        by_contra hn
        apply ha
        apply Finset.sum_eq_zero
        intro b hb
        apply Finset.sum_eq_zero
        intro c hc
        apply if_neg
        intro e
        exact hn (Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr ⟨hb, hc⟩, e⟩))⟩

private theorem polynomial_mul (p q : ExecutablePolynomial σ) :
    (mul p q).polynomial = p.polynomial * q.polynomial := by
  ext a
  exact productCoeff_eq p.polynomial q.polynomial a

instance : CommRing (ExecutablePolynomial σ) := by
  letI : Zero (ExecutablePolynomial σ) := ⟨⟨AddMonoidAlgebra.ofCoeff 0⟩⟩
  letI : One (ExecutablePolynomial σ) := ⟨monomial 0 1⟩
  letI : Add (ExecutablePolynomial σ) := ⟨add⟩
  letI : Neg (ExecutablePolynomial σ) := ⟨neg⟩
  letI : Mul (ExecutablePolynomial σ) := ⟨mul⟩
  have h0 : (0 : ExecutablePolynomial σ).polynomial = 0 := rfl
  have h1 : (1 : ExecutablePolynomial σ).polynomial = 1 :=
    (polynomial_monomial _ _).trans MvPolynomial.one_def.symm
  have ha (p q : ExecutablePolynomial σ) : (p + q).polynomial = p.polynomial + q.polynomial :=
    polynomial_add p q
  have hm (p q : ExecutablePolynomial σ) : (p * q).polynomial = p.polynomial * q.polynomial :=
    polynomial_mul p q
  have hn (p : ExecutablePolynomial σ) : (-p).polynomial = -p.polynomial := polynomial_neg p
  have inj : Function.Injective (polynomial (σ := σ)) := fun ⟨_⟩ ⟨_⟩ h => by cases h; rfl
  refine CommRing.ofMinimalAxioms ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> apply inj <;> simp only [ha, hm, hn, h0, h1]
  · exact add_assoc ..
  · exact zero_add _
  · exact neg_add_cancel _
  · exact mul_assoc ..
  · exact mul_comm ..
  · exact one_mul _
  · exact mul_add ..

/-- Forget the executable operations, preserving the value of the polynomial. -/
def toPolynomial : ExecutablePolynomial σ →+* MvPolynomial σ ℤ where
  toFun := polynomial
  map_add' := polynomial_add
  map_mul' := polynomial_mul
  map_zero' := rfl
  map_one' := (polynomial_monomial _ _).trans MvPolynomial.one_def.symm

@[simp] theorem toPolynomial_X (i : σ) : toPolynomial (X i) = MvPolynomial.X i := polynomial_X i

def isZero (p : ExecutablePolynomial σ) : Bool := decide (p.polynomial.support = ∅)

@[simp] theorem isZero_eq_true (p : ExecutablePolynomial σ) :
    isZero p = true ↔ toPolynomial p = 0 := by
  simp only [isZero, decide_eq_true_eq, MvPolynomial.support_eq_empty]
  rfl

instance [Encodable σ] : Encodable (ExecutablePolynomial σ) :=
  Encodable.ofEquiv ((σ →₀ ℕ) →₀ ℤ)
    { toFun := fun p => AddMonoidAlgebra.coeff p.polynomial
      invFun := fun f => ⟨AddMonoidAlgebra.ofCoeff f⟩
      left_inv := fun ⟨⟨_⟩⟩ => rfl
      right_inv := fun _ => rfl }

end ExecutablePolynomial
