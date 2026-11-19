import Model
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Universal killing exponents of finite locally free group schemes

The argument uses Cayley–Hamilton on right translations, followed by a trace
identity to control the nilpotent ideal cut out by a suitable power of a point.
-/

open scoped Coalgebra Pointwise TensorProduct
open WithConv

namespace FiniteLocallyFreeGroupSchemeExponent

universe u

/-- A uniform exponent obtained without any classification of the fibres. -/
def factorialBound (n : ℕ) : ℕ :=
  n.factorial * n ^ (n - 1)

/-- Check an ideal-membership certificate by multiplying the generators by the proposed
coefficients and comparing the resulting sum with the target. -/
def checkIdealCertificate {B ι : Type*} [CommRing B] [DecidableEq B] [Fintype ι]
    (relations : ι → B) (target : B) (multipliers : ι → B) : Bool :=
  decide (∑ i, multipliers i * relations i = target)

/-- Search the positive exponents up to the explicit bound using a Boolean test. -/
def boundedExponentSearch (n : ℕ+) (accept : ℕ → Bool) : ℕ :=
  ((Finset.Icc 1 (factorialBound n)).filter (fun m => accept m = true)).min.untopD 0

noncomputable section

variable {R A S : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing S] [Algebra R S]

def mapPoint {T : Type*} [CommRing T] [Algebra R T] (f : S →ₐ[R] T) :
    WithConv (A →ₐ[R] S) →* WithConv (A →ₐ[R] T) where
  toFun g := toConv (f.comp g.ofConv)
  map_one' := by
    apply WithConv.ext
    ext a
    change f (algebraMap R S (Coalgebra.counit a)) = algebraMap R T (Coalgebra.counit a)
    exact f.commutes _
  map_mul' g h := by
    exact congrArg toConv (AlgHom.comp_convMul_distrib f g h)

private theorem convolution_apply_repr {a : A} {ι : Type*}
    (r : Coalgebra.Repr R a ι) (f g : WithConv (A →ₐ[R] S)) :
    (f * g) a = ∑ i ∈ r.index, f (r.left i) * g (r.right i) := by
  exact r.convMul_apply (toConv f.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap)

private abbrev unitPoint (g : WithConv (A →ₐ[R] R)) :
    WithConv (A →ₐ[R] A) :=
  mapPoint (Algebra.ofId R A) g

def rightTranslation (g : WithConv (A →ₐ[R] R)) : A →ₐ[R] A :=
  (toConv (AlgHom.id R A) * unitPoint g).ofConv

theorem counit_rightTranslation (g : WithConv (A →ₐ[R] R)) :
    (Bialgebra.counitAlgHom R A).comp (rightTranslation g) = g.ofConv := by
  apply WithConv.toConv_injective
  change mapPoint (Bialgebra.counitAlgHom R A) (toConv (AlgHom.id R A) * unitPoint g) = g
  rw [map_mul]
  have h₁ : mapPoint (A := A) (Bialgebra.counitAlgHom R A) (toConv (AlgHom.id R A)) = 1 := by
    apply WithConv.ext
    ext a
    rfl
  have h₂ : mapPoint (A := A) (Bialgebra.counitAlgHom R A) (unitPoint g) = g := by
    apply WithConv.ext
    ext a
    exact (Bialgebra.counitAlgHom R A).commutes (g a)
  rw [h₁, h₂, one_mul]

/-- Right translations of points, acting on the coordinate algebra. -/
def translation : WithConv (A →ₐ[R] R) →* Module.End R A where
  toFun g := (rightTranslation g).toLinearMap
  map_one' := by
    change (toConv (AlgHom.id R A) * mapPoint (Algebra.ofId R A) 1).ofConv.toLinearMap = 1
    rw [map_one, mul_one]
    rfl
  map_mul' g h := by
    change (rightTranslation (g * h)).toLinearMap =
      ((rightTranslation g).comp (rightTranslation h)).toLinearMap
    congr 1
    apply WithConv.toConv_injective
    change toConv (AlgHom.id R A) * unitPoint (g * h) =
      mapPoint (rightTranslation g) (toConv (AlgHom.id R A) * unitPoint h)
    rw [map_mul, show unitPoint (g * h) = unitPoint g * unitPoint h from
      map_mul (mapPoint (Algebra.ofId R A)) g h]
    have h₁ : mapPoint (A := A) (rightTranslation g) (toConv (AlgHom.id R A)) =
        toConv (AlgHom.id R A) * unitPoint g := by
      apply WithConv.ext
      ext a
      rfl
    have h₂ : mapPoint (A := A) (rightTranslation g) (unitPoint h) = unitPoint h := by
      apply WithConv.ext
      ext a
      exact (rightTranslation g).commutes (h a)
    rw [h₁, h₂, mul_assoc]

private theorem counit_translation_pow (g : WithConv (A →ₐ[R] R)) (k : ℕ) (a : A) :
    Coalgebra.counit (R := R) ((translation g ^ k) a) = (g ^ k) a := by
  rw [← map_pow translation]
  exact DFunLike.congr_fun (counit_rightTranslation (g ^ k)) a

/-- The trace of a translation annihilates every coordinate of its difference from the identity. -/
theorem translation_trace_annihilates [Module.Free R A] [Module.Finite R A]
    (g : WithConv (A →ₐ[R] R)) (a : A) :
    LinearMap.trace R A (translation g) * (g a - (1 : WithConv (A →ₐ[R] R)) a) = 0 := by
  let T := translation g
  let L : A →ₗ[R] R :=
    (LinearMap.trace R A).comp ((LinearMap.mulRight R T).comp (Algebra.lmul R A).toLinearMap)
  have vanish (b c : A) : L (c * (rightTranslation g b - b)) = 0 := by
    have commute : T * LinearMap.mulLeft R b =
        LinearMap.mulLeft R (rightTranslation g b) * T := by
      ext x
      exact (rightTranslation g).map_mul b x
    have operator :
        LinearMap.mulLeft R (c * (rightTranslation g b - b)) * T =
          LinearMap.mulLeft R c * (T * LinearMap.mulLeft R b) -
          LinearMap.mulLeft R b * (LinearMap.mulLeft R c * T) := by
      rw [commute]
      ext x
      change (c * (rightTranslation g b - b)) * T x =
        c * (rightTranslation g b * T x) - b * (c * T x)
      ring
    change LinearMap.trace R A (LinearMap.mulLeft R (c * (rightTranslation g b - b)) * T) = 0
    rw [operator, map_sub, ← mul_assoc (LinearMap.mulLeft R c),
      LinearMap.trace_mul_comm _ (LinearMap.mulLeft R b), sub_self]
  let r := ℛ R a
  let antipode := HopfAlgebra.antipodeAlgHom R A
  have hprod : toConv antipode * toConv (rightTranslation g) = unitPoint g := by
    change toConv antipode * (toConv (AlgHom.id R A) * unitPoint g) = unitPoint g
    rw [← mul_assoc, AlgHom.antipode_id_cancel, one_mul]
  have hright : ∑ i ∈ r.index, antipode (r.left i) * rightTranslation g (r.right i) =
      algebraMap R A (g a) := by
    have h := congrArg (fun h : WithConv (A →ₐ[R] A) =>
      toConv h.ofConv.toLinearMap) hprod
    rw [AlgHom.toLinearMap_convMul] at h
    have h := DFunLike.congr_fun (congrArg WithConv.ofConv h) a
    exact (r.convMul_apply _ _).symm.trans h
  have hleft : ∑ i ∈ r.index, antipode (r.left i) * r.right i =
      algebraMap R A ((1 : WithConv (A →ₐ[R] R)) a) := by
    simpa [antipode, HopfAlgebra.toLinearMap_antipodeAlgHom, AlgHom.convOne_apply] using
      HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit r
  have hdiff :
      ∑ i ∈ r.index, antipode (r.left i) * (rightTranslation g (r.right i) - r.right i) =
        algebraMap R A (g a - (1 : WithConv (A →ₐ[R] R)) a) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, hright, hleft, map_sub]
  have h := congrArg L hdiff
  rw [map_sum] at h
  simp_rw [vanish, Finset.sum_const_zero] at h
  have halgebra (s : R) : L (algebraMap R A s) = s * LinearMap.trace R A T := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change s * LinearMap.trace R A (LinearMap.mulLeft R (1 : A) * T) = _
    congr 2
    ext x
    exact one_mul _
  rw [halgebra, mul_comm] at h
  exact h.symm

/-- Regard a point as an element of the linear convolution algebra. -/
def linearPoint : WithConv (A →ₐ[R] R) →* WithConv (A →ₗ[R] R) where
  toFun g := toConv g.ofConv.toLinearMap
  map_one' := AlgHom.toLinearMap_convOne
  map_mul' _ _ := AlgHom.toLinearMap_convMul ..

theorem linearPoint_injective : Function.Injective (linearPoint (R := R) (A := A)) :=
  fun _ _ h => WithConv.ext (AlgHom.toLinearMap_injective (WithConv.toConv_injective h))

/-- The characteristic polynomial of right translation by `g` vanishes at every power of `g`
in the linear convolution algebra. -/
theorem translation_charpoly_moments [Nontrivial R] [Module.Free R A] [Module.Finite R A]
    (g : WithConv (A →ₐ[R] R)) {n : ℕ} (rank : Module.finrank R A = n) (k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (translation g).charpoly.coeff j • (linearPoint g ^ j) ^ k = 0 := by
  let T := translation g
  let P := T.charpoly
  have degree : P.natDegree = n := T.charpoly_natDegree.trans rank
  have relation (a : A) : ∑ j ∈ Finset.range (n + 1), P.coeff j * (g ^ j) a = 0 := by
    have ch := T.aeval_self_charpoly
    rw [Polynomial.aeval_eq_sum_range, degree] at ch
    have h := congrArg (fun F : Module.End R A => Bialgebra.counitAlgHom R A (F a)) ch
    simpa [LinearMap.sum_apply, Algebra.smul_def, T, counit_translation_pow] using h
  have linEq (j : ℕ) : (linearPoint g ^ j) ^ k = linearPoint ((g ^ j) ^ k) := by
    rw [← map_pow linearPoint g j, ← map_pow linearPoint (g ^ j) k]
  suffices h : ∑ j ∈ Finset.range (n + 1), P.coeff j • linearPoint ((g ^ j) ^ k) = 0 by
    refine (Finset.sum_congr rfl fun j _ => ?_).trans h
    exact congrArg (fun x => P.coeff j • x) (linEq j)
  apply WithConv.ext
  ext a
  have h := relation (((toConv (AlgHom.id R A)) ^ k) a)
  have pow_apply (j : ℕ) : (g ^ j) (((toConv (AlgHom.id R A)) ^ k) a) = ((g ^ j) ^ k) a := by
    change (mapPoint (g ^ j).ofConv (toConv (AlgHom.id R A) ^ k)) a = _
    rw [map_pow]
    rfl
  simp only [pow_apply] at h
  simp only [WithConv.ofConv_sum, WithConv.ofConv_smul, WithConv.ofConv_zero,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
  exact h

private def differenceIdeal (g h : WithConv (A →ₐ[R] R)) : Ideal R :=
  Ideal.span (Set.range fun a : A => g a - h a)

private theorem differenceIdeal_le_iff (g h : WithConv (A →ₐ[R] R)) (I : Ideal R) :
    differenceIdeal g h ≤ I ↔
      mapPoint (Ideal.Quotient.mkₐ R I) g = mapPoint (Ideal.Quotient.mkₐ R I) h := by
  rw [differenceIdeal, Ideal.span_le]
  constructor
  · intro le
    apply WithConv.ext
    ext a
    exact Ideal.Quotient.eq.mpr (le ⟨a, rfl⟩)
  · intro eq r hr
    obtain ⟨a, rfl⟩ := hr
    exact Ideal.Quotient.eq.mp (DFunLike.congr_fun (congrArg ofConv eq) a)

private theorem pairwise_difference_product [Nontrivial R] [Module.Free R A]
    [Module.Finite R A] (g : WithConv (A →ₐ[R] R)) {n : ℕ}
    (rank : Module.finrank R A = n) :
    (∏ i ∈ Finset.range n, differenceIdeal (g ^ n) (g ^ i)) = ⊥ := by
  classical
  let T := translation g
  let P := T.charpoly
  have degree : P.natDegree = n := T.charpoly_natDegree.trans rank
  have monic : P.coeff n = 1 := by
    rw [← degree]
    exact T.charpoly_monic
  have relation (a : A) : ∑ j ∈ Finset.range (n + 1), P.coeff j * (g ^ j) a = 0 := by
    have ch := T.aeval_self_charpoly
    rw [Polynomial.aeval_eq_sum_range, degree] at ch
    have h := congrArg (fun F : Module.End R A => Bialgebra.counitAlgHom R A (F a)) ch
    simpa [LinearMap.sum_apply, Algebra.smul_def, T, counit_translation_pow] using h
  refine le_antisymm ?_ bot_le
  simp only [differenceIdeal, Ideal.prod_span, Ideal.span_le]
  intro x hx
  obtain ⟨v, hv, rfl⟩ := (Set.mem_finsetProd _ _ _).mp hx
  have witnesses (i : ℕ) : i ∈ Finset.range n → ∃ a : A, (g ^ n) a - (g ^ i) a = v i :=
    fun hi => hv hi
  let a (i : ℕ) : A := if hi : i ∈ Finset.range n then (witnesses i hi).choose else 0
  have ha (i : ℕ) (hi : i ∈ Finset.range n) : (g ^ n) (a i) - (g ^ i) (a i) = v i := by
    simpa only [a, dif_pos hi] using (witnesses i hi).choose_spec
  let b := ∏ i ∈ Finset.range n, (a i - algebraMap R A ((g ^ i) (a i)))
  have ev (j : ℕ) :
      (g ^ j) b = ∏ i ∈ Finset.range n, ((g ^ j) (a i) - (g ^ i) (a i)) := by
    change (g ^ j).ofConv b = _
    simp only [b, map_prod, map_sub, AlgHom.commutes]
    rfl
  have eliminate (j : ℕ) (hj : j ∈ Finset.range n) : (g ^ j) b = 0 := by
    rw [ev]
    exact Finset.prod_eq_zero hj (sub_self _)
  have h := relation b
  rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
    rw [eliminate j hj, mul_zero]), zero_add, monic, one_mul, ev] at h
  apply (Submodule.mem_bot R).mpr
  rwa [Finset.prod_congr rfl ha] at h

private theorem factorial_difference_nilpotent [Nontrivial R] [Module.Free R A]
    [Module.Finite R A] (g : WithConv (A →ₐ[R] R)) {n : ℕ}
    (rank : Module.finrank R A = n) :
    differenceIdeal (g ^ n.factorial) 1 ^ n = ⊥ := by
  let I := differenceIdeal (g ^ n.factorial) 1
  have contained (i : ℕ) (hi : i ∈ Finset.range n) : I ≤ differenceIdeal (g ^ n) (g ^ i) := by
    let J := differenceIdeal (g ^ n) (g ^ i)
    let π := mapPoint (A := A) (Ideal.Quotient.mkₐ R J)
    have hi' := Finset.mem_range.mp hi
    have small : (π g) ^ (n - i) = 1 := by
      rw [← map_pow, pow_sub _ hi'.le, map_mul,
        show π (g ^ n) = π (g ^ i) from (differenceIdeal_le_iff (g ^ n) (g ^ i) J).mp le_rfl,
        ← map_mul, mul_inv_cancel, map_one]
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hi') (Nat.sub_le n i)
    apply (differenceIdeal_le_iff _ _ J).mpr
    change π (g ^ n.factorial) = π 1
    rw [map_pow, map_one, hk, pow_mul, small, one_pow]
  apply le_antisymm _ bot_le
  calc
    I ^ n = ∏ _i ∈ Finset.range n, I := by simp
    _ ≤ ∏ i ∈ Finset.range n, differenceIdeal (g ^ n) (g ^ i) := by
      exact Finset.prod_le_prod' (fun i hi => contained i hi)
    _ = ⊥ := pairwise_difference_product g rank

private theorem natCast_mul_difference_le [Nontrivial R] [Module.Free R A] [Module.Finite R A]
    (g : WithConv (A →ₐ[R] R)) {n : ℕ} (rank : Module.finrank R A = n) :
    Ideal.span ({(n : R)} : Set R) * differenceIdeal g 1 ≤ differenceIdeal g 1 ^ 2 := by
  classical
  let I := differenceIdeal g 1
  let b := Module.Free.chooseBasis R A
  let T := translation g
  have trace_mod : LinearMap.trace R A (1 - T) ∈ I := by
    rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
    refine I.sum_mem fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    let r := ℛ R (b i)
    have hp : (1 - T) (b i) =
        ∑ j ∈ r.index, ((1 : WithConv (A →ₐ[R] R)) (r.right j) - g (r.right j)) • r.left j := by
      have entry (g' : WithConv (A →ₐ[R] R)) :
          translation g' (b i) = ∑ j ∈ r.index, g' (r.right j) • r.left j := by
        change (toConv (LinearMap.id : A →ₗ[R] A) *
          toConv (unitPoint g').ofConv.toLinearMap).ofConv (b i) = _
        rw [r.convMul_apply]
        simp [Algebra.smul_def, mul_comm]
        rfl
      change (1 : Module.End R A) (b i) - T (b i) = _
      rw [← map_one translation, entry, show T = translation g from rfl, entry]
      simp_rw [sub_smul, Finset.sum_sub_distrib]
    rw [hp, map_sum, Finsupp.finsetSum_apply]
    refine I.sum_mem fun j _ => ?_
    have mem : g (r.right j) - (1 : WithConv (A →ₐ[R] R)) (r.right j) ∈ I :=
      Ideal.subset_span ⟨r.right j, rfl⟩
    convert I.mul_mem_left (b.repr (r.left j) i) (I.neg_mem mem) using 1
    simp [sub_eq_add_neg, mul_comm]
  have htrace : (n : R) - LinearMap.trace R A T ∈ I := by
    simpa only [map_sub, LinearMap.trace_one, rank] using trace_mod
  change Ideal.span _ * Ideal.span (Set.range _) ≤ I ^ 2
  rw [Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨t, ht, _, ⟨a, rfl⟩, rfl⟩
  rw [Set.mem_singleton_iff.mp ht]
  let d := g a - (1 : WithConv (A →ₐ[R] R)) a
  have hd : d ∈ I := Ideal.subset_span ⟨a, rfl⟩
  have hz : LinearMap.trace R A T * d = 0 := translation_trace_annihilates g a
  change (n : R) * d ∈ I ^ 2
  have heq : (n : R) * d = ((n : R) - LinearMap.trace R A T) * d := by
    rw [sub_mul, hz, sub_zero]
  rw [heq, pow_two]
  exact Ideal.mul_mem_mul htrace hd

private theorem differenceIdeal_pow_le (I : Ideal R) (n k : ℕ) (hk : 0 < k)
    (scale : Ideal.span ({(n : R)} : Set R) * I ≤ I ^ 2)
    (g : WithConv (A →ₐ[R] R)) (hg : differenceIdeal g 1 ≤ I ^ k) :
    differenceIdeal (g ^ n) 1 ≤ I ^ (k + 1) := by
  let J := I ^ (k + 1)
  let π := Ideal.Quotient.mkₐ R J
  let p := mapPoint (A := A) π g
  let f : WithConv (A →ₗ[R] R ⧸ J) := toConv p.ofConv.toLinearMap
  let d := f - 1
  have apply_d (a : A) : d.ofConv a = π (g a - (1 : WithConv (A →ₐ[R] R)) a) := by
    rw [map_sub]
    rfl
  have mem (a : A) : g a - (1 : WithConv (A →ₐ[R] R)) a ∈ I ^ k :=
    hg (Ideal.subset_span ⟨a, rfl⟩)
  have d_squared : d * d = 0 := by
    apply WithConv.ext
    ext a
    let r := ℛ R a
    rw [r.convMul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [apply_d, apply_d, ← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.pow_le_pow_right (by omega : k + 1 ≤ k + k)
      (by rw [pow_add]; exact Ideal.mul_mem_mul (mem _) (mem _))
  have scalePow : Ideal.span ({(n : R)} : Set R) * I ^ k ≤ I ^ (k + 1) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [pow_succ' I, ← mul_assoc]
    calc
      _ ≤ I ^ 2 * I ^ j := Ideal.mul_mono_left scale
      _ = _ := by rw [← pow_add]; congr 1; omega
  have d_scaled : n • d = 0 := by
    apply WithConv.ext
    ext a
    change n • d.ofConv a = 0
    rw [apply_d, ← map_nsmul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [nsmul_eq_mul]
    exact scalePow (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (mem a))
  have pformula (j : ℕ) : f ^ j = 1 + j • d := by
    induction j with
    | zero => simp
    | succ j ih =>
      have df : d * f = d := by
        calc
          _ = d * (1 + d) := by rw [show f = 1 + d from by simp [d]]
          _ = d := by rw [mul_add, mul_one, d_squared, add_zero]
      rw [pow_succ, ih, add_mul, one_mul, smul_mul_assoc, df, succ_nsmul]
      have hf : f = 1 + d := by simp [d]
      rw [hf]
      abel
  have finish : f ^ n = 1 := by rw [pformula, d_scaled, add_zero]
  apply (differenceIdeal_le_iff _ _ J).mpr
  rw [map_pow, map_one]
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convPow, AlgHom.toLinearMap_convOne]
  exact finish

theorem factorialBound_kills_point [Nontrivial R] [Module.Free R A] [Module.Finite R A]
    (g : WithConv (A →ₐ[R] R)) {n : ℕ} (hn : 0 < n) (rank : Module.finrank R A = n) :
    g ^ factorialBound n = 1 := by
  let h := g ^ n.factorial
  let I := differenceIdeal h 1
  have scale : Ideal.span ({(n : R)} : Set R) * I ≤ I ^ 2 :=
    natCast_mul_difference_le h rank
  have nilpotent : I ^ n = ⊥ := factorial_difference_nilpotent g rank
  have iterate (j : ℕ) : differenceIdeal (h ^ (n ^ j)) 1 ≤ I ^ (j + 1) := by
    induction j with
    | zero => simp [I]
    | succ j ih =>
      rw [pow_succ n j, pow_mul]
      exact differenceIdeal_pow_le I n (j + 1) (Nat.succ_pos _) scale _ ih
  have bound := iterate (n - 1)
  rw [Nat.sub_add_cancel hn, nilpotent] at bound
  rw [factorialBound, pow_mul]
  apply WithConv.ext
  ext a
  have hx := bound (Ideal.subset_span (s := Set.range _) ⟨a, rfl⟩)
  exact sub_eq_zero.mp ((Submodule.mem_bot R).mp hx)

private def tensorRepr {a : A} {ι : Type*} (r : Coalgebra.Repr R a ι) :
    Coalgebra.Repr S ((1 : S) ⊗ₜ[R] a) ι where
  index := r.index
  left i := (1 : S) ⊗ₜ[R] r.left i
  right i := (1 : S) ⊗ₜ[R] r.right i
  eq := by
    rw [TensorProduct.comul_tmul, ← r.eq]
    simp [TensorProduct.tmul_sum]

def baseChangePoint :
    WithConv (A →ₐ[R] S) →* WithConv (S ⊗[R] A →ₐ[S] S) where
  toFun g := toConv (AlgHom.liftEquiv R S A S g.ofConv)
  map_one' := by
    apply WithConv.ext
    apply (AlgHom.liftEquiv R S A S).symm.injective
    ext a
    simp [AlgHom.convOne_apply, TensorProduct.counit_tmul, Algebra.smul_def]
  map_mul' f g := by
    apply WithConv.ext
    apply (AlgHom.liftEquiv R S A S).symm.injective
    ext a
    let r := ℛ R a
    simp only [AlgHom.liftEquiv_symm_apply, AlgHom.liftEquiv_tmul, one_smul]
    change (f * g) a =
      (toConv (AlgHom.liftEquiv R S A S f.ofConv) *
        toConv (AlgHom.liftEquiv R S A S g.ofConv)) ((1 : S) ⊗ₜ[R] a)
    rw [convolution_apply_repr r, convolution_apply_repr (tensorRepr (S := S) r)]
    simp [tensorRepr, AlgHom.liftEquiv_tmul]

theorem baseChangePoint_injective :
    Function.Injective (baseChangePoint (R := R) (A := A) (S := S)) := by
  intro g h eq
  apply WithConv.ofConv_injective
  exact (AlgHom.liftEquiv R S A S).injective (congrArg ofConv eq)

/-- A power map is trivial when it kills points over the localizations used to test it. -/
theorem isKilledBy_of_localized_points (n : ℕ+) (m : ℕ)
    [Module.Finite R A] [Module.Projective R A]
    (rank : Module.rankAtStalk (R := R) A = fun _ => (n : ℕ))
    (killPoint : ∀ (p : Ideal A) [p.IsMaximal],
      let K := Localization.AtPrime p
      ∀ [Module.Free K (K ⊗[R] A)] (g : WithConv ((K ⊗[R] A) →ₐ[K] K)),
        Module.finrank K (K ⊗[R] A) = (n : ℕ) → g ^ m = 1) :
    IsKilledBy R A m := by
  apply WithConv.ext
  ext a
  apply Module.eq_of_localization_maximal (R := A)
    (Mₚ := fun p _ => Localization.AtPrime p) (fun p _ => Algebra.linearMap A (Localization.AtPrime p))
  intro p hp
  let S := Localization.AtPrime p
  let f : A →ₐ[R] S := IsScalarTower.toAlgHom R A S
  let g := (mapPoint f) (toConv (AlgHom.id R A))
  let : Module.Free S (S ⊗[R] A) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank S (S ⊗[R] A) = (n : ℕ) := by
    let q : PrimeSpectrum S := ⟨IsLocalRing.maximalIdeal S, inferInstance⟩
    have hq := Module.rankAtStalk_baseChange (R := R) (M := A) q
    rw [Module.rankAtStalk_eq_finrank_of_free, rank] at hq
    exact hq
  have h := killPoint p (baseChangePoint g) hr
  have kill : g ^ m = 1 := baseChangePoint_injective (by
    rw [map_pow, map_one]
    exact h)
  have eq : mapPoint f (toConv (AlgHom.id R A) ^ m) = mapPoint f 1 := by
    rw [map_pow, map_one]
    exact kill
  exact DFunLike.congr_fun (congrArg ofConv eq) a

/-- It suffices to test Hopf algebras with an explicitly indexed basis. -/
theorem isUniversalKillingExponent_iff_basis (n m : ℕ+) :
    IsUniversalKillingExponent.{0, 0} n m ↔
      ∀ (K : Type) [CommRing K] [Nontrivial K] (B : Type) [CommRing B]
        [HopfAlgebra K B], Module.Basis (Fin (n : ℕ)) K B → IsKilledBy K B m := by
  constructor
  · intro h K _ _ B _ _ b
    let : Module.Free K B := Module.Free.of_basis b
    let : Module.Finite K B := Module.Finite.of_basis b
    apply h K B
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis b, Fintype.card_fin]
    rfl
  · intro h K _ B _ _ _ _ rank
    apply isKilledBy_of_localized_points n m rank
    intro p _ L _ g hr
    let C := L ⊗[K] B
    have hc := h L C (Module.finBasisOfFinrankEq L C hr)
    let π : WithConv (C →ₐ[L] C) →* WithConv (C →ₐ[L] L) := mapPoint g.ofConv
    let idPoint := toConv (AlgHom.id L C)
    have hpoint : π idPoint = g := by
      apply WithConv.ext
      ext a
      rfl
    calc
      g ^ (m : ℕ) = π (idPoint ^ (m : ℕ)) :=
        ((map_pow π idPoint (m : ℕ)).trans (congrArg (fun x => x ^ (m : ℕ)) hpoint)).symm
      _ = π 1 := congrArg π hc
      _ = 1 := map_one π

/-- The explicit factorial bound kills every finite locally free group scheme of rank `n`. -/
theorem isKilledBy_factorialBound (n : ℕ+) [Module.Finite R A] [Module.Projective R A]
    (rank : Module.rankAtStalk (R := R) A = fun _ => (n : ℕ)) :
    IsKilledBy R A (factorialBound n) := by
  apply isKilledBy_of_localized_points n (factorialBound n) rank
  intro p _ _ _ g hr
  exact factorialBound_kills_point g n.pos hr

private def factorialBoundPNat (n : ℕ+) : ℕ+ :=
  ⟨factorialBound n, Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos n.pos)⟩

theorem isUniversalKillingExponent_factorialBound (n : ℕ+) :
    IsUniversalKillingExponent.{0, 0} n (factorialBoundPNat n) := by
  intro R _ A _ _ _ _ rank
  exact isKilledBy_factorialBound n rank

private abbrev exponentSet (n : ℕ+) : Set ℕ :=
  ((↑) '' {m | IsUniversalKillingExponent.{0, 0} n m} : Set ℕ)

theorem exponentSet_nonempty (n : ℕ+) : (exponentSet n).Nonempty :=
  ⟨factorialBound n, factorialBoundPNat n, isUniversalKillingExponent_factorialBound n, rfl⟩

theorem sInf_exponent_pos (n : ℕ+) : 0 < sInf (exponentSet n) := by
  obtain ⟨m, _, hm⟩ := (isLeast_csInf (exponentSet_nonempty n)).1
  exact hm ▸ m.pos

/-- Every universal exponent is a multiple of the degree, as witnessed by `μₙ`. -/
theorem rank_dvd_universalExponent (n m : ℕ+)
    (hm : IsUniversalKillingExponent.{0, 0} n m) : (n : ℕ) ∣ (m : ℕ) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let D := Multiplicative (ZMod (n : ℕ))
  let g : D := Multiplicative.ofAdd 1
  have hk := isKilledBy_of_isUniversalKillingExponent n m hm ℚ
  have h := DFunLike.congr_fun (congrArg ofConv hk) (MonoidAlgebra.single g (1 : ℚ))
  rw [pow_apply_single] at h
  have hg : g ^ (m : ℕ) = 1 := by
    have h₁ :
        (1 : WithConv (MonoidAlgebra ℚ D →ₐ[ℚ] MonoidAlgebra ℚ D)).ofConv
          (MonoidAlgebra.single g (1 : ℚ)) = MonoidAlgebra.single 1 1 := by
      change algebraMap ℚ (MonoidAlgebra ℚ D)
        (Coalgebra.counit (R := ℚ) (MonoidAlgebra.single g (1 : ℚ))) = MonoidAlgebra.single 1 1
      rw [MonoidAlgebra.counit_single]
      simp
    apply (MonoidAlgebra.single_left_inj (one_ne_zero (α := ℚ))).mp
    exact h.trans h₁
  have hg' : ((m : ℕ) : ZMod (n : ℕ)) = 0 := by
    have h := congrArg Multiplicative.toAdd hg
    change (m : ℕ) • (1 : ZMod (n : ℕ)) = 0 at h
    simpa [nsmul_eq_mul] using h
  exact (ZMod.natCast_eq_zero_iff _ _).mp hg'

theorem rank_dvd_sInf_exponent (n : ℕ+) : (n : ℕ) ∣ sInf (exponentSet n) := by
  obtain ⟨m, hm, heq⟩ := (isLeast_csInf (exponentSet_nonempty n)).1
  rw [← heq]
  exact rank_dvd_universalExponent n m hm

theorem sInf_exponent_dvd_of_universal (n m : ℕ+)
    (hm : IsUniversalKillingExponent.{0, 0} n m) : sInf (exponentSet n) ∣ (m : ℕ) := by
  have least := isLeast_csInf (exponentSet_nonempty n)
  obtain ⟨e, he, heq⟩ := least.1
  rw [← heq, Nat.dvd_iff_mod_eq_zero]
  let k := (m : ℕ) % (e : ℕ)
  by_contra hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let r : ℕ+ := ⟨k, hkpos⟩
  have hr : IsUniversalKillingExponent.{0, 0} n r := by
    intro R _ A _ _ _ _ rank
    let g := toConv (AlgHom.id R A)
    have heA : g ^ (e : ℕ) = 1 := he R A rank
    have hmA : g ^ (m : ℕ) = 1 := hm R A rank
    change g ^ k = 1
    calc
      g ^ k = g ^ ((e : ℕ) * ((m : ℕ) / (e : ℕ)) + k) := by
        rw [pow_add, pow_mul, heA, one_pow, one_mul]
      _ = 1 := by rw [show (e : ℕ) * ((m : ℕ) / (e : ℕ)) + k = m from Nat.div_add_mod _ _, hmA]
  have hkr : k ∈ exponentSet n := ⟨r, hr, rfl⟩
  have hle := least.2 hkr
  rw [← heq] at hle
  exact (Nat.not_le_of_lt (Nat.mod_lt _ e.pos)) hle

theorem sInf_exponent_dvd_factorialBound (n : ℕ+) :
    sInf (exponentSet n) ∣ factorialBound n :=
  sInf_exponent_dvd_of_universal n _ (isUniversalKillingExponent_factorialBound n)

/-- To certify an exact value, rule out the proper divisors of a known universal exponent. -/
theorem optimal_exponent_of_excluding_proper_divisors (n u : ℕ+)
    (upper : IsUniversalKillingExponent.{0, 0} n u)
    (exclude : ∀ m : ℕ+, (m : ℕ) ∣ (u : ℕ) → (m : ℕ) < (u : ℕ) →
      ¬ IsUniversalKillingExponent.{0, 0} n m) :
    sInf (exponentSet n) = (u : ℕ) := by
  have least := isLeast_csInf (exponentSet_nonempty n)
  obtain ⟨m, hm, heq⟩ := least.1
  have hd := sInf_exponent_dvd_of_universal n u upper
  have hle := least.2 (show (u : ℕ) ∈ exponentSet n from ⟨u, upper, rfl⟩)
  apply le_antisymm hle
  by_contra! hlt
  rw [← heq] at hlt hd
  exact exclude m hd hlt hm

theorem rank_one_optimal_exponent :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} 1 m} : Set ℕ) = 1 := by
  apply le_antisymm
  · apply (isLeast_csInf (exponentSet_nonempty 1)).2
    simpa [factorialBound] using
      (show factorialBound (1 : ℕ+) ∈ exponentSet 1 from
        ⟨factorialBoundPNat 1, isUniversalKillingExponent_factorialBound 1, rfl⟩)
  · exact sInf_exponent_pos 1

theorem exists_idealCertificate_iff {B ι : Type*} [CommRing B] [DecidableEq B] [Fintype ι]
    (relations : ι → B) (target : B) :
    (∃ multipliers, checkIdealCertificate relations target multipliers = true) ↔
      target ∈ Ideal.span (Set.range relations) := by
  simp only [checkIdealCertificate, decide_eq_true_eq, Ideal.mem_span_range_iff_exists_fun]

/-- The quotient by the relations is itself a test ring. Therefore membership of a target in
the relation ideal is equivalent to vanishing at every assignment satisfying the equations. -/
theorem mem_relationIdeal_iff_forall_eval {σ : Type u} {ι : Type*}
    (relations : ι → MvPolynomial σ ℤ) (target : MvPolynomial σ ℤ) :
    target ∈ Ideal.span (Set.range relations) ↔
      ∀ (B : Type u) [CommRing B] (assignment : σ → B),
        (∀ i, MvPolynomial.eval₂ (Int.castRingHom B) assignment (relations i) = 0) →
        MvPolynomial.eval₂ (Int.castRingHom B) assignment target = 0 := by
  let I := Ideal.span (Set.range relations)
  constructor
  · intro ht B _ assignment eqs
    let ev := MvPolynomial.eval₂Hom (Int.castRingHom B) assignment
    have hI : I ≤ RingHom.ker ev := Ideal.span_le.mpr <| by
      rintro _ ⟨i, rfl⟩
      exact eqs i
    exact hI ht
  · intro h
    let q := Ideal.Quotient.mk I
    let assignment (x : σ) := q (MvPolynomial.X x)
    have heval : MvPolynomial.eval₂Hom (Int.castRingHom (_ ⧸ I)) assignment = q := by
      ext x <;> simp [assignment]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hs (i : ι) : q (relations i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    have heqs (i : ι) : MvPolynomial.eval₂ (Int.castRingHom (_ ⧸ I)) assignment (relations i) = 0 := by
      change (MvPolynomial.eval₂Hom _ _) _ = 0
      rw [heval, hs]
    have ht := h (_ ⧸ I) assignment heqs
    change (MvPolynomial.eval₂Hom _ _) target = 0 at ht
    rwa [heval] at ht

/-- If a Boolean test recognizes the universal exponents up to the explicit bound,
the search returns the value required by FC. This theorem assumes correctness of the test. -/
theorem boundedExponentSearch_spec (n : ℕ+) (accept : ℕ → Bool)
    (correct : ∀ m : ℕ+, (m : ℕ) ≤ factorialBound n →
      (accept m = true ↔ IsUniversalKillingExponent.{0, 0} n m)) :
    sInf ((↑) '' {m | IsUniversalKillingExponent.{0, 0} n m} : Set ℕ) =
      boundedExponentSearch n accept := by
  let s := (Finset.Icc 1 (factorialBound n)).filter (fun m => accept m = true)
  have least := isLeast_csInf (exponentSet_nonempty n)
  obtain ⟨m, hm, hmeq⟩ := least.1
  have hu : (m : ℕ) ≤ factorialBound n := by
    rw [hmeq]
    exact least.2 ⟨factorialBoundPNat n, isUniversalKillingExponent_factorialBound n, rfl⟩
  have hm' : (m : ℕ) ∈ s := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨m.pos, hu⟩, (correct m hu).mpr hm⟩
  have hmin : s.min = ((m : ℕ) : WithTop ℕ) := by
    apply le_antisymm (Finset.min_le hm')
    apply Finset.le_min
    intro k hk
    obtain ⟨hinterval, hcheck⟩ := Finset.mem_filter.mp hk
    obtain ⟨hpos, hkbound⟩ := Finset.mem_Icc.mp hinterval
    let p : ℕ+ := ⟨k, hpos⟩
    exact_mod_cast hmeq.symm ▸ least.2 (show k ∈ exponentSet n from
      ⟨p, (correct p hkbound).mp hcheck, rfl⟩)
  rw [← hmeq]
  change (m : ℕ) = s.min.untopD 0
  rw [hmin]
  rfl

end
end FiniteLocallyFreeGroupSchemeExponent

open FiniteLocallyFreeGroupSchemeExponent in
#guard boundedExponentSearch 2 (fun n => n % 2 == 0) == 2

#print axioms FiniteLocallyFreeGroupSchemeExponent.isUniversalKillingExponent_factorialBound
#print axioms FiniteLocallyFreeGroupSchemeExponent.isUniversalKillingExponent_iff_basis
#print axioms FiniteLocallyFreeGroupSchemeExponent.sInf_exponent_dvd_factorialBound
#print axioms FiniteLocallyFreeGroupSchemeExponent.rank_dvd_sInf_exponent
#print axioms FiniteLocallyFreeGroupSchemeExponent.boundedExponentSearch_spec
#print axioms FiniteLocallyFreeGroupSchemeExponent.rank_one_optimal_exponent
#print axioms FiniteLocallyFreeGroupSchemeExponent.exists_idealCertificate_iff
#print axioms FiniteLocallyFreeGroupSchemeExponent.mem_relationIdeal_iff_forall_eval
