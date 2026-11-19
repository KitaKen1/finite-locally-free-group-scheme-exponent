import OptimalExponent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Ring.GeomSum

/-! A point over a field has order dividing the dimension of the coordinate algebra. -/

open WithConv
open scoped TensorProduct Coalgebra

namespace FiniteLocallyFreeGroupSchemeExponent

noncomputable section

section Field

variable {K A : Type*} [Field K] [CommRing A] [HopfAlgebra K A] [Module.Finite K A]

private abbrev Pts := WithConv (A →ₐ[K] K)

private theorem point_surjective (f : Pts (K := K) (A := A)) :
    Function.Surjective f.ofConv := fun c => ⟨algebraMap K A c, f.ofConv.commutes c⟩

private def pointIdeal (f : Pts (K := K) (A := A)) : MaximalSpectrum A :=
  ⟨RingHom.ker (f.ofConv : A →+* K),
    RingHom.ker_isMaximal_of_surjective _ (point_surjective f)⟩

private theorem pointIdeal_injective :
    Function.Injective (pointIdeal (K := K) (A := A)) := by
  intro f g he
  apply WithConv.ext
  ext a
  let b := a - algebraMap K A (f a)
  have h : b ∈ (pointIdeal f).asIdeal := by
    change f.ofConv b = 0
    simp [b]
  rw [he] at h
  change g.ofConv b = 0 at h
  have h' : g.ofConv a - f.ofConv a = 0 := by simpa [b] using h
  exact (sub_eq_zero.mp h').symm

private theorem pointIdeal_surjective [IsAlgClosed K] :
    Function.Surjective (pointIdeal (K := K) (A := A)) := by
  intro i
  let I := i.asIdeal
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  let e : K ≃ₐ[K] A ⧸ I := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ I))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let f := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K I)
  use toConv f
  apply MaximalSpectrum.ext
  ext a
  change e.symm ((Ideal.Quotient.mk I) a) = 0 ↔ a ∈ I
  rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

private def translationEquiv (g : Pts (K := K) (A := A)) : A ≃ₐ[K] A :=
  AlgEquiv.ofAlgHom (rightTranslation g) (rightTranslation g⁻¹)
    (by
      apply AlgHom.toLinearMap_injective
      change translation g * translation g⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one])
    (by
      apply AlgHom.toLinearMap_injective
      change translation g⁻¹ * translation g = 1
      rw [← map_mul, inv_mul_cancel, map_one])

private theorem pointIdeal_map_translation (g : Pts (K := K) (A := A)) :
    (pointIdeal g).asIdeal.map (translationEquiv g : A →ₐ[K] A).toRingHom =
      (pointIdeal (1 : Pts (K := K) (A := A))).asIdeal := by
  have e : (pointIdeal g).asIdeal =
      (pointIdeal (1 : Pts (K := K) (A := A))).asIdeal.comap
        (translationEquiv g : A →ₐ[K] A).toRingHom := by
    ext a
    have h := DFunLike.congr_fun (counit_rightTranslation g) a
    change g a = 0 ↔ (Bialgebra.counitAlgHom K A) (rightTranslation g a) = 0
    change (Bialgebra.counitAlgHom K A) (rightTranslation g a) = g a at h
    rw [h]
  rw [e]
  exact Ideal.map_comap_of_surjective _ (translationEquiv g).surjective _

private theorem orderOf_dvd_finrank_algClosed [IsAlgClosed K]
    (g : Pts (K := K) (A := A)) : orderOf g ∣ Module.finrank K A := by
  classical
  letI : IsArtinianRing A := isArtinian_of_tower K (S := A) (M := A) inferInstance
  letI := Fintype.ofFinite (MaximalSpectrum A)
  let points := Equiv.ofBijective (pointIdeal (K := K) (A := A))
    ⟨pointIdeal_injective, pointIdeal_surjective⟩
  letI : Fintype (Pts (K := K) (A := A)) := Fintype.ofEquiv _ points.symm
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_nilradical (R := A)
  let V (i : MaximalSpectrum A) := A ⧸ i.asIdeal ^ k
  let I₁ := pointIdeal (1 : Pts (K := K) (A := A))
  have dimensions (i : MaximalSpectrum A) : Module.finrank K (V i) = Module.finrank K (V I₁) := by
    obtain ⟨f, rfl⟩ := pointIdeal_surjective (K := K) i
    let e := Ideal.quotientEquivAlg ((pointIdeal f).asIdeal ^ k) (I₁.asIdeal ^ k)
      (translationEquiv f) (by rw [Ideal.map_pow]; exact congrArg (· ^ k) (pointIdeal_map_translation f).symm)
    exact e.toLinearEquiv.finrank_eq
  let E : A ≃ₐ[A] ∀ i, V i :=
    (AlgEquiv.quotientBot A A).symm.trans <|
      (Ideal.quotientEquivAlgOfEq A hk.symm).trans (IsArtinianRing.quotNilradicalPowEquivPi A k)
  have hn := (E.restrictScalars K).toLinearEquiv.finrank_eq
  rw [Module.finrank_pi_fintype] at hn
  simp only [dimensions, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  rw [hn, ← Fintype.card_congr points]
  exact (orderOf_dvd_card (x := g)).trans (dvd_mul_right _ _)

/-- Over a field, every point of a finite-dimensional commutative Hopf algebra has order
dividing its dimension. -/
theorem orderOf_point_dvd_finrank (g : Pts (K := K) (A := A)) :
    orderOf g ∣ Module.finrank K A := by
  let L := AlgebraicClosure K
  let f : K →ₐ[K] L := Algebra.ofId K L
  let G := (baseChangePoint (R := K) (A := A) (S := L)).comp (mapPoint f)
  have inj : Function.Injective G := by
    apply (baseChangePoint_injective (R := K) (A := A) (S := L)).comp
    intro g h eq
    apply WithConv.ext
    ext a
    exact (algebraMap K L).injective (DFunLike.congr_fun (congrArg ofConv eq) a)
  have h := orderOf_dvd_finrank_algClosed (G g)
  rw [orderOf_injective _ inj, Module.finrank_baseChange] at h
  exact h

end Field

section Local

variable {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Free R A] [Module.Finite R A]

local notation "F" => IsLocalRing.ResidueField R

def residuePoint : WithConv (A →ₐ[R] R) →* WithConv ((F ⊗[R] A) →ₐ[F] F) :=
  (baseChangePoint (R := R) (A := A) (S := F)).comp (mapPoint (Algebra.ofId R F))

/-- On the closed fibre, the power corresponding to the rank is trivial. -/
theorem residuePoint_pow_finrank (g : WithConv (A →ₐ[R] R)) :
    residuePoint (g ^ Module.finrank R A) = 1 := by
  rw [map_pow]
  apply orderOf_dvd_iff_pow_eq_one.mp
  simpa only [Module.finrank_baseChange] using orderOf_point_dvd_finrank (residuePoint g)

private theorem translation_residue_entry (g : WithConv (A →ₐ[R] R))
    (a : A) (f : A →ₗ[R] R) (hg : residuePoint g = 1) :
    IsLocalRing.residue R (f (translation g a)) = IsLocalRing.residue R (f a) := by
  let ρ := Algebra.ofId R F
  have he : mapPoint ρ g = 1 := by
    apply baseChangePoint_injective (R := R) (A := A) (S := F)
    rw [map_one]
    exact hg
  have hk (a' : A) : IsLocalRing.residue R (g a') =
      IsLocalRing.residue R ((1 : WithConv (A →ₐ[R] R)) a') :=
    DFunLike.congr_fun (congrArg ofConv (he.trans (map_one (mapPoint ρ)).symm)) a'
  let r := ℛ R a
  have entry (g' : WithConv (A →ₐ[R] R)) :
      translation g' a = ∑ j ∈ r.index, g' (r.right j) • r.left j := by
    change (toConv (LinearMap.id : A →ₗ[R] A) *
      toConv (((Algebra.ofId R A).comp g'.ofConv).toLinearMap)).ofConv a = _
    rw [r.convMul_apply]
    simp [Algebra.smul_def, mul_comm]
  calc
    _ = IsLocalRing.residue R (f (translation (1 : WithConv (A →ₐ[R] R)) a)) := by
      rw [entry, entry]
      simp [map_sum, map_smul, smul_eq_mul, map_mul, hk]
    _ = _ := by rw [map_one]; rfl

private theorem isUnit_of_residue_ne_zero {x : R} (h : IsLocalRing.residue R x ≠ 0) :
    IsUnit x :=
  IsLocalRing.notMem_maximalIdeal.mp (fun hx => h ((IsLocalRing.residue_eq_zero_iff _).mpr hx))

/-- In invertible rank, a point trivial on the closed fibre is trivial. -/
theorem point_eq_one_of_residue_of_rank_unit (g : WithConv (A →ₐ[R] R))
    (hg : residuePoint g = 1) (unit : IsUnit (Module.finrank R A : R)) : g = 1 := by
  let b := Module.Free.chooseBasis R A
  let trace := LinearMap.trace R A (translation g)
  have traceEval : IsLocalRing.residue R trace =
      IsLocalRing.residue R (Module.finrank R A : R) := by
    have h : IsLocalRing.residue R trace =
        IsLocalRing.residue R (LinearMap.trace R A (translation (1 : WithConv (A →ₐ[R] R)))) := by
      rw [show trace = LinearMap.trace R A (translation g) from rfl,
        LinearMap.trace_eq_matrix_trace R b, LinearMap.trace_eq_matrix_trace R b]
      simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_one]
      exact translation_residue_entry g (b i) ((Finsupp.lapply i).comp b.repr.toLinearMap) hg
    rw [h, map_one, LinearMap.trace_one]
  have hunit : IsUnit trace := isUnit_of_residue_ne_zero (by
    rw [traceEval]
    exact (unit.map (IsLocalRing.residue R)).ne_zero)
  apply WithConv.ext
  ext a
  have h := translation_trace_annihilates g a
  exact sub_eq_zero.mp ((hunit.mul_left_cancel (h.trans (mul_zero _).symm)))

/-- The kernel on points of passage to the closed fibre has no prime-to-residue torsion. -/
theorem point_eq_one_of_residue_of_pow_unit (g : WithConv (A →ₐ[R] R)) (d : ℕ)
    (hg : residuePoint g = 1) (hd : g ^ d = 1) (unit : IsUnit (d : F)) : g = 1 := by
  classical
  let b := Module.Free.chooseBasis R A
  let M := LinearMap.toMatrixAlgEquiv b (translation g)
  let ρ := IsLocalRing.residue R
  have Mred : ρ.mapMatrix M = 1 := by
    ext i j
    have hM : M = LinearMap.toMatrix b b (translation g) := rfl
    simp only [RingHom.mapMatrix_apply, hM, Matrix.map_apply, LinearMap.toMatrix_apply]
    rw [Matrix.one_apply, ← map_one ρ, ← map_zero ρ, ← apply_ite ρ]
    change IsLocalRing.residue R (((Finsupp.lapply i).comp b.repr.toLinearMap) (translation g (b j))) = _
    rw [translation_residue_entry g _ _ hg]
    simp [ρ, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  let U := ∑ i ∈ Finset.range d, M ^ i
  have Ured : ρ.mapMatrix U = (d : F) • 1 := by
    simp [U, map_sum, map_pow, Mred]
    rw [← Algebra.algebraMap_eq_smul_one, map_natCast]
  have udet : IsUnit U.det := by
    apply isUnit_of_residue_ne_zero
    change ρ U.det ≠ 0
    rw [RingHom.map_det, Ured, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ unit.ne_zero
  have Mu : M ^ d = 1 := by
    dsimp [M]
    rw [← map_pow, ← map_pow, hd, map_one, map_one]
  have h := geom_sum_mul M d
  rw [Mu, sub_self] at h
  have M1 : M = 1 := by
    have hU : IsUnit U := (Matrix.isUnit_iff_isUnit_det _).mpr udet
    exact sub_eq_zero.mp (hU.mul_left_cancel (h.trans (mul_zero _).symm))
  have T1 : translation g = 1 := (LinearMap.toMatrixAlgEquiv b).injective (M1.trans (map_one _).symm)
  have e : rightTranslation g = rightTranslation (1 : WithConv (A →ₐ[R] R)) := by
    apply AlgHom.toLinearMap_injective
    change translation g = translation 1
    rw [T1, map_one]
  apply WithConv.ofConv_injective
  rw [← counit_rightTranslation g, e, counit_rightTranslation]

/-- A local point in rank nine either already dies at nine or is in residue characteristic
three and has order a power of three. -/
theorem rank_nine_local_cases (g : WithConv (A →ₐ[R] R)) (rank : Module.finrank R A = 9) :
    g ^ 9 = 1 ∨ (CharP F 3 ∧ g ^ (3 ^ 20 : ℕ) = 1) := by
  have res : (residuePoint (R := R) (A := A)) (g ^ 9) = 1 := by
    rw [← rank]
    exact residuePoint_pow_finrank g
  by_cases hunit : IsUnit (3 : R)
  · left
    apply point_eq_one_of_residue_of_rank_unit (g ^ 9) res
    rw [rank]
    rw [show ((9 : ℕ) : R) = (3 : R) ^ 2 by norm_num]
    exact hunit.pow 2
  · right
    have h3 : (3 : F) = 0 := by
      rw [← map_ofNat (IsLocalRing.residue R) 3, IsLocalRing.residue_eq_zero_iff]
      exact not_not.mp (by simpa only [IsLocalRing.notMem_maximalIdeal] using hunit)
    let : CharP F 3 := (CharP.charP_iff_prime_eq_zero (R := F) (by decide)).2 h3
    refine ⟨inferInstance, ?_⟩
    have hbig : residuePoint (g ^ (3 ^ 20 : ℕ)) = 1 := by
      have p : (3 ^ 20 : ℕ) = 9 * 3 ^ 18 := by decide
      rw [p, pow_mul, map_pow, res, one_pow]
    have fin : (g ^ (3 ^ 20 : ℕ)) ^ 4480 = 1 := by
      rw [← pow_mul, show (3 ^ 20 * 4480 : ℕ) = factorialBound 9 by decide]
      exact factorialBound_kills_point g (by decide) rank
    have h4480 : IsUnit (4480 : F) := by
      apply isUnit_iff_ne_zero.mpr
      exact (CharP.cast_eq_zero_iff F 3 4480).not.mpr (by decide)
    exact point_eq_one_of_residue_of_pow_unit _ 4480 hbig fin h4480

end Local
end
end FiniteLocallyFreeGroupSchemeExponent
