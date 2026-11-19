import RankNineBase
import SquareZeroCubicPlane
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.LinearCombination

/-! A rank-nine Hopf algebra whose universal point has order 27. -/

open WithConv
open scoped TensorProduct BigOperators

namespace RankNineExample

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

noncomputable section

private abbrev coeff (S : Type*) [Semiring S] [Algebra Base S] (a : Base) : S := algebraMap Base S a

private def weight {S : Type*} [Semiring S] [Algebra Base S] (x y : S) : S :=
  let a' := coeff S a
  let b' := coeff S b
  let c := a' * x + b' * y
  c + c ^ 2 + a' ^ 2 * b' * x ^ 2 * y + a' * b' ^ 2 * x * y ^ 2

private def scale {S : Type*} [Semiring S] [Algebra Base S] (x y : S) : S :=
  1 + coeff S a * x + coeff S b * y

private theorem map_weight {S T : Type*} [Semiring S] [Semiring T]
    [Algebra Base S] [Algebra Base T] (f : S →ₐ[Base] T) (x y : S) :
    f (weight x y) = weight (f x) (f y) := by simp [weight]

private theorem weight_product {S : Type*} [CommRing S] [Algebra Base S] (x y u v : S) :
    let l := scale x y
    weight (x + l * u) (y + l * v) =
      weight x y + l ^ 3 * weight u v -
        (coeff S a) ^ 3 * (x ^ 2 * l * u + x * l ^ 2 * u ^ 2) -
        (coeff S b) ^ 3 * (y ^ 2 * l * v + y * l ^ 2 * v ^ 2) := by
  dsimp [scale, weight]
  ring

private theorem product_relations {S : Type*} [CommRing S] [Algebra Base S] (x y u v : S)
    (hx : x ^ 3 = -(coeff S s * weight x y))
    (hy : y ^ 3 = -(coeff S t * weight x y))
    (hu : u ^ 3 = -(coeff S s * weight u v))
    (hv : v ^ 3 = -(coeff S t * weight u v)) :
    let l := scale x y
    (x + l * u) ^ 3 = -(coeff S s * weight (x + l * u) (y + l * v)) ∧
    (y + l * v) ^ 3 = -(coeff S t * weight (x + l * u) (y + l * v)) := by
  let l := scale x y
  have h := weight_product x y u v
  change weight (x + l * u) (y + l * v) = _ at h
  have ha : coeff S s * (coeff S a) ^ 3 = 3 := by
    simpa only [map_pow, map_mul, map_ofNat] using congrArg (algebraMap Base S) sa_cube
  have hb : coeff S t * (coeff S b) ^ 3 = 3 := by
    simpa only [map_pow, map_mul, map_ofNat] using congrArg (algebraMap Base S) tb_cube
  have hs : coeff S s * (coeff S b) ^ 3 = 0 := by simpa using congrArg (algebraMap Base S) sb_cube
  have ht : coeff S t * (coeff S a) ^ 3 = 0 := by simpa using congrArg (algebraMap Base S) ta_cube
  change (x + l * u) ^ 3 = _ ∧ (y + l * v) ^ 3 = _
  constructor
  · linear_combination hx + l ^ 3 * hu + coeff S s * h -
      (x ^ 2 * l * u + x * l ^ 2 * u ^ 2) * ha -
      (y ^ 2 * l * v + y * l ^ 2 * v ^ 2) * hs
  · linear_combination hy + l ^ 3 * hv + coeff S t * h -
      (x ^ 2 * l * u + x * l ^ 2 * u ^ 2) * ht -
      (y ^ 2 * l * v + y * l ^ 2 * v ^ 2) * hb

open SquareZeroCubicPlane in
private def W : Polynomials Base :=
  weight (monomial (1, 0)) (monomial (0, 1))

abbrev Coordinate := SquareZeroCubicPlane.Coord s t W

private abbrev x : Coordinate := SquareZeroCubicPlane.X s t W
private abbrev y : Coordinate := SquareZeroCubicPlane.Y s t W
private abbrev lambda : Coordinate := scale x y

private def coordinateBasis : Module.Basis (Fin 3 × Fin 3) Base Coordinate :=
  SquareZeroCubicPlane.basis s t W (by simpa [pow_two] using s_sq)
    st_zero (by simpa [pow_two] using t_sq)

instance : Module.Free Base Coordinate := Module.Free.of_basis coordinateBasis
instance : Module.Finite Base Coordinate := Module.Finite.of_basis coordinateBasis

theorem coordinate_finrank : Module.finrank Base Coordinate = 9 := by
  rw [Module.finrank_eq_card_basis coordinateBasis]
  decide

private theorem eval_W {S : Type*} [CommRing S] [Algebra Base S] (u v : S) :
    SquareZeroCubicPlane.evalMonomials u v W = weight u v := by
  rw [W, map_weight]
  simp

private theorem x_relation : x ^ 3 = -(coeff Coordinate s * weight x y) := by
  have h := SquareZeroCubicPlane.X_relation s t W
  have hW : SquareZeroCubicPlane.quotient s t W W = weight x y :=
    map_weight (SquareZeroCubicPlane.quotient s t W) _ _
  rw [hW, show -s • weight x y = coeff Coordinate (-s) * weight x y from
    Algebra.smul_def (R := Base) (-s) (weight x y),
    show coeff Coordinate (-s) = -coeff Coordinate s from map_neg (algebraMap Base Coordinate) s] at h
  exact h.trans (by ring)

private theorem y_relation : y ^ 3 = -(coeff Coordinate t * weight x y) := by
  have h := SquareZeroCubicPlane.Y_relation s t W
  have hW : SquareZeroCubicPlane.quotient s t W W = weight x y :=
    map_weight (SquareZeroCubicPlane.quotient s t W) _ _
  rw [hW, show -t • weight x y = coeff Coordinate (-t) * weight x y from
    Algebra.smul_def (R := Base) (-t) (weight x y),
    show coeff Coordinate (-t) = -coeff Coordinate t from map_neg (algebraMap Base Coordinate) t] at h
  exact h.trans (by ring)

private def makeHom {S : Type*} [CommRing S] [Algebra Base S] (u v : S)
    (hu : u ^ 3 = -(coeff S s * weight u v)) (hv : v ^ 3 = -(coeff S t * weight u v)) :
    Coordinate →ₐ[Base] S :=
  SquareZeroCubicPlane.lift s t W u v
    (by rw [eval_W, Algebra.smul_def, map_neg, neg_mul]; exact hu)
    (by rw [eval_W, Algebra.smul_def, map_neg, neg_mul]; exact hv)

@[simp] private theorem makeHom_x {S : Type*} [CommRing S] [Algebra Base S] (u v : S) (hu) (hv) :
    makeHom u v hu hv x = u := SquareZeroCubicPlane.lift_X _ _ _ _ _ _ _

@[simp] private theorem makeHom_y {S : Type*} [CommRing S] [Algebra Base S] (u v : S) (hu) (hv) :
    makeHom u v hu hv y = v := SquareZeroCubicPlane.lift_Y _ _ _ _ _ _ _

private abbrev Left : Coordinate →ₐ[Base] Coordinate ⊗[Base] Coordinate :=
  Algebra.TensorProduct.includeLeft
private abbrev Right : Coordinate →ₐ[Base] Coordinate ⊗[Base] Coordinate :=
  Algebra.TensorProduct.includeRight

private theorem map_scale {S T : Type*} [Semiring S] [Semiring T]
    [Algebra Base S] [Algebra Base T] (f : S →ₐ[Base] T) (u v : S) :
    f (scale u v) = scale (f u) (f v) := by simp [scale]

private theorem tensor_relations :
    let l := Left lambda
    let u := Left x + l * Right x
    let v := Left y + l * Right y
    u ^ 3 = -(coeff (Coordinate ⊗[Base] Coordinate) s * weight u v) ∧
    v ^ 3 = -(coeff (Coordinate ⊗[Base] Coordinate) t * weight u v) := by
  dsimp only
  rw [show Left lambda = scale (Left x) (Left y) from map_scale Left x y]
  apply product_relations (Left x) (Left y) (Right x) (Right y)
  · have hp : Left (x ^ 3) = Left x ^ 3 := Left.toRingHom.map_pow x 3
    simpa only [hp, map_neg, map_mul, AlgHom.commutes, map_weight] using congrArg Left x_relation
  · have hp : Left (y ^ 3) = Left y ^ 3 := Left.toRingHom.map_pow y 3
    simpa only [hp, map_neg, map_mul, AlgHom.commutes, map_weight] using congrArg Left y_relation
  · have hp : Right (x ^ 3) = Right x ^ 3 := Right.toRingHom.map_pow x 3
    simpa only [hp, map_neg, map_mul, AlgHom.commutes, map_weight] using congrArg Right x_relation
  · have hp : Right (y ^ 3) = Right y ^ 3 := Right.toRingHom.map_pow y 3
    simpa only [hp, map_neg, map_mul, AlgHom.commutes, map_weight] using congrArg Right y_relation

private def coproduct : Coordinate →ₐ[Base] Coordinate ⊗[Base] Coordinate :=
  makeHom (Left x + Left lambda * Right x) (Left y + Left lambda * Right y)
    tensor_relations.1 tensor_relations.2

@[simp] private theorem coproduct_x : coproduct x = Left x + Left lambda * Right x := by simp [coproduct]
@[simp] private theorem coproduct_y : coproduct y = Left y + Left lambda * Right y := by simp [coproduct]

@[simp] private theorem coproduct_lambda : coproduct lambda = Left lambda * Right lambda := by
  have h := map_scale coproduct x y
  rw [coproduct_x, coproduct_y] at h
  refine h.trans ?_
  rw [show Left lambda = scale (Left x) (Left y) from map_scale Left x y,
    show Right lambda = scale (Right x) (Right y) from map_scale Right x y]
  unfold scale
  ring

private def counit : Coordinate →ₐ[Base] Base := makeHom 0 0 (by simp [weight]) (by simp [weight])

@[simp] private theorem counit_x : counit x = 0 := by simp [counit]
@[simp] private theorem counit_y : counit y = 0 := by simp [counit]
@[simp] private theorem counit_lambda : counit lambda = 1 := by simp [map_scale, scale]

private theorem extCoordinate {S : Type*} [Semiring S] [Algebra Base S]
    {f g : Coordinate →ₐ[Base] S} (hx : f x = g x) (hy : f y = g y) : f = g :=
  SquareZeroCubicPlane.algHom_ext s t W hx hy

private theorem coassoc :
    (Algebra.TensorProduct.assoc Base Base Base Coordinate Coordinate Coordinate).toAlgHom.comp
        ((Algebra.TensorProduct.map coproduct (.id Base Coordinate)).comp coproduct) =
      (Algebra.TensorProduct.map (.id Base Coordinate) coproduct).comp coproduct := by
  have h₀ : coproduct 1 = 1 := coproduct.toRingHom.map_one
  apply extCoordinate <;>
    simp [h₀, Algebra.TensorProduct.one_def,
      TensorProduct.add_tmul, TensorProduct.tmul_add, add_assoc]

private theorem counit_left :
    (Algebra.TensorProduct.map counit (.id Base Coordinate)).comp coproduct =
      (Algebra.TensorProduct.lid Base Coordinate).symm := by
  apply extCoordinate <;> simp

private theorem counit_right :
    (Algebra.TensorProduct.map (.id Base Coordinate) counit).comp coproduct =
      (Algebra.TensorProduct.rid Base Base Coordinate).symm := by
  apply extCoordinate <;> simp

instance : Bialgebra Base Coordinate :=
  Bialgebra.ofAlgHom coproduct counit coassoc counit_left counit_right

def universalPoint : WithConv (Coordinate →ₐ[Base] Coordinate) :=
  toConv (AlgHom.id Base Coordinate)

private def powerMap (n : ℕ) : Coordinate →ₐ[Base] Coordinate := (universalPoint ^ n).ofConv

private theorem power_zero (z : Coordinate) : powerMap 0 z = coeff Coordinate (counit z) := rfl

private theorem power_succ (n : ℕ) (z : Coordinate) :
    powerMap (n + 1) z = (Algebra.TensorProduct.lift (powerMap n) (.id Base Coordinate)
      fun _ _ => Commute.all _ _) (coproduct z) := by
  change (universalPoint ^ (n + 1)).ofConv z = _
  rw [pow_succ universalPoint n, AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply]
  rfl

private theorem power_lambda (n : ℕ) : powerMap n lambda = lambda ^ n := by
  induction n with
  | zero => simp [power_zero]
  | succ n ih => rw [power_succ, coproduct_lambda, map_mul, pow_succ]; simp [ih]

private def geom (n : ℕ) : Coordinate := ∑ i ∈ Finset.range n, lambda ^ i

private theorem power_x (n : ℕ) : powerMap n x = geom n * x := by
  induction n with
  | zero => simp [power_zero, geom]
  | succ n ih =>
    rw [power_succ, coproduct_x]
    simp [ih, power_lambda, geom, Finset.sum_range_succ, add_mul]

private theorem power_y (n : ℕ) : powerMap n y = geom n * y := by
  induction n with
  | zero => simp [power_zero, geom]
  | succ n ih =>
    rw [power_succ, coproduct_y]
    simp [ih, power_lambda, geom, Finset.sum_range_succ, add_mul]

private theorem nine_coordinate : (9 : Coordinate) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap Base Coordinate) nine_zero

private theorem lambda_cube : lambda ^ 3 = 1 - 3 * weight x y := by
  have ha : coeff Coordinate s * (coeff Coordinate a) ^ 3 = 3 := by
    simpa only [map_mul, map_pow, map_ofNat] using congrArg (algebraMap Base Coordinate) sa_cube
  have hb : coeff Coordinate t * (coeff Coordinate b) ^ 3 = 3 := by
    simpa only [map_mul, map_pow, map_ofNat] using congrArg (algebraMap Base Coordinate) tb_cube
  change scale x y ^ 3 = _
  linear_combination (norm := (unfold scale weight; ring)) (coeff Coordinate a) ^ 3 * x_relation +
    (coeff Coordinate b) ^ 3 * y_relation - weight x y * ha - weight x y * hb

private theorem lambda_ninth : lambda ^ 9 = 1 := by
  have hp : lambda ^ 9 = (lambda ^ 3) ^ 3 := pow_mul lambda 3 3
  rw [hp, lambda_cube]
  linear_combination (-weight x y + 3 * weight x y ^ 2 - 3 * weight x y ^ 3) * nine_coordinate

private theorem geom_nine :
    geom 9 = 3 * (coeff Coordinate a * x + coeff Coordinate b * y) ^ 2 := by
  have block : geom 9 = (1 + lambda + lambda ^ 2) * (1 + lambda ^ 3 + lambda ^ 6) := by
    simp only [geom, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero]
    ring
  have third : 1 + lambda ^ 3 + lambda ^ 6 = 3 := by
    have hp : lambda ^ 6 = (lambda ^ 3) ^ 2 := pow_mul lambda 3 2
    rw [hp, lambda_cube]
    linear_combination (weight x y ^ 2 - weight x y) * nine_coordinate
  rw [block, third]
  change (1 + scale x y + (scale x y) ^ 2) * 3 = _
  unfold scale
  linear_combination (1 + coeff Coordinate a * x + coeff Coordinate b * y) * nine_coordinate

private theorem geom_add (m n : ℕ) : geom (m + n) = geom m + lambda ^ m * geom n := by
  simp [geom, Finset.sum_range_add, pow_add, Finset.mul_sum]

private theorem geom_twenty_seven : geom 27 = 0 := by
  rw [show (27 : ℕ) = (9 + 9) + 9 by decide, geom_add, geom_add,
    pow_add, lambda_ninth, one_mul, one_mul, one_mul, geom_nine]
  linear_combination (coeff Coordinate a * x + coeff Coordinate b * y) ^ 2 * nine_coordinate

private theorem point_pow_twenty_seven : universalPoint ^ 27 = 1 := by
  apply WithConv.ext
  apply extCoordinate
  · change powerMap 27 x = coeff Coordinate (counit x)
    simp [power_x, geom_twenty_seven]
  · change powerMap 27 y = coeff Coordinate (counit y)
    simp [power_y, geom_twenty_seven]

private theorem antipode_left :
    ((Algebra.TensorProduct.lift (powerMap 26) (.id Base Coordinate) fun _ _ => Commute.all _ _).comp
      (Bialgebra.comulAlgHom Base Coordinate)) =
      (Algebra.ofId Base Coordinate).comp (Bialgebra.counitAlgHom Base Coordinate) := by
  have h := congrArg WithConv.ofConv point_pow_twenty_seven
  rw [show (27 : ℕ) = 26 + 1 by decide, pow_succ] at h
  change (Algebra.TensorProduct.lmul' Base).comp
    ((Algebra.TensorProduct.map (powerMap 26) (.id Base Coordinate)).comp
      (Bialgebra.comulAlgHom Base Coordinate)) = _ at h
  rw [← AlgHom.comp_assoc, Algebra.TensorProduct.lmul'_comp_map] at h
  exact h

private theorem antipode_right :
    ((Algebra.TensorProduct.lift (.id Base Coordinate) (powerMap 26) fun _ _ => Commute.all _ _).comp
      (Bialgebra.comulAlgHom Base Coordinate)) =
      (Algebra.ofId Base Coordinate).comp (Bialgebra.counitAlgHom Base Coordinate) := by
  have h := congrArg WithConv.ofConv point_pow_twenty_seven
  rw [show (27 : ℕ) = 26 + 1 by decide, pow_succ'] at h
  change (Algebra.TensorProduct.lmul' Base).comp
    ((Algebra.TensorProduct.map (.id Base Coordinate) (powerMap 26)).comp
      (Bialgebra.comulAlgHom Base Coordinate)) = _ at h
  rw [← AlgHom.comp_assoc, Algebra.TensorProduct.lmul'_comp_map] at h
  exact h

instance : HopfAlgebra Base Coordinate :=
  HopfAlgebra.ofAlgHom (powerMap 26) antipode_left antipode_right

private theorem x_ninth :
    powerMap 9 x =
      (6 * a * b) • coordinateBasis (2, 1) + (3 * b ^ 2) • coordinateBasis (1, 2) := by
  have hs : (3 : Base) * s = 0 := by
    linear_combination -s * sa_cube + a ^ 3 * (by simpa [pow_two] using s_sq : s * s = 0)
  have ht : (3 : Base) * t = 0 := by
    linear_combination -t * tb_cube + b ^ 3 * (by simpa [pow_two] using t_sq : t * t = 0)
  have sx : (3 : Coordinate) * coeff Coordinate s = 0 := by
    simpa only [map_mul, map_ofNat, map_zero] using congrArg (algebraMap Base Coordinate) hs
  have tx : (3 : Coordinate) * coeff Coordinate t = 0 := by
    simpa only [map_mul, map_ofNat, map_zero] using congrArg (algebraMap Base Coordinate) ht
  have b21 : coordinateBasis (2, 1) = x ^ 2 * y := by
    have h := SquareZeroCubicPlane.basis_apply s t W (by simpa [pow_two] using s_sq)
      st_zero (by simpa [pow_two] using t_sq) (2, 1)
    change coordinateBasis (2, 1) = x ^ (2 : ℕ) * y ^ (1 : ℕ) at h
    rwa [pow_one] at h
  have b12 : coordinateBasis (1, 2) = x * y ^ 2 := by
    have h := SquareZeroCubicPlane.basis_apply s t W (by simpa [pow_two] using s_sq)
      st_zero (by simpa [pow_two] using t_sq) (1, 2)
    change coordinateBasis (1, 2) = x ^ (1 : ℕ) * y ^ (2 : ℕ) at h
    rwa [pow_one] at h
  have sm (r : Base) (z : Coordinate) : r • z = coeff Coordinate r * z :=
    Algebra.smul_def (R := Base) r z
  simp only [b21, b12, power_x, geom_nine, sm, map_mul, map_ofNat, map_pow]
  change _ = 6 * coeff Coordinate a * coeff Coordinate b * (x ^ 2 * y) +
    3 * (coeff Coordinate b) ^ 2 * (x * y ^ 2)
  linear_combination 3 * (coeff Coordinate a) ^ 2 * x_relation -
    (coeff Coordinate a) ^ 2 * weight x y * sx

theorem point_pow_nine_ne_one : universalPoint ^ 9 ≠ 1 := by
  intro he
  have h : powerMap 9 x = 0 := by
    have e := DFunLike.congr_fun (congrArg WithConv.ofConv he) x
    exact e.trans (by change coeff Coordinate (counit x) = 0; simp)
  rw [x_ninth] at h
  have e := congrArg (fun z => coordinateBasis.repr z (1, 2)) h
  apply three_b_sq_ne_zero
  simpa [Module.Basis.repr_self, Finsupp.single_apply] using e

theorem orderOf_universalPoint : orderOf universalPoint = 27 := by
  have d : orderOf universalPoint ∣ 3 ^ 3 := orderOf_dvd_of_pow_eq_one point_pow_twenty_seven
  have hn : ¬ orderOf universalPoint ∣ 9 := by
    intro h
    exact point_pow_nine_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp d
  have hk₀ : ¬k ≤ 2 := fun h => hn (hk' ▸ pow_dvd_pow 3 h)
  obtain rfl : k = 3 := by omega
  exact hk'

end
end RankNineExample

#print axioms RankNineExample.orderOf_universalPoint
