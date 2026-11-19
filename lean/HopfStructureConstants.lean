import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Tactic.DeriveFintype

/-!
# Finite structure constants for commutative Hopf algebras

The coordinate equations use an arbitrary ordered basis. In particular, the unit
and counit have their own coordinates. Products of basis indices encode tensor
products without imposing cocommutativity.
-/

open scoped TensorProduct
open Module WithConv

namespace HopfStructureConstants

noncomputable section

universe u v

variable {R : Type u} {ι : Type v} {κ τ : Type*} [CommRing R]

/-- A linear map is recorded by the coordinates of the images of the basis vectors. -/
def applyTable [Fintype ι] (f : ι → κ → R) (x : ι → R) : κ → R :=
  fun k => ∑ i, x i * f i k

/-- The coordinate vector of a basis element. -/
def basisVector [DecidableEq ι] (i : ι) : ι → R :=
  fun j => if i = j then 1 else 0

/-- The coordinate vector of a pure tensor. -/
def pureTensor (x : ι → R) (y : κ → R) : ι × κ → R :=
  fun p => x p.1 * y p.2

/-- Apply a table that is linear in each of two arguments. -/
def applyBilinear [Fintype ι] [Fintype κ] (f : ι → κ → τ → R)
    (x : ι → R) (y : κ → R) : τ → R :=
  applyTable (fun i => applyTable (f i) y) x

@[simp] theorem applyTable_basisVector [Fintype ι] [DecidableEq ι]
    (f : ι → κ → R) (i : ι) : applyTable f (basisVector i) = f i := by
  funext k
  simp [applyTable, basisVector, eq_comm]

/-- The five tables before imposing any identities. -/
@[ext] structure Tables (R ι : Type*) where
  unit : ι → R
  mul : ι → ι → ι → R
  counit : ι → R
  comul : ι → ι × ι → R
  antipode : ι → ι → R

section Coordinates

variable {V W U : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup U] [Module R U]

/-- The coordinate function of an element in a given basis. -/
abbrev coordinates (b : Basis ι R V) (v : V) : ι → R := b.repr v

theorem coordinates_injective (b : Basis ι R V) : Function.Injective (coordinates b) :=
  fun _ _ h => b.repr.injective (Finsupp.ext (congrFun h))

@[simp] theorem coordinates_basis [DecidableEq ι] (b : Basis ι R V) (i : ι) :
    coordinates b (b i) = basisVector i := by
  funext j
  simp [coordinates, basisVector, Finsupp.single_apply, eq_comm]

@[simp] theorem coordinates_tmul (b : Basis ι R V) (c : Basis κ R W) (x : V) (y : W) :
    coordinates (b.tensorProduct c) (x ⊗ₜ[R] y) =
      pureTensor (coordinates b x) (coordinates c y) := by
  funext ⟨i, j⟩
  simp [coordinates, pureTensor, mul_comm]

theorem coordinates_map [Fintype ι] (b : Basis ι R V) (c : Basis κ R W)
    (f : V →ₗ[R] W) (v : V) :
    coordinates c (f v) = applyTable (fun i => coordinates c (f (b i))) (coordinates b v) := by
  funext k
  change c.repr (f v) k = _
  have hv : (∑ i, b.repr v i • f (b i)) = f v := by
    simpa only [map_sum, map_smul] using congrArg f (b.sum_repr v)
  rw [← hv, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, applyTable]

theorem scalar_map [Fintype ι] (b : Basis ι R V) (f : V →ₗ[R] R) (v : V) :
    f v = ∑ i, b.repr v i * f (b i) := by
  simpa only [map_sum, map_smul, smul_eq_mul] using (congrArg f (b.sum_repr v)).symm

theorem coordinates_bilinear [Fintype ι] [Fintype κ] (b : Basis ι R V) (c : Basis κ R W)
    (e : Basis τ R U) (f : V →ₗ[R] W →ₗ[R] U) (x : V) (y : W) :
    coordinates e (f x y) =
      applyBilinear (fun i j => coordinates e (f (b i) (c j))) (coordinates b x) (coordinates c y) := by
  change coordinates e (f.flip y x) = _
  rw [coordinates_map b e (f.flip y)]
  change applyTable (fun i => coordinates e (f (b i) y)) (coordinates b x) = _
  unfold applyBilinear
  congr 1
  funext i
  exact coordinates_map c e (f (b i)) y

private theorem bilinear_ext (b : Basis ι R V) (c : Basis κ R W)
    {f g : V →ₗ[R] W →ₗ[R] U} (h : ∀ i j, f (b i) (c j) = g (b i) (c j)) :
    f = g :=
  b.ext fun i => c.ext (h i)

private theorem bilinear_assoc_of_basis (b : Basis ι R V) (f : V →ₗ[R] V →ₗ[R] V)
    (h : ∀ i j k, f (f (b i) (b j)) (b k) = f (b i) (f (b j) (b k))) (x y z : V) :
    f (f x y) z = f x (f y z) := by
  have hz (i j : ι) : f (f (b i) (b j)) = (f (b i)).comp (f (b j)) :=
    b.ext (h i j)
  have hxy : f.compr₂ (f.flip z) = f.compl₂ (f.flip z) :=
    bilinear_ext b b fun i j => DFunLike.congr_fun (hz i j) z
  exact DFunLike.congr_fun (DFunLike.congr_fun hxy x) y

end Coordinates

section BasedRing

variable [Fintype ι] [DecidableEq ι]

/-- The coordinate module with room for a multiplication other than pointwise multiplication. -/
structure Space (R ι : Type*) where
  entries : ι → R

private def spaceEquiv : Space R ι ≃ (ι → R) where
  toFun := Space.entries
  invFun := Space.mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance : AddCommGroup (Space R ι) := spaceEquiv.addCommGroup
private def spaceAddEquiv : Space R ι ≃+ (ι → R) :=
  { spaceEquiv with map_add' := fun _ _ => rfl }

instance : Module R (Space R ι) := spaceAddEquiv.module R

/-- The standard basis of the coordinate space. -/
def spaceBasis : Basis ι R (Space R ι) :=
  Basis.ofEquivFun { (spaceAddEquiv : Space R ι ≃+ (ι → R)) with
    map_smul' := fun _ _ => rfl }

@[simp] theorem coordinates_spaceBasis (x : Space R ι) :
    coordinates spaceBasis x = x.entries := by
  change spaceBasis.equivFun x = x.entries
  rw [spaceBasis, Basis.equivFun_ofEquivFun]
  rfl

/-- The ring identities that only involve the multiplication and unit tables. -/
structure RingLaws (t : Tables R ι) : Prop where
  comm : ∀ i j, t.mul i j = t.mul j i
  assoc : ∀ i j k,
    applyTable (fun a => t.mul a k) (t.mul i j) = applyTable (t.mul i) (t.mul j k)
  one_mul : ∀ i, applyTable (fun a => t.mul a i) t.unit = basisVector i

private def spaceMul (t : Tables R ι) : Space R ι →ₗ[R] Space R ι →ₗ[R] Space R ι :=
  (spaceBasis (R := R) (ι := ι)).constr R fun i => spaceBasis.constr R fun j => ⟨t.mul i j⟩

@[simp] private theorem spaceMul_basis (t : Tables R ι) (i j : ι) :
    spaceMul t (spaceBasis i) (spaceBasis j) = ⟨t.mul i j⟩ := by
  unfold spaceMul
  rw [Basis.constr_basis, Basis.constr_basis]

private theorem spaceMul_comm (t : Tables R ι) (h : RingLaws t) (a b : Space R ι) :
    spaceMul t a b = spaceMul t b a := by
  have he : spaceMul t = (spaceMul t).flip := by
    apply bilinear_ext spaceBasis spaceBasis
    intro i j
    rw [LinearMap.flip_apply, spaceMul_basis, spaceMul_basis]
    exact congrArg Space.mk (h.comm i j)
  exact DFunLike.congr_fun (DFunLike.congr_fun he a) b

private theorem spaceMul_assoc (t : Tables R ι) (h : RingLaws t) (a b c : Space R ι) :
    spaceMul t (spaceMul t a b) c = spaceMul t a (spaceMul t b c) := by
  apply bilinear_assoc_of_basis spaceBasis
  intro i j k
  apply coordinates_injective spaceBasis
  rw [spaceMul_basis, spaceMul_basis]
  change coordinates spaceBasis ((spaceMul t).flip (spaceBasis k) ⟨t.mul i j⟩) =
    coordinates spaceBasis (spaceMul t (spaceBasis i) ⟨t.mul j k⟩)
  rw [coordinates_map spaceBasis, coordinates_map spaceBasis]
  simpa using h.assoc i j k

private theorem spaceUnit_mul (t : Tables R ι) (h : RingLaws t) (a : Space R ι) :
    spaceMul t ⟨t.unit⟩ a = a := by
  have he : spaceMul t ⟨t.unit⟩ = LinearMap.id := by
    apply spaceBasis.ext
    intro i
    apply coordinates_injective spaceBasis
    change coordinates spaceBasis ((spaceMul t).flip (spaceBasis i) ⟨t.unit⟩) =
      coordinates spaceBasis (spaceBasis i)
    rw [coordinates_map spaceBasis, coordinates_basis]
    simpa using h.one_mul i
  exact DFunLike.congr_fun he a

/-- A multiplication table satisfying the ring equations defines a commutative ring on its
coordinate module. The given additive and scalar operations on the module are preserved. -/
@[instance_reducible]
def spaceCommRing (t : Tables R ι) (h : RingLaws t) : CommRing (Space R ι) where
  __ := (inferInstance : AddCommGroup (Space R ι))
  one := ⟨t.unit⟩
  mul a b := spaceMul t a b
  left_distrib a b c := (spaceMul t a).map_add b c
  right_distrib a b c := ((spaceMul t).flip c).map_add a b
  zero_mul a := ((spaceMul t).flip a).map_zero
  mul_zero a := (spaceMul t a).map_zero
  mul_assoc := spaceMul_assoc t h
  mul_comm := spaceMul_comm t h
  one_mul := spaceUnit_mul t h
  mul_one a := (spaceMul_comm t h a ⟨t.unit⟩).trans (spaceUnit_mul t h a)

/-- The algebra structure on the ring reconstructed from a table. -/
@[instance_reducible]
def spaceAlgebra (t : Tables R ι) (h : RingLaws t) :
    letI := spaceCommRing t h
    Algebra R (Space R ι) := by
  letI := spaceCommRing t h
  exact Algebra.ofModule
    (fun r a b => show spaceMul t (r • a) b = r • spaceMul t a b from
      ((spaceMul t).flip b).map_smul r a)
    (fun r a b => show spaceMul t a (r • b) = r • spaceMul t a b from
      (spaceMul t a).map_smul r b)

end BasedRing

section HopfTables

variable [Fintype ι] [DecidableEq ι] (t : Tables R ι)

/-- The table for multiplication in the tensor square. -/
def tensorMulTable (p q : ι × ι) : ι × ι → R :=
  pureTensor (t.mul p.1 q.1) (t.mul p.2 q.2)

def coassocLeft (p : ι × ι) (q : ι × ι × ι) : R :=
  t.comul p.1 (q.1, q.2.1) * basisVector p.2 q.2.2

def coassocRight (p : ι × ι) (q : ι × ι × ι) : R :=
  basisVector p.1 q.1 * t.comul p.2 q.2

def leftCounit (p : ι × ι) (k : ι) : R :=
  t.counit p.1 * basisVector p.2 k

def rightCounit (p : ι × ι) (k : ι) : R :=
  t.counit p.2 * basisVector p.1 k

def antipodeLeft (p : ι × ι) : ι → R :=
  applyTable (fun j => t.mul j p.2) (t.antipode p.1)

def antipodeRight (p : ι × ι) : ι → R :=
  applyTable (t.mul p.1) (t.antipode p.2)

def convolutionUnit (i : ι) (k : ι) : R :=
  t.counit i * t.unit k

/-- The Hopf identities written on basis elements. -/
structure HopfLaws : Prop extends RingLaws t where
  coassoc : ∀ i,
    applyTable (coassocLeft t) (t.comul i) = applyTable (coassocRight t) (t.comul i)
  counit_left : ∀ i, applyTable (leftCounit t) (t.comul i) = basisVector i
  counit_right : ∀ i, applyTable (rightCounit t) (t.comul i) = basisVector i
  counit_one : (∑ i, t.unit i * t.counit i) = 1
  counit_mul : ∀ i j, (∑ k, t.mul i j k * t.counit k) = t.counit i * t.counit j
  comul_one : applyTable t.comul t.unit = pureTensor t.unit t.unit
  comul_mul : ∀ i j, applyTable t.comul (t.mul i j) =
    applyBilinear (tensorMulTable t) (t.comul i) (t.comul j)
  antipode_left : ∀ i, applyTable (antipodeLeft t) (t.comul i) = convolutionUnit t i
  antipode_right : ∀ i, applyTable (antipodeRight t) (t.comul i) = convolutionUnit t i

/-- The coefficients of the power map obtained by repeated convolution with the identity. -/
def powerTable : ℕ → ι → ι → R
  | 0 => convolutionUnit t
  | m + 1 => fun i =>
    applyTable (fun p => applyTable (fun k => t.mul k p.2) (powerTable m p.1)) (t.comul i)

end HopfTables

section Realization

variable {A : Type*} [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]

/-- Read the table with respect to the actual multiplication and three linear operations. -/
def readTables (b : Basis ι R A) (D : A →ₗ[R] A ⊗[R] A) (C : A →ₗ[R] R)
    (S : A →ₗ[R] A) : Tables R ι where
  unit := coordinates b 1
  mul i j := coordinates b (b i * b j)
  counit i := C (b i)
  comul i := coordinates (b.tensorProduct b) (D (b i))
  antipode i := coordinates b (S (b i))

/-- A table represented by linear maps on an algebra, without any coalgebra axioms yet. -/
structure Realization (b : Basis ι R A) (t : Tables R ι) where
  comul : A →ₗ[R] A ⊗[R] A
  counit : A →ₗ[R] R
  antipode : A →ₗ[R] A
  table_eq : readTables b comul counit antipode = t

namespace Realization

variable {b : Basis ι R A} {t : Tables R ι} (z : Realization b t)

include z

@[simp] theorem unit_coordinates : coordinates b 1 = t.unit :=
  congrArg Tables.unit z.table_eq

@[simp] theorem basis_mul_coordinates (i j : ι) :
    coordinates b (b i * b j) = t.mul i j :=
  congrArg (fun a => a.mul i j) z.table_eq

@[simp] theorem basis_comul_coordinates (i : ι) :
    coordinates (b.tensorProduct b) (z.comul (b i)) = t.comul i :=
  congrArg (fun a => a.comul i) z.table_eq

@[simp] theorem basis_counit (i : ι) : z.counit (b i) = t.counit i :=
  congrArg (fun a => a.counit i) z.table_eq

@[simp] theorem basis_antipode_coordinates (i : ι) :
    coordinates b (z.antipode (b i)) = t.antipode i :=
  congrArg (fun a => a.antipode i) z.table_eq

theorem mul_coordinates (x y : A) :
    coordinates b (x * y) = applyBilinear t.mul (coordinates b x) (coordinates b y) := by
  simpa only [LinearMap.mul_apply_apply, z.basis_mul_coordinates] using
    coordinates_bilinear b b b (LinearMap.mul R A) x y

theorem mul_left_coordinates (i : ι) (y : A) :
    coordinates b (b i * y) = applyTable (t.mul i) (coordinates b y) := by
  simp only [z.mul_coordinates, coordinates_basis, applyBilinear, applyTable_basisVector]

theorem mul_right_coordinates (x : A) (j : ι) :
    coordinates b (x * b j) = applyTable (fun i => t.mul i j) (coordinates b x) := by
  simp only [z.mul_coordinates, coordinates_basis, applyBilinear, applyTable_basisVector]

theorem tensorMul_coordinates (x y : A ⊗[R] A) :
    coordinates (b.tensorProduct b) (x * y) =
      applyBilinear (tensorMulTable t) (coordinates (b.tensorProduct b) x)
        (coordinates (b.tensorProduct b) y) := by
  have eq (p q : ι × ι) :
      coordinates (b.tensorProduct b) (b.tensorProduct b p * b.tensorProduct b q) =
        tensorMulTable t p q := by
    rcases p with ⟨i, j⟩
    rcases q with ⟨k, l⟩
    simp [tensorMulTable, z.basis_mul_coordinates]
  simpa only [LinearMap.mul_apply_apply, eq] using coordinates_bilinear
    (b.tensorProduct b) (b.tensorProduct b) (b.tensorProduct b) (LinearMap.mul R (A ⊗[R] A)) x y

theorem comul_coordinates (x : A) :
    coordinates (b.tensorProduct b) (z.comul x) = applyTable t.comul (coordinates b x) := by
  simpa only [z.basis_comul_coordinates] using coordinates_map b (b.tensorProduct b) z.comul x

theorem counit_coordinates (x : A) : z.counit x = ∑ i, b.repr x i * t.counit i := by
  simpa only [z.basis_counit] using scalar_map b z.counit x

theorem toRingLaws : RingLaws t where
  comm i j := by rw [← z.basis_mul_coordinates, ← z.basis_mul_coordinates, mul_comm]
  assoc i j k := by
    have he := congrArg (coordinates b) (mul_assoc (b i) (b j) (b k))
    rwa [z.mul_right_coordinates (b i * b j) k, z.mul_left_coordinates i (b j * b k),
      z.basis_mul_coordinates, z.basis_mul_coordinates] at he
  one_mul i := by
    simpa only [z.mul_right_coordinates, z.unit_coordinates, coordinates_basis] using
      congrArg (coordinates b) (one_mul (b i))

omit z in
private theorem coordinates_assoc (x : (A ⊗[R] A) ⊗[R] A) (p : ι × ι × ι) :
    coordinates (b.tensorProduct (b.tensorProduct b)) (TensorProduct.assoc R A A A x) p =
      coordinates ((b.tensorProduct b).tensorProduct b) x ((p.1, p.2.1), p.2.2) := by
  let l := (b.tensorProduct b).tensorProduct b
  let r := b.tensorProduct (b.tensorProduct b)
  have hm : (r.coord p).comp (TensorProduct.assoc R A A A).toLinearMap =
      l.coord ((p.1, p.2.1), p.2.2) := by
    apply l.ext
    rintro ⟨⟨i, j⟩, k⟩
    change coordinates r (TensorProduct.assoc R A A A (l ((i, j), k))) p =
      coordinates l (l ((i, j), k)) ((p.1, p.2.1), p.2.2)
    have hp : TensorProduct.assoc R A A A (l ((i, j), k)) = r (i, j, k) := by
      simp [l, r]
    rw [hp, coordinates_basis, coordinates_basis]
    rcases p with ⟨a, d, e⟩
    simp [basisVector, Prod.mk.injEq, and_assoc]
  exact DFunLike.congr_fun hm x

omit z in
private theorem tensorInput_coordinates {W κ : Type*} [AddCommGroup W] [Module R W]
    (c : Basis κ R W) (f : A ⊗[R] A →ₗ[R] W)
    (table : ι × ι → κ → R)
    (h : ∀ i j, coordinates c (f (b i ⊗ₜ[R] b j)) = table (i, j))
    (x : A ⊗[R] A) :
    coordinates c (f x) = applyTable table (coordinates (b.tensorProduct b) x) := by
  rw [coordinates_map (b.tensorProduct b)]
  congr 1
  funext p
  rcases p with ⟨i, j⟩
  simpa using h i j

private def coassocLeftMap : A ⊗[R] A →ₗ[R] A ⊗[R] (A ⊗[R] A) :=
  (TensorProduct.assoc R A A A).toLinearMap ∘ₗ z.comul.rTensor A

private theorem coassocLeft_coordinates (x : A ⊗[R] A) :
    coordinates (b.tensorProduct (b.tensorProduct b)) (z.coassocLeftMap x) =
      applyTable (coassocLeft t) (coordinates (b.tensorProduct b) x) := by
  apply tensorInput_coordinates
  intro i j
  funext p
  change coordinates (b.tensorProduct (b.tensorProduct b))
      (TensorProduct.assoc R A A A (z.comul.rTensor A (b i ⊗ₜ[R] b j))) p = _
  rw [LinearMap.rTensor_tmul, coordinates_assoc]
  simp only [coordinates_tmul, pureTensor, z.basis_comul_coordinates, coordinates_basis]
  rfl

private theorem coassocRight_coordinates (x : A ⊗[R] A) :
    coordinates (b.tensorProduct (b.tensorProduct b)) (z.comul.lTensor A x) =
      applyTable (coassocRight t) (coordinates (b.tensorProduct b) x) := by
  apply tensorInput_coordinates
  intro i j
  rw [LinearMap.lTensor_tmul, coordinates_tmul, coordinates_basis, z.basis_comul_coordinates]
  rfl

private def leftCounitMap : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ z.counit.rTensor A

private def rightCounitMap : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.rid R A).toLinearMap ∘ₗ z.counit.lTensor A

private theorem leftCounit_coordinates (x : A ⊗[R] A) :
    coordinates b (z.leftCounitMap x) = applyTable (leftCounit t) (coordinates (b.tensorProduct b) x) := by
  apply tensorInput_coordinates
  intro i j
  funext k
  have eq : z.leftCounitMap (b i ⊗ₜ[R] b j) = z.counit (b i) • b j := by simp [leftCounitMap]
  rw [eq, z.basis_counit]
  simp [leftCounit, coordinates, basisVector, Finsupp.single_apply, eq_comm]

private theorem rightCounit_coordinates (x : A ⊗[R] A) :
    coordinates b (z.rightCounitMap x) = applyTable (rightCounit t) (coordinates (b.tensorProduct b) x) := by
  apply tensorInput_coordinates
  intro i j
  funext k
  have eq : z.rightCounitMap (b i ⊗ₜ[R] b j) = z.counit (b j) • b i := by simp [rightCounitMap]
  rw [eq, z.basis_counit]
  simp [rightCounit, coordinates, basisVector, Finsupp.single_apply, eq_comm]

private def antipodeLeftMap : A ⊗[R] A →ₗ[R] A :=
  LinearMap.mul' R A ∘ₗ z.antipode.rTensor A

private def antipodeRightMap : A ⊗[R] A →ₗ[R] A :=
  LinearMap.mul' R A ∘ₗ z.antipode.lTensor A

private theorem antipodeLeft_coordinates (x : A ⊗[R] A) :
    coordinates b (z.antipodeLeftMap x) = applyTable (antipodeLeft t) (coordinates (b.tensorProduct b) x) := by
  apply tensorInput_coordinates
  intro i j
  simpa only [antipodeLeftMap, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
    z.mul_right_coordinates, z.basis_antipode_coordinates, antipodeLeft]

private theorem antipodeRight_coordinates (x : A ⊗[R] A) :
    coordinates b (z.antipodeRightMap x) = applyTable (antipodeRight t) (coordinates (b.tensorProduct b) x) := by
  apply tensorInput_coordinates
  intro i j
  simpa only [antipodeRightMap, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
    z.mul_left_coordinates, z.basis_antipode_coordinates, antipodeRight]

private theorem convolutionUnit_coordinates (i : ι) :
    coordinates b (algebraMap R A (z.counit (b i))) = convolutionUnit t i := by
  rw [Algebra.algebraMap_eq_smul_one]
  funext k
  simp only [coordinates, map_smul, Finsupp.smul_apply, smul_eq_mul, z.basis_counit, convolutionUnit]
  exact congrArg (t.counit i * ·) (congrFun z.unit_coordinates k)

/-- Reassemble a coalgebra from its identities on basis elements. -/
@[instance_reducible]
def coalgebra (h : HopfLaws t) : Coalgebra R A where
  comul := z.comul
  counit := z.counit
  coassoc := by
    apply b.ext
    intro i
    apply coordinates_injective (b.tensorProduct (b.tensorProduct b))
    change coordinates _ (z.coassocLeftMap (z.comul (b i))) =
      coordinates _ (z.comul.lTensor A (z.comul (b i)))
    simpa only [z.coassocLeft_coordinates, z.coassocRight_coordinates, z.basis_comul_coordinates] using h.coassoc i
  rTensor_counit_comp_comul := by
    apply b.ext
    intro i
    apply (TensorProduct.lid R A).injective
    apply coordinates_injective b
    have hr : TensorProduct.lid R A (TensorProduct.mk R R A 1 (b i)) = b i := by simp
    change coordinates b (z.leftCounitMap (z.comul (b i))) =
      coordinates b (TensorProduct.lid R A (TensorProduct.mk R R A 1 (b i)))
    simpa only [hr, z.leftCounit_coordinates, z.basis_comul_coordinates, coordinates_basis] using h.counit_left i
  lTensor_counit_comp_comul := by
    apply b.ext
    intro i
    apply (TensorProduct.rid R A).injective
    apply coordinates_injective b
    have hr : TensorProduct.rid R A ((TensorProduct.mk R A R).flip 1 (b i)) = b i := by simp
    change coordinates b (z.rightCounitMap (z.comul (b i))) =
      coordinates b (TensorProduct.rid R A ((TensorProduct.mk R A R).flip 1 (b i)))
    simpa only [hr, z.rightCounit_coordinates, z.basis_comul_coordinates, coordinates_basis] using h.counit_right i

/-- Reassemble the compatibility between the multiplication and the coalgebra. -/
@[instance_reducible]
def bialgebra (h : HopfLaws t) : Bialgebra R A where
  __ := z.coalgebra h
  __ := (inferInstance : Algebra R A)
  counit_one := by
    change z.counit 1 = 1
    simpa only [z.counit_coordinates, z.unit_coordinates] using h.counit_one
  mul_compr₂_counit := by
    apply bilinear_ext b b
    intro i j
    change z.counit (b i * b j) = z.counit (b i) * z.counit (b j)
    rw [z.counit_coordinates (b i * b j), z.basis_counit, z.basis_counit]
    simpa only [z.basis_mul_coordinates] using h.counit_mul i j
  comul_one := by
    apply coordinates_injective (b.tensorProduct b)
    change coordinates _ (z.comul 1) = coordinates _ ((1 : A) ⊗ₜ[R] (1 : A))
    simpa only [z.comul_coordinates, coordinates_tmul, z.unit_coordinates] using h.comul_one
  mul_compr₂_comul := by
    apply bilinear_ext b b
    intro i j
    apply coordinates_injective (b.tensorProduct b)
    change coordinates _ (z.comul (b i * b j)) = coordinates _ (z.comul (b i) * z.comul (b j))
    rw [z.comul_coordinates (b i * b j), z.tensorMul_coordinates, z.basis_mul_coordinates,
      z.basis_comul_coordinates, z.basis_comul_coordinates]
    exact h.comul_mul i j

/-- Reassemble all the Hopf identities. -/
@[instance_reducible]
def hopfAlgebra (h : HopfLaws t) : HopfAlgebra R A where
  __ := z.bialgebra h
  antipode := z.antipode
  mul_antipode_rTensor_comul := by
    apply b.ext
    intro i
    apply coordinates_injective b
    change coordinates _ (z.antipodeLeftMap (z.comul (b i))) =
      coordinates _ (algebraMap R A (z.counit (b i)))
    simpa only [z.antipodeLeft_coordinates, z.basis_comul_coordinates, z.convolutionUnit_coordinates] using h.antipode_left i
  mul_antipode_lTensor_comul := by
    apply b.ext
    intro i
    apply coordinates_injective b
    change coordinates _ (z.antipodeRightMap (z.comul (b i))) =
      coordinates _ (algebraMap R A (z.counit (b i)))
    simpa only [z.antipodeRight_coordinates, z.basis_comul_coordinates, z.convolutionUnit_coordinates] using h.antipode_right i

end Realization

end Realization

section FromHopf

variable {A : Type*} [CommRing A] [HopfAlgebra R A] [Fintype ι] [DecidableEq ι]

def tablesOf (b : Basis ι R A) : Tables R ι :=
  readTables b Coalgebra.comul Coalgebra.counit (HopfAlgebra.antipode R)

private def realizeTables {b : Basis ι R A} {t : Tables R ι} (h : tablesOf b = t) :
    Realization b t where
  comul := Coalgebra.comul
  counit := Coalgebra.counit
  antipode := HopfAlgebra.antipode R
  table_eq := h

/-- The tables read from any Hopf algebra satisfy the displayed finite equations. -/
theorem tablesOf_laws (b : Basis ι R A) : HopfLaws (tablesOf b) := by
  let z : Realization b (tablesOf b) := realizeTables rfl
  refine { z.toRingLaws with
    coassoc := ?_, counit_left := ?_, counit_right := ?_, counit_one := ?_,
    counit_mul := ?_, comul_one := ?_, comul_mul := ?_, antipode_left := ?_, antipode_right := ?_ }
  · intro i
    have he := congrArg (coordinates (b.tensorProduct (b.tensorProduct b)))
      (Coalgebra.coassoc_apply (R := R) (b i))
    change coordinates _ (z.coassocLeftMap (z.comul (b i))) =
      coordinates _ (z.comul.lTensor A (z.comul (b i))) at he
    simpa only [z.coassocLeft_coordinates, z.coassocRight_coordinates, z.basis_comul_coordinates] using he
  · intro i
    have he := congrArg (fun x => coordinates b (TensorProduct.lid R A x))
      (Coalgebra.rTensor_counit_comul (R := R) (b i))
    change coordinates _ (z.leftCounitMap (z.comul (b i))) =
      coordinates _ (TensorProduct.lid R A (1 ⊗ₜ[R] b i)) at he
    simpa only [z.leftCounit_coordinates, z.basis_comul_coordinates, TensorProduct.lid_tmul,
      one_smul, coordinates_basis] using he
  · intro i
    have he := congrArg (fun x => coordinates b (TensorProduct.rid R A x))
      (Coalgebra.lTensor_counit_comul (R := R) (b i))
    change coordinates _ (z.rightCounitMap (z.comul (b i))) =
      coordinates _ (TensorProduct.rid R A (b i ⊗ₜ[R] 1)) at he
    simpa only [z.rightCounit_coordinates, z.basis_comul_coordinates, TensorProduct.rid_tmul,
      one_smul, coordinates_basis] using he
  · have he : z.counit 1 = 1 := Bialgebra.counit_one
    simpa only [z.counit_coordinates, z.unit_coordinates] using he
  · intro i j
    have he : z.counit (b i * b j) = z.counit (b i) * z.counit (b j) := Bialgebra.counit_mul _ _
    rw [z.counit_coordinates (b i * b j), z.basis_counit, z.basis_counit] at he
    exact he
  · have he := congrArg (coordinates (b.tensorProduct b)) (Bialgebra.comul_one (R := R) (A := A))
    change coordinates _ (z.comul 1) = coordinates _ ((1 : A) ⊗ₜ[R] (1 : A)) at he
    simpa only [z.comul_coordinates, coordinates_tmul, z.unit_coordinates] using he
  · intro i j
    have he := congrArg (coordinates (b.tensorProduct b)) (Bialgebra.comul_mul (R := R) (b i) (b j))
    change coordinates _ (z.comul (b i * b j)) = coordinates _ (z.comul (b i) * z.comul (b j)) at he
    rwa [z.comul_coordinates (b i * b j), z.tensorMul_coordinates, z.basis_mul_coordinates,
      z.basis_comul_coordinates, z.basis_comul_coordinates] at he
  · intro i
    have he := congrArg (coordinates b) (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) (b i))
    change coordinates _ (z.antipodeLeftMap (z.comul (b i))) =
      coordinates _ (algebraMap R A (z.counit (b i))) at he
    simpa only [z.antipodeLeft_coordinates, z.basis_comul_coordinates, z.convolutionUnit_coordinates] using he
  · intro i
    have he := congrArg (coordinates b) (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) (b i))
    change coordinates _ (z.antipodeRightMap (z.comul (b i))) =
      coordinates _ (algebraMap R A (z.counit (b i))) at he
    simpa only [z.antipodeRight_coordinates, z.basis_comul_coordinates, z.convolutionUnit_coordinates] using he

theorem coordinates_power {b : Basis ι R A} {t : Tables R ι} (agree : tablesOf b = t)
    (m : ℕ) (i : ι) :
    coordinates b ((toConv (AlgHom.id R A) ^ m).ofConv (b i)) = powerTable t m i := by
  let z : Realization b t := realizeTables agree
  induction m generalizing i with
  | zero =>
    change coordinates b (algebraMap R A (z.counit (b i))) = convolutionUnit t i
    exact z.convolutionUnit_coordinates i
  | succ m ih =>
    let f := (toConv (AlgHom.id R A) ^ m).ofConv.toLinearMap
    let Q := LinearMap.mul' R A ∘ₗ f.rTensor A
    rw [pow_succ]
    change coordinates b (Q (z.comul (b i))) =
      applyTable (fun p : ι × ι => applyTable (fun k => t.mul k p.2) (powerTable t m p.1)) (t.comul i)
    rw [Realization.tensorInput_coordinates (b := b) (c := b) Q
      (fun p => applyTable (fun k => t.mul k p.2) (powerTable t m p.1)) _,
      z.basis_comul_coordinates]
    intro j k
    simp only [Q, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
      z.mul_right_coordinates]
    rw [← ih j]
    rfl

theorem power_eq_unit_iff {b : Basis ι R A} {t : Tables R ι} (agree : tablesOf b = t)
    (m : ℕ) :
    toConv (AlgHom.id R A) ^ m = 1 ↔ ∀ i, powerTable t m i = convolutionUnit t i := by
  let z : Realization b t := realizeTables agree
  have hu (i : ι) :
      coordinates b ((1 : WithConv (A →ₐ[R] A)).ofConv (b i)) = convolutionUnit t i :=
    z.convolutionUnit_coordinates i
  constructor
  · intro he i
    rw [← coordinates_power agree, he, hu]
  · intro he
    apply WithConv.ext
    apply AlgHom.toLinearMap_injective
    apply b.ext
    intro i
    apply coordinates_injective b
    simpa only [AlgHom.toLinearMap_apply, coordinates_power agree, hu] using he i

end FromHopf

section Reconstruct

variable [Fintype ι] [DecidableEq ι] (t : Tables R ι)

private def reconstructedBasis (h : RingLaws t) :
    letI := spaceCommRing t h
    letI := spaceAlgebra t h
    Basis ι R (Space R ι) := by
  letI := spaceCommRing t h
  letI := spaceAlgebra t h
  exact Basis.ofEquivFun
    { toEquiv := spaceEquiv
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private def spaceRealization (h : RingLaws t) :
    letI := spaceCommRing t h
    letI := spaceAlgebra t h
    Realization (reconstructedBasis t h) t := by
  letI := spaceCommRing t h
  letI := spaceAlgebra t h
  let b := reconstructedBasis t h
  have coords (x : Space R ι) : coordinates b x = x.entries := by
    change (reconstructedBasis t h).equivFun x = x.entries
    rw [reconstructedBasis, Basis.equivFun_ofEquivFun]
    rfl
  have bases_eq (i : ι) : b i = spaceBasis (R := R) i := by
    simp only [b, reconstructedBasis, spaceBasis, Basis.coe_ofEquivFun]
    rfl
  let D := b.constr R fun i => (b.tensorProduct b).equivFun.symm (t.comul i)
  let C := b.constr R t.counit
  let S := b.constr R fun i => b.equivFun.symm (t.antipode i)
  refine ⟨D, C, S, ?_⟩
  apply Tables.ext
  · exact coords (⟨t.unit⟩ : Space R ι)
  · funext i j
    change coordinates b (spaceMul t (b i) (b j)) = t.mul i j
    rw [bases_eq, bases_eq, spaceMul_basis, coords]
  · funext i
    exact b.constr_basis R t.counit i
  · funext i
    change coordinates (b.tensorProduct b) (D (b i)) = _
    rw [show D (b i) = _ from b.constr_basis R _ i]
    exact LinearEquiv.apply_symm_apply (b.tensorProduct b).equivFun _
  · funext i
    change coordinates b (S (b i)) = _
    rw [show S (b i) = _ from b.constr_basis R _ i]
    exact LinearEquiv.apply_symm_apply b.equivFun _

/-- Every table satisfying the coordinate equations is realized by a Hopf algebra
with the prescribed basis. -/
theorem exists_hopf_realization (h : HopfLaws t) :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : HopfAlgebra R A)
      (b : Basis ι R A), tablesOf b = t := by
  letI := spaceCommRing t h.toRingLaws
  letI := spaceAlgebra t h.toRingLaws
  let z := spaceRealization t h.toRingLaws
  letI := z.hopfAlgebra h
  refine ⟨Space R ι, spaceCommRing t h.toRingLaws, z.hopfAlgebra h,
    reconstructedBasis t h.toRingLaws, ?_⟩
  exact z.table_eq

end Reconstruct

/-- One variable for each entry in the five tables. -/
inductive Variable (ι : Type*) where
  | unit (i : ι)
  | mul (i j k : ι)
  | counit (i : ι)
  | comul (i j k : ι)
  | antipode (i j : ι)
  deriving DecidableEq, Fintype

def fromAssignment (a : Variable ι → R) : Tables R ι where
  unit i := a (.unit i)
  mul i j k := a (.mul i j k)
  counit i := a (.counit i)
  comul i p := a (.comul i p.1 p.2)
  antipode i j := a (.antipode i j)

def assignmentOf (t : Tables R ι) : Variable ι → R
  | .unit i => t.unit i
  | .mul i j k => t.mul i j k
  | .counit i => t.counit i
  | .comul i j k => t.comul i (j, k)
  | .antipode i j => t.antipode i j

@[simp] theorem fromAssignment_assignmentOf (t : Tables R ι) :
    fromAssignment (assignmentOf t) = t := by
  apply Tables.ext
  · rfl
  · rfl
  · rfl
  · funext i ⟨j, k⟩; rfl
  · rfl

/-- The index of one scalar equation, including an output coefficient when the
corresponding identity has values in a free module. -/
inductive Relation (ι : Type*) where
  | comm (i j k : ι)
  | assoc (i j k l : ι)
  | oneMul (i j : ι)
  | coassoc (i : ι) (p : ι × ι × ι)
  | counitLeft (i j : ι)
  | counitRight (i j : ι)
  | counitOne
  | counitMul (i j : ι)
  | comulOne (p : ι × ι)
  | comulMul (i j : ι) (p : ι × ι)
  | antipodeLeft (i j : ι)
  | antipodeRight (i j : ι)
  deriving DecidableEq, Fintype

section Equations

variable [Fintype ι] [DecidableEq ι]

def equation (t : Tables R ι) : Relation ι → R
  | .comm i j k => t.mul i j k - t.mul j i k
  | .assoc i j k l =>
      applyTable (fun a => t.mul a k) (t.mul i j) l - applyTable (t.mul i) (t.mul j k) l
  | .oneMul i j => applyTable (fun a => t.mul a i) t.unit j - basisVector i j
  | .coassoc i p =>
      applyTable (coassocLeft t) (t.comul i) p - applyTable (coassocRight t) (t.comul i) p
  | .counitLeft i j => applyTable (leftCounit t) (t.comul i) j - basisVector i j
  | .counitRight i j => applyTable (rightCounit t) (t.comul i) j - basisVector i j
  | .counitOne => (∑ i, t.unit i * t.counit i) - 1
  | .counitMul i j => (∑ k, t.mul i j k * t.counit k) - t.counit i * t.counit j
  | .comulOne p => applyTable t.comul t.unit p - pureTensor t.unit t.unit p
  | .comulMul i j p => applyTable t.comul (t.mul i j) p -
      applyBilinear (tensorMulTable t) (t.comul i) (t.comul j) p
  | .antipodeLeft i j => applyTable (antipodeLeft t) (t.comul i) j - convolutionUnit t i j
  | .antipodeRight i j => applyTable (antipodeRight t) (t.comul i) j - convolutionUnit t i j

theorem hopfLaws_iff_equations (t : Tables R ι) : HopfLaws t ↔ ∀ r, equation t r = 0 := by
  constructor
  · intro h r
    cases r with
    | comm i j k => exact sub_eq_zero.mpr (congrFun (h.comm i j) k)
    | assoc i j k l => exact sub_eq_zero.mpr (congrFun (h.assoc i j k) l)
    | oneMul i j => exact sub_eq_zero.mpr (congrFun (h.one_mul i) j)
    | coassoc i p => exact sub_eq_zero.mpr (congrFun (h.coassoc i) p)
    | counitLeft i j => exact sub_eq_zero.mpr (congrFun (h.counit_left i) j)
    | counitRight i j => exact sub_eq_zero.mpr (congrFun (h.counit_right i) j)
    | counitOne => exact sub_eq_zero.mpr h.counit_one
    | counitMul i j => exact sub_eq_zero.mpr (h.counit_mul i j)
    | comulOne p => exact sub_eq_zero.mpr (congrFun h.comul_one p)
    | comulMul i j p => exact sub_eq_zero.mpr (congrFun (h.comul_mul i j) p)
    | antipodeLeft i j => exact sub_eq_zero.mpr (congrFun (h.antipode_left i) j)
    | antipodeRight i j => exact sub_eq_zero.mpr (congrFun (h.antipode_right i) j)
  · intro h
    refine
      { toRingLaws := ⟨?_, ?_, ?_⟩
        coassoc := ?_
        counit_left := ?_
        counit_right := ?_
        counit_one := ?_
        counit_mul := ?_
        comul_one := ?_
        comul_mul := ?_
        antipode_left := ?_
        antipode_right := ?_ }
    · intro i j; funext k; exact sub_eq_zero.mp (h (.comm i j k))
    · intro i j k; funext l; exact sub_eq_zero.mp (h (.assoc i j k l))
    · intro i; funext j; exact sub_eq_zero.mp (h (.oneMul i j))
    · intro i; funext p; exact sub_eq_zero.mp (h (.coassoc i p))
    · intro i; funext j; exact sub_eq_zero.mp (h (.counitLeft i j))
    · intro i; funext j; exact sub_eq_zero.mp (h (.counitRight i j))
    · exact sub_eq_zero.mp (h .counitOne)
    · intro i j; exact sub_eq_zero.mp (h (.counitMul i j))
    · funext p; exact sub_eq_zero.mp (h (.comulOne p))
    · intro i j; funext p; exact sub_eq_zero.mp (h (.comulMul i j p))
    · intro i; funext j; exact sub_eq_zero.mp (h (.antipodeLeft i j))
    · intro i; funext j; exact sub_eq_zero.mp (h (.antipodeRight i j))

def universalTables : Tables (MvPolynomial (Variable ι) ℤ) ι :=
  fromAssignment MvPolynomial.X

/-- The integer polynomial attached to each Hopf law. -/
def relationPolynomial (r : Relation ι) : MvPolynomial (Variable ι) ℤ :=
  equation universalTables r

/-- The coefficient of the difference between the power map and the unit map. -/
def powerDefect (m : ℕ) (i j : ι) : MvPolynomial (Variable ι) ℤ :=
  powerTable universalTables m i j - convolutionUnit universalTables i j

private theorem eval_basisVector (a : Variable ι → R) (i j : ι) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) a (basisVector i j) = basisVector i j := by
  by_cases h : i = j <;> simp only [basisVector, h, if_true, if_false, map_zero, map_one]

@[simp] theorem eval_relationPolynomial (a : Variable ι → R) (r : Relation ι) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) a (relationPolynomial r) =
      equation (fromAssignment a) r := by
  cases r <;> simp only [relationPolynomial, equation, universalTables, fromAssignment, applyTable,
    applyBilinear, pureTensor, coassocLeft, coassocRight, leftCounit, rightCounit,
    antipodeLeft, antipodeRight, tensorMulTable, convolutionUnit, map_sum, map_sub, map_mul,
    map_one, eval_basisVector, MvPolynomial.eval₂Hom_X']

private theorem eval_powerTable (a : Variable ι → R) (m : ℕ) (i j : ι) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) a (powerTable universalTables m i j) =
      powerTable (fromAssignment a) m i j := by
  induction m generalizing i j with
  | zero => simp only [powerTable, convolutionUnit, universalTables, fromAssignment, map_mul,
      MvPolynomial.eval₂Hom_X']
  | succ m ih =>
    simp only [powerTable, applyTable, map_sum, map_mul, ih]
    simp only [universalTables, fromAssignment, MvPolynomial.eval₂Hom_X']

@[simp] theorem eval_powerDefect (a : Variable ι → R) (m : ℕ) (i j : ι) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) a (powerDefect m i j) =
      powerTable (fromAssignment a) m i j - convolutionUnit (fromAssignment a) i j := by
  rw [powerDefect, map_sub, eval_powerTable]
  simp only [convolutionUnit, universalTables, fromAssignment, map_mul, MvPolynomial.eval₂Hom_X']

end Equations

end
end HopfStructureConstants
