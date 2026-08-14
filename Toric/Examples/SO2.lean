/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Toric.GroupScheme.Torus
public import Toric.Mathlib.Algebra.Polynomial.Bivariate

/-!
# Demo of `SO(2, ℝ)` as a non-split torus

In this file, we construct `SO(2, R)` as a group scheme for an arbitrary commutative ring `R`,
and show that `SO(2, ℂ)` is a split torus while `SO(2, ℝ)` isn't, which implies that `SO(2, ℝ)` is
a non-split torus.
-/

public noncomputable section

local notation3:max R "[X][Y]" => Polynomial (Polynomial R)
local notation3:max "Y" => Polynomial.C (Polynomial.X)

open Coalgebra HopfAlgebra Polynomial TensorProduct CategoryTheory
open scoped AddMonoidAlgebra MonObj

/-! ### `SO(2, R)` as a Hopf algebra -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- The ring whose spectrum is `SO(2, R)`, defined as `R[X, Y] / ⟨X ^ 2 + Y ^ 2 - 1⟩`. -/
abbrev SO2Ring : Type _ := AdjoinRoot (X ^ 2 + Y ^ 2 - 1 : R[X][Y])

namespace SO2Ring

instance : CommRing (SO2Ring R) := by delta SO2Ring; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : Algebra R (SO2Ring S) := by delta SO2Ring; infer_instance

instance : IsScalarTower R S (SO2Ring S) := by delta SO2Ring; infer_instance

/-- The quotient map from `R[X, Y]` to `SO2Ring R`. -/
@[expose]
def mk : R[X][Y] →ₐ[R] SO2Ring R := Ideal.Quotient.mkₐ R _

/-- `X` as an element of `SO2Ring R`. -/
@[expose] nonrec def X : SO2Ring R := .mk X

/-- `Y` as an element of `SO2Ring R`. -/
@[expose] nonrec def «Y» : SO2Ring R := .mk Y

@[simp] lemma X_def : mk .X = .X (R := R) := rfl
@[simp] lemma Y_def : mk Y = .Y (R := R) := rfl

-- TODO: make equiv
/-- Lift two elements of `S` with squares summing to `1` to an algebra hom from `SO2Ring R` to `S`.
-/
@[expose]
def liftₐ (x y : S) (H : x ^ 2 + y ^ 2 = 1) : SO2Ring R →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAEval x y)
    (show Ideal.span _ ≤ RingHom.ker _ by simp [Ideal.span_le, Set.singleton_subset_iff, H])

@[simp]
lemma liftₐ_X (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .X = x := aevalAEval_X ..

@[simp]
lemma liftₐ_Y (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .Y = y := aevalAEval_Y ..

@[simp]
lemma relation : SO2Ring.X (R := R) ^ 2 + .Y ^ 2 = 1 := by
  simp_rw [SO2Ring.X, SO2Ring.Y, ← map_pow, ← map_add, ← map_one SO2Ring.mk]
  exact Ideal.Quotient.eq.mpr <| by simp

lemma relation' : SO2Ring.X (R := R) ^ 2 = 1 - .Y ^ 2 := by simp [← relation]

@[simp] lemma relation'' : SO2Ring.X (R := R) * .X + .Y * .Y = 1 := by simp [← pow_two]

@[ext]
lemma algebraMap_ext {A : Type*} [Semiring A] [Algebra R A] {f g : SO2Ring R →ₐ[R] A}
    (h1 : f .X = g .X) (h2 : f .Y = g .Y) : f = g := by
  simp_rw [SO2Ring] at f g; apply Ideal.Quotient.algHom_ext; ext <;> assumption

/-- The comultiplication on `SO2Ring R`, given by `X ↦ X ⊗ X - Y ⊗ Y, Y ↦ X ⊗ Y + Y ⊗ X`. -/
@[expose]
def comulAlgHom : SO2Ring R →ₐ[R] SO2Ring R ⊗[R] SO2Ring R := by
  refine liftₐ (.X ⊗ₜ .X - .Y ⊗ₜ .Y) (.X ⊗ₜ .Y + .Y ⊗ₜ .X) ?_
  ring_nf
  simp only [Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_pow (A := SO2Ring R) (B := SO2Ring R), relation', tmul_sub,
    sub_tmul, ← Algebra.TensorProduct.one_def (A := SO2Ring R) (B := SO2Ring R)]
  ring_nf

@[simp]
lemma comulAlgHom_apply_X : comulAlgHom (R := R) .X = (.X ⊗ₜ .X - .Y ⊗ₜ .Y) := by
  simp [comulAlgHom]

@[simp]
lemma comulAlgHom_apply_Y : comulAlgHom (R := R) .Y = (.X ⊗ₜ .Y + .Y ⊗ₜ .X) := by
  simp [comulAlgHom]

/-- The counit on `SO2Ring R`, given by `X ↦ 1, Y ↦ 0`. -/
@[expose]
def counitAlgHom : SO2Ring R →ₐ[R] R := liftₐ 1 0 (by simp)

@[simp] lemma counitAlgHom.apply_X : counitAlgHom (R := R) .X = 1 := by simp [counitAlgHom]
@[simp] lemma counitAlgHom.apply_Y : counitAlgHom (R := R) .Y = 0 := by simp [counitAlgHom]

attribute [-ext] AdjoinRoot.algHom_ext' in
instance : Bialgebra R (SO2Ring R) := by
  refine .ofAlgHom comulAlgHom counitAlgHom ?_ ?_ ?_ <;> ext
    <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul] <;> ring

@[simp] lemma comul_def : comul (R := R) (A := SO2Ring R) = comulAlgHom (R := R) := rfl
@[simp] lemma counit_def : counit (R := R) (A := SO2Ring R) = counitAlgHom (R := R) := rfl

/-- The comultiplication on `SO2Ring R`, given by `X ↦ X, Y ↦ -Y`. -/
@[expose]
def antipodeAlgHom : SO2Ring R →ₐ[R] SO2Ring R := liftₐ .X (-.Y) (by simp)

@[simp] lemma antipodeAlgHom_X : antipodeAlgHom (R := R) .X = X := by simp [antipodeAlgHom]
@[simp] lemma antipodeAlgHom_Y : antipodeAlgHom (R := R) .Y = -.Y := by simp [antipodeAlgHom]

attribute [-ext] AdjoinRoot.algHom_ext' in
set_option backward.isDefEq.respectTransparency false in
instance : HopfAlgebra R (SO2Ring R) := by
  refine .ofAlgHom antipodeAlgHom ?_ <| by ext <;> simp; ring_nf
  ext
  · simp [← sq]
  · simp
    ring_nf

@[simp] lemma antipode_X : antipode R X = X (R := R) := antipodeAlgHom_X
@[simp] lemma antipode_Y : antipode R SO2Ring.Y = - .Y (R := R) := antipodeAlgHom_Y

/-! #### `SO(2, ℂ)` -/

set_option backward.isDefEq.respectTransparency false in
/-- The group-like element `X + iY` of `SO2Ring ℂ`. -/
@[simps!, expose]
def T : GroupLike ℂ (SO2Ring ℂ) where
  val := .X + Complex.I • .Y
  isGroupLikeElem_val.counit_eq_one := by simp
  isGroupLikeElem_val.comul_eq_tmul_self := by
    simp [tmul_add, add_tmul, ← smul_tmul', smul_smul]; ring_nf

private def complexEquivInv : MonoidAlgebra ℂ (Multiplicative ℤ) →ₐc[ℂ] SO2Ring ℂ :=
  MonoidAlgebra.liftGroupLikeBialgHom.comp <| MonoidAlgebra.mapDomainBialgHom ℂ <|
    AddMonoidHom.toMultiplicativeLeft <| zmultiplesHom _ <| .ofMul T

set_option backward.isDefEq.respectTransparency false in
private lemma complexEquivInv_single (a : Multiplicative ℤ) (b : ℂ) :
    complexEquivInv (.single a b) = b • (T ^ a.toAdd).1 := by
  simp [complexEquivInv, Algebra.smul_def]

set_option allowUnsafeReducibility true in
attribute [-ext] AdjoinRoot.algHom_ext' in
attribute [local semireducible] MonoidAlgebra.single in
private def complexEquivFun : SO2Ring ℂ →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative ℤ) := by
  refine .ofAlgHom
    (liftₐ
      ((1 / 2 : ℂ) • (.single (.ofAdd 1) 1 + .single (.ofAdd (-1)) 1))
      (- (.I / 2 : ℂ) • (.single (.ofAdd 1) 1 - .single (.ofAdd (-1)) 1)) ?_) ?_ ?_
  · simp [pow_two, add_mul, mul_add, MonoidAlgebra.single_mul_single, ← ofAdd_add,
      ← two_nsmul, ← mul_smul, ← mul_inv_rev, div_mul_div_comm, neg_div, smul_sub,
      MonoidAlgebra.one_def, -MonoidAlgebra.smul_single]
    module
  · ext <;> simp; norm_num
  · ext
    · simp [smul_add, tmul_add, add_tmul, smul_sub, neg_tmul, tmul_neg, ← smul_tmul', tmul_smul,
        smul_smul, div_mul_div_comm, Complex.I_mul_I, -MonoidAlgebra.smul_single]
      module
    · simp [smul_add, tmul_add, add_tmul, smul_sub, neg_tmul, tmul_neg, ← smul_tmul', tmul_smul,
        smul_smul, -MonoidAlgebra.smul_single]
      module

set_option backward.isDefEq.respectTransparency false in
attribute [-ext] AdjoinRoot.algHom_ext' in
/-- `SO2Ring ℂ` is isomorphic to the monoid algebra `ℂ[Multiplicative ℤ]`. -/
private def complexEquivMul : SO2Ring ℂ ≃ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative ℤ) where
  __ := complexEquivFun
  __ : SO2Ring ℂ ≃ₐ[ℂ] MonoidAlgebra ℂ (Multiplicative ℤ) := by
    refine .symm <| .ofAlgHom (AlgHomClass.toAlgHom complexEquivInv) complexEquivFun ?_ ?_
    · ext
      · simp [complexEquivInv_single, complexEquivFun]
        module
      simp [complexEquivFun, complexEquivInv_single, smul_smul, div_mul_eq_mul_div]
      module
    · refine MonoidAlgebra.algHom_ext' (MonoidHom.ext_mint ?_) (by ext)
      simp [complexEquivFun, complexEquivInv_single, smul_smul, smul_sub,
        ← mul_div_assoc, Complex.I_mul_I, -MonoidAlgebra.smul_single]
      module

/-- `SO2Ring ℂ` is isomorphic to Laurent series `ℂ[ℤ]`. -/
def complexEquiv : SO2Ring ℂ ≃ₐc[ℂ] ℂ[ℤ] :=
  complexEquivMul.trans (AddMonoidAlgebra.toMultiplicativeBialgEquiv ℂ ℂ ℤ).symm

@[simp high, nolint simpNF] lemma complexEquiv_inv_single (a : ℤ) (b : ℂ) :
    complexEquiv.symm (.single a b) = b • (T ^ a).1 := by
  change complexEquivMul.symm (AddMonoidAlgebra.toMultiplicativeBialgEquiv ℂ ℂ ℤ (.single a b)) = _
  rw [show AddMonoidAlgebra.toMultiplicativeBialgEquiv ℂ ℂ ℤ (.single a b) =
    .single (.ofAdd a) b from AddMonoidAlgebra.toMultiplicative_single ..]
  exact complexEquivInv_single (.ofAdd a) b

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma complexEquiv_inv_C (b : ℂ) :
    complexEquiv.symm (LaurentPolynomial.C b) = algebraMap ℂ (SO2Ring ℂ) b := by
  simp [LaurentPolynomial.C, -LaurentPolynomial.single_eq_C_mul_T, Algebra.algebraMap_eq_smul_one]

@[simp] lemma complexEquiv_symm_comp_algebraMap :
    .comp complexEquiv.symm (algebraMap ℂ ℂ[ℤ]) = algebraMap ℂ (SO2Ring ℂ) := by
  ext; simp [Algebra.algebraMap_eq_smul_one]

/-! #### `R`-points of `SO(2, R)` -/

open Matrix

attribute [-ext] AdjoinRoot.algHom_ext' in
/-- The isomorphism between the `R-algebra` homomorphisms from `SO2Ring(R)` to `S` and the group
  `SO(2,S)`. -/
def algHomMulEquiv : WithConv (SO2Ring R →ₐ[R] S) ≃* specialOrthogonalGroup (Fin 2) S where
  toFun f := ⟨!![f .X, f .Y; - f .Y, f .X], by
    simp [← map_mul, ← map_add, mem_specialOrthogonalGroup_fin_two_iff, pow_two]⟩
  invFun M := .toConv <| SO2Ring.liftₐ (M.1 0 0) (M.1 0 1)
    (mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.2
  left_inv f := by ext <;> simp
  right_inv M := by ext i j; fin_cases i, j <;>
    simp [(mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.1,
      (mem_specialOrthogonalGroup_fin_two_iff.mp M.2).1]
  map_mul' f g := by
    ext i j
    fin_cases i, j
    · simp [sub_eq_add_neg, AlgHom.convMul_apply]
    · simp [sub_eq_add_neg, AlgHom.convMul_apply]
    · simp [sub_eq_add_neg, AlgHom.convMul_apply]
    · simp [sub_eq_neg_add, AlgHom.convMul_apply]

/-! #### Base change -/

instance : Algebra S (S ⊗[R] SO2Ring R) := Algebra.TensorProduct.leftAlgebra

set_option backward.isDefEq.respectTransparency false in
variable (R S) in
/-- `SO2Ring` is invariant under base change of algebras. -/
def baseChangeAlgEquiv : S ⊗[R] SO2Ring R ≃ₐ[S] SO2Ring S :=
  (AdjoinRoot.tensorAlgEquiv _ _ rfl).trans <|
    AdjoinRoot.mapAlgEquiv (polyEquivTensor' _ _).symm _ _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma baseChangeAlgEquiv_X : (baseChangeAlgEquiv R S) (1 ⊗ₜ X) = X := by
  change (baseChangeAlgEquiv R S) (1 ⊗ₜ (AdjoinRoot.root _)) = AdjoinRoot.root _
  simp [baseChangeAlgEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma baseChangeAlgEquiv_Y : (baseChangeAlgEquiv R S) (1 ⊗ₜ «Y») = «Y» := by
  change (baseChangeAlgEquiv R S) (1 ⊗ₜ (AdjoinRoot.of _ _)) = AdjoinRoot.of _ _
  simp [baseChangeAlgEquiv]

set_option backward.isDefEq.respectTransparency false in
attribute [-ext] AdjoinRoot.algHom_ext' in
variable (R S) in
/-- `SO2Ring` is invariant under base change of bialgebras. -/
@[expose]
def baseChangeBialgEquiv : S ⊗[R] SO2Ring R ≃ₐc[S] SO2Ring S :=
  .ofAlgEquiv (baseChangeAlgEquiv R S) (by aesop) (by aesop (add simp [tmul_add, tmul_sub]))

@[simp]
lemma coe_baseChangeBialgEquiv : ⇑(baseChangeBialgEquiv R S) = baseChangeAlgEquiv R S := rfl

lemma baseChangeBialgEquiv_comp_algebraMap :
    .comp (baseChangeBialgEquiv R S) (Algebra.ofId S (S ⊗[R] SO2Ring R)) =
      Algebra.ofId S (SO2Ring S) := by ext

end SO2Ring

/-! ### `SO(2, R)` as a scheme -/

open AlgebraicGeometry CategoryTheory Limits SO2Ring
open scoped Hom

namespace AlgebraicGeometry.SO₂

open Scheme

/-- Notation for the special orghogonal group of 2x2 matrices as a scheme. -/
scoped notation3 "SO₂("R")" => Spec <| .of <| SO2Ring R

/-! #### `SO(2, ℂ)` is a split torus -/

/-- The isomorphism between `SO₂(ℂ)` and the 1-dimensional `ℂ`-torus. -/
@[expose]
def so₂ComplexIso : SO₂(ℂ) ≅ Diag (Spec <| .of ℂ) ℤ :=
  Scheme.Spec.mapIso complexEquiv.toAlgEquiv.toRingEquiv.toCommRingCatIso.symm.op ≪≫
    (diagSpecIso (.of ℂ) ℤ).symm

@[simp] lemma so₂ComplexIso_hom :
    so₂ComplexIso.hom =
      ((bialgSpec <| .of ℂ).map <| .op <| CommBialgCat.ofHom complexEquiv.symm.toBialgHom).hom.left
        ≫ (diagSpecIso (.of ℂ) ℤ).inv := rfl

@[simp] lemma so₂ComplexIso_inv :
    so₂ComplexIso.inv =
      (diagSpecIso (.of ℂ) ℤ).hom ≫
        ((bialgSpec <| .of ℂ).map <| .op <|
          CommBialgCat.ofHom complexEquiv.toBialgHom).hom.left := rfl

set_option backward.isDefEq.respectTransparency false in
instance : so₂ComplexIso.hom.IsOver <| Spec <| .of ℂ := by rw [so₂ComplexIso_hom]; infer_instance

lemma so₂ComplexIso_hom_asOver :
    so₂ComplexIso.hom.asOver (Spec <| .of ℂ) =
      ((bialgSpec <| .of ℂ).map <| .op <| CommBialgCat.ofHom complexEquiv.symm.toBialgHom).hom ≫
        (diagSpecIso (.of ℂ) ℤ).inv.asOver (Spec <| .of ℂ) := rfl

set_option backward.isDefEq.respectTransparency false in
instance : IsMonHom <| so₂ComplexIso.hom.asOver <| Spec <| .of ℂ := by
  rw [so₂ComplexIso_hom_asOver]; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : SO₂(ℂ).IsSplitTorusOver <| Spec <| .of ℂ := .of_iso so₂ComplexIso

/-! #### `SO(2, ℝ)` is a torus -/

/-- The isomorphism between the base change of `SO₂(ℝ)` to `ℂ` and `SO₂(ℂ)`. -/
@[expose]
def pullbackSO₂RealComplex :
    pullback (SO₂(ℝ) ↘ Spec (.of ℝ)) (Spec (.of ℂ) ↘ Spec (.of ℝ)) ≅ SO₂(ℂ) :=
  pullbackSymmetry .. ≪≫ pullbackSpecIso .. ≪≫ Scheme.Spec.mapIso
    (baseChangeBialgEquiv ℝ ℂ).symm.toAlgEquiv.toRingEquiv.toCommRingCatIso.op

@[simp] lemma pullbackSO₂RealComplex_hom :
    pullbackSO₂RealComplex.hom = (pullbackSymmetry .. ≪≫ pullbackSpecIso' ℝ ℂ (SO2Ring ℝ)).hom ≫
      ((bialgSpec <| .of ℂ).map <| .op <|
        CommBialgCat.ofHom (baseChangeBialgEquiv ℝ ℂ).symm.toBialgHom).hom.left := rfl

set_option backward.isDefEq.respectTransparency false in
instance : pullbackSO₂RealComplex.hom.IsOver <| Spec <| .of ℂ := by
  rw [pullbackSO₂RealComplex_hom]; infer_instance

lemma pullbackSO₂RealComplex_hom_asOver :
    pullbackSO₂RealComplex.hom.asOver (Spec <| .of ℂ) =
      (pullbackSymmetry .. ≪≫ pullbackSpecIso' ℝ ℂ (SO2Ring ℝ)).hom.asOver (Spec <| .of ℂ) ≫
        ((bialgSpec <| .of ℂ).map <| .op <|
          CommBialgCat.ofHom (baseChangeBialgEquiv ℝ ℂ).symm.toBialgHom).hom := rfl

set_option backward.isDefEq.respectTransparency false in
instance : IsMonHom <| pullbackSO₂RealComplex.hom.asOver (Spec <| .of ℂ) := by
  rw [pullbackSO₂RealComplex_hom_asOver]; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance pullback_SO₂_real_isSplitTorusOver_complex :
    (pullback (SO₂(ℝ) ↘ Spec (.of ℝ)) (Spec (.of ℂ) ↘ Spec (.of ℝ))).IsSplitTorusOver <|
      Spec <| .of ℂ :=
  .of_iso pullbackSO₂RealComplex

/-- `SO(2)` is a torus over the reals. -/
instance : (Spec <| .of <| SO2Ring ℝ).IsTorusOver ℝ where
  existsSplit :=
    ⟨ℂ, inferInstance, inferInstance, inferInstance, pullback_SO₂_real_isSplitTorusOver_complex⟩

/-! #### `SO(2, ℝ)` is not split -/

open Matrix

variable (R) in
/-- The `R`-points of `SO₂(R)` as a group `R`-scheme are isomorphic to the group `SO(2, R)`. -/
def pointsMulEquiv :
    ((Spec <| .of R).asOver (Spec <| .of R) ⟶ SO₂(R).asOver (Spec <| .of R)) ≃*
       specialOrthogonalGroup (Fin 2) R :=
  Spec.mapMulEquiv.symm.trans algHomMulEquiv

/-- A 4-torsion element of `SO(2, ℝ)`. -/
def I : specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![0, 1; -1, 0], by simp [mem_specialOrthogonalGroup_fin_two_iff]⟩

lemma I_sq_ne_1 : I ^ 2 ≠ 1 := by
  intro h
  have := congr_fun₂ congr(($h).val) 0 0
  norm_num [I, pow_two] at this

@[simp] lemma I_ord_4' : I ^ 4 = 1 := by simp [I, pow_succ, one_fin_two]

private lemma aux1 {x : ℝ} : x ^ 4 = 1 ↔ x ^ 2 = 1 := by
  simpa [← pow_mul] using sq_eq_sq₀ (sq_nonneg x) zero_le_one

private lemma aux2 {σ : Type*} {x : σ → ℝˣ} : x ^ 4 = 1 → x ^ 2 = 1 := by
  simp [aux1, funext_iff, ← Units.val_eq_one]

private lemma aux3 (σ : Type*) : IsEmpty <| specialOrthogonalGroup (Fin 2) ℝ ≃* (σ → ℝˣ) := by
  constructor
  intro e
  have h₁ : e I ^ 4 = 1 := by simp [← map_pow]
  have h₂ : e I ^ 2 ≠ 1 := by
    rw [← map_pow, ← e.map_one, e.injective.ne_iff]
    exact I_sq_ne_1
  exact h₂ <| aux2 h₁

open scoped AddMonoidAlgebra

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `SO(2)` is not a split torus over the real numbers. -/
theorem not_isSplitTorusOver_SO₂_real : ¬ SO₂(ℝ).IsSplitTorusOver (Spec <| .of ℝ) := by
  intro
  obtain ⟨σ, _, e, _, _⟩ := exists_iso_diag_finite_of_isSplitTorusOver_locallyOfFiniteType SO₂(ℝ) <|
    Spec <| .of ℝ
  have : (e ≪≫ diagSpecIso _ ℤ[σ]).hom.IsOver (Spec <| .of ℝ) := by dsimp; infer_instance
  have : IsMonHom ((e ≪≫ diagSpecIso _ ℤ[σ]).asOver <| Spec <| .of ℝ).hom := by
    dsimp; infer_instance
  have e₁ := Hom.mulEquivCongrRight ((e ≪≫ diagSpecIso _ ℤ[σ]).asOver <| Spec <| .of ℝ)
    ((Spec <| .of ℝ).asOver <| Spec <| .of ℝ)
  have e₂ : (ℤ[σ] →+ Additive ℝˣ) ≃+ (σ → Additive ℝˣ) :=
    AddMonoidAlgebra.coeffAddEquiv.addMonoidHomCongrLeft.trans <| Finsupp.liftAddHom.symm.trans <|
      .piCongrRight («η» := σ) fun _ ↦ (zmultiplesAddHom <| Additive ℝˣ).symm
  exact (aux3 σ).1 <| (pointsMulEquiv ℝ).symm.trans <| e₁.trans <| Spec.mapMulEquiv.symm.trans <|
    (AddMonoidAlgebra.liftMulEquiv ℝ ℝ ℤ[σ]).symm.trans <| MonoidHom.toHomUnitsMulEquiv.trans <|
      MonoidHom.toAdditiveRightMulEquiv.trans <| e₂.toMultiplicative.trans <| .refl _

end AlgebraicGeometry.SO₂
