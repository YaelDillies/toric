/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Toric.Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Convolution product on Hopf algebra maps

This file constructs the ring structure on bialgebra homs `C → A` where `C` and `A` are Hopf
algebras and multiplication is given by
```
         |
         μ
|   |   / \
f * g = f g
|   |   \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.
-/

@[expose] public section

suppress_compilation

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R A C : Type*} [CommSemiring R]

namespace HopfAlgebra
section Semiring
variable [Semiring A] [HopfAlgebra R A]

lemma antipode_comp_mul_comp_comm :
    antipode R ∘ₗ .mul' R A ∘ₗ (TensorProduct.comm R A A).toLinearMap =
      .mul' R A ∘ₗ map (antipode R) (antipode R) := by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv <| LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A) <;>
    ext a b
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R b).mul (ℛ R a)),
      ← Finset.map_swap_product (ℛ R b).index (ℛ R a).index]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply,
      ← Finset.map_swap_product (ℛ R a).index (ℛ R b).index,
      Finset.sum_product (ℛ R b).index, ← Finset.mul_sum, mul_assoc ((ℛ R b).left _),
      ← mul_assoc ((ℛ R a).left _), ← Finset.sum_mul, sum_mul_antipode_eq_algebraMap_counit,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).left_comm,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).eq]

lemma antipode_mul_antidistrib (a b : A) : antipode R (a * b) = antipode R b * antipode R a := by
  exact congr($antipode_comp_mul_comp_comm (b ⊗ₜ a))

variable (R A) in
@[simps!]
def antipodeAlgHomOp : A →ₐ[R] Aᵐᵒᵖ := .ofLinearMap
    ((MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ antipode R)
    (MulOpposite.op_injective (by simp))
    (fun x y ↦ MulOpposite.op_injective (by simp [antipode_mul_antidistrib]))

end Semiring

variable [CommSemiring A] [HopfAlgebra R A]

lemma antipode_mul_distrib (a b : A) : antipode R (a * b) = antipode R a * antipode R b := by
  rw [antipode_mul_antidistrib, mul_comm]

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an algebra hom. -/
@[simps!]
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap (antipode R) antipode_one antipode_mul_distrib

@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode R := rfl

end HopfAlgebra

namespace LinearMap

local notation "η" => Algebra.linearMap R A
local notation "ε" => counit (R := R) (A := C)
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

variable [Semiring C] [HopfAlgebra R C]

@[simp] lemma antipode_mul_id : toConv (antipode R (A := C)) * toConv id = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_antipode_mul_eq_algebraMap_counit (ℛ R c)]

@[simp] lemma id_mul_antipode : toConv id * toConv (antipode R (A := C)) = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_mul_antipode_eq_algebraMap_counit (ℛ R c)]

end LinearMap

namespace LinearMap
variable [Semiring C] [HopfAlgebra R C]

local notation "ε₁" => counit (R := R) (A := C)
local notation "ε₂" => counit (R := R) (A := C ⊗[R] C)
local notation "μ₁" => LinearMap.mul' R C
local notation "μ₂" => LinearMap.mul' R (C ⊗[R] C)
local notation "δ₁" => comul (R := R) (A := C)
local notation "δ₂" => comul (R := R) (A := C ⊗[R] C)
local notation "η₁" => Algebra.linearMap R C
local notation "η₂" => Algebra.linearMap R (C ⊗[R] C)
local infix:90 " ◁ " => LinearMap.lTensor
local notation:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local notation "α" => TensorProduct.assoc R
local notation "β" => TensorProduct.comm R
local notation "𝑺" => antipode R (A := C)
local notation "𝑭" => δ₁ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 ⊗ₘ 𝑺) ∘ₗ (β C C) ∘ₗ δ₁

lemma comul_right_inv : toConv δ₁ * toConv 𝑭 = 1 := by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  calc μ₂ ∘ₗ map δ₁ (δ₁ ∘ₗ 𝑺) ∘ₗ δ₁
      = μ₂ ∘ₗ ((δ₁ ∘ₗ id) ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁ := rfl
    _ = μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
        simp only [_root_.TensorProduct.map_comp, comp_assoc]
    _ = δ₁ ∘ₗ μ₁ ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
        have : μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) = δ₁ ∘ₗ μ₁ := by ext; simp
        simp [this, ← comp_assoc]
    _ = δ₁ ∘ₗ (toConv id * toConv 𝑺).ofConv := by simp [LinearMap.convMul_def]
    _ = δ₁ ∘ₗ (1 : WithConv (C →ₗ[R] C)).ofConv := by rw [id_mul_antipode]
    _ = Algebra.linearMap R (C ⊗[R] C) ∘ₗ ε₁ := by
        simp [LinearMap.convOne_def, show δ₁ ∘ₗ η₁ = η₂ from by ext; simp; rfl, ← comp_assoc]

end LinearMap

namespace AlgHom
variable [CommSemiring A] [CommSemiring C] [Bialgebra R C] [HopfAlgebra R A]

instance convInv : Inv (WithConv <| A →ₐ[R] C) where
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)

instance convGroup : Group (WithConv <| A →ₐ[R] C) where
  inv_mul_cancel f := by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
    trans toConv <| ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] C)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

instance [IsCocomm R A] : CommGroup (WithConv <| A →ₐ[R] C) where

lemma antipode_id_cancel :
    toConv (HopfAlgebra.antipodeAlgHom R A) * toConv (AlgHom.id R A) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  simp [LinearMap.antipode_mul_id]

lemma counitAlgHom_comp_antipodeAlgHom :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective <| by simp

private lemma inv_convMul_cancel (f : WithConv <| C →ₐc[R] A) :
    (toConv (.comp (antipodeAlgHom R A) f.ofConv) * toConv f.ofConv.toAlgHom) = 1 := calc
  _ = toConv (.comp (HopfAlgebra.antipodeAlgHom R A) f.ofConv : C →ₐ[R] A) *
        toConv (.comp (.id R A) f.ofConv) := by simp
  _ = toConv (.comp (lmul' R) (.comp (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A)
       (.id R A)) <| .comp (Algebra.TensorProduct.map f.ofConv f.ofConv) (comulAlgHom R C))) := by
    rw [convMul_def, Algebra.TensorProduct.map_comp]
    simp only [comp_assoc]
  _ = toConv ((toConv (antipodeAlgHom R A) * toConv (AlgHom.id R A)).ofConv.comp f.ofConv) := by
    simp only [convMul_def, BialgHom.map_comp_comulAlgHom]
    simp only [comp_assoc]
  _ = _ := by simp [antipode_id_cancel, convOne_def, comp_assoc]

end AlgHom

section HopfAlgebra

section Semiring

variable [Semiring A] [Semiring C] [HopfAlgebra R A] [HopfAlgebra R C]

@[coassoc_simps] --todo : add the assoc version
lemma HopfAlgebra.mul_antipode_rTensor_comul'.{u, v} {R : Type u} {A : Type v}
    {_ : CommSemiring R} {_ : Semiring A} [self : HopfAlgebra R A] :
    LinearMap.mul' R A ∘ₗ TensorProduct.map (HopfAlgebraStruct.antipode R) .id ∘ₗ
      CoalgebraStruct.comul = Algebra.linearMap R A ∘ₗ CoalgebraStruct.counit :=
  HopfAlgebra.mul_antipode_rTensor_comul ..

@[coassoc_simps] --todo : add the assoc version
lemma HopfAlgebra.mul_antipode_lTensor_comul'.{u, v} {R : Type u} {A : Type v}
    {_ : CommSemiring R} {_ : Semiring A} [self : HopfAlgebra R A] :
    LinearMap.mul' R A ∘ₗ TensorProduct.map .id (HopfAlgebraStruct.antipode R) ∘ₗ
      CoalgebraStruct.comul = Algebra.linearMap R A ∘ₗ CoalgebraStruct.counit :=
  HopfAlgebra.mul_antipode_lTensor_comul ..

lemma Algebra.linearMap_tensorProduct {R A B : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] :
    Algebra.linearMap R (A ⊗[R] B) = (Algebra.linearMap R A ⊗ₘ Algebra.linearMap R B) ∘ₗ
      (_root_.TensorProduct.lid _ _).symm.toLinearMap := by
  ext
  simp

lemma Bialgebra.mul'_comp_map_comul_comul {R C : Type*} [CommSemiring R]
    [Semiring C] [Bialgebra R C] :
    LinearMap.mul' R (C ⊗[R] C) ∘ₗ (δ ⊗ₘ δ) = δ ∘ₗ LinearMap.mul' R C := by
  ext; simp

lemma map_antipode_antipode_comp_comul' :
    (TensorProduct.comm R C C).toLinearMap ∘ₗ (antipode R ⊗ₘ antipode R) ∘ₗ δ =
      δ ∘ₗ antipode R := by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv <| comul (R := R) (A := C))
  · trans toConv ((Algebra.linearMap R C ⊗ₘ LinearMap.mul' R C ∘ₗ (antipode R ⊗ₘ LinearMap.id)) ∘ₗ
      (TensorProduct.assoc R R C C).toLinearMap ∘ₗ
      ((TensorProduct.comm R C R).toLinearMap ∘ₗ (.id ⊗ₘ ε) ∘ₗ δ ⊗ₘ LinearMap.id) ∘ₗ δ)
    · simp only [coassoc_simps, LinearMap.mul'_tensor, LinearMap.convMul_def]
    · simp only [coassoc_simps, LinearMap.convOne_def, Algebra.linearMap_tensorProduct]
  · trans toConv ((LinearMap.mul' R (C ⊗[R] C) ∘ₗ (δ ⊗ₘ δ)) ∘ₗ (.id ⊗ₘ antipode R) ∘ₗ δ)
    · simp [LinearMap.convMul_def, coassoc_simps]
    trans (δ ∘ₗ Algebra.linearMap R C) ∘ₗ ε
    · rw [Bialgebra.mul'_comp_map_comul_comul]
      simp [coassoc_simps]
    · congr
      ext
      simp [TensorProduct.one_def]

open MulOpposite

lemma map_antipode_antipode_comp_comul : (antipode R ⊗ₘ antipode R) ∘ₗ δ =
    (TensorProduct.comm R C C).toLinearMap ∘ₗ δ ∘ₗ antipode R := by
  rw [← map_antipode_antipode_comp_comul']
  simp [coassoc_simps]

/-- The antipode as a coalgebra hom. -/
def antipodeCoalgHom [IsCocomm R C] : C →ₗc[R] C where
  __ := antipode R
  map_smul' := _
  counit_comp := counit_comp_antipode
  map_comp_comul := by
    dsimp
    rw [map_antipode_antipode_comp_comul, ← LinearMap.comp_assoc, comm_comp_comul]

lemma LinearMap.algHom_comp_convOne
    {R A B C : Type*} [CommSemiring R] [AddCommMonoid A] [Semiring B] [Semiring C]
    [Module R A] [Coalgebra R A] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) :
    f.toLinearMap.comp (1 : WithConv <| A →ₗ[R] B).ofConv = (1 : WithConv <| A →ₗ[R] C).ofConv := by
  ext
  exact (f : B →ₐ[R] C).commutes _

lemma LinearMap.convOne_comp_coalgHom
    {R A B C : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Semiring C]
    [Module R A] [Coalgebra R A] [Module R B] [Coalgebra R B]
    [Algebra R C] (f : A →ₗc[R] B) :
    (1 : WithConv <| B →ₗ[R] C).ofConv.comp f.toLinearMap = (1 : WithConv <| A →ₗ[R] C).ofConv := by
  ext
  exact congr(algebraMap R C ($(f.counit_comp) _))

lemma BialgHom.comp_antipode (f : A →ₐc[R] C) :
    f.toLinearMap.comp (antipode R) = (antipode R).comp f.toLinearMap := by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv f.toLinearMap)
  · refine (LinearMap.algHom_comp_convMul_distrib (f : A →ₐ[R] C) (antipode R) .id).symm.trans ?_
    rw [LinearMap.antipode_mul_id, LinearMap.algHom_comp_convOne]
  · refine (LinearMap.convMul_comp_coalgHom_distrib .id (antipode R) f.toCoalgHom).symm.trans ?_
    rw [LinearMap.id_mul_antipode, LinearMap.convOne_comp_coalgHom]

end Semiring
section CommSemiring

variable [CommSemiring A] [CommSemiring C] [HopfAlgebra R A] [HopfAlgebra R C]

/-- The antipode as a coalgebra hom. -/
def antipodeBialgHom : C →ₐc[R] C where
  __ := antipodeAlgHom R C
  map_smul' := _
  counit_comp := counit_comp_antipode
  map_comp_comul := by
    dsimp
    rw [map_antipode_antipode_comp_comul, ← LinearMap.comp_assoc, comm_comp_comul]

instance [IsCocomm R A] : Inv (C →ₐc[R] A) where inv := antipodeBialgHom.comp

instance [IsCocomm R C] : Inv (C →ₐc[R] A) where
  inv f := (f.comp (antipodeBialgHom)).copy (antipode R ∘ f) congr($(f.comp_antipode.symm))

lemma inv_def [IsCocomm R A] (f : C →ₐc[R] A) : f⁻¹ = antipodeBialgHom.comp f := rfl

@[simp] lemma inv_apply [IsCocomm R A] (f : C →ₐc[R] A) (c : C) : f⁻¹ c = antipode R (f c) := rfl

@[simp]
lemma toAlgHom_inv [IsCocomm R A] (f : C →ₐc[R] A) : (↑(f⁻¹) : C →ₐ[R] A) = (↑f)⁻¹ := by
  ext x
  exact congr($(f.comp_antipode) x).symm

@[simp]
lemma toAlgHom_inv' [IsCocomm R C] (f : C →ₐc[R] A) : (↑(f⁻¹) : C →ₐ[R] A) = (↑f)⁻¹ := by
  ext x
  exact congr($(f.comp_antipode) x).symm

instance [IsCocomm R C] : CommGroup (C →ₐc[R] A) where
  inv_mul_cancel f := by
    ext x
    simpa only [← toAlgHom_inv'] using congr($(inv_mul_cancel (f : C →ₐ[R] A)) x)

end CommSemiring

end HopfAlgebra
